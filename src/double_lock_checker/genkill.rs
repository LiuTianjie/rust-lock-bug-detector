extern crate rustc_hir;
extern crate rustc_middle;

use super::config::RUN_LIMIT;
use super::lock::DoubleLockInfo;
use super::lock::{LockGuardId, LockGuardInfo};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{BasicBlock, Body, START_BLOCK};
use std::collections::HashMap;
use std::collections::HashSet;
pub struct GenKill<'a> {
    gen: HashMap<BasicBlock, HashSet<LockGuardId>>,
    kill: HashMap<BasicBlock, HashSet<LockGuardId>>,
    //before中存储的进入bb前的lockguardInfo
    before: HashMap<BasicBlock, HashSet<LockGuardId>>,
    //after中存储的是出去bb后的lockguardInfo
    after: HashMap<BasicBlock, HashSet<LockGuardId>>,
    worklist: Vec<BasicBlock>,
    crate_lockguards: &'a HashMap<LockGuardId, LockGuardInfo>,
}

impl<'a> GenKill<'a> {
    //其实这个new方法就是把lockguardInfo里面的关于gen，kill基本块的信息提取出来存到GenKill的实例对象中
    pub fn new(
        fn_id: LocalDefId,
        body: &Body,
        crate_lockguards: &'a HashMap<LockGuardId, LockGuardInfo>,
        context: &HashSet<LockGuardId>,
    ) -> GenKill<'a> {
        let mut gen: HashMap<BasicBlock, HashSet<LockGuardId>> = HashMap::new();
        let mut kill: HashMap<BasicBlock, HashSet<LockGuardId>> = HashMap::new();
        let mut before: HashMap<BasicBlock, HashSet<LockGuardId>> = HashMap::new();
        let mut after: HashMap<BasicBlock, HashSet<LockGuardId>> = HashMap::new();
        let mut worklist = Vec::new();
        for (id, lockguard) in crate_lockguards.iter() {
            if id.fn_id != fn_id {
                continue;
            }
            for bb in lockguard.gen_bbs.iter() {
                gen.entry(*bb).or_insert_with(HashSet::new).insert(*id);
            }
            for bb in lockguard.kill_bbs.iter() {
                kill.entry(*bb).or_insert_with(HashSet::new).insert(*id);
            }
        }
        // worklist存储的是从body中查询到的basicblocks,
        // gen,kill都是从之前收集到的lockguardInfo里面收集到的
        for (bb, _) in body.basic_blocks().iter_eumerated() {
            before.insert(bb, HashSet::new());
            after.insert(bb, HashSet::new());
            worklist.push(bb);
        }
        if let Some(v) = before.get_mut(&START_BLOCK) {
            *v = context.clone();
        }
        Self {
            gen,
            kill,
            before,
            after,
            worklist,
            crate_lockguards,
        }
    }
    pub fn analyze(&mut self, body: &Body) -> Vec<DoubleLockInfo> {
        let mut double_lock_bugs: Vec<DoubleLockInfo> = Vec::new();
        let mut count: u32 = 0;
        while !self.worklist.is_empty() && count <= RUN_LIMIT {
            count += 1;
            // worklist中存储的是BasicBlock，是一个对u32的封装，表示了其索引
            let cur = self.worklist.pop().unwrap();
            let mut new_before: HashSet<LockGuardId> = HashSet::new();
            // copy after[prev] to new_before
            // body.predecessors()返回body中所有基本块的前驱节点：IndecVec<BasicBlock,BasicBlockData>
            //body.predecessorr()[cur]:在所有前驱节点中查询当前worklist中的basicblock的前驱节点
            let prevs = &body.predecessors()[cur];
            if !prevs.is_empty() {
                for prev in prevs {
                    // 对于每一个前驱节点，将其after(出节点后的LockGuardInfo，前驱节点的after就是当前节点的bfore)
                    //将其加入到newbefore里面
                    new_before.extend(self.after[prev].clone().into_iter());
                    //更新当前节点的before
                    self.before
                        .get_mut(&cur)
                        .unwrap()
                        .extend(new_before.clone().into_iter());
                }
            //更新完所有bb的before
            } else {
                // 如果当前节点没有前驱节点，则直接将当前节点的before视作newbefore
                new_before.extend(self.before[&cur].clone().into_iter());
            }
            // first kill, then gen
            if let Some(lockguards) = self.kill.get(&cur) {
                self.kill_kill_set(&mut new_before, lockguards);
            }
            if let Some(lockguards) = self.gen.get(&cur) {
                let double_locks = self.union_gen_set(&mut new_before, lockguards);
                double_lock_bugs.extend(double_locks.into_iter());
            }
            if !self.compare_lockguards(&new_before, &self.after[&cur]) {
                // 如果newbefore和after的数量lockguard不一致，或者数量一致但内容不同，
                // 则将当前节点的后继节点加入worklist，继续以上操作
                self.after.insert(cur, new_before);
                self.worklist
                    .extend(body.basic_blocks()[cur].terminator().successors().clone());
            }
        }
        double_lock_bugs
    }

    pub fn get_live_lockguards(&self, bb: &BasicBlock) -> Option<&HashSet<LockGuardId>> {
        if let Some(context) = self.before.get(bb) {
            if !context.is_empty() {
                return Some(context);
            } else {
                return None;
            }
        }
        None
    }
    fn union_gen_set(
        &self,
        new_before: &mut HashSet<LockGuardId>,
        lockguards: &HashSet<LockGuardId>,
    ) -> Vec<DoubleLockInfo> {
        let mut double_locks: Vec<DoubleLockInfo> = Vec::new();
        for first in new_before.iter() {
            for second in lockguards.iter() {
                if self
                    .crate_lockguards
                    .get(first)
                    .unwrap()
                    .deadlock_with(self.crate_lockguards.get(second).unwrap())
                {
                    //如果形成死锁，则将其加入double_lock
                    double_locks.push(DoubleLockInfo {
                        first: *first,
                        second: *second,
                    });
                }
            }
        }
        new_before.extend(lockguards.clone().into_iter());
        double_locks
    }

    fn kill_kill_set(
        &self,
        new_before: &mut HashSet<LockGuardId>,
        lockguards: &HashSet<LockGuardId>,
    ) {
        // 对于newbore中的每一个lockguard，使其与lockguards中的每一个进行比较，如果存在一个相同就返回false，
        // 即将其从newbefore中移除
        new_before.retain(move |b| {
            let b = self.crate_lockguards.get(b).unwrap();
            if lockguards
                .iter()
                .map(move |k| self.crate_lockguards.get(k).unwrap())
                .any(|e| *e == *b)
            {
                return false;
            }
            true
        });
    }

    fn compare_lockguards(&self, lhs: &HashSet<LockGuardId>, rhs: &HashSet<LockGuardId>) -> bool {
        if lhs.len() != rhs.len() {
            return false;
        }
        // 如果左边和右边数量相同，则判断内容是否相同，是则返回true
        let rhs_info = rhs
            .iter()
            .map(|r| self.crate_lockguards.get(r).unwrap())
            .collect::<Vec<_>>();
        lhs.iter()
            .map(move |l| self.crate_lockguards.get(l).unwrap())
            .all(move |li| rhs_info.contains(&li))
    }
}
