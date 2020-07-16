extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
use super::callgraph::Callgraph;
use super::collector::collect_lockguard_info;
use super::config::{CrateNameLists, CALLCHAIN_DEPTH};
use super::genkill::GenKill;
use super::lock::{ConflictLockInfo, LockGuardId, LockGuardInfo, LockGuardSrc};
use rustc_hir::def_id::{LocalDefId, LOCAL_CRATE};
use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;

struct FnLockContext {
    fn_id: LocalDefId,
    context: HashSet<LockGuardId>,
    callchain: Vec<(LocalDefId, BasicBlock)>,
}

impl FnLockContext {
    fn new(
        fn_id: LocalDefId,
        context: HashSet<LockGuardId>,
        callchain: Vec<(LocalDefId, BasicBlock)>,
    ) -> Self {
        Self {
            fn_id,
            context,
            callchain,
        }
    }
}
pub struct ConflictLockChecker {
    crate_name_lists: CrateNameLists,
    crate_lockguards: HashMap<LockGuardId, LockGuardInfo>,
    crate_callgraph: Callgraph,
    crate_lock_pairs: RefCell<Vec<ConflictLockInfo>>,
    crate_lockguard_pairs: RefCell<HashMap<(LockGuardId, LockGuardId), HashSet<Vec<Span>>>>,
}

impl ConflictLockChecker {
    pub fn new(is_white: bool, crate_name_lists: Vec<String>) -> Self {
        if is_white {
            Self {
                crate_name_lists: CrateNameLists::White(crate_name_lists),
                crate_lockguards: HashMap::new(),
                crate_callgraph: Callgraph::new(),
                crate_lock_pairs: RefCell::new(Vec::new()),
                crate_lockguard_pairs: RefCell::new(HashMap::new()),
            }
        } else {
            Self {
                crate_name_lists: CrateNameLists::Black(crate_name_lists),
                crate_lockguards: HashMap::new(),
                crate_callgraph: Callgraph::new(),
                crate_lock_pairs: RefCell::new(Vec::new()),
                crate_lockguard_pairs: RefCell::new(HashMap::new()),
            }
        }
    }
    pub fn check(&mut self, tcx: TyCtxt) {
        let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
        match &self.crate_name_lists {
            CrateNameLists::White(lists) => {
                if !lists.contains(&crate_name) {
                    return;
                }
            }
            CrateNameLists::Black(lists) => {
                if lists.contains(&crate_name) {
                    return;
                }
            }
        }
        // println!("{}", crate_name);
        // collect fn
        let ids = tcx.mir_keys(LOCAL_CRATE);
        let fn_ids: Vec<LocalDefId> = ids
            .clone()
            .into_iter()
            .filter(|id| {
                let hir = tcx.hir();
                hir.body_owner_kind(hir.as_local_hir_id(*id))
                    .is_fn_or_closure()
            })
            .collect();
        // println!("fn_ids: {:#?}", fn_ids);
        // collect lockguard_info
        let lockguards: HashMap<LocalDefId, HashMap<LockGuardId, LockGuardInfo>> = fn_ids
            .clone()
            .into_iter()
            .filter_map(|fn_id| {
                let body = tcx.optimized_mir(fn_id);
                let lockguards = collect_lockguard_info(fn_id, body);
                if lockguards.is_empty() {
                    None
                } else {
                    Some((fn_id, lockguards))
                }
            })
            .collect();
        if lockguards.is_empty() {
            return;
        }
        for (_, info) in lockguards.iter() {
            self.crate_lockguards.extend(info.clone().into_iter());
        }
        println!(
            "fn with locks: {}, lockguards num: {}, local fn num: {}",
            lockguards.len(),
            self.crate_lockguards.len(),
            fn_ids.len()
        );
        // generate callgraph
        for fn_id in &fn_ids {
            self.crate_callgraph
                .generate(*fn_id, tcx.optimized_mir(*fn_id), &fn_ids);
        }
        // self.crate_callgraph.print();
        for (fn_id, _) in lockguards.iter() {
            // self.check_entry_fn(&tcx, *fn_id);
            self.check_entry_fn2(&tcx, *fn_id);
        }
    }

    fn check_entry_fn2(&mut self, tcx: &TyCtxt, fn_id: LocalDefId) {
        let context: HashSet<LockGuardId> = HashSet::new();
        let callchain: Vec<(LocalDefId, BasicBlock)> = Vec::new();

        let mut worklist: Vec<FnLockContext> = Vec::new();
        // visited: fn_id is inserted at most twice (u8 is insertion times, must <= 2)
        let mut visited: HashMap<LocalDefId, u8> = HashMap::new();
        worklist.push(FnLockContext::new(fn_id, context, callchain));
        visited.insert(fn_id, 1);
        while let Some(FnLockContext {
            fn_id,
            context,
            callchain,
        }) = worklist.pop()
        {
            let body = tcx.optimized_mir(fn_id);
            let mut genkill = GenKill::new(fn_id, body, &self.crate_lockguards, &context);
            let lockguard_pairs = genkill.analyze(body);
            if !lockguard_pairs.is_empty() {
                // println!(
                //     "DoubleLockReport: {:#?}",
                //     double_lock_reports
                //         .iter()
                //         .map(|p| (p.0.span, p.1.span))
                //         .collect::<Vec<_>>()
                // );
                let callchain_reports = callchain
                    .iter()
                    .map(move |(fn_id, bb)| {
                        tcx.optimized_mir(*fn_id).basic_blocks()[*bb]
                            .terminator()
                            .source_info
                            .span
                    })
                    .collect::<Vec<Span>>();
                // println!("Callchain: {:#?}", callchain_reports);
                // for report in double_lock_reports {
                //     self.crate_doublelock_reports.borrow_mut().add(report, &callchain_reports);
                // }
                for lockguard_pair in lockguard_pairs {
                    self.crate_lockguard_pairs.borrow_mut().entry((lockguard_pair.first, lockguard_pair.second))
                    .or_insert(HashSet::new())
                    .insert(callchain_reports.clone());
                }
            }
            if let Some(callsites) = self.crate_callgraph.get(&fn_id) {
                for (bb, callee_id) in callsites {
                    if let Some(context) = genkill.get_live_lockguards(bb) {
                        let mut callchain = callchain.clone();
                        callchain.push((fn_id, *bb));
                        if let Some(times) = visited.get(callee_id) {
                            if *times == 1 {
                                visited.insert(*callee_id, 2);
                                worklist.push(FnLockContext::new(
                                    *callee_id,
                                    context.clone(),
                                    callchain,
                                ));
                            }
                        } else {
                            visited.insert(*callee_id, 1);
                            worklist.push(FnLockContext::new(
                                *callee_id,
                                context.clone(),
                                callchain,
                            ));
                        }
                    }
                }
            }
        }
        self.conflict();
    }

    fn conflict(&self) {
        // println!("{:#?}", self.crate_lockguard_pairs);
        let direct = self.crate_lockguard_pairs.borrow().iter().filter_map(|((first, second), _)| {
            if let (Some(first_lock), Some(second_lock)) = (self.crate_lockguards.get(first).unwrap().src.clone(),
            self.crate_lockguards.get(second).unwrap().src.clone()
            ) {
                if first_lock != second_lock {
                    Some((first_lock, second_lock))
                } else {
                    None
                }
            } else {
                None
            }
        }).collect::<HashSet<_>>();
        let mut direct_map: HashMap<LockGuardSrc, HashSet<LockGuardSrc>> = HashMap::new();
        for pair in direct {
            direct_map.entry(pair.0).or_insert(HashSet::new()).insert(pair.1);
        }
        let mut transitive_map: HashMap<LockGuardSrc, HashSet<LockGuardSrc>> = HashMap::new();
        for (first, _) in direct_map.iter() {
            let mut worklist: Vec<LockGuardSrc> = Vec::new();
            let mut visited: HashSet<LockGuardSrc> = HashSet::new();
            worklist.push(first.clone());
            visited.insert(first.clone());
            while let Some(curr) = worklist.pop() {
               if let Some(seconds) = direct_map.get(&curr) {
                   transitive_map.entry(curr).or_insert(HashSet::new()).extend(seconds.clone());
                   for second in seconds {
                       if !visited.contains(second) {
                           worklist.push(second.clone());
                           visited.insert(second.clone());
                       }
                   }
               }
            }
        }
        let conflict_lock_src: HashSet<(LockGuardSrc, LockGuardSrc)> = HashSet::new();
        for (first, seconds) in transitive_map.iter() {
            for second in seconds {
                if let Some(true) = transitive_map.get(second).and_then(|sec_seconds|Some(sec_seconds.contains(first))) {
                    println!("{:?}, {:?}", first, second);
                    conflict_lock_src.insert((first.clone(), second.clone()));
                }
            }
        }
        // find paths between locksrc_A -> ? -> locksrc_B
        let mut paths: HashSet<Vec<(LockGuardSrc, LockGuardSrc)>> = HashSet::new();
        for (first, second) in conflict_lock_src {
            let mut worklist: Vec<LockGuardSrc> = Vec::new();
            let mut visited: HashSet<LockGuardSrc> = HashSet::new();
            let mut backtrack: Vec<LockGuardSrc> = Vec::new();
            worklist.push(first.clone());
            visited.insert(first.clone());
            while let Some(curr) = worklist.pop() {
                if curr == second {
                    let mut path: Vec<(LockGuardSrc, LockGuardSrc)> = Vec::new();
                    for idx in 1..backtrack.len() {
                        path.push((backtrack[idx-1].clone(), backtrack[idx].clone()));
                    }
                    backtrack.clear();
                    paths.insert(path);
                }
               if let Some(seconds) = direct_map.get(&curr) {
                   transitive_map.entry(curr).or_insert(HashSet::new()).extend(seconds.clone());
                   for second in seconds {
                       if !visited.contains(second) {
                           worklist.push(second.clone());
                           visited.insert(second.clone());
                       }
                   }
               }
            }
        }
        
    }

    fn check_entry_fn(&self, tcx: &TyCtxt, fn_id: LocalDefId) {
        type ConflictLockBugType<'a> = (
            (&'a LockGuardInfo, &'a LockGuardInfo),
            (&'a LockGuardInfo, &'a LockGuardInfo),
        );
        // println!("checking entry fn: {:?}", fn_id);
        let body = tcx.optimized_mir(fn_id);
        let context = HashSet::new();
        let mut genkill = GenKill::new(fn_id, body, &self.crate_lockguards, &context);
        let conflict_lock_pairs = genkill.analyze(body);

        let mut conflict_lock_bugs: Vec<ConflictLockBugType> = Vec::new();
        for lhs in conflict_lock_pairs.iter() {
            for rhs in conflict_lock_pairs.iter() {
                let lf = self.crate_lockguards.get(&lhs.first).unwrap();
                let ls = self.crate_lockguards.get(&lhs.second).unwrap();
                let rf = self.crate_lockguards.get(&rhs.first).unwrap();
                let rs = self.crate_lockguards.get(&rhs.second).unwrap();
                if *lf == *rs && *ls == *rf {
                    conflict_lock_bugs.push(((lf, ls), (rf, rs)));
                }
            }
        }
        for lhs in conflict_lock_pairs.iter() {
            for rhs in self.crate_lock_pairs.borrow().iter() {
                let lf = self.crate_lockguards.get(&lhs.first).unwrap();
                let ls = self.crate_lockguards.get(&lhs.second).unwrap();
                let rf = self.crate_lockguards.get(&rhs.first).unwrap();
                let rs = self.crate_lockguards.get(&rhs.second).unwrap();
                if *lf == *rs && *ls == *rf {
                    conflict_lock_bugs.push(((lf, ls), (rf, rs)));
                }
            }
        }
        if !conflict_lock_bugs.is_empty() {
            println!("ConflictLockReport: {:#?}", conflict_lock_bugs);
        }
        self.crate_lock_pairs
            .borrow_mut()
            .extend(conflict_lock_pairs.into_iter());

        let mut callchain: Vec<(LocalDefId, BasicBlock)> = Vec::new();
        if let Some(callsites) = self.crate_callgraph.get(&fn_id) {
            for (bb, callee_id) in callsites {
                if let Some(context) = genkill.get_live_lockguards(bb) {
                    callchain.push((fn_id, *bb));
                    self.check_fn(&tcx, *callee_id, context, &mut callchain);
                    callchain.pop();
                }
            }
        }
    }

    fn check_fn(
        &self,
        tcx: &TyCtxt,
        fn_id: LocalDefId,
        context: &HashSet<LockGuardId>,
        callchain: &mut Vec<(LocalDefId, BasicBlock)>,
    ) {
        type ConflictLockBugType<'a> = (
            (&'a LockGuardInfo, &'a LockGuardInfo),
            (&'a LockGuardInfo, &'a LockGuardInfo),
        );
        if callchain.len() > CALLCHAIN_DEPTH {
            return;
        }
        // println!("checking fn: {:?}", fn_id);
        let body = tcx.optimized_mir(fn_id);
        let mut genkill = GenKill::new(fn_id, body, &self.crate_lockguards, context);
        let conflict_lock_pairs = genkill.analyze(body);
        let mut conflict_lock_bugs: Vec<ConflictLockBugType> = Vec::new();
        for lhs in conflict_lock_pairs.iter() {
            for rhs in conflict_lock_pairs.iter() {
                let lf = self.crate_lockguards.get(&lhs.first).unwrap();
                let ls = self.crate_lockguards.get(&lhs.second).unwrap();
                let rf = self.crate_lockguards.get(&rhs.first).unwrap();
                let rs = self.crate_lockguards.get(&rhs.second).unwrap();
                if *lf == *rs && *ls == *rf {
                    conflict_lock_bugs.push(((lf, ls), (rf, rs)));
                }
            }
        }
        for lhs in conflict_lock_pairs.iter() {
            for rhs in self.crate_lock_pairs.borrow().iter() {
                let lf = self.crate_lockguards.get(&lhs.first).unwrap();
                let ls = self.crate_lockguards.get(&lhs.second).unwrap();
                let rf = self.crate_lockguards.get(&rhs.first).unwrap();
                let rs = self.crate_lockguards.get(&rhs.second).unwrap();
                if *lf == *rs && *ls == *rf {
                    conflict_lock_bugs.push(((lf, ls), (rf, rs)));
                }
            }
        }
        if !conflict_lock_bugs.is_empty() {
            println!("ConflictLockReport: {:#?}", conflict_lock_bugs);
            let callchain_reports = callchain
                .iter()
                .map(move |(fn_id, bb)| {
                    tcx.optimized_mir(*fn_id).basic_blocks()[*bb]
                        .terminator()
                        .source_info
                        .span
                })
                .collect::<Vec<Span>>();
            println!("{:#?}", callchain_reports);
        }

        self.crate_lock_pairs
            .borrow_mut()
            .extend(conflict_lock_pairs.into_iter());

        if let Some(callsites) = self.crate_callgraph.get(&fn_id) {
            for (bb, callee_id) in callsites {
                if let Some(context) = genkill.get_live_lockguards(bb) {
                    callchain.push((fn_id, *bb));
                    self.check_fn(tcx, *callee_id, context, callchain);
                    callchain.pop();
                }
            }
        }
    }
}
