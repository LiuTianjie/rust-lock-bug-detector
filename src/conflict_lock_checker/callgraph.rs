extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{BasicBlock, Body, Operand, TerminatorKind};
use rustc_middle::ty::TyKind;
use std::collections::HashMap;
pub struct Callgraph {
    // direct:HashMap<调用者ID,HashMap<调用发生的基本块，被调用者ID>>
    pub direct: HashMap<LocalDefId, HashMap<BasicBlock, LocalDefId>>,
}

impl Callgraph {
    pub fn new() -> Self {
        Self {
            direct: HashMap::new(),
        }
    }

    fn insert_direct(&mut self, caller: LocalDefId, bb: BasicBlock, callee: LocalDefId) {
        // 如果调用者已经存在于Callgraph中，直接将其插入到调用者对应的HashMap中
        if let Some(callees) = self.direct.get_mut(&caller) {
            callees.insert(bb, callee);
        } else {
            //如果调用者不存在于Callgraph中，则创建一个调用者HashMap，并将被调用者的基本块、ID等插入新建的调用者HashMap中
            // 最后将调用者插入Callgraph
            let mut callees: HashMap<BasicBlock, LocalDefId> = HashMap::new();
            callees.insert(bb, callee);
            self.direct.insert(caller, callees);
        }
    }

    pub fn generate(&mut self, caller: LocalDefId, body: &Body, crate_fn_ids: &[LocalDefId]) {
        for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
            let terminator = bb_data.terminator();
            // 对于每个bb，匹配termitor的kind，（不是每个bb的termitor都是函数/闭包调用？）
            if let TerminatorKind::Call { ref func, .. } = terminator.kind {
                if let Operand::Constant(box constant) = func {
                    match constant.literal.ty.kind {
                        TyKind::FnDef(callee_def_id, _) | TyKind::Closure(callee_def_id, _) => {
                            if let Some(local_callee_def_id) = callee_def_id.as_local() {
                                if crate_fn_ids.contains(&local_callee_def_id) {
                                    // callee_def_id是通过tcx.optimized_mir(*fn_id)查询后，经过一系列if let得到的
                                    self.insert_direct(caller, bb, local_callee_def_id);
                                } else {
                                    // dbg!("The fn/closure is not body owner");
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    pub fn get(&self, fn_id: &LocalDefId) -> Option<&HashMap<BasicBlock, LocalDefId>> {
        if let Some(callsites) = self.direct.get(fn_id) {
            if !callsites.is_empty() {
                return Some(callsites);
            } else {
                return None;
            }
        }
        None
    }

    pub fn _print(&self) {
        for (caller, callees) in &self.direct {
            println!("caller: {:?}", caller);
            for callee in callees {
                println!("\tcallee: {:?}", callee);
            }
        }
    }
}
