/*
for fn in crate.fns:
    atomic.load and atomic.store and (not atomic.CAS) in fn.callees?
    first arg of atomic.load/store alias?
    return of atomic.load -> Eq -> switchInt -> bb -> atomic.store
    or return of atomic.load == second arg of atomic.store
*/
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_span;
// use super::callgraph::Callgraph;
use super::config::{CrateNameLists, CALLCHAIN_DEPTH};
// use super::genkill::GenKill;
// use super::lock::{DoubleLockInfo, LockGuardId, LockGuardInfo};
// use super::report::DoubleLockReports;
use rustc_hir::def_id::{LocalDefId, LOCAL_CRATE};
use rustc_middle::mir::visit::*;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::*;
use rustc_mir::util::def_use::DefUseAnalysis;
use rustc_span::Span;

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
// struct FnLockContext {
//     fn_id: LocalDefId,
//     context: HashSet<LockGuardId>,
//     callchain: Vec<(LocalDefId, BasicBlock)>,
// }
//
// impl FnLockContext {
//     fn new(
//         fn_id: LocalDefId,
//         context: HashSet<LockGuardId>,
//         callchain: Vec<(LocalDefId, BasicBlock)>,
//     ) -> Self {
//         Self {
//             fn_id,
//             context,
//             callchain,
//         }
//     }
// }
pub struct AtomicityViolationAtomicChecker {
    crate_name_lists: CrateNameLists,
    // crate_callgraph: Callgraph,
    // crate_doublelock_reports: RefCell<DoubleLockReports>,
}

impl AtomicityViolationAtomicChecker {
    pub fn new(is_white: bool, crate_name_lists: Vec<String>) -> Self {
        if is_white {
            Self {
                crate_name_lists: CrateNameLists::White(crate_name_lists),
                // crate_lockguards: HashMap::new(),
                // crate_callgraph: Callgraph::new(),
                // crate_doublelock_reports: RefCell::new(DoubleLockReports::new()),
            }
        } else {
            Self {
                crate_name_lists: CrateNameLists::Black(crate_name_lists),
                // crate_lockguards: HashMap::new(),
                // crate_callgraph: Callgraph::new(),
                // crate_doublelock_reports: RefCell::new(DoubleLockReports::new()),
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
        println!("{}", crate_name);
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
        for fn_id in fn_ids {
            println!("{:?}", fn_id);
            // intra-procedural analysis on load and store
            let mut atomic_info = HashMap::<Place, (HashSet<Location>, HashSet<Location>)>::new();
            let body = tcx.optimized_mir(fn_id);
            let mut def_use_analysis = DefUseAnalysis::new(body);
            def_use_analysis.analyze(body);
            for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
                let terminator = bb_data.terminator();
                if let TerminatorKind::Call {
                    ref func,
                    ref args,
                    ref destination,
                    ..
                } = terminator.kind
                {
                    if let Operand::Constant(box constant) = func {
                        match constant.literal.ty.kind {
                            TyKind::FnDef(callee_def_id, substs)
                            | TyKind::Closure(callee_def_id, substs) => {
                                // "const xxxx": [6:] to remove the const
                                match parse_atomic_func(&format!("{:?}", func)[6..]) {
                                    Some(AtomicOperator::Load) => match args[0] {
                                        Operand::Copy(place) | Operand::Move(place) => {
                                            println!("{:?}", func);
                                            println!("{:?}", args[0]);
                                            let res =
                                                trace_atomic_src(place, body, &def_use_analysis);
                                            println!("src: {:?}", res);
                                            if let Ok(src) = res {
                                                atomic_info
                                                    .entry(src)
                                                    .or_default()
                                                    .0
                                                    .insert(body.terminator_loc(bb));
                                            }
                                        }
                                        _ => {}
                                    },
                                    Some(AtomicOperator::Store) => match args[0] {
                                        Operand::Copy(place) | Operand::Move(place) => {
                                            println!("{:?}", func);
                                            println!("{:?}", args[0]);
                                            let res =
                                                trace_atomic_src(place, body, &def_use_analysis);
                                            println!("src: {:?}", res);
                                            if let Ok(src) = res {
                                                atomic_info
                                                    .entry(src)
                                                    .or_default()
                                                    .1
                                                    .insert(body.terminator_loc(bb));
                                            }
                                        }
                                        _ => {}
                                    },
                                    Some(AtomicOperator::New) => {}
                                    Some(AtomicOperator::CAS) => {}
                                    None => {}
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            //println!("{:#?}", atomic_info);
            for (_, pair) in atomic_info.iter() {
                for load in pair.0.iter() {
                    for store in pair.1.iter() {
                        let load_term = &body.basic_blocks()[load.block].terminator();
                        let store_term = &body.basic_blocks()[store.block].terminator();
                        if data_dependent(load_term, store_term, body, &def_use_analysis) {
                            println!("DP: {:?} data-depends on {:?}", load_term, store_term);
                        } else if control_dependent(load_term, store, body, &def_use_analysis) {
                            println!("CP: {:?} control-depend on {:?}", load_term, store_term);
                        } else {
                            println!("NP: {:?} not-depends on {:?}", load_term, store_term);
                        }
                    }
                }
            }
        }
    }
}

enum AtomicOperator {
    Load,
    Store,
    New,
    CAS,
}

fn is_deref_func(func_name: &str) -> bool {
    if func_name.ends_with("as std::ops::Deref>::deref") {
        true
    } else {
        false
    }
}

fn parse_atomic_func(func_name: &str) -> Option<AtomicOperator> {
    if !func_name.starts_with("std::sync::atomic::Atomic") {
        None
    } else {
        let atomic_operator = if func_name.ends_with("load") {
            AtomicOperator::Load
        } else if func_name.ends_with("store") {
            AtomicOperator::Store
        } else if func_name.ends_with("new") {
            AtomicOperator::New
        } else {
            AtomicOperator::CAS
        };
        Some(atomic_operator)
    }
}

fn parse_ref_atomic_type(place: Place, body: &Body) -> bool {
    let type_name = body.local_decls[place.local].ty.to_string();
    if type_name.starts_with("&std::sync::atomic::Atomic") {
        true
    } else {
        false
    }
}

fn parse_atomic_type(place: Place, body: &Body) -> bool {
    if place.projection.is_empty() {
        let type_name = body.local_decls[place.local].ty.to_string();
        if type_name.starts_with("std::sync::atomic::Atomic")
            || type_name.starts_with("std::sync::Arc<std::sync::atomic::Atomic")
        {
            return true;
        }
    } else {
        if let Some(ProjectionElem::Field(field, ty)) = place.projection.last() {
            let type_name = ty.to_string();
            if type_name.starts_with("std::sync::atomic::Atomic")
                || type_name.starts_with("std::sync::Arc<std::sync::atomic::Atomic")
            {
                return true;
            }
        }
    }
    false
}
/// (load|store|CAS)(RefAtomic)
/// 1. self field: Arc<Atomic>
/// RefAtomic = RefAtomic
/// RefAtomic = deref(RefArc<Atomic>)
/// RefArc<Atomic> = &((*self)).0
/// 2. self field: Atomic
/// RefAtomic = &((*self)).0
/// 3. local: Atomic
/// RefAtomic = &Atomic
fn trace_atomic_src<'tcx>(
    ref_atomic: Place<'tcx>,
    body: &Body<'tcx>,
    def_use_analysis: &DefUseAnalysis,
) -> Result<Place<'tcx>, String> {
    // 1. check if ref_atomic is RefAtomic
    if !parse_ref_atomic_type(ref_atomic, body) {
        return Err("ref_atomic is not &std::sync::atomic::Atomic".to_string());
    }
    // // 2. check if ref_atomic comes from a local Atomic or a field of self
    // let use_info = def_use_analysis.local_info(ref_atomic.local);
    // for u in &use_info.defs_and_uses {
    //     match u.context {
    //         PlaceContext::MutatingUse(MutatingUseContext::Store) => {
    //             let stmt =
    //                 &body.basic_blocks()[u.location.block].statements[u.location.statement_index];
    //             if let StatementKind::Assign(box (lhs, ref rvalue)) = stmt.kind {
    //                 match rvalue {
    //                     Rvalue::Ref(_, _, rhs) => {
    //                         println!("{:?}", rhs);
    //                         println!("ty: {:?}", rhs.projection);
    //                         if parse_atomic_type(*rhs, body) {
    //                             return Ok(*rhs);
    //                         }
    //                     }
    //                     _ => {}
    //                 }
    //             }
    //         }
    //         _ => {}
    //     }
    // }
    // 3. check if ref_atomic comes from Arc::deref
    let mut worklist = VecDeque::new();
    let mut visited = HashSet::new();
    worklist.push_back(ref_atomic);
    visited.insert(ref_atomic);
    while let Some(place) = worklist.pop_front() {
        let use_info = def_use_analysis.local_info(place.local);
        for u in &use_info.defs_and_uses {
            match u.context {
                PlaceContext::MutatingUse(MutatingUseContext::Store) => {
                    let stmt = &body.basic_blocks()[u.location.block].statements
                        [u.location.statement_index];
                    if let StatementKind::Assign(box (lhs, ref rvalue)) = stmt.kind {
                        match rvalue {
                            Rvalue::Ref(_, _, rhs) => {
                                if parse_atomic_type(*rhs, body) {
                                    return Ok(*rhs);
                                }
                            }
                            Rvalue::Use(operand) => match operand {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    if !visited.contains(place) {
                                        worklist.push_back(*place);
                                        visited.insert(*place);
                                    }
                                }
                                _ => {}
                            },
                            _ => {}
                        }
                    }
                }
                PlaceContext::MutatingUse(MutatingUseContext::Call) => {
                    let term = body.basic_blocks()[u.location.block].terminator();
                    if let TerminatorKind::Call {
                        ref func,
                        ref args,
                        destination: Some((lhs, _)),
                        ..
                    } = term.kind
                    {
                        if lhs != place {
                            continue;
                        }
                        if let Operand::Constant(box constant) = func {
                            match constant.literal.ty.kind {
                                TyKind::FnDef(callee_def_id, substs)
                                | TyKind::Closure(callee_def_id, substs) => {
                                    if is_deref_func(&format!("{:?}", constant)) {
                                        if let Operand::Copy(first_arg_place)
                                        | Operand::Move(first_arg_place) = args[0]
                                        {
                                            if !visited.contains(&first_arg_place) {
                                                worklist.push_back(first_arg_place);
                                                visited.insert(first_arg_place);
                                            }
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
    Err("Cannot find atomic ref src".to_string())
}

//    fn trace_ref_to_obj(place: Place, body: &Body, def_use_analysis: &DefUseAnalysis) -> Place {
//        let use_info = self.def_use_analysis.local_info(place.local);
//        for u in &use_info.defs_and_uses {
//            match u.context {
//                PlaceContext::MutatingUse(MutatingUseContext::Store) => {
//                    assert!(!is_terminator_location(&u.location, self.body));
//                    let stmt = &self.body.basic_blocks()[u.location.block].statements
//                        [u.location.statement_index];
//                    if let StatementKind::Assign(box (lhs, ref rvalue)) = stmt.kind {
//                        if lhs != place {
//                            continue;
//                        }
//                        match rvalue {
//                            Rvalue::Use(operand) => {
//                                match operand {
//                                    Operand::Move(rhs) => {}
//                                    Operand::Copy(rhs) => {
//                                        self.depend_query_info.add_depend(
//                                            DependPair(lhs, *rhs),
//                                            DependResult::CopyDepend,
//                                        );
//                                    }
//                                    _ => {
//                                        // TODO
//                                    }
//                                };
//                            }
//                            Rvalue::Ref(_, _, rhs) => {
//                                self.depend_query_info
//                                    .add_depend(DependPair(lhs, *rhs), DependResult::RefDepend);
//                            }
//                            _ => {
//                                // TODO
//                            }
//                        }
//                    }
//                }
//                _ => {}
//            }
//        }
//    }

enum AliasResult {
    MustAlias,
    NoAlias,
    MayAlias,
}

fn alias(a: Place, b: Place, def_use_analysis: &DefUseAnalysis) -> AliasResult {
    if a == b {
        return AliasResult::MustAlias;
    } else {
        unimplemented! {}
    }
}
// let mut def_use_analysis = DefUseAnalysis::new(body);
//    def_use_analysis.analyze(body);
//    fn self_alias(
//        atomic_load: &Terminator,
//        atomic_store: &Terminator,
//        def_use_analysis: &DefUseAnalysis,
//    ) -> bool {
//        // let a = AtomicXXX::load(&atomic1, ...)
//        // AtomicXXX::store(&atomic2, a, ...)
//        // atomic1 == atomic2
//        if let TerminatorKind::Call {
//            ref func, ref args, ..
//        } = atomic_load.kind
//        {
//            let load_self = args[0];
//        }
//        if let TerminatorKind::Call {
//            ref func, ref args, ..
//        } = atomic_store.kind
//        {
//            let store_self = args[0];
//            let store_data = args[1];
//        }
//
//        unimplemented! {}
//    }

//     fn control_dependent(atomic_load: &Terminator, atomic_store: &Terminator) -> bool {
//         unimplemented! {}
//     }
//

/// worklist
/// data = load(a, _)
/// cmp = compare(data, _)
/// switchInt(cmp, bbx, bby)
/// bbx: store(a, _, _)
fn control_dependent(
    atomic_load: &Terminator,
    atomic_store_loc: &Location,
    body: &Body,
    def_use_analysis: &DefUseAnalysis,
) -> bool {
    let mut source: Option<Place> = None;
    if let TerminatorKind::Call {
        ref func,
        ref args,
        ref destination,
        ..
    } = atomic_load.kind
    {
        if let Some((place, bb)) = destination {
            source = Some(*place);
        } else {
            return false;
        }
    } else {
        return false;
    }
    if let None = source {
        return false;
    }
    let sink_bb = atomic_store_loc.block;
    let mut sink_bbs = vec![sink_bb];
    for pred in body.predecessors()[sink_bb].iter() {
        let mut cnt = 0;
        for _ in body.basic_blocks()[*pred].terminator().successors() {
            cnt += 1;
        }
        if cnt == 1 {
            sink_bbs.push(*pred);
        }
    }
    // track source -> sink
    let mut worklist = VecDeque::new();
    let mut visited = HashSet::new();
    worklist.push_back(source.unwrap());
    visited.insert(source.unwrap());
    while let Some(place) = worklist.pop_front() {
        let use_info = def_use_analysis.local_info(place.local);
        for u in &use_info.defs_and_uses {
            if !is_terminator_location(&u.location, body) {
                let stmt =
                    &body.basic_blocks()[u.location.block].statements[u.location.statement_index];
                // data = data | data = move (data, _).0
                if let StatementKind::Assign(box (lhs, ref rvalue)) = stmt.kind {
                    if lhs != place {
                        if !visited.contains(&lhs) {
                            worklist.push_back(lhs);
                            visited.insert(lhs);
                        }
                    }
                }
            } else {
                let term = body.basic_blocks()[u.location.block].terminator();
                // flag = Eq(dest, _)
                match term.kind {
                    TerminatorKind::Call {
                        ref func,
                        ref args,
                        destination: Some((lhs, _)),
                        ..
                    } => {
                        if lhs != place {
                            if !visited.contains(&lhs) {
                                worklist.push_back(lhs);
                                visited.insert(lhs);
                            }
                        }
                    }
                    TerminatorKind::SwitchInt { ref discr, ref switch_ty, ref values, ref targets} => {
                        if targets.iter().any(|target| sink_bbs.contains(target)) {
                            return true;
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    false
}
    /// worklist
    /// dest = load(a, _)
    /// (data, _) = CheckedAdd(dest, _)
    /// data = move (data, _).0
    /// data = data
    /// _ = store(a, data, _)
    fn data_dependent(
        atomic_load: &Terminator,
        atomic_store: &Terminator,
        body: &Body,
        def_use_analysis: &DefUseAnalysis,
    ) -> bool {
        let mut source: Option<Place> = None;
        let mut sink: Option<Place> = None;
        if let TerminatorKind::Call {
            ref func,
            ref args,
            ref destination,
            ..
        } = atomic_load.kind
        {
            if let Some((place, bb)) = destination {
                source = Some(*place);
            } else {
                return false;
            }
        } else {
            return false;
        }
        if let TerminatorKind::Call {
            ref func,
            ref args,
            ref destination,
            ..
        } = atomic_store.kind
        {
            if let Some(operand) = args.get(1) {
                match operand {
                    Operand::Copy(place) | Operand::Move(place) => {
                        sink = Some(*place);
                    }
                    _ => {}
                }
            } else {
                return false;
            }
        } else {
            return false;
        }
        if let None = source {
            return false;
        }
        if let None = sink {
            return false;
        }
        // track source -> sink
        let mut worklist = VecDeque::new();
        let mut visited = HashSet::new();
        worklist.push_back(source.unwrap());
        visited.insert(source.unwrap());
        while let Some(place) = worklist.pop_front() {
            let use_info = def_use_analysis.local_info(place.local);
            for u in &use_info.defs_and_uses {
                if !is_terminator_location(&u.location, body) {
                    let stmt = &body.basic_blocks()[u.location.block].statements
                        [u.location.statement_index];
                    // data = data | data = move (data, _).0
                    if let StatementKind::Assign(box (lhs, ref rvalue)) = stmt.kind {
                        if lhs == sink.unwrap() {
                            return true;
                        }
                        if lhs != place {
                            if !visited.contains(&lhs) {
                                worklist.push_back(lhs);
                                visited.insert(lhs);
                            }
                        }
                    }
                } else {
                    let term = body.basic_blocks()[u.location.block].terminator();
                    // (data, _) = CheckedAdd(dest, _)
                    if let TerminatorKind::Call {
                        ref func,
                        ref args,
                        destination: Some((lhs, _)),
                        ..
                    } = term.kind
                    {
                        if lhs == sink.unwrap() {
                            return true;
                        }
                        if lhs != place {
                            if !visited.contains(&lhs) {
                                worklist.push_back(lhs);
                                visited.insert(lhs);
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    fn is_terminator_location(location: &Location, body: &Body) -> bool {
        location.statement_index >= body.basic_blocks()[location.block].statements.len()
    }

