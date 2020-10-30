/// A simple assumption to track lockguard to lock:
/// For two places: A and B
/// if A = move B:
/// then A depends on B by move
/// if A = B:
/// then A depends on B by copy
/// if A = &B or A = &mut B
/// then A depends on B by ref
/// if A = call func(move B)
/// then A depends on B by call
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_mir;

use rustc_middle::mir::visit::*;
use rustc_middle::mir::*;
use rustc_mir::util::def_use::DefUseAnalysis;

use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct DependPair<'tcx>(Place<'tcx>, Place<'tcx>);

pub type DependCache<'tcx> = HashMap<DependPair<'tcx>, DependResult>;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DependResult {
    MoveDepend,
    CopyDepend,
    RefDepend,
    CallDepend,
}

pub struct BatchDependResults<'a, 'b, 'tcx> {
    depend_query_info: DependQueryInfo<'tcx>,
    pub body: &'a Body<'tcx>,
    def_use_analysis: &'b DefUseAnalysis,
}

impl<'a, 'b, 'tcx> BatchDependResults<'a, 'b, 'tcx> {
    pub fn new(body: &'a Body<'tcx>, def_use_analysis: &'b DefUseAnalysis) -> Self {
        Self {
            depend_query_info: DependQueryInfo::<'tcx>::new(),
            body,
            def_use_analysis,
        }
    }

    pub fn get_depends(&self, place: Place<'tcx>) -> Vec<(Place<'tcx>, DependResult)> {
        self.depend_query_info.get_depends(place)
    }

    pub fn gen_depends(&mut self, place: Place<'tcx>) {
        // use_info包含本地变量的定义和使用的location信息
        let use_info = self.def_use_analysis.local_info(place.local);
        // def_and_uses:Vec<Use>, Use结构体包含对应的上下文contex和location
        for u in &use_info.defs_and_uses {
            match u.context {
                // 如果左操作数是可变借用
                PlaceContext::MutatingUse(MutatingUseContext::Store) => {
                    // 判断当前变量是否是termitor，不是才继续
                    assert!(!is_terminator_location(&u.location, self.body));
                    let stmt = &self.body.basic_blocks()[u.location.block].statements
                        [u.location.statement_index];
                    // Assign将右值写入左值位置，这里if let可以看做解构赋值？
                    if let StatementKind::Assign(box (lhs, ref rvalue)) = stmt.kind {
                        if lhs != place {
                            continue;
                        }
                        match rvalue {
                            // 移动或复制语义
                            Rvalue::Use(operand) => {
                                match operand {
                                    Operand::Move(rhs) => {
                                        self.depend_query_info.add_depend(
                                            DependPair(lhs, *rhs),
                                            DependResult::MoveDepend,
                                        );
                                    }
                                    Operand::Copy(rhs) => {
                                        self.depend_query_info.add_depend(
                                            DependPair(lhs, *rhs),
                                            DependResult::CopyDepend,
                                        );
                                    }
                                    _ => {
                                        // TODO
                                    }
                                };
                            }
                            //引用语义
                            Rvalue::Ref(_, _, rhs) => {
                                self.depend_query_info
                                    .add_depend(DependPair(lhs, *rhs), DependResult::RefDepend);
                            }
                            _ => {
                                // TODO
                            }
                        }
                    }
                }
                // 如果是函数调用
                PlaceContext::MutatingUse(MutatingUseContext::Call) => {
                    // 同样判断当前变量是不是termitor，是才继续
                    assert!(is_terminator_location(&u.location, self.body));
                    // term是Option<Terminator<'tcx>>类型
                    let term = self.body.basic_blocks()[u.location.block].terminator();
                    // 这里也类似解构赋值，如果term.kind是Call类型， 则将其中的对应值赋值给func、args和destination
                    if let TerminatorKind::Call {
                        func: _,
                        // args是Vec<Operand>，其中Operand可以是Copy，Move和constant
                        ref args,
                        // destination是Option<(Place<'tcx>,BasicBlock)>类型
                        destination: Some((lhs, _)),
                        ..
                    } = term.kind
                    {
                        // 如果左操作数不是一个place
                        if lhs != place {
                            continue;
                        }
                        // heuristically consider the first move arg to be associated with return.
                        // TODO: check the type relations to decide if they are related.
                        for arg in args {
                            if let Operand::Move(rhs) = arg {
                                // 如果右操作数是move语义
                                self.depend_query_info
                                    .add_depend(DependPair(lhs, *rhs), DependResult::CallDepend);
                                break;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

pub struct DependQueryInfo<'tcx> {
    depend_cache: DependCache<'tcx>,
}

impl<'tcx> DependQueryInfo<'tcx> {
    pub fn new() -> Self {
        Self {
            depend_cache: HashMap::<DependPair<'tcx>, DependResult>::new(),
        }
    }

    pub fn get_depends(&self, place: Place<'tcx>) -> Vec<(Place<'tcx>, DependResult)> {
        self.depend_cache
            .iter()
            .filter_map(|(pair, result)| {
                if pair.0 == place {
                    Some((pair.1, *result))
                } else {
                    None
                }
            })
            .collect()
    }

    fn add_depend(&mut self, pair: DependPair<'tcx>, result: DependResult) {
        // 检查depend_cache中是否已经存在这个调用，若不存在则加入
        self.depend_cache.entry(pair).or_insert(result);
    }
}

fn is_terminator_location(location: &Location, body: &Body) -> bool {
    // body.basic_blocks()返回一个IndexVec<BasicBlock,BasicBlockData<'tcx>>
    // BasicBlockData.statements是该基本块的语句列表
    // location.statement_index是从语句开始位置到当前变量的语句数，如果其大于BasicBlockData.statements
    // 则证明当前变量的位置是termitor的位置
    location.statement_index >= body.basic_blocks()[location.block].statements.len()
}
