extern crate rustc_span;
use std::collections::{HashMap, HashSet};
use super::lock::{LockGuardType, LockGuardSrc, LockGuardId};
use rustc_span::Span;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(PartialEq, Eq, Hash, Debug)]
struct CallChain(Vec<Span>);

struct LockGuardCallChain(HashMap<(LockGuardId, LockGuardId), HashSet<CallChain>>);
#[derive(PartialEq, Eq, Hash, Debug)]
struct LockGuardRelationPath(Vec<(LockGuardId, LockGuardId)>);

struct TransitiveRelationPath(HashMap<(LockGuardId, LockGuardId), LockGuardRelationPath>);

struct ConflictLockReport {
    report: HashMap<(LockGuardSrc, LockGuardSrc), (TransitiveRelationPath, TransitiveRelationPath)>,
}



