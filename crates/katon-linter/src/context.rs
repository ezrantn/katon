use katon_core::ast::NodeId;
use katon_core::span::Span;
use std::collections::{HashMap, HashSet};

#[derive(Default)]
pub struct LintContext {
    pub declared_vars: HashMap<NodeId, Span>, // count usages of how many declared variables
    pub used_vars: HashSet<NodeId>,
}
