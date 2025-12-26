use crate::context::LintContext;
use katon_core::Span;
use katon_core::ast::*;

#[derive(Debug, Clone)]
pub enum LintLevel {
    Warning,
    Error,
    Help,
}

#[derive(Debug, Clone)]
pub struct LintDiagnostic {
    pub code: &'static str,
    pub message: String,
    pub span: Span,
    pub level: LintLevel,
}

pub trait Lint {
    fn name(&self) -> &'static str;

    fn check_stmt(&self, _stmt: &SStmt, _ctx: &mut LintContext, _diags: &mut Vec<LintDiagnostic>) {}

    fn check_expr(&self, _expr: &SExpr, _ctx: &mut LintContext, _diags: &mut Vec<LintDiagnostic>) {}
}
