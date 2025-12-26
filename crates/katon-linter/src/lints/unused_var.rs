use crate::context::LintContext;
use crate::lint::{Lint, LintDiagnostic};
use katon_core::ast::*;

pub struct UnusedVar;

impl Lint for UnusedVar {
    fn name(&self) -> &'static str {
        "unused-variable"
    }

    fn check_stmt(&self, stmt: &SStmt, ctx: &mut LintContext, _diags: &mut Vec<LintDiagnostic>) {
        if let Stmt::Let { id: Some(id), .. } = &stmt.node {
            ctx.declared_vars.insert(*id, stmt.span);
        }
    }

    fn check_expr(&self, expr: &SExpr, ctx: &mut LintContext, _diags: &mut Vec<LintDiagnostic>) {
        if let Expr::Var(_, Some(id)) = &expr.node {
            ctx.used_vars.insert(*id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runner::Linter;
    use katon_core::{Span, Spanned};

    fn stmt(node: Stmt) -> SStmt {
        Spanned::new(node, Span::new(0, 1))
    }

    fn expr(node: Expr) -> SExpr {
        Spanned::new(node, Span::new(0, 1))
    }

    #[test]
    fn detects_unused_variable() {
        let id = NodeId(1);

        let func = FnDecl {
            name: "f".into(),
            params: vec![],
            param_names: vec![],
            requires: vec![],
            ensures: vec![],
            body: vec![stmt(Stmt::Let {
                name: "x".into(),
                ty: None,
                value: Some(expr(Expr::IntLit(1))),
                id: Some(id),
            })],
            span: Span::new(0, 1),
        };

        let linter = Linter::new(vec![Box::new(UnusedVar)]);
        let diags = linter.run_fn(&func);

        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, "unused-variable");
    }

    #[test]
    fn does_not_flag_used_variable() {
        let id = NodeId(1);

        let func = FnDecl {
            name: "f".into(),
            params: vec![],
            param_names: vec![],
            requires: vec![],
            ensures: vec![],
            body: vec![
                stmt(Stmt::Let {
                    name: "x".into(),
                    ty: None,
                    value: Some(expr(Expr::IntLit(1))),
                    id: Some(id),
                }),
                stmt(Stmt::Assign {
                    target: "x".into(),
                    target_id: Some(id),
                    value: expr(Expr::Binary(
                        Box::new(expr(Expr::Var("x".into(), Some(id)))),
                        Op::Add,
                        Box::new(expr(Expr::IntLit(1))),
                    )),
                }),
            ],
            span: Span::new(0, 1),
        };

        let linter = Linter::new(vec![Box::new(UnusedVar)]);
        let diags = linter.run_fn(&func);

        assert!(diags.is_empty());
    }
}
