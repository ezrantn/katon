pub mod ast;
pub mod check;
pub mod parser;
pub mod vc;

use ast::{Expr, FnDecl, Op, Stmt};
use vc::compile;

fn main() {
    // func Abs(x) {
    //   if x < 0 { x = 0 - x } else { x = x }
    //   ensures x >= 0
    // }

    let func = FnDecl {
        params: vec!["x".to_string()],
        requires: vec![],
        body: vec![Stmt::If {
            cond: Expr::Binary(
                Box::new(Expr::Var("x".to_string())),
                Op::Eq,
                Box::new(Expr::IntLit(0)),
            ),
            then_block: vec![Stmt::Assign {
                target: "x".to_string(),
                value: Expr::IntLit(-5),
            }],
            else_block: vec![Stmt::Assign {
                target: "x".to_string(),
                value: Expr::IntLit(200),
            }],
        }],
        ensures: vec![Expr::Binary(
            Box::new(Expr::Var("x".to_string())),
            Op::Gt,
            Box::new(Expr::IntLit(0)),
        )],
    };

    println!("{}", compile(&func));
}
