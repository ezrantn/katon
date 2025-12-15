pub mod ast;
pub mod check;
pub mod parser;
pub mod vc;

use ariadne::{Label, Report, ReportKind, Source};
use ast::{Expr, FnDecl, Op, Stmt};
use chumsky::Parser;
use vc::compile;

fn main() {
    // func Abs(x) {
    //   if x < 0 { x = 0 - x } else { x = x }
    //   ensures x >= 0
    // }

    // 1. The Source Code
    let src = r#"
        func Abs(x) {
            requires x > -100
            
            if x < 0 { 
                x = 0 - x 
            } else { 
                x = x 
            }

            ensures x > 0
        }
    "#;

    // 2. PARSE IT
    let parse_result = parser::parser().parse(src);

    match parse_result {
        Ok(func_decl) => {
            println!("✅ Parsed '{}' successfully.", func_decl.name);

            // 3. BORROW CHECK IT
            let mut checker = check::BorrowChecker::new();
            match checker.check_fn(&func_decl) {
                Ok(_) => {
                    println!("✅ Borrow Checker Passed.");

                    // 4. COMPILE IT
                    let z3_code = compiler::compile(&func_decl); // You need to implement this in compiler.rs
                    println!("\n--- Z3 SMT OUTPUT ---\n");
                    println!("{}", z3_code);
                }
                Err(e) => println!("❌ Borrow Check Failed: {}", e),
            }
        }
        Err(errors) => {
            // Pretty Error Printing
            Report::build(ReportKind::Error, (), 0)
                .with_message("Parsing failed")
                .with_label(Label::new(0..src.len()).with_message(format!("{:?}", errors)))
                .finish()
                .print(Source::from(src))
                .unwrap();
        }
    }
}
