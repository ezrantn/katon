use crate::ast::{Expr, FnDecl, Op, Stmt};
use std::collections::HashMap;

struct Env {
    global_gen: HashMap<String, usize>,
    current_scope: HashMap<String, usize>,
}

impl Env {
    fn new() -> Self {
        Self {
            global_gen: HashMap::new(),
            current_scope: HashMap::new(),
        }
    }

    // Get current SSA name (e.g., "x_2")
    fn get(&self, name: &str) -> String {
        let ver = self.current_scope.get(name).unwrap_or(&0);
        format!("{}_{}", name, ver)
    }

    // Get original entry name (e.g., "x_0") for old()
    fn get_old(&self, name: &str) -> String {
        format!("{}_0", name)
    }

    fn new_version(&mut self, name: &str) -> String {
        let new_gen = self.global_gen.entry(name.to_string()).or_insert(0);
        *new_gen += 1; // Always increment global counter
        let new_ver = *new_gen;

        self.current_scope.insert(name.to_string(), new_ver);
        format!("{}_{}", name, new_ver)
    }
}

fn expr_to_smt(expr: &Expr, env: &Env) -> String {
    match expr {
        Expr::IntLit(n) => n.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Var(name) => env.get(name),
        Expr::Old(name) => env.get_old(name),
        Expr::Binary(lhs, op, rhs) => {
            let l = expr_to_smt(lhs, env);
            let r = expr_to_smt(rhs, env);
            let op_str = match op {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Eq => "=",
                Op::Gt => ">",
                Op::Lt => "<",
                Op::Gte => ">=",
                Op::Lte => "<=",
                Op::Mul => "*",
                Op::Neq => "!=",
                Op::Div => "/",
            };
            format!("({} {} {})", op_str, l, r)
        }
    }
}

fn process_block(stmts: &[Stmt], env: &mut Env, smt: &mut String) {
    for stmt in stmts {
        match stmt {
            Stmt::Assign { target, value } => {
                let val_smt = expr_to_smt(value, env);
                let new_target = env.new_version(target);
                smt.push_str(&format!("(declare-const {} Int)\n", new_target));
                smt.push_str(&format!("(assert (= {} {}))\n", new_target, val_smt));
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let cond_smt = expr_to_smt(cond, env);

                // 1. Save Scope (NOT global counters)
                let start_scope = env.current_scope.clone();

                // 2. Process THEN
                process_block(then_block, env, smt);
                let then_scope = env.current_scope.clone();

                // 3. Restore Scope & Process ELSE
                env.current_scope = start_scope.clone(); // Reset local scope
                process_block(else_block, env, smt);
                let else_scope = env.current_scope.clone();

                // 4. MERGE (Phi Node)
                // Identify all vars modified in either branch
                for (var, &v_start) in &start_scope {
                    let v_then = then_scope.get(var).copied().unwrap_or(v_start);
                    let v_else = else_scope.get(var).copied().unwrap_or(v_start);

                    // If the version changed in EITHER branch...
                    if v_then != v_start || v_else != v_start {
                        let name_then = format!("{}_{}", var, v_then);
                        let name_else = format!("{}_{}", var, v_else);

                        // Create x_3
                        let name_merged = env.new_version(var);

                        smt.push_str(&format!("(declare-const {} Int)\n", name_merged));
                        smt.push_str(&format!(
                            "(assert (= {} (ite {} {} {})))\n",
                            name_merged, cond_smt, name_then, name_else
                        ));
                    }
                }
            }
        }
    }
}

pub fn compile(func: &FnDecl) -> String {
    let mut smt = String::from("(set-logic QF_LIA)\n");
    let mut env = Env::new();

    // Inputs (Version 0)
    for param in &func.params {
        smt.push_str(&format!("(declare-const {}_0 Int)\n", param));
    }

    // Preconditions
    for req in &func.requires {
        smt.push_str(&format!("(assert {})\n", expr_to_smt(req, &env)));
    }

    // Body
    process_block(&func.body, &mut env, &mut smt);

    // Postconditions
    for ens in &func.ensures {
        let cond = expr_to_smt(ens, &env);
        smt.push_str(&format!("(assert (not {}))\n", cond));
    }

    smt.push_str("(check-sat)\n");
    smt
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(s: &str) -> Box<Expr> {
        Box::new(Expr::Var(s.to_string()))
    }

    fn int(i: i64) -> Box<Expr> {
        Box::new(Expr::IntLit(i))
    }

    fn bin(l: Box<Expr>, op: Op, r: Box<Expr>) -> Expr {
        Expr::Binary(l, op, r)
    }

    #[test]
    fn test_compile_abs_function_with_merge() {
        // LOGIC TO TEST:
        // fn abs(x: int) {
        //    let y = x;       <-- y_1 defined here (Start Scope for IF)
        //    if x < 0 {
        //       y = 0 - x;    <-- y_2 (Then Branch)
        //    } else {
        //       y = x;        <-- y_3 (Else Branch)
        //    }
        //    // Merge happens here: y_4 = ite(..., y_2, y_3)
        // }
        // ensures y >= 0

        let func = FnDecl {
            name: "abs".to_string(),
            params: vec!["x".to_string()], // x_0 declared automatically
            requires: vec![],
            body: vec![
                // 1. Init y = x
                Stmt::Assign {
                    target: "y".to_string(),
                    value: Expr::Var("x".to_string()),
                },
                // 2. If x < 0
                Stmt::If {
                    cond: bin(var("x"), Op::Lt, int(0)),
                    then_block: vec![
                        // y = 0 - x
                        Stmt::Assign {
                            target: "y".to_string(),
                            value: bin(int(0), Op::Sub, var("x")),
                        },
                    ],
                    else_block: vec![
                        // y = x
                        Stmt::Assign {
                            target: "y".to_string(),
                            value: Expr::Var("x".to_string()),
                        },
                    ],
                },
            ],
            ensures: vec![
                // y >= 0
                bin(var("y"), Op::Gte, int(0)),
            ],
        };

        let smt_output = compile(&func);

        println!("Generated SMT:\n{}", smt_output);

        // --- ASSERTIONS ---

        // 1. Verify Inputs
        assert!(smt_output.contains("(declare-const x_0 Int)"));

        // 2. Verify Initial Assignment (y = x) -> y_1
        // Note: env.new_version increments first, so 0->1.
        assert!(smt_output.contains("(declare-const y_1 Int)"));
        assert!(smt_output.contains("(= y_1 x_0)"));

        // 3. Verify Branches (y_2 and y_3)
        // Then block: y = 0 - x
        assert!(smt_output.contains("(= y_2 (- 0 x_0))"));

        // Else block: y = x (Depending on scope reuse, likely y_3)
        assert!(smt_output.contains("(= y_3 x_0)"));

        // 4. Verify THE MERGE (Phi Node)
        // This is the critical part. It must define y_4 using 'ite'
        assert!(smt_output.contains("(declare-const y_4 Int)"));
        assert!(smt_output.contains("ite (< x_0 0) y_2 y_3"));

        // 5. Verify Post-condition Negation
        // Must check (not (>= y_4 0))
        assert!(smt_output.contains("(assert (not (>= y_4 0)))"));

        // 6. Verify Solver Command
        assert!(smt_output.contains("(check-sat)"));
    }
}
