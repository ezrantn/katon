// Implement the parser
use crate::ast::{Expr, FnDecl, Op, Stmt};
use chumsky::pratt::*;
use chumsky::prelude::*;

pub fn parser<'a>() -> impl Parser<'a, &'a char, FnDecl, extra::Err<Simple<'a, char>>> {
    let ident = text::ident().padded();

    let int = text::int(10)
        .map(|s: String| Expr::IntLit(s.parse().unwrap()))
        .padded();

    // 2. Expressions (The Pratt Parser)
    let expr = recursive(|expr| {
        // A. The Atom
        let atom = choice((
            int,
            // old(x)
            just("old")
                .ignore_then(ident.delimited_by(just('('), just(')')))
                .map(Expr::Old),
            // Variables: x
            ident.map(Expr::Var),
            // Parentheses: (x + 1)
            expr.delimited_by(just('('), just(')')),
        ))
        .padded();

        // B. The Pratt Operator Logic
        atom.pratt((
            // Level 2: + -
            infix(left(2), just('+'), |l, _, r, _| {
                Expr::Binary(Box::new(l), Op::Add, Box::new(r))
            }),
            infix(left(2), just('-'), |l, _, r, _| {
                Expr::Binary(Box::new(l), Op::Sub, Box::new(r))
            }),
            // Level 1: comparisons
            infix(left(1), just("=="), |l, _, r, _| {
                Expr::Binary(Box::new(l), Op::Eq, Box::new(r))
            }),
            infix(left(1), just('>'), |l, _, r, _| {
                Expr::Binary(Box::new(l), Op::Gt, Box::new(r))
            }),
            infix(left(1), just('<'), |l, _, r, _| {
                Expr::Binary(Box::new(l), Op::Lt, Box::new(r))
            }),
        ))
    });

    // 3. Statements
    let stmt = recursive(|stmt| {
        // assignment: x = expr
        let assign = ident
            .clone()
            .then_ignore(just('=').padded())
            .then(expr.clone())
            .map(|(target, value)| Stmt::Assign { target, value });

        // reusable block: { stmt* }
        let block = just('{')
            .ignore_then(stmt.clone().repeated())
            .then_ignore(just('}'))
            .padded();

        // if statement
        let if_stmt = just("if")
            .padded()
            .ignore_then(expr.clone())
            .then(block.clone())
            .then(just("else").padded().ignore_then(block.clone()).or_not())
            .map(|((cond, then_block), else_block)| Stmt::If {
                cond,
                then_block,
                else_block: else_block.unwrap_or_default(),
            });

        assign.or(if_stmt).padded()
    });

    // 4. Contracts
    let requires = just("requires").ignore_then(expr.clone());
    let ensures = just("ensures").ignore_then(expr.clone());

    // 5. Function Declaration
    just("func")
        .padded()
        .ignore_then(ident.clone())
        .then(
            ident
                .clone()
                .separated_by(just(','))
                .allow_trailing()
                .delimited_by(just('('), just(')'))
                .padded(),
        )
        .then(
            just('{')
                .ignore_then(requires.repeated())
                .then(stmt.repeated())
                .then(ensures.repeated())
                .then_ignore(just('}')),
        )
        .map(|((name, params), ((requires, body), ensures))| FnDecl {
            name,
            params,
            requires,
            ensures,
            body,
        })
}
