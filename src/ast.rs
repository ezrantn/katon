use crate::errors::Spanned;
use std::fmt::{Display, Formatter, Result};

pub type SExpr = Spanned<Expr>;
pub type SStmt = Spanned<Stmt>;

#[derive(Debug, Clone, PartialEq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Gt,
    Lt,
    Gte,
    Lte,
    Index,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    IntLit(i64),
    BoolLit(bool),
    Var(String),
    Old(String),
    Binary(Box<SExpr>, Op, Box<SExpr>),
    Cast(Type, Box<SExpr>),
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Assign {
        target: String,
        value: SExpr,
    },
    If {
        cond: SExpr,
        then_block: Vec<SStmt>,
        else_block: Vec<SStmt>,
    },
    While {
        cond: SExpr,
        invariant: SExpr, // The user MUST use invariant for now
        body: Vec<SStmt>,
    },
    ArrayUpdate {
        target: String,
        index: SExpr,
        value: SExpr,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Nat,
    Array(Box<Type>),
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Nat => write!(f, "nat"),
            Type::Array(inner) => write!(f, "[{}]", inner),
        }
    }
}
pub struct FnDecl {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub requires: Vec<SExpr>,
    pub ensures: Vec<SExpr>,
    pub body: Vec<SStmt>,
}
