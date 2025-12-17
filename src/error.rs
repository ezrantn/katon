use std::fmt;

use crate::ast::Type;

#[derive(Debug, Clone)]
pub enum CheckError {
    UseAfterMove { var: String },
    TypeMismatch { expected: Type, found: Type },
    InvalidIndex { ty: Type },
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CheckError::UseAfterMove { var } => {
                write!(f, "Borrow Error: use of moved value '{}'", var)
            }
            CheckError::TypeMismatch { expected, found } => {
                write!(f, "Type Error: expected '{}', found '{}'", expected, found)
            }
            CheckError::InvalidIndex { ty } => {
                write!(f, "Type Error: cannot index into value of type `{}`", ty)
            }
        }
    }
}
