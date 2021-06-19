use crate::query_model::{BoxRef, QGBox, QuantifierRef, QuantifierSet, QuantifierType};
use itertools::Itertools;
use std::cell::RefCell;
use std::cmp::*;
use std::collections::*;
use std::fmt;
use std::rc::*;

pub type ColumnRefDesc = (i32, usize);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ColumnReference {
    pub quantifier: QuantifierRef,
    pub position: usize,
}

impl ColumnReference {
    pub fn to_desc(&self) -> ColumnRefDesc {
        (self.quantifier.borrow().id, self.position)
    }
}

#[derive(Clone)]
pub struct BaseColumn {
    pub parent_box: Weak<RefCell<QGBox>>,
    pub position: usize,
}

impl PartialEq for BaseColumn {
    fn eq(&self, other: &Self) -> bool {
        assert!(self.parent_box.as_ptr() == other.parent_box.as_ptr());
        self.position == other.position
    }
}

impl Eq for BaseColumn {}

impl Ord for BaseColumn {
    fn cmp(&self, other: &Self) -> Ordering {
        assert!(self.parent_box.as_ptr() == other.parent_box.as_ptr());
        self.position.cmp(&other.position)
    }
}

impl PartialOrd for BaseColumn {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum LogicalExprType {
    And,
    Or,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Value {
    Null,
    BigInt(i64),
    Boolean(bool),
    String(String),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Value::*;
        match &self {
            // @todo escape string
            String(v) => write!(f, "'{}'", v),
            BigInt(v) => write!(f, "{}", v),
            Boolean(v) if *v => write!(f, "TRUE"),
            Boolean(_) => write!(f, "FALSE"),
            Null => write!(f, "NULL"),
        }
    }
}

impl Value {}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CmpOpType {
    Eq,
    Neq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
}

impl fmt::Display for CmpOpType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use CmpOpType::*;
        match &self {
            Eq => write!(f, "="),
            Neq => write!(f, "!="),
            LessEq => write!(f, "<="),
            GreaterEq => write!(f, ">="),
            Less => write!(f, "<"),
            Greater => write!(f, ">"),
        }
    }
}

trait Commutate {
    fn commutate(&self) -> Self;
}

impl Commutate for CmpOpType {
    fn commutate(&self) -> Self {
        match self {
            Self::Eq => Self::Eq {},
            Self::Neq => Self::Neq {},
            Self::Less => Self::Greater {},
            Self::LessEq => Self::GreaterEq {},
            Self::Greater => Self::Less {},
            Self::GreaterEq => Self::LessEq {},
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExprType {
    Column((usize, usize)),
    BaseColumn(BaseColumn),
    ColumnReference(ColumnReference),
    InList,
    Cmp(CmpOpType),
    Logical(LogicalExprType),
    Not,
    IsNull,
    Case,
    Tuple,
    Literal(Value),
    Parameter(u64),
}

pub type ExprRef = Rc<RefCell<Expr>>;
pub type ColumnReferenceMap = HashMap<usize, Vec<ExprRef>>;
pub type PerQuantifierColumnReferenceMap = BTreeMap<QuantifierRef, ColumnReferenceMap>;
pub type PerBoxColumnReferenceMap = HashMap<i32, ColumnReferenceMap>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Expr {
    pub expr_type: ExprType,
    pub operands: Option<Vec<ExprRef>>,
}

impl Expr {
    pub fn make_base_column(parent_box: &BoxRef, position: usize) -> Self {
        let base_col = BaseColumn {
            parent_box: Rc::downgrade(&parent_box),
            position,
        };
        Self {
            expr_type: ExprType::BaseColumn(base_col),
            operands: None,
        }
    }

    pub fn make_column_ref(quantifier: QuantifierRef, position: usize) -> Self {
        let col_ref = ColumnReference {
            quantifier,
            position,
        };
        Self {
            expr_type: ExprType::ColumnReference(col_ref),
            operands: None,
        }
    }

    pub fn make_parameter(index: u64) -> Self {
        Self {
            expr_type: ExprType::Parameter(index),
            operands: None,
        }
    }

    pub fn make_in_list(term: ExprRef, list: Vec<ExprRef>) -> Self {
        let mut operands = vec![term];
        operands.extend(list);
        Self {
            expr_type: ExprType::InList,
            operands: Some(operands),
        }
    }

    pub fn make_logical(type_: LogicalExprType, list: Vec<ExprRef>) -> Self {
        Self {
            expr_type: ExprType::Logical(type_),
            operands: Some(list),
        }
    }

    pub fn make_literal(value: Value) -> Self {
        Self {
            expr_type: ExprType::Literal(value),
            operands: None,
        }
    }

    pub fn make_null() -> Self {
        Self {
            expr_type: ExprType::Literal(Value::Null),
            operands: None,
        }
    }

    pub fn make_cmp(cmp_type: CmpOpType, left: ExprRef, right: ExprRef) -> Self {
        Self {
            expr_type: ExprType::Cmp(cmp_type),
            operands: Some(vec![left, right]),
        }
    }

    pub fn make_case(operands: Vec<ExprRef>) -> Self {
        Self {
            expr_type: ExprType::Case,
            operands: Some(operands),
        }
    }

    pub fn make_is_null(operand: ExprRef) -> Self {
        Self {
            expr_type: ExprType::IsNull,
            operands: Some(vec![operand]),
        }
    }

    pub fn make_not(operand: ExprRef) -> Self {
        Self {
            expr_type: ExprType::Not,
            operands: Some(vec![operand]),
        }
    }

    pub fn make_tuple(operands: Vec<ExprRef>) -> Self {
        Self {
            expr_type: ExprType::Tuple,
            operands: Some(operands),
        }
    }

    pub fn is_equiv(&self, o: &Self) -> bool {
        match (&self.expr_type, &o.expr_type) {
            (ExprType::Column(l), ExprType::Column(r)) => l == r,
            (ExprType::BaseColumn(l), ExprType::BaseColumn(r)) => l == r,
            (ExprType::Literal(l), ExprType::Literal(r)) => l == r,
            (ExprType::ColumnReference(l), ExprType::ColumnReference(r)) => {
                l.position == r.position && l.quantifier == r.quantifier
            }
            (ExprType::Cmp(l), ExprType::Cmp(r)) => l == r && self.equiv_operands(o),
            (ExprType::Logical(l), ExprType::Logical(r)) => l == r && self.equiv_operands(o),
            (ExprType::Parameter(l), ExprType::Parameter(r)) => l == r,
            (ExprType::Case, ExprType::Case)
            | (ExprType::Not, ExprType::Not)
            | (ExprType::IsNull, ExprType::IsNull)
            | (ExprType::InList, ExprType::InList)
            | (ExprType::Tuple, ExprType::Tuple) => self.equiv_operands(o),
            _ => false,
        }
    }

    pub fn equiv_operands(&self, o: &Self) -> bool {
        let l = self.operands.as_ref().expect("operands expected");
        let r = o.operands.as_ref().expect("operands expected");
        l.len() == r.len()
            && l.iter()
                .zip(r.iter())
                .all(|(x, y)| x.borrow().is_equiv(&y.borrow()))
    }

    pub fn is_column_ref(&self) -> bool {
        if let ExprType::ColumnReference(_) = &self.expr_type {
            true
        } else {
            false
        }
    }

    pub fn get_quantifier(&self) -> Option<QuantifierRef> {
        if let ExprType::ColumnReference(c) = &self.expr_type {
            Some(Rc::clone(&c.quantifier))
        } else {
            None
        }
    }

    pub fn is_compilation_constant(&self) -> bool {
        match self.expr_type {
            ExprType::Literal(_) => true,
            ExprType::Tuple => self
                .operands
                .iter()
                .all(|x| x.iter().all(|x| x.borrow().is_compilation_constant())),
            _ => false,
        }
    }

    pub fn is_runtime_constant(&self) -> bool {
        match self.expr_type {
            ExprType::Parameter(_) | ExprType::Literal(_) => true,
            ExprType::Tuple => self
                .operands
                .iter()
                .all(|x| x.iter().all(|x| x.borrow().is_runtime_constant())),
            _ => false,
        }
    }

    pub fn is_aggregate_function(&self) -> bool {
        false
    }

    pub fn dereference(&self) -> Option<ExprRef> {
        if let ExprType::ColumnReference(c) = &self.expr_type {
            let q = c.quantifier.borrow();
            let b = q.input_box.borrow();
            Some(Rc::clone(&b.columns[c.position].expr))
        } else {
            None
        }
    }

    pub fn is_true_predicate(&self) -> bool {
        match &self.expr_type {
            ExprType::Literal(c) => {
                if let Value::Boolean(true) = c {
                    true
                } else {
                    false
                }
            }
            ExprType::Cmp(c) if *c == CmpOpType::Eq => {
                if let Some(operands) = &self.operands {
                    operands.iter().dedup().count() == 1
                } else {
                    // panic!
                    false
                }
            }
            _ => false,
        }
    }

    pub fn is_false_predicate(&self) -> bool {
        match &self.expr_type {
            ExprType::Literal(c) => {
                if let Value::Boolean(false) = c {
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    pub fn is_not_null(&self) -> Option<ExprRef> {
        if let ExprType::Not = &self.expr_type {
            let op = self.operands.as_ref().unwrap()[0].borrow();
            if let ExprType::IsNull = &op.expr_type {
                return Some(op.operands.as_ref().unwrap()[0].clone());
            }
        }
        None
    }

    pub fn result_arity(&self) -> usize {
        match &self.expr_type {
            ExprType::Tuple => self.operands.as_ref().unwrap().len(),
            _ => 1,
        }
    }

    pub fn is_existential_operand(&self) -> bool {
        match &self.expr_type {
            ExprType::Tuple => self
                .operands
                .iter()
                .all(|x| x.iter().all(|x| x.borrow().is_existential_operand())),
            ExprType::ColumnReference(c) => {
                c.quantifier.borrow().quantifier_type == QuantifierType::Existential
            }
            _ => false,
        }
    }

    pub fn is_existential_comparison(&self) -> bool {
        match &self.expr_type {
            ExprType::Cmp(CmpOpType::Eq) => self
                .operands
                .iter()
                .all(|x| x.iter().any(|x| x.borrow().is_existential_operand())),
            _ => false,
        }
    }

    pub fn normalize(&mut self) {
        if let Some(operands) = &self.operands {
            for o in operands {
                o.borrow_mut().normalize();
            }
        }
        match &mut self.expr_type {
            ExprType::Column(_)
            | ExprType::BaseColumn(_)
            | ExprType::ColumnReference(_)
            | ExprType::Literal(_)
            | ExprType::Parameter(_)
            | ExprType::IsNull
            | ExprType::Case
            | ExprType::Tuple
            | ExprType::Not => {}
            ExprType::Logical(_) => {
                if let Some(operands) = &mut self.operands {
                    operands.sort();
                    operands.dedup();
                }
            }
            ExprType::InList => {
                if let Some(operands) = &mut self.operands {
                    let sorted = operands.drain(1..).sorted().dedup().collect::<Vec<_>>();
                    operands.extend(sorted);
                }
            }
            ExprType::Cmp(t) => {
                if let Some(operands) = &mut self.operands {
                    let r = operands.pop().unwrap();
                    let l = operands.pop().unwrap();
                    if l > r {
                        operands.push(r);
                        operands.push(l);
                        *t = t.commutate();
                    } else {
                        operands.push(l);
                        operands.push(r);
                    }
                }
            }
        }
    }

    pub fn is_constant_within_context(&self, context: &QuantifierSet) -> bool {
        !self.references_context(context)
    }

    /// Whether the expression contains any column reference of the given
    /// context. Used to detect correlation.
    pub fn references_context(&self, context: &QuantifierSet) -> bool {
        match &self.expr_type {
            ExprType::ColumnReference(c) => context.contains(&c.quantifier),
            _ => self.operands.iter().any(|operands| {
                operands
                    .iter()
                    .any(|o| o.borrow().references_context(context))
            }),
        }
    }

    pub fn visit_mut<F, E>(&mut self, f: &mut F) -> Result<(), E>
    where
        F: FnMut(&mut Expr) -> Result<(), E>,
    {
        f(self)?;
        if let Some(operands) = &mut self.operands {
            for o in operands {
                o.borrow_mut().visit_mut(f)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ExprType::*;
        match &self.expr_type {
            InList => {
                let operands = self.operands.as_ref().unwrap();
                write!(f, "{} IN (", operands[0].borrow())?;
                let mut sep = "";
                for o in &operands[1..] {
                    write!(f, "{}{}", sep, o.borrow())?;
                    sep = ", ";
                }
                write!(f, ")")
            }
            ColumnReference(c) => write!(f, "Q{}.c{}", c.quantifier.borrow().id, c.position),
            Parameter(c) => write!(f, "?:{}", c),
            Column((id, c)) => write!(f, "c{}_{}", id, c),
            // @todo print the column name
            BaseColumn(c) => write!(f, "c{}", c.position),
            Literal(c) => write!(f, "{}", c),
            Cmp(t) => {
                let operands = self.operands.as_ref().unwrap();
                write!(
                    f,
                    "({}) {} ({})",
                    operands[0].borrow(),
                    t,
                    operands[1].borrow()
                )
            }
            Logical(t) => {
                let operands = self.operands.as_ref().unwrap();
                let sep = {
                    match t {
                        LogicalExprType::And => "AND",
                        LogicalExprType::Or => "OR",
                    }
                };
                for (i, o) in operands.iter().enumerate() {
                    if i > 0 {
                        write!(f, " {} ", sep)?;
                    }
                    write!(f, "({})", o.borrow())?;
                }
                Ok(())
            }
            Case => {
                let operands = self.operands.as_ref().unwrap();
                write!(f, "CASE")?;
                for (i, o) in operands.iter().enumerate() {
                    let word = if i % 2 == 1 {
                        "THEN"
                    } else if i == operands.len() - 1 {
                        "ELSE"
                    } else {
                        "WHEN"
                    };
                    write!(f, " {} {}", word, o.borrow())?;
                }
                write!(f, " END")
            }
            IsNull => {
                let operands = self.operands.as_ref().unwrap();
                write!(f, "({}) IS NULL", operands[0].borrow())
            }
            Tuple => {
                let operands = self.operands.as_ref().unwrap();
                write!(f, "({}", operands[0].borrow())?;
                for o in &operands[1..] {
                    write!(f, ", {}", o.borrow())?;
                }
                write!(f, ")")
            }
            Not => {
                let operands = self.operands.as_ref().unwrap();
                write!(f, "NOT ({})", operands[0].borrow())
            }
        }
    }
}
