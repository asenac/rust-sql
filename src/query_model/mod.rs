use crate::ast;
use crate::metadata::*;
use itertools::Itertools;
use std::cell::RefCell;
use std::cmp::*;
use std::collections::*;
use std::fmt;
use std::hash::Hash;
use std::hash::Hasher;
use std::rc::*;

mod dot_generator;
pub use dot_generator::DotGenerator;

mod model_generator;
pub use model_generator::ModelGenerator;

type BoxRef = Rc<RefCell<QGBox>>;
type BoxWeakRef = Weak<RefCell<QGBox>>;
type QuantifierRef = Rc<RefCell<Quantifier>>;
type QuantifierWeakRef = Weak<RefCell<Quantifier>>;
type ModelRef = Rc<RefCell<Model>>;
type ModelWeakRef = Weak<RefCell<Model>>;

type ColumnRefDesc = (i32, usize);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ColumnReference {
    quantifier: QuantifierRef,
    position: usize,
}

impl ColumnReference {
    fn to_desc(&self) -> ColumnRefDesc {
        (self.quantifier.borrow().id, self.position)
    }
}

#[derive(Clone)]
struct BaseColumn {
    parent_box: Weak<RefCell<QGBox>>,
    position: usize,
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
enum LogicalExprType {
    And,
    Or,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Value {
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
enum CmpOpType {
    Eq,
    Neq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
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
enum ExprType {
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

type ExprRef = Rc<RefCell<Expr>>;
type ColumnReferenceMap = HashMap<usize, Vec<ExprRef>>;
type PerQuantifierColumnReferenceMap = BTreeMap<QuantifierRef, ColumnReferenceMap>;
type PerBoxColumnReferenceMap = HashMap<i32, ColumnReferenceMap>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Expr {
    expr_type: ExprType,
    operands: Option<Vec<ExprRef>>,
}

impl Expr {
    fn make_base_column(parent_box: &BoxRef, position: usize) -> Self {
        let base_col = BaseColumn {
            parent_box: Rc::downgrade(&parent_box),
            position,
        };
        Self {
            expr_type: ExprType::BaseColumn(base_col),
            operands: None,
        }
    }

    fn make_column_ref(quantifier: QuantifierRef, position: usize) -> Self {
        let col_ref = ColumnReference {
            quantifier,
            position,
        };
        Self {
            expr_type: ExprType::ColumnReference(col_ref),
            operands: None,
        }
    }

    fn make_parameter(index: u64) -> Self {
        Self {
            expr_type: ExprType::Parameter(index),
            operands: None,
        }
    }

    fn make_in_list(term: ExprRef, list: Vec<ExprRef>) -> Self {
        let mut operands = vec![term];
        operands.extend(list);
        Self {
            expr_type: ExprType::InList,
            operands: Some(operands),
        }
    }

    fn make_logical(type_: LogicalExprType, list: Vec<ExprRef>) -> Self {
        Self {
            expr_type: ExprType::Logical(type_),
            operands: Some(list),
        }
    }

    fn make_literal(value: Value) -> Self {
        Self {
            expr_type: ExprType::Literal(value),
            operands: None,
        }
    }

    fn make_null() -> Self {
        Self {
            expr_type: ExprType::Literal(Value::Null),
            operands: None,
        }
    }

    fn make_cmp(cmp_type: CmpOpType, left: ExprRef, right: ExprRef) -> Self {
        Self {
            expr_type: ExprType::Cmp(cmp_type),
            operands: Some(vec![left, right]),
        }
    }

    fn make_case(operands: Vec<ExprRef>) -> Self {
        Self {
            expr_type: ExprType::Case,
            operands: Some(operands),
        }
    }

    fn make_is_null(operand: ExprRef) -> Self {
        Self {
            expr_type: ExprType::IsNull,
            operands: Some(vec![operand]),
        }
    }

    fn make_not(operand: ExprRef) -> Self {
        Self {
            expr_type: ExprType::Not,
            operands: Some(vec![operand]),
        }
    }

    fn make_tuple(operands: Vec<ExprRef>) -> Self {
        Self {
            expr_type: ExprType::Tuple,
            operands: Some(operands),
        }
    }

    fn is_equiv(&self, o: &Self) -> bool {
        match (&self.expr_type, &o.expr_type) {
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

    fn equiv_operands(&self, o: &Self) -> bool {
        let l = self.operands.as_ref().expect("operands expected");
        let r = o.operands.as_ref().expect("operands expected");
        l.len() == r.len()
            && l.iter()
                .zip(r.iter())
                .all(|(x, y)| x.borrow().is_equiv(&y.borrow()))
    }

    fn is_column_ref(&self) -> bool {
        if let ExprType::ColumnReference(_) = &self.expr_type {
            true
        } else {
            false
        }
    }

    fn get_quantifier(&self) -> Option<QuantifierRef> {
        if let ExprType::ColumnReference(c) = &self.expr_type {
            Some(Rc::clone(&c.quantifier))
        } else {
            None
        }
    }

    fn is_runtime_constant(&self) -> bool {
        match self.expr_type {
            ExprType::Parameter(_) | ExprType::Literal(_) => true,
            ExprType::Tuple => self
                .operands
                .iter()
                .all(|x| x.iter().all(|x| x.borrow().is_runtime_constant())),
            _ => false,
        }
    }

    fn is_aggregate_function(&self) -> bool {
        false
    }

    fn dereference(&self) -> Option<ExprRef> {
        if let ExprType::ColumnReference(c) = &self.expr_type {
            let q = c.quantifier.borrow();
            let b = q.input_box.borrow();
            Some(Rc::clone(&b.columns[c.position].expr))
        } else {
            None
        }
    }

    fn is_false_predicate(&self) -> bool {
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

    fn is_not_null(&self) -> Option<ExprRef> {
        if let ExprType::Not = &self.expr_type {
            let op = self.operands.as_ref().unwrap()[0].borrow();
            if let ExprType::IsNull = &op.expr_type {
                return Some(op.operands.as_ref().unwrap()[0].clone());
            }
        }
        None
    }

    fn result_arity(&self) -> usize {
        match &self.expr_type {
            ExprType::Tuple => self.operands.as_ref().unwrap().len(),
            _ => 1,
        }
    }

    fn is_existential_operand(&self) -> bool {
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

    fn is_existential_comparison(&self) -> bool {
        match &self.expr_type {
            ExprType::Cmp(CmpOpType::Eq) => self
                .operands
                .iter()
                .all(|x| x.iter().any(|x| x.borrow().is_existential_operand())),
            _ => false,
        }
    }

    fn normalize(&mut self) {
        if let Some(operands) = &self.operands {
            for o in operands {
                o.borrow_mut().normalize();
            }
        }
        match &mut self.expr_type {
            ExprType::BaseColumn(_)
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
}

fn visit_boxes_recurisvely<F>(obj: BoxRef, mut f: F)
where
    F: FnMut(&BoxRef),
{
    let mut stack = vec![obj];
    let mut visited = HashSet::new();

    while !stack.is_empty() {
        let top = stack.pop().unwrap();
        let box_id = top.borrow().id;
        if visited.insert(box_id) {
            f(&top);
            for q in top.borrow().quantifiers.iter() {
                let q = q.borrow();
                stack.push(q.input_box.clone());
            }
        }
    }
}

fn collect_column_references(
    expr_ref: &ExprRef,
    column_references: &mut PerQuantifierColumnReferenceMap,
) {
    let expr = expr_ref.borrow();
    if let ExprType::ColumnReference(c) = &expr.expr_type {
        column_references
            .entry(c.quantifier.clone())
            .or_insert(HashMap::new())
            .entry(c.position)
            .or_insert(Vec::new())
            .push(expr_ref.clone());
    }
    if let Some(operands) = &expr.operands {
        for o in operands {
            collect_column_references(o, column_references);
        }
    }
}

fn collect_column_references_recursively(
    obj: BoxRef,
    column_references: &mut PerQuantifierColumnReferenceMap,
) {
    visit_boxes_recurisvely(obj, |obj| {
        let mut f = |e: &mut ExprRef| {
            collect_column_references(e, column_references);
        };
        obj.borrow_mut().visit_expressions(&mut f);
    });
}

fn collect_used_columns(expr_ref: &ExprRef, column_references: &mut PerBoxColumnReferenceMap) {
    let expr = expr_ref.borrow();
    if let ExprType::ColumnReference(c) = &expr.expr_type {
        column_references
            .entry(c.quantifier.borrow().input_box.borrow().id)
            .or_insert(HashMap::new())
            .entry(c.position)
            .or_insert(Vec::new())
            .push(expr_ref.clone());
    }
    if let Some(operands) = &expr.operands {
        for o in operands {
            collect_used_columns(o, column_references);
        }
    }
}

/// Note: this is very column-removal specific
fn collect_used_columns_recursively(obj: BoxRef, column_references: &mut PerBoxColumnReferenceMap) {
    visit_boxes_recurisvely(obj, |top| {
        let mut f = |e: &mut ExprRef| {
            collect_used_columns(e, column_references);
        };
        top.borrow_mut().visit_expressions(&mut f);
        let top = top.borrow();

        // Note: mark the used from the same branch as used for the rest of the branches
        if let BoxType::Union = top.box_type {
            let first_branch_id = top
                .first_quantifier()
                .unwrap()
                .borrow()
                .input_box
                .borrow()
                .id;
            let used_cols = column_references
                .entry(first_branch_id)
                .or_default()
                .into_iter()
                .map(|(col, _)| (*col, Vec::new()))
                .collect::<ColumnReferenceMap>();
            for q in top.quantifiers.iter().skip(1) {
                let id = q.borrow().input_box.borrow().id;
                column_references.insert(id, used_cols.clone());
            }
        }
    });
}

fn get_quantifiers(expr: &ExprRef) -> QuantifierSet {
    let mut result = BTreeSet::new();
    collect_quantifiers(&mut result, expr);
    result
}

fn get_existential_quantifiers(expr: &ExprRef) -> QuantifierSet {
    get_quantifiers(expr)
        .iter()
        .filter(|q| q.borrow().quantifier_type == QuantifierType::Existential)
        .cloned()
        .collect()
}

fn collect_quantifiers(quantifiers: &mut QuantifierSet, expr: &ExprRef) {
    let mut stack = vec![Rc::clone(expr)];
    while let Some(expr) = stack.pop() {
        let e = expr.borrow();
        if let Some(q) = e.get_quantifier() {
            quantifiers.insert(q);
        } else if let Some(operands) = &e.operands {
            for o in operands {
                stack.push(Rc::clone(&o));
            }
        }
    }
}

/// Deep clone of an expression
fn deep_clone(expr: &ExprRef) -> ExprRef {
    let mut e = expr.borrow().clone();
    if let Some(operands) = &mut e.operands {
        for o in operands.iter_mut() {
            *o = deep_clone(o);
        }
    }
    make_ref(e)
}

fn compute_class_equivalence(predicates: &Vec<ExprRef>) -> HashMap<ColumnRefDesc, usize> {
    let mut classes = HashMap::new();
    let mut next_class: usize = 0;
    for p in predicates.iter() {
        let p = p.borrow();
        if let ExprType::Cmp(CmpOpType::Eq) = &p.expr_type {
            if let Some(operands) = &p.operands {
                let column_refs = operands
                    .iter()
                    .filter_map(|x| {
                        let x = x.borrow();
                        if let ExprType::ColumnReference(c) = &x.expr_type {
                            Some(c.to_desc())
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();
                if column_refs.len() == 2 {
                    let mut class = None;
                    for c in column_refs.iter() {
                        if let Some(c) = classes.get(c) {
                            class = Some(*c);
                            break;
                        }
                    }
                    let class = if let Some(c) = class {
                        c
                    } else {
                        let c = next_class;
                        next_class += 1;
                        c
                    };
                    column_refs.iter().for_each(|x| {
                        classes.insert(*x, class);
                    });
                }
            }
        }
    }
    classes
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

#[derive(Clone)]
struct Column {
    name: Option<String>,
    expr: ExprRef,
}

use ast::{Direction, JoinType};

#[derive(Clone)]
struct KeyItem {
    expr: ExprRef,
    dir: Direction,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum DistinctOperation {
    Permit,
    Enforce,
    Preserve,
}

struct Select {
    limit: Option<ExprRef>,
    order_by: Option<Vec<KeyItem>>,
}

impl Select {
    fn new() -> Self {
        Self {
            limit: None,
            order_by: None,
        }
    }
}

struct Grouping {
    groups: Vec<KeyItem>,
}

impl Grouping {
    fn new() -> Self {
        Self { groups: Vec::new() }
    }
}

enum BoxType {
    Select(Select),
    BaseTable(TableMetadata),
    Grouping(Grouping),
    OuterJoin,
    Union,
}

struct QGBox {
    model: ModelWeakRef,
    id: i32,
    box_type: BoxType,
    columns: Vec<Column>,
    quantifiers: QuantifierSet,
    ranging_quantifiers: Vec<QuantifierWeakRef>,
    predicates: Option<Vec<ExprRef>>,
    distinct_operation: DistinctOperation,
    unique_keys: Vec<Vec<usize>>,
}

fn make_quantifier_set(v: Vec<QuantifierRef>) -> QuantifierSet {
    let mut s = BTreeSet::new();
    s.extend(v);
    s
}

impl QGBox {
    fn new(model: ModelWeakRef, id: i32, box_type: BoxType) -> BoxRef {
        make_ref(Self {
            model,
            id,
            box_type,
            columns: Vec::new(),
            quantifiers: BTreeSet::new(),
            ranging_quantifiers: Vec::new(),
            predicates: None,
            distinct_operation: DistinctOperation::Preserve,
            unique_keys: Vec::new(),
        })
    }
    /// use add_quantifier_to_box instead to properly set the parent box of the quantifier
    fn add_quantifier(&mut self, q: QuantifierRef) {
        self.quantifiers.insert(q);
    }
    fn remove_quantifier(&mut self, q: &QuantifierRef) {
        self.quantifiers.remove(q);
    }
    fn add_column(&mut self, mut name: Option<String>, expr: ExprRef) -> usize {
        if name.is_none() {
            if let ExprType::ColumnReference(c) = &expr.borrow().expr_type {
                let q = c.quantifier.borrow();
                let input_box = q.input_box.borrow();
                name = input_box.columns[c.position].name.clone();
            }
        }
        let pos = self.columns.len();
        self.columns.push(Column { name, expr });
        pos
    }
    fn add_column_if_not_exists(&mut self, expr: Expr) -> usize {
        for (i, c) in self.columns.iter().enumerate() {
            if c.expr.borrow().is_equiv(&expr) {
                return i;
            }
        }
        self.add_column(None, make_ref(expr))
    }
    fn add_predicate(&mut self, predicate: ExprRef) {
        let predicates = {
            let borrowed = predicate.borrow();
            if let ExprType::Logical(LogicalExprType::And) = &borrowed.expr_type {
                drop(borrowed);
                predicate.borrow_mut().operands.as_ref().unwrap().clone()
            } else {
                drop(borrowed);
                vec![predicate]
            }
        };
        if predicates.len() > 0 {
            if self.predicates.is_none() {
                self.predicates = Some(Vec::new());
            }
            // do not insert duplicated predicates
            let mut_p = self.predicates.as_mut().unwrap();
            for p in predicates {
                let mut found = false;
                for existing in mut_p.iter() {
                    if p.borrow().is_equiv(&existing.borrow()) {
                        found = true;
                        break;
                    }
                }
                if !found {
                    mut_p.push(p);
                }
            }
        }
    }

    fn remove_predicate(&mut self, predicate: &ExprRef) {
        if let Some(predicates) = &mut self.predicates {
            predicates.retain(|x| x.as_ptr() != predicate.as_ptr());
        }
    }

    fn add_unique_key(&mut self, key: Vec<usize>) {
        self.unique_keys.push(key);
    }

    fn has_predicates(&self) -> bool {
        !self.predicates.is_none() && !self.predicates.as_ref().unwrap().is_empty()
    }

    fn is_select(&self) -> bool {
        match self.box_type {
            BoxType::Select(_) => true,
            _ => false,
        }
    }

    fn get_box_type_str(&self) -> &'static str {
        match self.box_type {
            BoxType::Select(_) => "Select",
            BoxType::OuterJoin => "OuterJoin",
            BoxType::BaseTable(_) => "BaseTable",
            BoxType::Grouping(_) => "Grouping",
            BoxType::Union => "Union",
        }
    }

    fn set_order_by(&mut self, order_by: Vec<KeyItem>) {
        match &mut self.box_type {
            BoxType::Select(a) => {
                a.order_by = Some(order_by);
            }
            _ => panic!(),
        }
    }

    fn set_limit(&mut self, limit: ExprRef) {
        match &mut self.box_type {
            BoxType::Select(a) => {
                a.limit = Some(limit);
            }
            _ => panic!(),
        }
    }

    fn add_group(&mut self, group: KeyItem) {
        match &mut self.box_type {
            BoxType::Grouping(g) => {
                g.groups.push(group);
            }
            _ => panic!(),
        }
    }

    fn recompute_unique_keys(&mut self) {
        self.unique_keys.clear();

        // helper function: look at the keys in the single input box and
        // check if any of them is fully projected by the current box
        let single_quantifier_case =
            |quantifiers: Vec<QuantifierRef>, columns: &Vec<Column>| -> Vec<Vec<usize>> {
                let q = quantifiers.iter().next().expect("expected quantifier");
                // note: the same input column may be projected several times
                let mut input_col_to_col = HashMap::new();
                let mut keys = Vec::new();

                for (col, column) in columns.iter().enumerate() {
                    if let ExprType::ColumnReference(c) = &column.expr.borrow().expr_type {
                        if c.quantifier == *q {
                            input_col_to_col
                                .entry(c.position)
                                .or_insert_with(Vec::new)
                                .push(col);
                        }
                    }
                }

                for key in q.borrow().input_box.borrow().unique_keys.iter() {
                    let new_key = key
                        .iter()
                        .filter_map(|x| input_col_to_col.get(x))
                        .cloned()
                        .collect::<Vec<_>>();
                    if new_key.len() == key.len() {
                        keys.extend(new_key.into_iter().multi_cartesian_product());
                    }
                }

                keys
            };

        match &self.box_type {
            BoxType::OuterJoin | BoxType::Select(_) => {
                let is_outer_join = if let BoxType::OuterJoin = &self.box_type {
                    true
                } else {
                    false
                };
                // collect non-subquery quantifiers
                let quantifiers = self
                    .quantifiers
                    .iter()
                    .filter(|q| !q.borrow().is_subquery())
                    .cloned()
                    .collect::<Vec<_>>();

                if quantifiers.len() == 1 {
                    assert!(!is_outer_join);
                    single_quantifier_case(quantifiers, &self.columns)
                        .into_iter()
                        .for_each(|key| {
                            self.add_unique_key(key);
                        });
                } else if quantifiers.len() > 1 {
                    // general case: for any input unique key all key items
                    // must be connected to a unique key from all other quantifiers
                    // via equality predicates.
                    let classes = if let Some(predicates) = &self.predicates {
                        Some(compute_class_equivalence(predicates))
                    } else {
                        None
                    };
                    if let Some(classes) = &classes {
                        // classes projected by the box
                        let mut projected_classes = HashMap::new();
                        for (i, c) in self.columns.iter().enumerate() {
                            if let ExprType::ColumnReference(c) = &c.expr.borrow().expr_type {
                                // outer join: the columns from the non-preserving side may
                                // not be unique
                                if is_outer_join
                                    && c.quantifier.borrow().quantifier_type
                                        == QuantifierType::Foreach
                                {
                                    continue;
                                }
                                if let Some(class) = classes.get(&c.to_desc()) {
                                    // the same class may be projected several times through different columns
                                    projected_classes
                                        .entry(class)
                                        .or_insert_with(Vec::new)
                                        .push(i);
                                }
                            }
                        }
                        let keys_by_q: HashMap<_, _> = quantifiers
                            .iter()
                            .map(|q| {
                                let q = q.borrow();
                                let b = q.input_box.borrow();
                                (q.id, b.unique_keys.clone())
                            })
                            .collect();
                        let first_id: i32 = quantifiers.first().unwrap().borrow().id;
                        if let Some(unique_keys) = keys_by_q.get(&first_id) {
                            // given a key returns the classes of the key
                            let key_classes = |id: i32, key: &Vec<usize>| {
                                key.iter()
                                    .filter_map(|x| {
                                        if let Some(class) = classes.get(&(id, *x)) {
                                            Some(*class)
                                        } else {
                                            None
                                        }
                                    })
                                    .collect::<HashSet<_>>()
                            };
                            for outer_key in unique_keys {
                                let outer_key_classes = key_classes(first_id, outer_key);
                                if outer_key_classes.len() == outer_key.len() {
                                    let eq_keys = keys_by_q
                                        .iter()
                                        .filter(|(x, _)| **x != first_id)
                                        .filter_map(|(id, keys)| {
                                            for key in keys {
                                                if key.len() == outer_key.len() {
                                                    let kc = key_classes(*id, key);
                                                    if kc == outer_key_classes {
                                                        return Some((*id, key.clone()));
                                                    }
                                                }
                                            }
                                            None
                                        })
                                        .count();
                                    // check if an equivalent key was found for every other quantifier
                                    if eq_keys + 1 == quantifiers.len() {
                                        let mut projected_key = outer_key_classes
                                            .iter()
                                            .filter_map(|class| projected_classes.get(&class))
                                            .cloned()
                                            .collect::<Vec<_>>();
                                        // check if all column from the key are projected
                                        if projected_key.len() == outer_key.len() {
                                            for key in
                                                projected_key.drain(..).multi_cartesian_product()
                                            {
                                                self.add_unique_key(key);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            BoxType::BaseTable(metadata) => {
                let projected_cols: HashSet<_> = self
                    .columns
                    .iter()
                    .filter_map(|x| {
                        if let ExprType::BaseColumn(c) = &x.expr.borrow().expr_type {
                            Some(c.position)
                        } else {
                            None
                        }
                    })
                    .collect();
                for index in metadata.indexes.iter() {
                    if index.unique && index.columns.iter().all(|x| projected_cols.contains(x)) {
                        self.unique_keys.push(index.columns.clone());
                    }
                }
            }
            BoxType::Grouping(grouping) => {
                let quantifiers = self.quantifiers.iter().cloned().collect::<Vec<_>>();

                // projected columns for each element of the grouping key
                let mut projected_key_columns = grouping
                    .groups
                    .iter()
                    .map(|x| {
                        self.columns
                            .iter()
                            .enumerate()
                            .filter_map(|(i, y)| {
                                if x.expr.borrow().is_equiv(&y.expr.borrow()) {
                                    Some(i)
                                } else {
                                    None
                                }
                            })
                            .collect::<Vec<_>>()
                    })
                    .filter(|x| !x.is_empty())
                    .collect::<Vec<_>>();
                // the grouping key is a unique key of the output relation iff all
                // the elements of the grouping key are projected
                if projected_key_columns.len() == grouping.groups.len() {
                    // note: multi_cartesian_product is used since the same key elements
                    // may be projected several times
                    for key in projected_key_columns.drain(..).multi_cartesian_product() {
                        self.add_unique_key(key);
                    }
                }

                // if the input quantifier has a unique key that is fully
                // included in the projected grouping key, then add it as a
                // unique key of the grouping relation
                single_quantifier_case(quantifiers, &self.columns)
                    .into_iter()
                    .for_each(|key| {
                        self.add_unique_key(key);
                    });
            }
            _ => {}
        }

        if let DistinctOperation::Enforce = self.distinct_operation {
            let num_columns = self.columns.len();
            self.unique_keys.push((0..num_columns).collect());
        }

        // remove duplicated keys. We could remove keys which prefix is also a key
        self.unique_keys.dedup();
    }

    fn visit_expressions<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut ExprRef) -> (),
    {
        for c in &mut self.columns {
            f(&mut c.expr);
        }
        if let Some(predicates) = &mut self.predicates {
            for p in predicates.iter_mut() {
                f(p);
            }
        }
        match &mut self.box_type {
            BoxType::Select(s) => {
                if s.limit.is_some() {
                    f(s.limit.as_mut().unwrap());
                }
                if s.order_by.is_some() {
                    for p in s.order_by.as_mut().unwrap().iter_mut() {
                        f(&mut p.expr);
                    }
                }
            }
            BoxType::Grouping(g) => {
                for p in g.groups.iter_mut() {
                    f(&mut p.expr);
                }
            }
            _ => {}
        }
    }

    fn visit_expressions_recursively<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut ExprRef) -> (),
    {
        let mut i = |e: &mut ExprRef| {
            let mut stack = vec![Rc::clone(e)];
            while let Some(mut e) = stack.pop() {
                f(&mut e);
                if let Some(operands) = &mut e.borrow_mut().operands {
                    stack.extend(operands.iter().cloned());
                }
            }
        };
        self.visit_expressions(&mut i);
    }

    fn first_quantifier(&self) -> Option<QuantifierRef> {
        self.quantifiers.iter().cloned().next()
    }

    fn distinct_tuples(&self) -> bool {
        self.distinct_operation == DistinctOperation::Enforce || !self.unique_keys.is_empty()
    }

    fn add_all_columns(&mut self) {
        let quantifiers = self.quantifiers.clone();
        for q in quantifiers {
            let bq = q.borrow();
            if bq.is_subquery() {
                continue;
            }
            let input_box = bq.input_box.borrow();
            for (i, c) in input_box.columns.iter().enumerate() {
                let expr = Expr::make_column_ref(Rc::clone(&q), i);
                self.add_column(c.name.clone(), make_ref(expr));
            }
        }
    }
}

fn add_quantifier_to_box(b: &BoxRef, q: &QuantifierRef) {
    let mut bb = b.borrow_mut();
    bb.add_quantifier(Rc::clone(q));
    let mut bq = q.borrow_mut();
    bq.parent_box = Rc::downgrade(&b);
}

#[derive(PartialEq, Copy, Clone)]
enum QuantifierType {
    Foreach,
    PreservedForeach,
    Existential,
    All,
    Any,
    Scalar,
}

impl fmt::Display for QuantifierType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            QuantifierType::Foreach => write!(f, "F"),
            QuantifierType::PreservedForeach => write!(f, "P"),
            QuantifierType::Existential => write!(f, "E"),
            QuantifierType::All => write!(f, "All"),
            QuantifierType::Any => write!(f, "Any"),
            QuantifierType::Scalar => write!(f, "S"),
        }
    }
}

type QuantifierSet = BTreeSet<QuantifierRef>;

struct Quantifier {
    id: i32,
    quantifier_type: QuantifierType,
    input_box: BoxRef,
    parent_box: Weak<RefCell<QGBox>>,
    alias: Option<String>,
    weak_self: Option<QuantifierWeakRef>,
}

impl Quantifier {
    fn new(
        id: i32,
        quantifier_type: QuantifierType,
        input_box: BoxRef,
        parent_box: &BoxRef,
    ) -> QuantifierRef {
        let q = make_ref(Self {
            id,
            quantifier_type,
            input_box: input_box.clone(),
            parent_box: Rc::downgrade(parent_box),
            alias: None,
            weak_self: None,
        });
        input_box
            .borrow_mut()
            .ranging_quantifiers
            .push(Rc::downgrade(&q));
        q.borrow_mut().weak_self = Some(Rc::downgrade(&q));
        q
    }

    fn set_alias(&mut self, alias: String) {
        self.alias = Some(alias);
    }

    fn get_effective_name(&self) -> Option<String> {
        if self.alias.is_some() {
            return self.alias.clone();
        }
        let b = self.input_box.borrow();
        if let BoxType::BaseTable(t) = &b.box_type {
            return Some(t.name.clone());
        }
        return None;
    }

    fn is_subquery(&self) -> bool {
        match &self.quantifier_type {
            QuantifierType::Existential
            | QuantifierType::Scalar
            | QuantifierType::All
            | QuantifierType::Any => true,
            _ => false,
        }
    }

    fn weak(&self) -> QuantifierWeakRef {
        self.weak_self.as_ref().unwrap().clone()
    }

    fn replace_input_box(&mut self, b: BoxRef) {
        // deatch from previous box
        self.input_box
            .borrow_mut()
            .ranging_quantifiers
            .retain(|x| x.as_ptr() != self.weak().as_ptr());

        // attach to new box
        self.input_box = b;
        self.input_box
            .borrow_mut()
            .ranging_quantifiers
            .push(self.weak());
    }
}

impl Drop for Quantifier {
    fn drop(&mut self) {
        self.input_box
            .borrow_mut()
            .ranging_quantifiers
            .retain(|x| x.as_ptr() != self.weak().as_ptr())
    }
}

impl PartialEq for Quantifier {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Quantifier {}

impl PartialOrd for Quantifier {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.id.cmp(&other.id))
    }
}

impl Ord for Quantifier {
    fn cmp(&self, other: &Self) -> Ordering {
        self.id.cmp(&other.id)
    }
}

impl Hash for Quantifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

struct ModelIds {
    next_box_id: i32,
    next_quantifier_id: i32,
}

impl ModelIds {
    fn new() -> Self {
        Self {
            next_box_id: 0,
            next_quantifier_id: 0,
        }
    }

    fn get_box_id(&mut self) -> i32 {
        let id = self.next_box_id;
        self.next_box_id += 1;
        id
    }

    fn get_quantifier_id(&mut self) -> i32 {
        let id = self.next_quantifier_id;
        self.next_quantifier_id += 1;
        id
    }
}

pub struct Model {
    top_box: BoxRef,
    ids: ModelIds,
}

impl Model {
    fn new() -> ModelRef {
        make_ref(Self {
            // dummy box, will be replaced later
            top_box: QGBox::new(ModelWeakRef::new(), 0, BoxType::Select(Select::new())),
            ids: ModelIds::new(),
        })
    }

    fn replace_top_box(&mut self, new_box: BoxRef) -> BoxRef {
        let other = Rc::clone(&self.top_box);
        self.top_box = new_box;
        other
    }

    // @todo validate that distinct operation can only be enforeced by selects and unions
    fn validate(&self) -> Result<(), String> {
        let mut box_stack = vec![(Rc::clone(&self.top_box), BTreeSet::<QuantifierRef>::new())];
        let mut visited = HashSet::new();
        while let Some((b, parent_scope)) = box_stack.pop() {
            visited.insert(b.as_ptr());

            let mut b = b.borrow_mut();
            let mut collected_quantifiers = BTreeSet::new();
            let mut f = |e: &mut ExprRef| {
                collect_quantifiers(&mut collected_quantifiers, e);
            };
            b.visit_expressions(&mut f);

            for uq in b.quantifiers.iter() {
                collected_quantifiers.remove(uq);
                let q = uq.borrow();
                let input_box = Rc::clone(&q.input_box);
                if visited.contains(&input_box.as_ptr()) {
                    continue;
                }

                // @todo perhaps use a COW wrapper
                let mut nested_scope = parent_scope.clone();
                if q.is_subquery() {
                    // add all the sibling quantifiers of the current one but not the current one
                    for oq in b.quantifiers.iter() {
                        if oq.as_ptr() != uq.as_ptr() {
                            nested_scope.insert(Rc::clone(&oq));
                        }
                    }
                }
                box_stack.push((input_box, nested_scope));
            }

            let diff: Vec<QuantifierRef> = collected_quantifiers
                .difference(&parent_scope)
                .cloned()
                .collect();
            if !diff.is_empty() {
                // Note: this is valid for quantifiers from the outer context
                return Err(format!(
                    "box {} contains references to external quantifiers",
                    b.id
                ));
            }
        }
        Ok(())
    }
}

fn make_ref<T>(t: T) -> Rc<RefCell<T>> {
    Rc::new(RefCell::new(t))
}

//
// Rewrite rules for the graph
//

use crate::rewrite_engine;

struct EmptyRule {}

impl rewrite_engine::Rule<BoxRef> for EmptyRule {
    fn name(&self) -> &'static str {
        "EmptyRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, _obj: &BoxRef) -> bool {
        true
    }
    fn action(&mut self, _obj: &mut BoxRef) {}
}

struct SingleTraversalRule {
    rules: Vec<RuleBox>,
    current: usize,
}

impl SingleTraversalRule {
    fn new(rules: Vec<RuleBox>) -> Self {
        Self { rules, current: 0 }
    }
}

impl rewrite_engine::Rule<BoxRef> for SingleTraversalRule {
    fn name(&self) -> &'static str {
        "SingleTraversalRule"
    }
    fn apply_top_down(&self) -> bool {
        if let Some(r) = self.rules.iter().next() {
            r.apply_top_down()
        } else {
            false
        }
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.current = 0;
        while self.current < self.rules.len() {
            if self.rules[self.current].condition(obj) {
                return true;
            }
            self.current += 1;
        }
        false
    }
    fn action(&mut self, obj: &mut BoxRef) {
        self.rules[self.current].action(obj);
        self.current += 1;
        while self.current < self.rules.len() {
            if self.rules[self.current].condition(obj) {
                self.rules[self.current].action(obj);
            }
            self.current += 1;
        }
    }
}

struct NormalizationRule {}

impl NormalizationRule {
    fn new() -> Self {
        Self {}
    }
}

impl rewrite_engine::Rule<BoxRef> for NormalizationRule {
    fn name(&self) -> &'static str {
        "NormalizationRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, _obj: &BoxRef) -> bool {
        true
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let mut f = |e: &mut ExprRef| e.borrow_mut().normalize();
        obj.borrow_mut().visit_expressions(&mut f);
    }
}

struct ConstraintPropagationRule {
    new_predicates: Vec<ExprRef>,
}

impl ConstraintPropagationRule {
    fn new() -> Self {
        Self {
            new_predicates: Vec::new(),
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for ConstraintPropagationRule {
    fn name(&self) -> &'static str {
        "ConstraintPropagationRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        let obj = obj.borrow();
        if let BoxType::Select(_) = &obj.box_type {
            if let Some(predicates) = &obj.predicates {
                for p in predicates.iter() {
                    let p = p.borrow();
                    match &p.expr_type {
                        ExprType::Cmp(_) => {
                            if let Some(operands) = &p.operands {
                                for o in operands.iter().filter_map(|e| {
                                    let x = e.borrow();
                                    if let ExprType::ColumnReference(_) = &x.expr_type {
                                        Some(e.clone())
                                    } else {
                                        None
                                    }
                                }) {
                                    let is_null = make_ref(Expr::make_is_null(o));
                                    let not = make_ref(Expr::make_not(is_null));
                                    self.new_predicates.push(not);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        !self.new_predicates.is_empty()
    }
    fn action(&mut self, obj: &mut BoxRef) {
        for p in self.new_predicates.drain(..) {
            obj.borrow_mut().add_predicate(p);
        }
    }
}

struct SemiJoinRemovalRule {
    to_convert: QuantifierSet,
}

impl SemiJoinRemovalRule {
    fn new() -> Self {
        Self {
            to_convert: BTreeSet::new(),
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for SemiJoinRemovalRule {
    fn name(&self) -> &'static str {
        "SemiJoinRemovalRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.to_convert.clear();
        let obj = obj.borrow();
        if let BoxType::Select(_) = &obj.box_type {
            if let Some(predicates) = &obj.predicates {
                // collect all existential quantifiers which belong in top level predicates
                // and which input box returns unique tuples
                self.to_convert = predicates
                    .iter()
                    .filter_map(|x| {
                        if x.borrow().is_existential_comparison() {
                            let existential_quantifiers = get_existential_quantifiers(x);
                            // @note this should actually be an assert
                            if existential_quantifiers.len() == 1 {
                                let q = existential_quantifiers.into_iter().next().unwrap();
                                if q.borrow().input_box.borrow().distinct_tuples() {
                                    return Some(q);
                                }
                            }
                        }
                        None
                    })
                    .fold(BTreeSet::new(), |mut acc, x| {
                        acc.insert(x);
                        acc
                    });
            }
        }
        !self.to_convert.is_empty()
    }
    fn action(&mut self, _obj: &mut BoxRef) {
        for q in self.to_convert.iter() {
            q.borrow_mut().quantifier_type = QuantifierType::Foreach;
        }
    }
}

//
// GroupByRemoval
//

struct GroupByRemovalRule {}

impl GroupByRemovalRule {
    fn new() -> Self {
        Self {}
    }
}

impl rewrite_engine::Rule<BoxRef> for GroupByRemovalRule {
    fn name(&self) -> &'static str {
        "GroupByRemovalRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        let obj = obj.borrow();
        // note: this should be an assert
        if obj.quantifiers.len() == 1 {
            if let BoxType::Grouping(grouping) = &obj.box_type {
                // no aggregate function is used. note: could this be relazed?
                // sum(a) = a if a is unique, for example.
                if !obj
                    .columns
                    .iter()
                    .any(|c| c.expr.borrow().is_aggregate_function())
                {
                    let column_refs_in_key = grouping
                        .groups
                        .iter()
                        .filter_map(|x| {
                            let x = x.expr.borrow();
                            if let ExprType::ColumnReference(c) = &x.expr_type {
                                Some(c.position)
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<_>>();
                    // all items in the grouping key must be column references
                    if column_refs_in_key.len() == grouping.groups.len() {
                        let q = obj.quantifiers.iter().next().unwrap();
                        let q = q.borrow();
                        let b = q.input_box.borrow();
                        // there must be a unique key in the input box that
                        // contains all members of the grouping key
                        return b
                            .unique_keys
                            .iter()
                            .any(|key| column_refs_in_key.iter().all(|x| key.contains(x)));
                    }
                }
            }
        }
        false
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let mut obj = obj.borrow_mut();
        obj.box_type = BoxType::Select(Select::new());
        obj.recompute_unique_keys();
    }
}

//
// MergeRule
//

struct MergeRule {
    to_merge: QuantifierSet,
}

impl MergeRule {
    fn new() -> Self {
        Self {
            to_merge: BTreeSet::new(),
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for MergeRule {
    fn name(&self) -> &'static str {
        "MergeRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.to_merge.clear();
        let borrowed_obj = obj.borrow();

        match &borrowed_obj.box_type {
            BoxType::Select(outer_select) => {
                for q in &borrowed_obj.quantifiers {
                    let borrowed_q = q.borrow();
                    if let QuantifierType::Foreach = borrowed_q.quantifier_type {
                        let input_box = borrowed_q.input_box.borrow();
                        if let BoxType::Select(inner_select) = &input_box.box_type {
                            if inner_select.order_by.is_none() && inner_select.limit.is_none() {
                                self.to_merge.insert(Rc::clone(q));
                            } else if borrowed_obj.quantifiers.len() == 1
                                && (outer_select.order_by.is_none() || inner_select.limit.is_none())
                            // @todo revisit this
                            {
                                self.to_merge.insert(Rc::clone(q));
                            }
                        }
                    }
                }
            }
            BoxType::OuterJoin => {
                for q in &borrowed_obj.quantifiers {
                    let borrowed_q = q.borrow();
                    match borrowed_q.quantifier_type {
                        QuantifierType::PreservedForeach | QuantifierType::Foreach => {
                            let input_box = borrowed_q.input_box.borrow();
                            if let BoxType::Select(inner_select) = &input_box.box_type {
                                if input_box.quantifiers.len() == 1
                                    && inner_select.order_by.is_none()
                                    && inner_select.limit.is_none()
                                    && !input_box.has_predicates()
                                {
                                    self.to_merge.insert(Rc::clone(q));
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        !self.to_merge.is_empty()
    }
    fn action(&mut self, obj: &mut BoxRef) {
        // collect all column references under `obj` to be able to replace the
        // column references to the quantifiers being removed from within correlated
        // siblings.
        let mut column_references = BTreeMap::new();
        collect_column_references_recursively(obj.clone(), &mut column_references);

        let mut to_merge = self.to_merge.iter().cloned().collect::<Vec<_>>();
        self.to_merge.clear();

        for q in to_merge.drain(..) {
            // predicates in the boxes being removed that will be added to the current box
            let mut pred_to_add = Vec::new();
            let mut to_replace = BTreeMap::new();

            // borrow scope
            {
                let input_box = q.borrow().input_box.clone();
                let input_box = input_box.borrow();
                if let Some(pred_to_merge) = &input_box.predicates {
                    // deep_clone :facepalm:
                    pred_to_add.extend(pred_to_merge.iter().map(|x| deep_clone(x)));
                }
                for oq in &input_box.quantifiers {
                    if input_box.ranging_quantifiers.len() == 1 {
                        add_quantifier_to_box(obj, oq);
                    } else {
                        // this is a CTE: we must clone its quantifiers before adding
                        // to the current box
                        let b_oq = oq.borrow();
                        let new_q = Quantifier::new(
                            input_box
                                .model
                                .upgrade()
                                .expect("invalid model")
                                .borrow_mut()
                                .ids
                                .get_quantifier_id(),
                            b_oq.quantifier_type,
                            b_oq.input_box.clone(),
                            &obj,
                        );
                        add_quantifier_to_box(obj, &new_q);
                        to_replace.insert(oq.clone(), new_q);
                    }
                }
            }

            let mut obj = obj.borrow_mut();
            obj.remove_quantifier(&q);

            // @todo revisit this
            if let BoxType::Select(outer_select) = &mut obj.box_type {
                if let BoxType::Select(inner_select) = &q.borrow().input_box.borrow().box_type {
                    if outer_select.limit.is_none() {
                        outer_select.limit = inner_select.limit.clone();
                    }
                    if outer_select.order_by.is_none() {
                        outer_select.order_by = inner_select.order_by.clone();
                    }
                }
            }

            let mut rule = ReplaceQuantifierRule {
                to_replace: &to_replace,
            };

            if let Some(column_refs) = column_references.remove(&q) {
                column_refs
                    .into_iter()
                    .map(|(_, v)| v)
                    .flatten()
                    // note: it is theoretically possible for the map to contain multiple references
                    // to the same underlying expression
                    .sorted_by_key(|e| e.as_ptr())
                    .dedup_by(|x, y| x.as_ptr() == y.as_ptr())
                    .for_each(|e| {
                        let original_e = e.clone();
                        let mut e = e.borrow().dereference().expect("expected column reference");
                        if !to_replace.is_empty() {
                            rewrite_engine::deep_apply_rule(&mut rule, &mut e);
                        }
                        // note: this is sort of a trick: instead of traversing the subgraph using
                        // the rewrite engine we have already collected all column references to
                        // all quantifiers, and here we overwrite the expression
                        *original_e.borrow_mut() = e.borrow().clone();
                    });
            }
            if !pred_to_add.is_empty() {
                // predicates come from the box pointed by the quantifier being removed, so they
                // are already dereferenced.
                if !to_replace.is_empty() {
                    for obj in pred_to_add.iter_mut() {
                        rewrite_engine::deep_apply_rule(&mut rule, obj);
                    }
                }
                if obj.predicates.is_none() {
                    obj.predicates = Some(pred_to_add);
                } else {
                    obj.predicates.as_mut().unwrap().extend(pred_to_add);
                }
            }
        }

        obj.borrow_mut().recompute_unique_keys();
    }
}

//
// ColumnRemovalRule
//

struct ColumnRemovalRule {
    column_references: Option<PerBoxColumnReferenceMap>,
    top_box: Option<BoxRef>,
    stack_count: usize,
}

impl ColumnRemovalRule {
    fn new() -> Self {
        Self {
            column_references: None,
            top_box: None,
            stack_count: 0,
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for ColumnRemovalRule {
    fn name(&self) -> &'static str {
        "ColumnRemovalRule"
    }
    fn apply_top_down(&self) -> bool {
        true
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        if obj.as_ptr() == self.top_box.as_ref().unwrap().as_ptr() {
            return false;
        }
        let obj = obj.borrow();
        obj.columns.len()
            != self
                .column_references
                .as_mut()
                .unwrap()
                .entry(obj.id)
                .or_default()
                .len()
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let mut obj = obj.borrow_mut();
        let column_references = self
            .column_references
            .as_mut()
            .unwrap()
            .entry(obj.id)
            .or_default();
        let mut new_columns_spec = column_references.iter().collect::<Vec<_>>();
        new_columns_spec.sort_by_key(|(x, _)| *x);
        for (new_pos, (_old_pos, col_refs)) in new_columns_spec.iter().enumerate() {
            for col_ref in col_refs.iter() {
                let mut col_ref = col_ref.borrow_mut();
                if let ExprType::ColumnReference(c) = &mut col_ref.expr_type {
                    c.position = new_pos;
                }
            }
        }
        obj.columns = obj
            .columns
            .drain(..)
            .enumerate()
            .filter(|(i, _)| column_references.contains_key(i))
            .map(|(_, x)| x)
            .collect::<Vec<_>>();
        obj.recompute_unique_keys();
        // invalidate column references
        self.column_references = None;
    }
    fn begin(&mut self, obj: &BoxRef) {
        if self.stack_count == 0 {
            self.top_box = Some(obj.clone());
        }
        if self.column_references.is_none() {
            // Re-compute the column referneces map starting from the top level box of the
            // query graph
            let mut column_references = HashMap::new();
            collect_used_columns_recursively(self.top_box.clone().unwrap(), &mut column_references);
            self.column_references = Some(column_references);
        }
        self.stack_count += 1;
    }
    fn end(&mut self, _obj: &BoxRef) {
        self.stack_count -= 1;
        if self.stack_count == 0 {
            self.column_references = None;
            self.top_box = None;
        }
    }
}

//
// EmptyBoxes
//

struct EmptyBoxesRule {}

impl EmptyBoxesRule {
    fn new() -> Self {
        Self {}
    }
}

impl rewrite_engine::Rule<BoxRef> for EmptyBoxesRule {
    fn name(&self) -> &'static str {
        "EmptyBoxes"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        let obj = obj.borrow();
        match obj.box_type {
            BoxType::Select(..) | BoxType::OuterJoin => obj
                .predicates
                .iter()
                .any(|x| x.iter().any(|x| x.borrow().is_false_predicate())),
            _ => false,
        }
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let mut obj = obj.borrow_mut();
        match &obj.box_type {
            BoxType::Select(..) => {
                obj.quantifiers.clear();
                obj.box_type = BoxType::Select(Select::new());
                obj.predicates = None;
                for c in obj.columns.iter_mut() {
                    c.expr = make_ref(Expr::make_null());
                }
            }
            BoxType::OuterJoin => {
                let (removed_quantifiers, remaining_quantifiers): (
                    Vec<QuantifierRef>,
                    Vec<QuantifierRef>,
                ) = obj
                    .quantifiers
                    .iter()
                    .map(|x| x.clone())
                    .partition(|q| q.borrow().quantifier_type == QuantifierType::Foreach);
                // preserved foreach -> foreach
                remaining_quantifiers.iter().for_each(|q| {
                    q.borrow_mut().quantifier_type = QuantifierType::Foreach;
                });
                obj.quantifiers = make_quantifier_set(remaining_quantifiers);
                obj.box_type = BoxType::Select(Select::new());
                obj.predicates = None;

                // Rewrite all expressions
                let removed_quantifiers = make_quantifier_set(removed_quantifiers);

                let mut f = |e: &mut ExprRef| {
                    let mut replace = false;
                    if let ExprType::ColumnReference(c) = &e.borrow().expr_type {
                        replace = removed_quantifiers.contains(&c.quantifier);
                    }
                    if replace {
                        *e = make_ref(Expr::make_null());
                    }
                };
                obj.visit_expressions(&mut f);
            }
            _ => {}
        }
    }
}

//
// ConstantLifting
//

struct ConstantLiftingRule {
    to_rewrite: Vec<(ExprRef, ExprRef)>,
}

impl ConstantLiftingRule {
    fn new() -> Self {
        Self {
            to_rewrite: Vec::new(),
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for ConstantLiftingRule {
    fn name(&self) -> &'static str {
        "ConstantLifting"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.to_rewrite.clear();
        let mut obj = obj.borrow_mut();
        let is_outer_join = match obj.box_type {
            BoxType::OuterJoin => true,
            _ => false,
        };

        match obj.box_type {
            BoxType::Grouping(_) | BoxType::Select(_) | BoxType::OuterJoin => {
                let mut visit_expression = |e: &mut ExprRef| {
                    // whether the outer box is an outer join
                    let mut is_outer_join = is_outer_join;
                    let mut dereferenced = e.clone();

                    let get_col_ref = |e: &ExprRef| -> Option<ColumnReference> {
                        if let ExprType::ColumnReference(c) = &e.borrow().expr_type {
                            Some(c.clone())
                        } else {
                            None
                        }
                    };
                    while let Some(c) = get_col_ref(&dereferenced) {
                        let q = c.quantifier.borrow();
                        let input_box = q.input_box.borrow();

                        match (is_outer_join, &q.quantifier_type, &input_box.box_type) {
                            (_, _, BoxType::Union) => break,
                            (false, QuantifierType::Foreach, _)
                            | (true, QuantifierType::PreservedForeach, _) => {
                                is_outer_join = match input_box.box_type {
                                    BoxType::OuterJoin => true,
                                    _ => false,
                                };
                                dereferenced = input_box.columns[c.position].expr.clone();
                            }
                            (_, _, _) => break,
                        };
                    }
                    if e.as_ptr() != dereferenced.as_ptr()
                        && dereferenced.borrow().is_runtime_constant()
                    {
                        self.to_rewrite.push((e.clone(), dereferenced));
                    }
                };
                obj.visit_expressions_recursively(&mut visit_expression);
            }

            _ => {}
        }

        !self.to_rewrite.is_empty()
    }
    fn action(&mut self, _obj: &mut BoxRef) {
        for (x, y) in self.to_rewrite.iter() {
            x.replace(y.borrow().clone());
        }
    }
}

//
// PushDownPredicates
//

struct PushDownPredicatesRule {
    // original predicate -> predicate -> quantifier
    to_pushdown: Vec<(ExprRef, ExprRef, QuantifierRef)>,
}

impl PushDownPredicatesRule {
    fn new() -> Self {
        Self {
            to_pushdown: Vec::new(),
        }
    }

    fn dereference_predicate(p: &ExprRef, q: &QuantifierRef) -> ExprRef {
        // 1. deep clone of the predicate
        let mut p = deep_clone(&p);
        // 2. dereference the only_quantifier
        let to_dereference = make_quantifier_set(vec![q.clone()]);
        let mut rule = DereferenceRule {
            to_dereference: &to_dereference,
        };
        rewrite_engine::deep_apply_rule(&mut rule, &mut p);
        p
    }

    fn finish_path(&mut self, path: Vec<(ExprRef, BoxRef, Option<QuantifierRef>)>) {
        let mut path = path;
        if path.len() > 2 {
            // @todo we don't not to save the entire path but just the last two steps
            let (original_p, _, _) = path.iter().next().unwrap().clone();
            let (_, _, q) = path.pop().unwrap();
            let (p, _, _) = path.pop().unwrap();
            self.to_pushdown.push((original_p, p, q.unwrap()));
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for PushDownPredicatesRule {
    fn name(&self) -> &'static str {
        "PushDownPredicatesRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.to_pushdown.clear();
        let mut stack: Vec<Vec<(ExprRef, BoxRef, Option<QuantifierRef>)>> = Vec::new();
        if let Some(predicates) = &obj.borrow().predicates {
            stack.extend(
                predicates
                    .iter()
                    .map(|x| vec![(x.clone(), obj.clone(), None)]),
            );
        }

        while !stack.is_empty() {
            let mut path = stack.pop().unwrap();
            let (p, b, _) = path.last().unwrap().clone();
            let quantifiers = get_quantifiers(&p);
            if quantifiers.len() == 1 {
                let q_ref = quantifiers.iter().next().unwrap();
                let only_quantifier = q_ref.borrow();
                // cannnot push down the predicate into a shared box
                let is_dead_end = only_quantifier.input_box.borrow().ranging_quantifiers.len() > 1;
                let b = b.borrow();
                match (&b.box_type, &only_quantifier.quantifier_type) {
                    (BoxType::OuterJoin, QuantifierType::Foreach) => {
                        self.finish_path(path);
                    }
                    (BoxType::OuterJoin, QuantifierType::PreservedForeach)
                    | (BoxType::Select(_), QuantifierType::Foreach)
                    | (BoxType::Grouping(_), QuantifierType::Foreach) => {
                        // @todo special handling for aggregate functions
                        let p = Self::dereference_predicate(&p, &q_ref);
                        // append the predicate to the stack
                        path.push((p, only_quantifier.input_box.clone(), Some(q_ref.clone())));
                        if is_dead_end {
                            self.finish_path(path);
                        } else {
                            stack.push(path);
                        }
                    }
                    (BoxType::Union, QuantifierType::Foreach) => {
                        drop(only_quantifier);
                        for q in b.quantifiers.iter() {
                            let mut path = path.clone();
                            let mut p = deep_clone(&p);
                            // Replace the first quantifier with the current one
                            let to_replace = {
                                let mut t = BTreeMap::new();
                                t.insert(q_ref.clone(), q.clone());
                                t
                            };
                            let mut rule = ReplaceQuantifierRule {
                                to_replace: &to_replace,
                            };
                            rewrite_engine::deep_apply_rule(&mut rule, &mut p);

                            // Dereference the current quantifier
                            let to_dereference = make_quantifier_set(vec![q.clone()]);
                            let mut rule = DereferenceRule {
                                to_dereference: &to_dereference,
                            };
                            rewrite_engine::deep_apply_rule(&mut rule, &mut p);

                            // Push the new path
                            path.push((p, q.borrow().input_box.clone(), Some(q.clone())));
                            if is_dead_end {
                                // note: this should not be possible
                                self.finish_path(path);
                            } else {
                                stack.push(path);
                            }
                        }
                    }
                    _ => {}
                }
            } else {
                self.finish_path(path);
            }
        }

        !self.to_pushdown.is_empty()
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let model = obj.borrow().model.upgrade().expect("expect valid model");
        for (original_p, p, q) in self.to_pushdown.drain(..) {
            let parent_box = q.borrow().parent_box.upgrade().unwrap();
            if parent_box.borrow().is_select() {
                // if the parent box is already a select, just add the predicate there
                parent_box.borrow_mut().add_predicate(p);
            } else {
                let select = QGBox::new(
                    Rc::downgrade(&model),
                    model.borrow_mut().ids.get_box_id(),
                    BoxType::Select(Select::new()),
                );

                let new_q = Quantifier::new(
                    model.borrow_mut().ids.get_quantifier_id(),
                    QuantifierType::Foreach,
                    q.borrow().input_box.clone(),
                    &select,
                );
                add_quantifier_to_box(&select, &new_q);
                select.borrow_mut().add_all_columns();
                select.borrow_mut().recompute_unique_keys();

                q.borrow_mut().replace_input_box(select.clone());

                let p = Self::dereference_predicate(&p, &q);
                select.borrow_mut().add_predicate(p);
            }

            obj.borrow_mut().remove_predicate(&original_p);
        }
    }
}

/// Converts an outer join box into a select box if there box right above
/// is a select box that contains an explicit IS NOT NULL predicate on a
/// column coming from the non-preserving side of the outer join.
struct OuterToInnerJoinRule {
    to_convert: QuantifierSet,
}

impl OuterToInnerJoinRule {
    fn new() -> Self {
        Self {
            to_convert: QuantifierSet::new(),
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for OuterToInnerJoinRule {
    fn name(&self) -> &'static str {
        "OuterToInnerJoinRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.to_convert.clear();
        let obj = obj.borrow();
        if let BoxType::Select(_) = &obj.box_type {
            if let Some(predicates) = &obj.predicates {
                for p in predicates {
                    if let Some(expr) = p.borrow().is_not_null() {
                        let expr = expr.borrow();
                        if let ExprType::ColumnReference(c1) = &expr.expr_type {
                            let input_box = c1.quantifier.borrow().input_box.clone();
                            let input_box = input_box.borrow();
                            if let BoxType::OuterJoin = &input_box.box_type {
                                if let Some(deref) = expr.dereference() {
                                    if let ExprType::ColumnReference(c2) = &deref.borrow().expr_type
                                    {
                                        if let QuantifierType::Foreach =
                                            c2.quantifier.borrow().quantifier_type
                                        {
                                            self.to_convert.insert(c1.quantifier.clone());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        !self.to_convert.is_empty()
    }
    fn action(&mut self, _obj: &mut BoxRef) {
        for q in self.to_convert.iter() {
            // Convert the outer join box into a select box.
            let input_box = q.borrow().input_box.clone();
            let mut input_box = input_box.borrow_mut();
            input_box.box_type = BoxType::Select(Select::new());

            // Convert the preserved quantifier into a foreach one.
            for q in input_box.quantifiers.iter() {
                let mut q = q.borrow_mut();
                if let QuantifierType::PreservedForeach = q.quantifier_type {
                    q.quantifier_type = QuantifierType::Foreach;
                }
            }
        }
        self.to_convert.clear();
    }
}

type BoxRule = dyn rewrite_engine::Rule<BoxRef>;
type RuleBox = Box<BoxRule>;

struct DereferenceRule<'a> {
    to_dereference: &'a QuantifierSet,
}

impl<'a> rewrite_engine::Rule<ExprRef> for DereferenceRule<'a> {
    fn name(&self) -> &'static str {
        "DereferenceRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &ExprRef) -> bool {
        let o = obj.borrow();
        if let ExprType::ColumnReference(c) = &o.expr_type {
            self.to_dereference.contains(&c.quantifier)
        } else {
            false
        }
    }
    fn action(&mut self, obj: &mut ExprRef) {
        let mut last;
        loop {
            last = obj.borrow().dereference();
            if !last.is_some() || !self.condition(last.as_ref().unwrap()) {
                break;
            }
        }
        if last.is_some() {
            *obj = deep_clone(last.as_ref().unwrap());
        }
    }
}

struct ReplaceQuantifierRule<'a> {
    to_replace: &'a BTreeMap<QuantifierRef, QuantifierRef>,
}

impl<'a> rewrite_engine::Rule<ExprRef> for ReplaceQuantifierRule<'a> {
    fn name(&self) -> &'static str {
        "ReplaceQuantifierRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &ExprRef) -> bool {
        let o = obj.borrow();
        if let ExprType::ColumnReference(c) = &o.expr_type {
            self.to_replace.get(&c.quantifier).is_some()
        } else {
            false
        }
    }
    fn action(&mut self, obj: &mut ExprRef) {
        // note: expressions should not be shared pointers
        *obj = deep_clone(obj);

        if let ExprType::ColumnReference(c) = &mut obj.borrow_mut().expr_type {
            if let Some(oq) = self.to_replace.get(&c.quantifier) {
                c.quantifier = oq.clone();
            }
        }
    }
}

fn apply_rule(m: &ModelRef, rule: &mut BoxRule) {
    let mut top_box = m.borrow().top_box.clone();
    rewrite_engine::deep_apply_rule(rule, &mut top_box);
    m.borrow_mut().replace_top_box(top_box);
}

fn apply_rules(m: &ModelRef, rules: &mut Vec<RuleBox>) {
    for rule in rules.iter_mut() {
        apply_rule(m, &mut **rule);
    }
}

pub fn rewrite_model(m: &ModelRef) {
    let mut rules: Vec<RuleBox> = vec![
        Box::new(MergeRule::new()),
        Box::new(ColumnRemovalRule::new()),
        Box::new(EmptyBoxesRule::new()),
        Box::new(ConstantLiftingRule::new()),
        Box::new(SemiJoinRemovalRule::new()),
        Box::new(GroupByRemovalRule::new()),
        Box::new(PushDownPredicatesRule::new()),
        Box::new(ConstraintPropagationRule::new()),
        Box::new(OuterToInnerJoinRule::new()),
        Box::new(NormalizationRule::new()),
    ];
    for _ in 0..5 {
        apply_rules(m, &mut rules);
    }
}

impl rewrite_engine::Traverse<BoxRef> for BoxRef {
    fn descend_and_apply(rule: &mut dyn rewrite_engine::Rule<BoxRef>, target: &mut BoxRef) {
        // We need to release all borrow references before descending, since some rules such
        // as ColumnRemoval may traverse the graph from the top.
        let quantifiers = target.borrow().quantifiers.clone();
        for q in quantifiers.iter() {
            let mut input_box = q.borrow().input_box.clone();
            rewrite_engine::deep_apply_rule(rule, &mut input_box);
            q.borrow_mut().input_box = input_box;
        }
    }
}

type ExprRule = dyn rewrite_engine::Rule<ExprRef>;
type RuleExpr = Box<ExprRule>;

impl rewrite_engine::Traverse<ExprRef> for ExprRef {
    fn descend_and_apply(rule: &mut dyn rewrite_engine::Rule<ExprRef>, target: &mut ExprRef) {
        if let Some(operands) = &mut target.borrow_mut().operands {
            // @todo probably there is a better way of doing this
            for i in 0..operands.len() {
                rewrite_engine::deep_apply_rule(rule, &mut operands[i]);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_rule() {
        let m = Model::new();
        let top_box = QGBox::new(Rc::downgrade(&m), 0, BoxType::Select(Select::new()));
        m.borrow_mut().replace_top_box(top_box);
        let rule = Box::new(EmptyRule {});
        let mut rules = Vec::<RuleBox>::new();
        rules.push(rule);
        apply_rules(&m, &mut rules);
    }

    #[test]
    fn test_merge_rule() {
        let m = Model::new();
        let m_weak = Rc::downgrade(&m);
        let top_box = QGBox::new(m_weak.clone(), 0, BoxType::Select(Select::new()));
        let nested_box = QGBox::new(m_weak.clone(), 1, BoxType::Select(Select::new()));
        let quantifier = Quantifier::new(1, QuantifierType::Foreach, nested_box, &top_box);
        top_box.borrow_mut().add_quantifier(quantifier);
        m.borrow_mut().replace_top_box(top_box);
        let mut rule = MergeRule::new();
        assert_eq!(m.borrow().top_box.borrow().quantifiers.len(), 1);
        apply_rule(&m, &mut rule);
        assert_eq!(m.borrow().top_box.borrow().quantifiers.len(), 0);
    }

    #[test]
    fn test_merge_rule_deep_apply() {
        let m = Model::new();
        let m_weak = Rc::downgrade(&m);
        let top_box = QGBox::new(m_weak.clone(), 0, BoxType::Select(Select::new()));
        let nested_box1 = QGBox::new(m_weak.clone(), 1, BoxType::Select(Select::new()));
        let quantifier1 = Quantifier::new(
            1,
            QuantifierType::Foreach,
            Rc::clone(&nested_box1),
            &top_box,
        );
        let nested_box2 = QGBox::new(m_weak.clone(), 2, BoxType::Select(Select::new()));
        let quantifier2 = Quantifier::new(2, QuantifierType::Foreach, nested_box2, &nested_box1);
        nested_box1.borrow_mut().add_quantifier(quantifier2);
        top_box.borrow_mut().add_quantifier(quantifier1);
        m.borrow_mut().replace_top_box(top_box);
        assert!(m.borrow().validate().is_ok());
        let mut rule = MergeRule::new();
        assert_eq!(m.borrow().top_box.borrow().quantifiers.len(), 1);
        apply_rule(&m, &mut rule);
        assert!(m.borrow().validate().is_ok());
        assert_eq!(m.borrow().top_box.borrow().quantifiers.len(), 0);
    }

    #[test]
    fn test_name_resolution() {
        let mut table_a = TableMetadata::new("A");
        for c in &["A", "B", "C"] {
            table_a.add_column(&c);
        }
        let mut catalog = FakeCatalog::new();
        catalog.add_table(table_a);

        let parser = ast::Parser {};
        let test_valid_query = |q| {
            println!("{}", q);
            let result = parser.parse(q);
            println!("{:?}", result);
            assert!(result.is_ok());
            let stmts = result.ok().unwrap();
            assert_eq!(stmts.len(), 1);
            if let ast::Statement::Select(c) = &stmts[0] {
                let generator = ModelGenerator::new(&catalog);
                let model = generator.process(&c);
                assert!(model.is_ok(), "{}", model.err().unwrap());
                let mut model = model.ok().unwrap();
                assert!(model.borrow().validate().is_ok());

                let output = DotGenerator::new().generate(&model.borrow(), q);
                assert!(output.is_ok());
                let output = output.ok().unwrap();
                println!("{}", output);

                rewrite_model(&mut model);
                assert!(model.borrow().validate().is_ok());

                let output = DotGenerator::new().generate(&model.borrow(), q);
                assert!(output.is_ok());
                let output = output.ok().unwrap();
                println!("{}", output);
            } else {
                assert!(false);
            }
        };

        test_valid_query("select * from a");
        test_valid_query("select a from a");
        test_valid_query("select a from a where a = 10");
        test_valid_query("select a from a where a = ?");
        test_valid_query("select a from a where a != ?");
        test_valid_query("select a from a where a < ?");
        test_valid_query("select a from a where a <= ?");
        test_valid_query("select a from a where a > ?");
        test_valid_query("select a from a where a >= ?");
        test_valid_query("select a, b, c from a");
        test_valid_query("select a, b, c from (select * from a)");
        test_valid_query("select a, b, c from (select * from a) b");
        test_valid_query("select b.a from (select * from a) b");
        test_valid_query("select z from (select a as z from a) b");
        test_valid_query("select b.z from (select a as z from a) b");
        test_valid_query("select b.z from (select a as z from a) b join a");
        test_valid_query("select a from a where a");
        test_valid_query("select a from a where a in (?, ?)");
        test_valid_query("select a from (select a from a) where a in (?, ?)");
        test_valid_query("select a from (select a from a) where a or ?");
        test_valid_query("select a from (select * from a) where a in (a, b, c)");
        test_valid_query("select a from (select * from a where b in (?, ?)) where a in (a, b, c)");
        test_valid_query("select a from a group by a asc");
        test_valid_query("select a from a group by a asc, b");
        test_valid_query("select a, b from a group by a asc, b");
        test_valid_query("select a, b from a group by a asc, b having b > 1");
        test_valid_query("select a, b from a group by a asc, b having b > (select a from a)");
        test_valid_query(
            "select a, b from a group by a asc, b having b > (select a from a) limit 1",
        );
        test_valid_query("select a, b from a union all select a, b from a");
        test_valid_query("select a, b from a union all select a, b from a order by a");
        test_valid_query("select a, b from a group by a asc, b having b > (select a from a) union all select a, b from a order by a");

        test_valid_query("select a, b from a z where z.a > 1");
        test_valid_query("select a, b from a z where (select z.a from a) > 1");
        test_valid_query("select a, b from a z where (select a from a where a = z.a) > 1");
        test_valid_query("select a, b from a z where (select a from a where a = (select a from a where z.a > 2)) > 1");
        test_valid_query(
            "select a, b from a z where (select a from (select a from a where z.a > 2))",
        );

        test_valid_query("select case when a = 1 then true else false end as caseexpr from a");
        test_valid_query("with b as (select a from a) select * from b");
        test_valid_query("with b(b) as (select a from a) select * from b");
        test_valid_query(
            "with b(b) as (select a from a), c(c) as (select a from a) select * from b, c",
        );
        test_valid_query("with b(b) as (select a from a) select * from b, b c, (with c(c) as (select b from b) select * from c) as d");
        test_valid_query("with b(b) as (select a from a) select * from b, b c, (with c(c) as (select b from b) select * from c, b where b.b = c.c) as d where b.b = c.b and b.b = d.c");
    }

    struct TestRunner {
        catalog: FakeCatalog,
    }
    impl TestRunner {
        pub fn new() -> Self {
            Self {
                catalog: FakeCatalog::new(),
            }
        }

        pub fn process_ddl(&mut self, line: &str) -> Result<String, String> {
            let parser = ast::Parser::new();
            let result = parser.parse(line)?;
            for stmt in result {
                self.process_ddl_statement(&stmt)?;
            }
            Ok(String::new())
        }

        fn process_ddl_statement(&mut self, stmt: &ast::Statement) -> Result<(), String> {
            use ast::Statement::*;
            match stmt {
                CreateTable(c) => {
                    self.catalog.add_table(TableMetadata::from_create(c));
                }
                DropTable(c) => {
                    let table = self.catalog.get_table(c.name.get_name())?.clone();
                    self.catalog.drop_table(&table);
                }
                CreateIndex(c) => {
                    let table = self.catalog.get_table(c.tablename.get_name())?;
                    let mut cloned = table.clone();
                    let mut columns = Vec::new();
                    for ic in c.columns.iter() {
                        let mut idx = None;
                        for (i, tc) in cloned.columns.iter().enumerate() {
                            if tc.name == *ic {
                                idx = Some(i);
                                break;
                            }
                        }
                        if let Some(i) = idx {
                            columns.push(i);
                        } else {
                            return Err(format!("column {} not found", ic));
                        }
                    }
                    cloned.indexes.push(Index {
                        name: c.name.clone(),
                        unique: c.unique,
                        columns,
                    });
                    self.catalog.add_table(cloned);
                }
                _ => return Err(format!("unsupported statement: {:?}", stmt)),
            }
            Ok(())
        }

        pub fn process_query(
            &mut self,
            query: &str,
            rules: Option<&Vec<String>>,
            dump: bool,
        ) -> Result<String, String> {
            let parser = ast::Parser::new();
            let mut result = parser.parse(query)?;
            let mut output = String::new();
            if let Some(stmt) = result.pop() {
                use ast::Statement::*;
                match stmt {
                    Select(c) => {
                        let mut label = query.to_string();
                        let generator = ModelGenerator::new(&self.catalog);
                        let model = generator.process(&c)?;
                        if let Some(rules) = &rules {
                            for rule in rules.iter() {
                                Self::apply_rule(&model, rule)?;
                                label.push_str(&format!(" + {}", rule));
                            }
                        }
                        if dump {
                            output
                                .push_str(&DotGenerator::new().generate(&model.borrow(), &label)?);
                        }
                    }
                    _ => return Err(format!("invalid query")),
                }
            }
            Ok(output)
        }

        fn apply_rule(model: &ModelRef, rule: &str) -> Result<(), String> {
            let mut rule: RuleBox = Self::get_rule_by_name(rule)?;
            super::apply_rule(model, &mut *rule);
            Ok(())
        }

        fn get_rule_by_name(rule: &str) -> Result<RuleBox, String> {
            let mut rules = Vec::new();
            for name in rule.split("-") {
                let rule = Self::get_single_rule_by_name(name)?;
                rules.push(rule);
            }
            Ok(match rules.len() {
                1 => rules.pop().unwrap(),
                _ => Box::new(SingleTraversalRule::new(rules)),
            })
        }

        fn get_single_rule_by_name(rule: &str) -> Result<RuleBox, String> {
            let rule: RuleBox = match rule {
                "ColumnRemoval" => Box::new(ColumnRemovalRule::new()),
                "ConstantLifting" => Box::new(ConstantLiftingRule::new()),
                "ConstraintPropagation" => Box::new(ConstraintPropagationRule::new()),
                "EmptyBoxes" => Box::new(EmptyBoxesRule::new()),
                "GroupByRemoval" => Box::new(GroupByRemovalRule::new()),
                "Merge" => Box::new(MergeRule::new()),
                "Normalization" => Box::new(NormalizationRule::new()),
                "OuterToInnerJoin" => Box::new(OuterToInnerJoinRule::new()),
                "PushDownPredicates" => Box::new(PushDownPredicatesRule::new()),
                _ => return Err(format!("invalid rule")),
            };
            Ok(rule)
        }
    }

    #[test]
    fn run() {
        use datadriven::walk;

        walk("tests/querymodel", |f| {
            let mut interpreter = TestRunner::new();
            f.run(|test_case| -> String {
                let apply = test_case.args.get("apply");
                let result = match &test_case.directive[..] {
                    "ddl" => interpreter.process_ddl(&test_case.input[..]),
                    "query" => interpreter.process_query(&test_case.input[..], apply, true),
                    "check" => interpreter.process_query(&test_case.input[..], apply, false),
                    _ => Err(format!("invalid test directive")),
                };
                match result {
                    Ok(c) => format!("{}{}", c, if c.is_empty() { "" } else { "\n" }),
                    Err(c) => format!("Err: {}{}", c, if c.is_empty() { "" } else { "\n" }),
                }
            })
        });
    }
}
