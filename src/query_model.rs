use crate::ast;
use crate::metadata::*;
use std::cell::RefCell;
use std::cmp::*;
use std::collections::*;
use std::fmt;
use std::rc::*;

#[derive(Clone)]
struct ColumnReference {
    quantifier: QuantifierRef,
    position: usize,
}

#[derive(Clone)]
struct BaseColumn {
    parent_box: Weak<RefCell<QGBox>>,
    position: usize,
}

#[derive(Clone)]
enum LogicalExprType {
    And,
    Or,
}

#[derive(Clone)]
enum Value {
    BigInt(i64),
    Boolean(bool),
    String(String),
    Null,
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

#[derive(Clone)]
enum CmpOpType {
    Eq,
    Neq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
}

#[derive(Clone)]
enum ExprType {
    BaseColumn(BaseColumn),
    Cmp(CmpOpType),
    ColumnReference(ColumnReference),
    InList,
    Literal(Value),
    Logical(LogicalExprType),
    Parameter(u64),
    Case,
    IsNull,
    Tuple,
}

type ExprRef = Rc<RefCell<Expr>>;
type ColumnReferenceMap = HashMap<usize, Vec<ExprRef>>;
type PerBoxColumnReferenceMap = HashMap<i32, ColumnReferenceMap>;

fn collect_column_references(expr_ref: &ExprRef, column_references: &mut PerBoxColumnReferenceMap) {
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
            collect_column_references(o, column_references);
        }
    }
}

#[derive(Clone)]
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

    fn make_tuple(operands: Vec<ExprRef>) -> Self {
        Self {
            expr_type: ExprType::Tuple,
            operands: Some(operands),
        }
    }

    fn is_equiv(&self, o: &Self) -> bool {
        match (&self.expr_type, &o.expr_type) {
            (ExprType::ColumnReference(l), ExprType::ColumnReference(r)) => {
                l.position == r.position && l.quantifier == r.quantifier
            }
            (ExprType::Parameter(l), ExprType::Parameter(r)) => l == r,
            _ => false,
        }
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
            _ => false,
        }
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
}

fn collect_column_refs(expr: &ExprRef) -> Vec<ExprRef> {
    let mut stack = vec![Rc::clone(expr)];
    let mut result = Vec::new();
    while let Some(expr) = stack.pop() {
        let e = expr.borrow();
        if e.is_column_ref() {
            result.push(Rc::clone(&expr));
        } else if let Some(operands) = &e.operands {
            for o in operands {
                stack.push(Rc::clone(&o));
            }
        }
    }
    result
}

fn get_quantifiers(expr: &ExprRef) -> BTreeSet<QuantifierRef> {
    let mut result: BTreeSet<QuantifierRef> = BTreeSet::new();
    collect_quantifiers(&mut result, expr);
    result
}

fn get_existential_quantifiers(expr: &ExprRef) -> BTreeSet<QuantifierRef> {
    get_quantifiers(expr)
        .iter()
        .filter(|q| q.borrow().quantifier_type == QuantifierType::Existential)
        .cloned()
        .collect()
}

fn collect_quantifiers(quantifiers: &mut BTreeSet<QuantifierRef>, expr: &ExprRef) {
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

#[derive(Clone, Debug)]
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
    id: i32,
    box_type: BoxType,
    distinct_tuples: bool,
    columns: Vec<Column>,
    quantifiers: BTreeSet<QuantifierRef>,
    predicates: Option<Vec<ExprRef>>,
    distinct_operation: DistinctOperation,
}

fn make_quantifier_set(v: Vec<QuantifierRef>) -> BTreeSet<QuantifierRef> {
    let mut s = BTreeSet::new();
    s.extend(v);
    s
}

impl QGBox {
    fn new(id: i32, box_type: BoxType) -> Self {
        Self {
            id,
            distinct_tuples: false,
            box_type,
            columns: Vec::new(),
            quantifiers: BTreeSet::new(),
            predicates: None,
            distinct_operation: DistinctOperation::Preserve,
        }
    }
    /// use add_quantifier_to_box instead to properly set the parent box of the quantifier
    fn add_quantifier(&mut self, q: QuantifierRef) {
        self.quantifiers.insert(q);
    }
    fn remove_quantifier(&mut self, q: &QuantifierRef) {
        self.quantifiers.remove(q);
    }
    fn add_column(&mut self, mut name: Option<String>, expr: ExprRef) {
        if name.is_none() {
            if let ExprType::ColumnReference(c) = &expr.borrow().expr_type {
                let q = c.quantifier.borrow();
                let input_box = q.input_box.borrow();
                name = input_box.columns[c.position].name.clone();
            }
        }
        self.columns.push(Column { name, expr });
    }
    fn add_column_if_not_exists(&mut self, expr: Expr) -> usize {
        for (i, c) in self.columns.iter().enumerate() {
            if c.expr.borrow().is_equiv(&expr) {
                return i;
            }
        }
        let pos = self.columns.len();
        self.columns.push(Column {
            name: None,
            expr: make_ref(expr),
        });
        pos
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
        if self.predicates.is_some() {
            self.predicates.as_mut().unwrap().extend(predicates);
        } else {
            self.predicates = Some(predicates);
        }
    }

    fn has_predicates(&self) -> bool {
        !self.predicates.is_none() && !self.predicates.as_ref().unwrap().is_empty()
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
}

fn add_quantifier_to_box(b: &BoxRef, q: &QuantifierRef) {
    let mut bb = b.borrow_mut();
    bb.add_quantifier(Rc::clone(q));
    let mut bq = q.borrow_mut();
    bq.parent_box = Rc::downgrade(&b);
}

#[derive(PartialEq)]
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

struct Quantifier {
    id: i32,
    quantifier_type: QuantifierType,
    input_box: BoxRef,
    parent_box: Weak<RefCell<QGBox>>,
    alias: Option<String>,
}

impl Quantifier {
    fn new(
        id: i32,
        quantifier_type: QuantifierType,
        input_box: BoxRef,
        parent_box: &BoxRef,
    ) -> Self {
        Self {
            id,
            quantifier_type,
            input_box,
            parent_box: Rc::downgrade(parent_box),
            alias: None,
        }
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

pub struct Model {
    top_box: BoxRef,
}

impl Model {
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
                    // @todo we should break the loop here, to avoid memory leaks
                    return Err(format!(
                        "box in quantifier {} already visited, loop in the model",
                        q.id
                    ));
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

/// Generates a query graph model from the AST
pub struct ModelGenerator<'a> {
    catalog: &'a dyn MetadataCatalog,
    next_box_id: i32,
    next_quantifier_id: i32,
}

struct NameResolutionContext<'a> {
    owner_box: BoxRef,
    quantifiers: Vec<QuantifierRef>,
    parent_quantifiers: HashMap<i32, QuantifierRef>,
    subquery_quantifiers: Option<HashMap<*const ast::QueryBlock, QuantifierRef>>,
    parent_context: Option<&'a NameResolutionContext<'a>>,
}

impl<'a> NameResolutionContext<'a> {
    fn new(owner_box: BoxRef, parent_context: Option<&'a Self>) -> Self {
        Self {
            owner_box,
            quantifiers: Vec::new(),
            parent_quantifiers: HashMap::new(),
            subquery_quantifiers: None,
            parent_context,
        }
    }

    fn add_quantifier(&mut self, q: &QuantifierRef) {
        self.parent_quantifiers
            .insert(q.borrow().input_box.borrow().id, Rc::clone(q));
        self.quantifiers.push(Rc::clone(q))
    }

    fn add_subquery_quantifier(&mut self, s: *const ast::QueryBlock, q: &QuantifierRef) {
        if self.subquery_quantifiers.is_none() {
            self.subquery_quantifiers = Some(HashMap::new());
        }
        self.subquery_quantifiers
            .as_mut()
            .unwrap()
            .insert(s, Rc::clone(q));
    }

    fn get_subquery_quantifier(&self, s: *const ast::QueryBlock) -> QuantifierRef {
        Rc::clone(
            self.subquery_quantifiers
                .as_ref()
                .unwrap()
                .get(&s)
                .expect("bug"),
        )
    }

    /// adds all the quantifier from the given context into the current one
    fn merge_quantifiers(&mut self, o: Self) {
        for q in o.quantifiers {
            self.quantifiers.push(q);
        }
        self.parent_quantifiers.extend(o.parent_quantifiers);
    }

    fn resolve_column(&self, table: Option<&str>, column: &str) -> Result<Option<ExprRef>, String> {
        if table.is_some() {
            let tn = table.unwrap();
            for q in &self.quantifiers {
                // @todo case insensitive comparisons
                let q_name = q.borrow().get_effective_name();
                if q_name.is_some() && q_name.as_ref().unwrap() == tn {
                    return Ok(self.resolve_column_in_quantifier(q, column));
                }
            }
        } else {
            let mut found = None;
            for q in &self.quantifiers {
                // @todo check for column name ambiguity
                let r = self.resolve_column_in_quantifier(q, column);
                if r.is_some() {
                    if found.is_some() {
                        return Err(format!("column {} is ambigouts", column));
                    }
                    found = r;
                }
            }
            if found.is_some() {
                return Ok(found);
            }
        }
        if let Some(parent) = &self.parent_context {
            return parent.resolve_column(table, column);
        }
        Ok(None)
    }

    fn resolve_column_in_quantifier(&self, q: &QuantifierRef, column: &str) -> Option<ExprRef> {
        for (i, c) in q.borrow().input_box.borrow().columns.iter().enumerate() {
            // ideally, this should be a reference to avoid the cloning... (*)
            let mut c: Option<Column> = Some(c.clone());
            while let Some(col) = c {
                if col.name.is_some() {
                    // @todo case insensitive comparisons
                    if column == col.name.as_ref().unwrap() {
                        let column_ref = Expr::make_column_ref(Rc::clone(&q), i);
                        let column_ref = self.pullup_column_ref(column_ref);
                        return Some(make_ref(column_ref));
                    } else {
                        c = None;
                    }
                } else {
                    if let ExprType::ColumnReference(cref) = &col.expr.borrow().expr_type {
                        let q = cref.quantifier.borrow();
                        let b = q.input_box.borrow();
                        // (*) but this makes the compiler complain about the reference being to a temporary value
                        // c = Some(&b.columns[cref.position]);
                        c = Some(b.columns[cref.position].clone());
                    } else {
                        c = None;
                    }
                }
            }
        }
        None
    }

    fn pullup_column_ref(&self, column_ref: Expr) -> Expr {
        let mut column_ref = column_ref;
        match &mut column_ref.expr_type {
            ExprType::ColumnReference(c) => {
                loop {
                    let parent_box = c.quantifier.borrow().parent_box.upgrade();
                    if parent_box.is_none() {
                        break;
                    }
                    let parent_box = parent_box.unwrap();
                    let parent_box_id = parent_box.borrow().id;
                    if parent_box_id == self.owner_box.borrow().id {
                        break;
                    }
                    // @todo we need ranging quantifiers!
                    let parent_q = self
                        .parent_quantifiers
                        .get(&parent_box_id)
                        .expect("must be a valid id");
                    c.position = parent_q
                        .borrow()
                        .input_box
                        .borrow_mut()
                        .add_column_if_not_exists(Expr::make_column_ref(
                            Rc::clone(&c.quantifier),
                            c.position,
                        ));
                    c.quantifier = Rc::clone(parent_q);
                }
                column_ref
            }
            _ => {
                panic!();
            }
        }
    }
}

impl<'a> ModelGenerator<'a> {
    pub fn new(catalog: &'a dyn MetadataCatalog) -> Self {
        Self {
            catalog,
            // @todo move this to the model
            next_box_id: 0,
            next_quantifier_id: 0,
        }
    }

    pub fn process(&mut self, quer_block: &ast::QueryBlock) -> Result<Model, String> {
        let top_box = self.process_query_block(quer_block, None)?;
        let model = Model { top_box };
        Ok(model)
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

    fn make_select_box(&mut self) -> BoxRef {
        make_ref(QGBox::new(
            self.get_box_id(),
            BoxType::Select(Select::new()),
        ))
    }

    fn make_outer_join_box(&mut self) -> BoxRef {
        make_ref(QGBox::new(self.get_box_id(), BoxType::OuterJoin))
    }

    fn make_union_box(&mut self, distinct: bool, mut branches: Vec<BoxRef>) -> BoxRef {
        let union_box = make_ref(QGBox::new(self.get_box_id(), BoxType::Union));
        {
            let mut union_mut = union_box.borrow_mut();
            union_mut.distinct_tuples = distinct;
            if distinct {
                union_mut.distinct_operation = DistinctOperation::Enforce;
            }
        }
        for (i, branch) in branches.drain(..).enumerate() {
            let q = self.make_quantifier(branch, &union_box);
            union_box.borrow_mut().add_quantifier(q);

            if i == 0 {
                self.add_all_columns(&union_box);
            }
        }
        union_box
    }

    fn make_quantifier(&mut self, input_box: BoxRef, parent_box: &BoxRef) -> QuantifierRef {
        make_ref(Quantifier::new(
            self.get_quantifier_id(),
            QuantifierType::Foreach,
            input_box,
            &parent_box,
        ))
    }

    fn process_query_block_source(
        &mut self,
        source: &ast::QueryBlockSource,
        parent_context: &NameResolutionContext,
    ) -> Result<BoxRef, String> {
        match source {
            ast::QueryBlockSource::Select(select) => {
                self.process_select(select, Some(&parent_context))
            }
            ast::QueryBlockSource::Union(union) => {
                let left = self.process_query_block_source(&union.left, &parent_context)?;
                let right = self.process_query_block_source(&union.right, &parent_context)?;
                Ok(self.make_union_box(union.distinct, vec![left, right]))
            }
            _ => Err(format!("unsupported source")),
        }
    }

    fn process_query_block(
        &mut self,
        query_block: &ast::QueryBlock,
        parent_context: Option<&NameResolutionContext>,
    ) -> Result<BoxRef, String> {
        let current_box = self.make_select_box();
        let mut current_context =
            NameResolutionContext::new(Rc::clone(&current_box), parent_context);

        let input_box = self.process_query_block_source(&query_block.source, &current_context)?;
        let q = self.make_quantifier(input_box, &current_box);
        current_box.borrow_mut().add_quantifier(Rc::clone(&q));
        current_context.add_quantifier(&q);

        self.add_all_columns(&current_box);

        if let Some(order_by_clause) = &query_block.order_by_clause {
            let mut keys = Vec::new();
            for key in order_by_clause {
                let expr = self.process_expr(&key.expr, &current_context)?;
                keys.push(KeyItem {
                    expr,
                    dir: key.direction,
                });
            }
            current_box.borrow_mut().set_order_by(keys);
        }
        if let Some(limit_clause) = &query_block.limit_clause {
            // @todo empty context
            let expr = self.process_expr(&limit_clause, &current_context)?;
            current_box.borrow_mut().set_limit(expr);
        }
        Ok(current_box)
    }

    fn process_select(
        &mut self,
        select: &ast::Select,
        parent_context: Option<&NameResolutionContext>,
    ) -> Result<BoxRef, String> {
        let mut current_box = self.make_select_box();

        // distinct property
        if select.distinct {
            let mut box_mut = current_box.borrow_mut();
            box_mut.distinct_tuples = true;
            box_mut.distinct_operation = DistinctOperation::Enforce;
        }

        let mut current_context =
            NameResolutionContext::new(Rc::clone(&current_box), parent_context);
        for join_item in &select.from_clause {
            self.add_join_term_to_select_box(join_item, &current_box, &mut current_context)?;
        }
        if let Some(where_clause) = &select.where_clause {
            self.add_subqueries(&current_box, &where_clause, &mut current_context)?;
            let expr = self.process_expr(&where_clause, &current_context)?;
            current_box.borrow_mut().add_predicate(expr);
        }
        if let Some(grouping) = &select.grouping {
            self.add_all_columns(&current_box);

            let grouping_box = make_ref(QGBox::new(
                self.get_box_id(),
                BoxType::Grouping(Grouping::new()),
            ));
            let q = self.make_quantifier(current_box, &grouping_box);
            grouping_box.borrow_mut().add_quantifier(Rc::clone(&q));
            // context for resolving the grouping keys
            current_context = NameResolutionContext::new(Rc::clone(&grouping_box), parent_context);
            current_context.add_quantifier(&q);
            for key in &grouping.groups {
                let expr = self.process_expr(&key.expr, &current_context)?;
                grouping_box.borrow_mut().add_column(None, expr.clone());
                grouping_box.borrow_mut().add_group(KeyItem {
                    expr,
                    dir: key.direction,
                });
            }

            // put a select box on top of the grouping box and use the grouping quantifier for name resolution
            current_box = self.make_select_box();
            let q = self.make_quantifier(grouping_box, &current_box);
            current_context = NameResolutionContext::new(Rc::clone(&current_box), parent_context);
            current_context.add_quantifier(&q);
            current_box.borrow_mut().add_quantifier(q);

            if let Some(having_clause) = &grouping.having_clause {
                self.add_subqueries(&current_box, &having_clause, &mut current_context)?;
                let expr = self.process_expr(&having_clause, &current_context)?;
                current_box.borrow_mut().add_predicate(expr);
            }
        }
        if let Some(selection_list) = &select.selection_list {
            for item in selection_list {
                self.add_subqueries(&current_box, &item.expr, &mut current_context)?;
                let expr = self.process_expr(&item.expr, &current_context)?;
                current_box
                    .borrow_mut()
                    .add_column(item.alias.clone(), expr);
            }
        } else {
            // add all columns from all quantifiers
            self.add_all_columns(&current_box);
        }

        Ok(current_box)
    }

    fn add_all_columns(&mut self, select_box: &BoxRef) {
        let quantifiers = select_box.borrow().quantifiers.clone();
        for q in quantifiers {
            let bq = q.borrow();
            if bq.is_subquery() {
                continue;
            }
            let input_box = bq.input_box.borrow();
            for (i, c) in input_box.columns.iter().enumerate() {
                let expr = Expr::make_column_ref(Rc::clone(&q), i);
                select_box
                    .borrow_mut()
                    .add_column(c.name.clone(), make_ref(expr));
            }
        }
    }

    /// adds a quantifier in the given select box with the result of parsing the given join term subtree
    fn add_join_term_to_select_box(
        &mut self,
        join_term: &ast::JoinTerm,
        select_box: &BoxRef,
        current_context: &mut NameResolutionContext,
    ) -> Result<QuantifierRef, String> {
        let b = self.process_join_item(&join_term.join_item, current_context)?;
        let q = self.make_quantifier(b, &select_box);
        if join_term.alias.is_some() {
            q.borrow_mut()
                .set_alias(join_term.alias.as_ref().unwrap().clone());
        }
        current_context.add_quantifier(&q);
        select_box.borrow_mut().add_quantifier(Rc::clone(&q));
        Ok(q)
    }

    fn process_join_item(
        &mut self,
        item: &ast::JoinItem,
        current_context: &mut NameResolutionContext,
    ) -> Result<BoxRef, String> {
        use ast::JoinItem::*;
        match item {
            // the derived table should not see its siblings
            DerivedTable(s) => self.process_query_block(s, current_context.parent_context),
            // but lateral joins do see its siblings
            Lateral(s) => self.process_query_block(s, Some(current_context)),
            TableRef(s) => {
                // @todo suport for schemas and catalogs
                let metadata = self.catalog.get_table(s.get_name());
                if !metadata.is_some() {
                    return Err(format!("table {} not found", s.get_name()));
                }
                let metadata = metadata.unwrap();
                // @todo avoid cloning the metadata. The catalog should return a ref counted instance
                let base_table = BoxType::BaseTable(metadata.clone());
                let table_box = make_ref(QGBox::new(self.get_box_id(), base_table));
                // add the columns of the table
                for (i, c) in metadata.columns.iter().enumerate() {
                    table_box.borrow_mut().add_column(
                        Some(c.name.clone()),
                        make_ref(Expr::make_base_column(&table_box, i)),
                    );
                }
                Ok(table_box)
            }
            Join(join_type, l, r, on) => {
                let select_box = match join_type {
                    JoinType::LeftOuter | JoinType::RightOuter => self.make_outer_join_box(),
                    JoinType::Inner => self.make_select_box(),
                };
                let mut child_context = NameResolutionContext::new(
                    Rc::clone(&select_box),
                    current_context.parent_context,
                );

                let lq = self.add_join_term_to_select_box(l, &select_box, &mut child_context)?;
                if let JoinType::LeftOuter = join_type {
                    lq.borrow_mut().quantifier_type = QuantifierType::PreservedForeach;
                }
                let rq = self.add_join_term_to_select_box(r, &select_box, &mut child_context)?;
                if let JoinType::RightOuter = join_type {
                    rq.borrow_mut().quantifier_type = QuantifierType::PreservedForeach;
                }

                if let Some(expr) = &on {
                    // subqueries in the ON clause should not see the siblings in the current context
                    self.add_subqueries(&select_box, expr, &mut child_context)?;
                    let expr = self.process_expr(expr, &child_context)?;
                    select_box.borrow_mut().add_predicate(expr);
                }

                // merge the temporary context into the current one
                current_context.merge_quantifiers(child_context);

                // project all columns from its quantifiers
                self.add_all_columns(&select_box);
                Ok(select_box)
            } // _ => Err(String::from("not implemented")),
        }
    }

    /// the suqbueries in the given expressions as quantifiers in the given select box
    fn add_subqueries(
        &mut self,
        select_box: &BoxRef,
        expr: &ast::Expr,
        current_context: &mut NameResolutionContext,
    ) -> Result<(), String> {
        use ast::Expr::*;
        let add_subquery = |s: &mut Self,
                            current_context: &mut NameResolutionContext,
                            quantifier_type: QuantifierType,
                            e: &ast::QueryBlock,
                            subquery_box: BoxRef| {
            let q = Quantifier::new(
                s.get_quantifier_id(),
                quantifier_type,
                subquery_box,
                &select_box,
            );
            let q = make_ref(q);
            current_context.add_subquery_quantifier(e as *const ast::QueryBlock, &q);
            select_box.borrow_mut().add_quantifier(q);
        };
        for expr in expr.iter() {
            match expr {
                ScalarSubquery(e) => {
                    let subquery_box = self.process_query_block(e, Some(current_context))?;
                    if subquery_box.borrow().columns.len() != 1 {
                        return Err(format!("scalar subqueries must project a single column"));
                    }
                    add_subquery(
                        self,
                        current_context,
                        QuantifierType::Scalar,
                        e.as_ref(),
                        subquery_box,
                    );
                }
                InSelect(_, e) => {
                    let subquery_box = self.process_query_block(e, Some(current_context))?;
                    add_subquery(
                        self,
                        current_context,
                        QuantifierType::Existential,
                        e.as_ref(),
                        subquery_box,
                    );
                }
                Exists(e) => {
                    let subquery_box = self.process_query_block(e, Some(current_context))?;
                    {
                        let mut mutable_box = subquery_box.borrow_mut();
                        mutable_box.columns.clear();
                        mutable_box.columns.push(Column {
                            name: None,
                            expr: make_ref(Expr::make_literal(Value::BigInt(1))),
                        });
                    }
                    add_subquery(
                        self,
                        current_context,
                        QuantifierType::Existential,
                        e.as_ref(),
                        subquery_box,
                    );
                }
                Any(e) | All(e) => {
                    let subquery_box = self.process_query_block(e, Some(current_context))?;
                    let quantifier_type = match expr {
                        Any(_) => QuantifierType::Any,
                        _ => QuantifierType::All,
                    };
                    add_subquery(
                        self,
                        current_context,
                        quantifier_type,
                        e.as_ref(),
                        subquery_box,
                    );
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn process_expr(
        &mut self,
        expr: &ast::Expr,
        current_context: &NameResolutionContext,
    ) -> Result<ExprRef, String> {
        match expr {
            ast::Expr::Reference(id) => {
                let expr = current_context
                    .resolve_column(id.get_qualifier_before_name(), &id.get_name())?;
                if expr.is_some() {
                    return Ok(expr.unwrap());
                }
                Err(format!("column {} not found", id.get_name()))
            }
            ast::Expr::Parameter(index) => Ok(make_ref(Expr::make_parameter(*index))),
            ast::Expr::InList(term, list) => {
                let term = self.process_expr(term, current_context)?;
                let mut list_exprs = Vec::new();
                for e in list {
                    list_exprs.push(self.process_expr(e, current_context)?);
                }
                Ok(make_ref(Expr::make_in_list(term, list_exprs)))
            }
            ast::Expr::ScalarSubquery(e) => Ok(make_ref(Expr::make_column_ref(
                current_context.get_subquery_quantifier(e.as_ref() as *const ast::QueryBlock),
                0,
            ))),
            ast::Expr::InSelect(l, e) => {
                let left = self.process_expr(l, current_context)?;
                let right = {
                    let q = current_context
                        .get_subquery_quantifier(e.as_ref() as *const ast::QueryBlock);
                    let column_count = q.borrow().input_box.borrow().columns.len();
                    if column_count == 1 {
                        let col_ref = Expr::make_column_ref(q, 0);
                        make_ref(col_ref)
                    } else {
                        let col_refs = (0..column_count)
                            .map(|x| make_ref(Expr::make_column_ref(q.clone(), x)))
                            .collect();
                        make_ref(Expr::make_tuple(col_refs))
                    }
                };
                if left.borrow().result_arity() != right.borrow().result_arity() {
                    Err(format!("unexpected number of columns"))
                } else {
                    Ok(make_ref(Expr::make_cmp(CmpOpType::Eq, left, right)))
                }
            }
            ast::Expr::Exists(e) => {
                let left = make_ref(Expr::make_literal(Value::BigInt(1)));
                let col_ref = Expr::make_column_ref(
                    current_context.get_subquery_quantifier(e.as_ref() as *const ast::QueryBlock),
                    0,
                );
                Ok(make_ref(Expr::make_cmp(
                    CmpOpType::Eq,
                    left,
                    make_ref(col_ref),
                )))
            }
            ast::Expr::Any(e) | ast::Expr::All(e) => {
                let q =
                    current_context.get_subquery_quantifier(e.as_ref() as *const ast::QueryBlock);
                let column_count = q.borrow().input_box.borrow().columns.len();
                if column_count == 1 {
                    let col_ref = Expr::make_column_ref(q, 0);
                    Ok(make_ref(col_ref))
                } else {
                    let col_refs = (0..column_count)
                        .map(|x| make_ref(Expr::make_column_ref(q.clone(), x)))
                        .collect();
                    Ok(make_ref(Expr::make_tuple(col_refs)))
                }
            }
            ast::Expr::BooleanLiteral(e) => Ok(make_ref(Expr::make_literal(Value::Boolean(*e)))),
            ast::Expr::NumericLiteral(e) => Ok(make_ref(Expr::make_literal(Value::BigInt(*e)))),
            ast::Expr::StringLiteral(e) => {
                Ok(make_ref(Expr::make_literal(Value::String(e.clone()))))
            }
            ast::Expr::Binary(t, l, r) => {
                let op = match t {
                    ast::BinaryExprType::Eq => CmpOpType::Eq,
                    ast::BinaryExprType::Neq => CmpOpType::Neq,
                    ast::BinaryExprType::Less => CmpOpType::Less,
                    ast::BinaryExprType::LessEq => CmpOpType::LessEq,
                    ast::BinaryExprType::Greater => CmpOpType::Greater,
                    ast::BinaryExprType::GreaterEq => CmpOpType::GreaterEq,
                };
                let l = self.process_expr(l, current_context)?;
                let r = self.process_expr(r, current_context)?;
                if l.borrow().result_arity() != r.borrow().result_arity() {
                    Err(format!("incompatible operands"))
                } else {
                    Ok(make_ref(Expr::make_cmp(op, l, r)))
                }
            }
            ast::Expr::Nary(t, list) => {
                let mut list_exprs = Vec::new();
                for e in list {
                    list_exprs.push(self.process_expr(e, current_context)?);
                }
                match t {
                    ast::NaryExprType::And => Ok(make_ref(Expr::make_logical(
                        LogicalExprType::And,
                        list_exprs,
                    ))),
                    ast::NaryExprType::Or => Ok(make_ref(Expr::make_logical(
                        LogicalExprType::Or,
                        list_exprs,
                    ))),
                    _ => Err(String::from("expression not supported!")),
                }
            }
            ast::Expr::Case(case_expr) => {
                let mut operands = Vec::new();
                for (c, t) in case_expr.case_branches.iter() {
                    operands.push(self.process_expr(c, current_context)?);
                    operands.push(self.process_expr(t, current_context)?);
                }
                for e in case_expr.else_branch.iter() {
                    operands.push(self.process_expr(e, current_context)?);
                }
                Ok(make_ref(Expr::make_case(operands)))
            }
            ast::Expr::IsNull(operand) => {
                let operand = self.process_expr(operand, current_context)?;
                Ok(make_ref(Expr::make_is_null(operand)))
            }
            ast::Expr::Tuple(values) => {
                let mut operands = Vec::new();
                for e in values.iter() {
                    operands.push(self.process_expr(e, current_context)?);
                }
                Ok(make_ref(Expr::make_tuple(operands)))
            }
            _ => Err(String::from("expression not supported!")),
        }
    }
}

pub struct DotGenerator {
    output: String,
    indent: u32,
}

impl DotGenerator {
    pub fn new() -> Self {
        Self {
            output: String::new(),
            indent: 0,
        }
    }

    pub fn generate(mut self, m: &Model, sql_string: &str) -> Result<String, String> {
        self.new_line("digraph G {");
        self.inc();
        self.new_line("compound = true");
        self.new_line("labeljust = l");
        self.new_line(&format!("label=\"{}\"", sql_string));
        self.new_line("node [ shape = box ]");

        let mut box_stack = vec![Rc::clone(&m.top_box)];
        let mut quantifiers = Vec::new();
        while let Some(b) = box_stack.pop() {
            let mut arrows: Vec<(ExprRef, QuantifierRef, QuantifierRef)> = Vec::new();
            let mut other_predicates: Vec<ExprRef> = Vec::new();

            let b = b.borrow();
            if let Some(predicates) = &b.predicates {
                for p in predicates {
                    let q = get_quantifiers(p);

                    // at least one quantifier must belong to the current box in order for the predicate to be displayed
                    // as an arrow
                    let mut any: bool = false;
                    for iq in b.quantifiers.iter() {
                        if q.contains(iq) {
                            any = true;
                            break;
                        }
                    }

                    match (any, q.len()) {
                        (true, 1) => {
                            let mut it = q.iter();
                            let q1 = it.next().unwrap();
                            arrows.push((Rc::clone(p), Rc::clone(q1), Rc::clone(q1)));
                        }
                        (true, 2) => {
                            let mut it = q.iter();
                            let q1 = it.next().unwrap();
                            let q2 = it.next().unwrap();
                            arrows.push((Rc::clone(p), Rc::clone(q1), Rc::clone(q2)));
                        }
                        _ => {
                            other_predicates.push(Rc::clone(p));
                        }
                    }
                }
            }

            self.new_line(&format!("subgraph cluster{} {{", b.id));
            self.inc();
            self.new_line(&format!(
                "label = \"Box{}:{}\"",
                b.id,
                Self::get_box_title(&b)
            ));
            self.new_line(&format!(
                "boxhead{} [ shape = record, label=\"{}\" ]",
                b.id,
                Self::get_box_head(&b, &other_predicates[..])
            ));

            self.new_line("{");
            self.inc();
            self.new_line("rank = same");

            if b.quantifiers.len() > 0 {
                self.new_line("node [ shape = circle ]");
            }

            for q in b.quantifiers.iter() {
                quantifiers.push(Rc::clone(&q));

                let q = q.borrow();
                box_stack.push(Rc::clone(&q.input_box));
                self.new_line(&format!(
                    "Q{0} [ label=\"Q{0}({1})\" ]",
                    q.id, q.quantifier_type
                ));
            }

            if arrows.len() > 0 {
                self.new_line("edge [ arrowhead = none, style = solid ]");
                for (e, q1, q2) in &arrows {
                    self.new_line(&format!(
                        "Q{0} -> Q{1} [ label=\"{2}\" ]",
                        q1.borrow().id,
                        q2.borrow().id,
                        e.borrow()
                    ));
                }
            }

            self.dec();
            self.new_line("}");
            self.dec();
            self.new_line("}");
        }

        if quantifiers.len() > 0 {
            self.new_line("edge [ arrowhead = none, style = dashed ]");
            for q in quantifiers.iter() {
                let q = q.borrow();
                self.new_line(&format!(
                    "Q{0} -> boxhead{1} [ lhead = cluster{1} ]",
                    q.id,
                    q.input_box.borrow().id
                ));
            }
        }

        self.dec();
        self.new_line("}");
        Ok(self.output)
    }

    fn get_box_head(b: &QGBox, predicates: &[ExprRef]) -> String {
        let mut r = String::new();
        for (i, c) in b.columns.iter().enumerate() {
            if r.len() > 0 {
                r.push('|');
            }
            r.push_str(&format!("{}: {}", i, c.expr.borrow()));
            if let Some(c) = &c.name {
                r.push_str(&format!(" AS {}", c));
            }
        }
        for expr in predicates {
            r.push_str(&format!("| {}", expr.borrow()));
        }
        match &b.box_type {
            BoxType::Select(s) => {
                if s.order_by.is_some() {
                    r.push_str("| ORDER");
                    for p in s.order_by.as_ref().unwrap().iter() {
                        r.push_str(&format!(" {} {:?}", p.expr.borrow(), p.dir));
                    }
                }
                if s.limit.is_some() {
                    r.push_str(&format!("| LIMIT {}", s.limit.as_ref().unwrap().borrow()));
                }
            }
            BoxType::Grouping(g) => {
                r.push_str("| GROUP");
                for p in g.groups.iter() {
                    r.push_str(&format!(" {} {:?}", p.expr.borrow(), p.dir));
                }
            }
            _ => {}
        }
        r.replace("<", "\\<").replace(">", "\\>")
    }

    fn get_box_title(b: &QGBox) -> String {
        match &b.box_type {
            BoxType::BaseTable(metadata) => format!("{} {}", b.get_box_type_str(), metadata.name),
            _ => b.get_box_type_str().to_string(),
        }
    }

    fn inc(&mut self) {
        self.indent += 1;
    }

    fn dec(&mut self) {
        self.indent -= 1;
    }

    fn append(&mut self, s: &str) {
        self.output.push_str(s);
    }

    fn new_line(&mut self, s: &str) {
        if self.output.rfind('\n') != Some(self.output.len()) {
            self.end_line();
            for _ in 0..self.indent * 4 {
                self.output.push(' ');
            }
        }
        self.output.push_str(s);
    }

    fn end_line(&mut self) {
        self.output.push('\n');
    }
}

//
// Rewrite rules for the graph
//

use crate::rewrite_engine;

type BoxRef = Rc<RefCell<QGBox>>;
type QuantifierRef = Rc<RefCell<Quantifier>>;

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

//
// MergeRule
//

struct MergeRule {
    to_merge: BTreeSet<QuantifierRef>,
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
                        if let BoxType::Select(inner_select) =
                            &borrowed_q.input_box.borrow().box_type
                        {
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
        // predicates in the boxes being removed that will be added to the current box
        let mut pred_to_add = Vec::new();
        for q in &self.to_merge {
            if let Some(pred_to_merge) = &q.borrow().input_box.borrow().predicates {
                pred_to_add.extend(pred_to_merge.clone());
            }
            for oq in &q.borrow().input_box.borrow().quantifiers {
                add_quantifier_to_box(obj, oq);
            }
            let mut obj = obj.borrow_mut();
            obj.remove_quantifier(q);

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
        }
        let mut rule = DereferenceRule {
            to_dereference: &self.to_merge,
        };
        let mut f = |e: &mut ExprRef| {
            rewrite_engine::deep_apply_rule(&mut rule, e);
        };
        obj.borrow_mut().visit_expressions(&mut f);
        let mut mut_obj = obj.borrow_mut();
        if mut_obj.predicates.is_none() {
            mut_obj.predicates = Some(pred_to_add);
        } else {
            mut_obj.predicates.as_mut().unwrap().extend(pred_to_add);
        }
        self.to_merge.clear();
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
            let mut stack = self.top_box.iter().cloned().collect::<Vec<_>>();
            let mut visited = HashSet::new();

            let mut column_references = HashMap::new();
            while !stack.is_empty() {
                let top = stack.pop().unwrap();
                let box_id = top.borrow().id;
                if visited.insert(box_id) {
                    let mut f = |e: &mut ExprRef| {
                        collect_column_references(e, &mut column_references);
                    };
                    top.borrow_mut().visit_expressions(&mut f);
                    for q in top.borrow().quantifiers.iter() {
                        let q = q.borrow();
                        stack.push(q.input_box.clone());
                    }
                }
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
            }
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
                        println!("{}", dereferenced.borrow());
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
    // source -> destination
    to_pushdown: Vec<Vec<(ExprRef, BoxRef)>>,
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
        let mut stack: Vec<Vec<(ExprRef, BoxRef)>> = Vec::new();
        if let Some(predicates) = &obj.borrow().predicates {
            stack.extend(predicates.iter().map(|x| vec![(x.clone(), obj.clone())]));
        }

        while !stack.is_empty() {
            let mut path = stack.pop().unwrap();
            let (p, b) = path.last().unwrap().clone();
            let quantifiers = get_quantifiers(&p);
            if quantifiers.len() == 1 {
                let q_ref = quantifiers.iter().next().unwrap();
                let only_quantifier = q_ref.borrow();
                match (&b.borrow().box_type, &only_quantifier.quantifier_type) {
                    (BoxType::OuterJoin, QuantifierType::PreservedForeach)
                    | (BoxType::Select(_), QuantifierType::Foreach) => {
                        let p = Self::dereference_predicate(&p, &q_ref);
                        // append the predicate to the stack
                        path.push((p, only_quantifier.input_box.clone()));
                        stack.push(path);
                    }
                    _ => {}
                }
            } else if path.len() > 1 {
                self.to_pushdown.push(path);
            }
        }

        !self.to_pushdown.is_empty()
    }
    fn action(&mut self, _obj: &mut BoxRef) {
        // @todo
    }
}

type BoxRule = dyn rewrite_engine::Rule<BoxRef>;
type RuleBox = Box<BoxRule>;

struct DereferenceRule<'a> {
    to_dereference: &'a BTreeSet<QuantifierRef>,
}

impl<'a> rewrite_engine::Rule<ExprRef> for DereferenceRule<'a> {
    fn name(&self) -> &'static str {
        "EmptyRule"
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
            *obj = last.unwrap();
        }
    }
}

fn apply_rule(m: &mut Model, rule: &mut BoxRule) {
    rewrite_engine::deep_apply_rule(rule, &mut m.top_box);
}

fn apply_rules(m: &mut Model, rules: &mut Vec<RuleBox>) {
    for rule in rules.iter_mut() {
        apply_rule(m, &mut **rule);
    }
}

pub fn rewrite_model(m: &mut Model) {
    let mut rules: Vec<RuleBox> = vec![
        Box::new(MergeRule::new()),
        Box::new(ColumnRemovalRule::new()),
        Box::new(EmptyBoxesRule::new()),
        Box::new(ConstantLiftingRule::new()),
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
        let top_box = make_ref(QGBox::new(0, BoxType::Select(Select::new())));
        let mut m = Model { top_box };
        let rule = Box::new(EmptyRule {});
        let mut rules = Vec::<RuleBox>::new();
        rules.push(rule);
        apply_rules(&mut m, &mut rules);
    }

    #[test]
    fn test_merge_rule() {
        let top_box = make_ref(QGBox::new(0, BoxType::Select(Select::new())));
        let nested_box = make_ref(QGBox::new(1, BoxType::Select(Select::new())));
        let quantifier = make_ref(Quantifier::new(
            1,
            QuantifierType::Foreach,
            nested_box,
            &top_box,
        ));
        top_box.borrow_mut().add_quantifier(quantifier);
        let mut m = Model { top_box };
        let mut rule = MergeRule::new();
        assert_eq!(m.top_box.borrow().quantifiers.len(), 1);
        apply_rule(&mut m, &mut rule);
        assert_eq!(m.top_box.borrow().quantifiers.len(), 0);
    }

    #[test]
    fn test_merge_rule_deep_apply() {
        let top_box = make_ref(QGBox::new(0, BoxType::Select(Select::new())));
        let nested_box1 = make_ref(QGBox::new(1, BoxType::Select(Select::new())));
        let quantifier1 = make_ref(Quantifier::new(
            1,
            QuantifierType::Foreach,
            Rc::clone(&nested_box1),
            &top_box,
        ));
        let nested_box2 = make_ref(QGBox::new(2, BoxType::Select(Select::new())));
        let quantifier2 = make_ref(Quantifier::new(
            2,
            QuantifierType::Foreach,
            nested_box2,
            &nested_box1,
        ));
        nested_box1.borrow_mut().add_quantifier(quantifier2);
        top_box.borrow_mut().add_quantifier(quantifier1);
        let mut m = Model { top_box };
        assert!(m.validate().is_ok());
        let mut rule = MergeRule::new();
        assert_eq!(m.top_box.borrow().quantifiers.len(), 1);
        apply_rule(&mut m, &mut rule);
        assert!(m.validate().is_ok());
        assert_eq!(m.top_box.borrow().quantifiers.len(), 0);
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
                let mut generator = ModelGenerator::new(&catalog);
                let model = generator.process(&c);
                assert!(model.is_ok(), "{}", model.err().unwrap());
                let mut model = model.ok().unwrap();
                assert!(model.validate().is_ok());

                let output = DotGenerator::new().generate(&model, q);
                assert!(output.is_ok());
                let output = output.ok().unwrap();
                println!("{}", output);

                rewrite_model(&mut model);
                assert!(model.validate().is_ok());

                let output = DotGenerator::new().generate(&model, q);
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
    }
}
