use crate::metadata::*;
use crate::query_model::{
    collect_quantifiers, compute_class_equivalence, make_ref, Expr, ExprRef, ExprType,
    LogicalExprType,
};
use itertools::Itertools;
use std::cell::RefCell;
use std::cmp::*;
use std::collections::*;
use std::fmt;
use std::hash::Hash;
use std::hash::Hasher;
use std::rc::*;

pub type ModelRef = Rc<RefCell<Model>>;
pub type ModelWeakRef = Weak<RefCell<Model>>;
pub type BoxRef = Rc<RefCell<QGBox>>;
pub type BoxWeakRef = Weak<RefCell<QGBox>>;
pub type QuantifierRef = Rc<RefCell<Quantifier>>;
pub type QuantifierWeakRef = Weak<RefCell<Quantifier>>;

pub struct Model {
    pub top_box: BoxRef,
    pub ids: ModelIds,
}

impl Model {
    pub fn new() -> ModelRef {
        make_ref(Self {
            // dummy box, will be replaced later
            top_box: QGBox::new(ModelWeakRef::new(), 0, BoxType::Select(Select::new())),
            ids: ModelIds::new(),
        })
    }

    pub fn replace_top_box(&mut self, new_box: BoxRef) -> BoxRef {
        let other = Rc::clone(&self.top_box);
        self.top_box = new_box;
        other
    }

    // @todo validate that distinct operation can only be enforeced by selects and unions
    pub fn validate(&self) -> Result<(), String> {
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

pub struct ModelIds {
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

    pub fn get_box_id(&mut self) -> i32 {
        let id = self.next_box_id;
        self.next_box_id += 1;
        id
    }

    pub fn get_quantifier_id(&mut self) -> i32 {
        let id = self.next_quantifier_id;
        self.next_quantifier_id += 1;
        id
    }
}

/// Conventions used so far:
///
///  * Grouping:
///    - A Grouping box is always owned by a Select box
///    - A Grouping box always have a Select box as its only input
///    - The projection of a Grouping box only contains columns, either appear in the
///      grouping key or functionally depend on columns in the grouping key and
///      aggregate functions which parameter must be column references from the input
///      box.
///  * Union
///    - A Union box is either owned by another Union box or a Select box
///    - A Grouping box always have Select boxes as its inputs
///    - The projection of a Union box does never re-order columns and cannot contain
///      computed expressions.
///  * OuterJoin
///    - A OuterJoin box is either owned by another OuterJoin box or a Select box
///    - The projection of an OuterJoin box cannot contain computed expressions.
///
///  However, there is no reason we could not relax them a bit.
pub struct QGBox {
    /// Weak pointer to the model that ultimately owns the box.
    pub model: ModelWeakRef,
    /// Uniquely identifies the box within the model.
    pub id: i32,
    pub box_type: BoxType,
    /// The projection of the box.
    pub columns: Vec<Column>,
    /// Set of input quantifiers.
    pub quantifiers: QuantifierSet,
    /// Quantifiers owning this box.
    pub ranging_quantifiers: Vec<QuantifierWeakRef>,
    /// Optional predicates. Only allowed in Select and OuterJoin boxes.
    pub predicates: Option<Vec<ExprRef>>,
    /// Distinct Operation. Only allowed in Select and Union Boxes.
    pub distinct_operation: DistinctOperation,
    /// Each key is a group of column positions within the projection of this box.
    pub unique_keys: Vec<Vec<usize>>,
}

impl QGBox {
    pub fn new(model: ModelWeakRef, id: i32, box_type: BoxType) -> BoxRef {
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
    /// whether the two boxes share the same box type.
    pub fn is_same_type(&self, o: &QGBox) -> bool {
        match (&self.box_type, &o.box_type) {
            (BoxType::BaseTable(..), BoxType::BaseTable(..)) => true,
            (BoxType::Grouping(..), BoxType::Grouping(..)) => true,
            (BoxType::OuterJoin, BoxType::OuterJoin) => true,
            (BoxType::Select(..), BoxType::Select(..)) => true,
            (BoxType::Union, BoxType::Union) => true,
            (BoxType::Values(..), BoxType::Values(..)) => true,
            _ => false,
        }
    }
    /// use add_quantifier_to_box instead to properly set the parent box of the quantifier
    pub fn add_quantifier(&mut self, q: QuantifierRef) {
        self.quantifiers.insert(q);
    }
    pub fn remove_quantifier(&mut self, q: &QuantifierRef) {
        self.quantifiers.remove(q);
    }
    pub fn add_column(&mut self, mut name: Option<String>, expr: ExprRef) -> usize {
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
    pub fn add_column_if_not_exists(&mut self, expr: Expr) -> usize {
        for (i, c) in self.columns.iter().enumerate() {
            if c.expr.borrow().is_equiv(&expr) {
                return i;
            }
        }
        self.add_column(None, make_ref(expr))
    }

    pub fn has_constant_projection(&self) -> bool {
        self.columns.iter().all(|c| {
            c.expr
                .borrow()
                .is_constant_within_context(&self.quantifiers)
        })
    }

    pub fn add_predicate(&mut self, predicate: ExprRef) {
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

    pub fn remove_predicate(&mut self, predicate: &ExprRef) {
        if let Some(predicates) = &mut self.predicates {
            predicates.retain(|x| x.as_ptr() != predicate.as_ptr());
        }
    }

    pub fn add_unique_key(&mut self, mut key: Vec<usize>) {
        // @todo consider using sets
        key.sort();
        key.dedup();
        self.unique_keys.push(key);
        self.unique_keys.sort();
        self.unique_keys.dedup();
    }

    pub fn has_predicates(&self) -> bool {
        !self.predicates.is_none() && !self.predicates.as_ref().unwrap().is_empty()
    }

    pub fn num_predicates(&self) -> usize {
        if let Some(predicates) = &self.predicates {
            predicates.len()
        } else {
            0
        }
    }

    pub fn is_select(&self) -> bool {
        match self.box_type {
            BoxType::Select(_) => true,
            _ => false,
        }
    }

    /// Return the underlying input box if this is a select box that doesn't perform
    /// any operation.
    pub fn is_dummy_select(&self) -> Option<QuantifierRef> {
        if let BoxType::Select(select) = &self.box_type {
            if self.quantifiers.len() == 1
                && select.order_by.is_none()
                && select.limit.is_none()
                && !self.has_predicates()
                && self.distinct_operation != DistinctOperation::Enforce
            {
                let input_cols = self
                    .first_quantifier()
                    .unwrap()
                    .borrow()
                    .input_box
                    .borrow()
                    .columns
                    .len();
                if self.columns.len() == input_cols
                    && self.columns.iter().enumerate().all(|(i, c)| {
                        if let ExprType::ColumnReference(c) = &c.expr.borrow().expr_type {
                            c.position == i
                        } else {
                            false
                        }
                    })
                {
                    return self.first_quantifier();
                }
            }
        }
        None
    }

    pub fn is_empty_box(&self) -> bool {
        self.is_select() && self.quantifiers.is_empty()
    }

    pub fn one_tuple_at_most(&self) -> bool {
        match &self.box_type {
            BoxType::Select(_) => {
                // a DISTINCT operator with a constant projection will return one tuple at most.
                if self.distinct_operation == DistinctOperation::Enforce
                    && self.has_constant_projection()
                {
                    return true;
                }
                let foreach_q = self
                    .quantifiers
                    .iter()
                    .filter(|q| q.borrow().quantifier_type == QuantifierType::Foreach)
                    .collect::<Vec<_>>();
                match foreach_q.len() {
                    // a single quantifier select return one tuple at most if any of the unique
                    // keys of its input quantifier is full bound via equality predicates, or
                    // it's a one tuple input
                    1 => foreach_q.iter().all(|q_ref| {
                        let q = q_ref.borrow();
                        let ib = q.input_box.borrow();
                        ib.one_tuple_at_most()
                            || ib.unique_keys.iter().any(|key| {
                                key.iter().all(|c| {
                                    let column_ref = Expr::make_column_ref((**q_ref).clone(), *c);
                                    self.predicates.iter().any(|predicates| {
                                        predicates.iter().any(|p| {
                                            let p = p.borrow();
                                            match &p.expr_type {
                                                ExprType::Cmp(super::CmpOpType::Eq) => {
                                                    !p.is_existential_comparison()
                                                        && p.operands
                                                            .as_ref()
                                                            .expect("malformed expression")
                                                            .iter()
                                                            .filter(|o| *o.borrow() == column_ref)
                                                            .count()
                                                            == 1
                                                }
                                                _ => false,
                                            }
                                        })
                                    })
                                })
                            })
                    }),
                    _ => false, // @todo fully connected joins of unique tuple quantiifers
                }
            }
            BoxType::OuterJoin => self
                .quantifiers
                .iter()
                .all(|q| q.borrow().input_box.borrow().one_tuple_at_most()),
            BoxType::Grouping(g) => g.groups.len() == 0,
            BoxType::Values(v) => v.len() <= 1,
            _ => false,
        }
    }

    pub fn exactly_one_row(&self) -> bool {
        match &self.box_type {
            BoxType::Select(_) => {
                self.predicates
                    .as_ref()
                    .map_or(true, |predicates| predicates.is_empty())
                    && self
                        .quantifiers
                        .iter()
                        .filter(|q| q.borrow().quantifier_type == QuantifierType::Foreach)
                        .all(|q| q.borrow().input_box.borrow().exactly_one_row())
            }
            BoxType::OuterJoin => {
                self.quantifiers
                    .iter()
                    .filter(|q| q.borrow().quantifier_type == QuantifierType::PreservedForeach)
                    .all(|q| q.borrow().input_box.borrow().exactly_one_row())
                    && self
                        .quantifiers
                        .iter()
                        .filter(|q| q.borrow().quantifier_type == QuantifierType::Foreach)
                        .all(|q| q.borrow().input_box.borrow().one_tuple_at_most())
            }
            BoxType::Grouping(g) => g.groups.len() == 0,
            BoxType::Values(v) => v.len() == 1,
            _ => false,
        }
    }

    pub fn get_box_type_str(&self) -> &'static str {
        match self.box_type {
            BoxType::Select(_) => "Select",
            BoxType::OuterJoin => "OuterJoin",
            BoxType::BaseTable(_) => "BaseTable",
            BoxType::Grouping(_) => "Grouping",
            BoxType::Union => "Union",
            BoxType::Values(..) => "Values",
        }
    }

    pub fn set_order_by(&mut self, order_by: Vec<KeyItem>) {
        match &mut self.box_type {
            BoxType::Select(a) => {
                a.order_by = Some(order_by);
            }
            _ => panic!(),
        }
    }

    pub fn set_limit(&mut self, limit: ExprRef) {
        match &mut self.box_type {
            BoxType::Select(a) => {
                a.limit = Some(limit);
            }
            _ => panic!(),
        }
    }

    pub fn add_group(&mut self, group: KeyItem) {
        match &mut self.box_type {
            BoxType::Grouping(g) => {
                g.groups.push(group);
            }
            _ => panic!(),
        }
    }

    pub fn recompute_unique_keys(&mut self) {
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

                        let first_id: i32 = quantifiers.first().unwrap().borrow().id;
                        if let Some(unique_keys) = keys_by_q.get(&first_id) {
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

                        // all the projected keys from the preserving side must be preserved if
                        // each row from the preserving side is guaranteed to match one tuple
                        // from the non-preserving side at most.
                        if is_outer_join {
                            // 1. check whether the non-preserving side is guaranteed to return one
                            // tuple at most for every tuple from the preserving side
                            let non_preserving_side_uniqueness = quantifiers
                                .iter()
                                .filter(|q| q.borrow().quantifier_type == QuantifierType::Foreach)
                                .all(|q| {
                                    let qid = q.borrow().id;
                                    if let Some(unique_keys) = keys_by_q.get(&qid) {
                                        unique_keys.iter().any(|key| {
                                            let key_classes = key_classes(qid, key);
                                            key_classes.len() == key.len()
                                        })
                                    } else {
                                        false
                                    }
                                });
                            if non_preserving_side_uniqueness {
                                let preserving_side = quantifiers.iter().find(|q| {
                                    q.borrow().quantifier_type == QuantifierType::PreservedForeach
                                });
                                if let Some(preserving_side) = preserving_side {
                                    // 2. keys from the preserving side projected through the current box
                                    let projected_keys = {
                                        let preserving_q = preserving_side.borrow();
                                        let preserving_box = preserving_q.input_box.borrow();
                                        preserving_box
                                            .unique_keys
                                            .iter()
                                            .filter_map(|input_key| {
                                                let projected_key = input_key
                                                    .iter()
                                                    .filter_map(|ic| {
                                                        let col_ref = Expr::make_column_ref(
                                                            preserving_side.clone(),
                                                            *ic,
                                                        );
                                                        self.columns
                                                            .iter()
                                                            .find_position(|c| {
                                                                c.expr.borrow().is_equiv(&col_ref)
                                                            })
                                                            .map(|(p, _)| p)
                                                    })
                                                    .collect::<Vec<_>>();
                                                if projected_key.len() == input_key.len() {
                                                    Some(projected_key)
                                                } else {
                                                    None
                                                }
                                            })
                                            .collect::<Vec<_>>()
                                    };
                                    for projected_key in projected_keys {
                                        self.add_unique_key(projected_key);
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
            if self.unique_keys.is_empty() {
                let num_columns = self.columns.len();
                self.unique_keys.push((0..num_columns).collect());
            } else {
                self.distinct_operation = DistinctOperation::Guaranteed;
            }
        }

        // remove duplicated keys. We could remove keys which prefix is also a key
        self.unique_keys.dedup();
    }

    pub fn visit_expressions<F>(&mut self, f: &mut F)
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

    pub fn visit_expressions_recursively<F>(&mut self, f: &mut F)
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

    pub fn first_quantifier(&self) -> Option<QuantifierRef> {
        self.quantifiers.iter().cloned().next()
    }

    /// True if this box always returns unique tuples.
    pub fn distinct_tuples(&self) -> bool {
        self.distinct_operation == DistinctOperation::Enforce || !self.unique_keys.is_empty()
    }

    /// Adds the columns from all non subquery quantifiers to the projection of this box.
    pub fn add_all_columns(&mut self) {
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

#[derive(Clone)]
pub struct Column {
    pub name: Option<String>,
    pub expr: ExprRef,
}

pub use crate::ast::Direction;

#[derive(Clone, Eq, PartialEq)]
pub struct KeyItem {
    pub expr: ExprRef,
    pub dir: Direction,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DistinctOperation {
    /// DISTINCTness is required but guaranteed
    Guaranteed,
    /// The box must enforce DISTINCT
    Enforce,
    /// DISTINCTness is not required
    Preserve,
}

pub struct Select {
    pub limit: Option<ExprRef>,
    pub order_by: Option<Vec<KeyItem>>,
}

impl Select {
    pub fn new() -> Self {
        Self {
            limit: None,
            order_by: None,
        }
    }
}

pub struct Grouping {
    pub groups: Vec<KeyItem>,
}

impl Grouping {
    pub fn new() -> Self {
        Self { groups: Vec::new() }
    }
}

pub enum BoxType {
    Select(Select),
    BaseTable(TableMetadata),
    Grouping(Grouping),
    OuterJoin,
    Union,
    Values(Vec<Vec<ExprRef>>),
}

pub type QuantifierSet = BTreeSet<QuantifierRef>;

pub struct Quantifier {
    pub id: i32,
    pub quantifier_type: QuantifierType,
    pub input_box: BoxRef,
    pub parent_box: Weak<RefCell<QGBox>>,
    pub alias: Option<String>,
    weak_self: Option<QuantifierWeakRef>,
}

impl Quantifier {
    pub fn new(
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

    pub fn set_alias(&mut self, alias: String) {
        self.alias = Some(alias);
    }

    pub fn get_effective_name(&self) -> Option<String> {
        if self.alias.is_some() {
            return self.alias.clone();
        }
        let b = self.input_box.borrow();
        if let BoxType::BaseTable(t) = &b.box_type {
            return Some(t.name.clone());
        }
        return None;
    }

    pub fn is_subquery(&self) -> bool {
        match &self.quantifier_type {
            QuantifierType::Existential
            | QuantifierType::Scalar
            | QuantifierType::All
            | QuantifierType::Any => true,
            _ => false,
        }
    }

    pub fn weak(&self) -> QuantifierWeakRef {
        self.weak_self.as_ref().unwrap().clone()
    }

    pub fn replace_input_box(&mut self, b: BoxRef) {
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

impl Drop for Quantifier {
    fn drop(&mut self) {
        self.input_box
            .borrow_mut()
            .ranging_quantifiers
            .retain(|x| x.as_ptr() != self.weak().as_ptr())
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug)]
pub enum QuantifierType {
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
