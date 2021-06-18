use itertools::Itertools;
use std::cell::RefCell;
use std::collections::*;
use std::rc::*;

mod dot_generator;
pub use dot_generator::DotGenerator;

mod model_generator;
pub use model_generator::ModelGenerator;

mod expr;
pub use expr::*;

mod model;
pub use model::*;

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

fn make_quantifier_set(v: Vec<QuantifierRef>) -> QuantifierSet {
    let mut s = BTreeSet::new();
    s.extend(v);
    s
}

fn add_quantifier_to_box(b: &BoxRef, q: &QuantifierRef) {
    let mut bb = b.borrow_mut();
    bb.add_quantifier(Rc::clone(q));
    let mut bq = q.borrow_mut();
    bq.parent_box = Rc::downgrade(&b);
}

/// Lift an expression through the projection of the given quantifier
fn lift_expression(q: &QuantifierRef, e: &ExprRef) -> Option<ExprRef> {
    if e.borrow().is_runtime_constant() {
        return Some(e.clone());
    }
    if let ExprType::ColumnReference(c) = &e.borrow().expr_type {
        if !q
            .borrow()
            .input_box
            .borrow()
            .quantifiers
            .contains(&c.quantifier)
        {
            // it's a column reference from a parent context
            return Some(e.clone());
        }
    }
    for (i, c) in q.borrow().input_box.borrow().columns.iter().enumerate() {
        if c.expr.borrow().is_equiv(&e.borrow()) {
            return Some(make_ref(Expr::make_column_ref(q.clone(), i)));
        }
    }
    let be = e.borrow();
    if let Some(operands) = &be.operands {
        let new_operands = operands
            .iter()
            .filter_map(|x| lift_expression(q, x))
            .collect::<Vec<_>>();
        if operands.len() == new_operands.len() {
            return Some(make_ref(Expr {
                expr_type: be.expr_type.clone(),
                operands: Some(new_operands),
            }));
        }
    }
    None
}

fn make_ref<T>(t: T) -> Rc<RefCell<T>> {
    Rc::new(RefCell::new(t))
}

//
// Rewrite rules for the graph
//

use crate::rewrite_engine;

/// Template for new model rewrite rules
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

/// Executes a collection of rules within the same model traversal.
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

/// Nomarlizes the expressions in the boxes of the model.
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

/// Uses class equivalences to propagate constraints.
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
                let quantifiers_by_id = obj
                    .quantifiers
                    .iter()
                    .map(|q| (q.borrow().id, q.clone()))
                    .collect::<HashMap<i32, QuantifierRef>>();

                // (quantifier, position) -> class
                let class_equivalences = compute_class_equivalence(predicates)
                    .into_iter()
                    // remove column references from the outer scope
                    .filter(|((qid, _), _)| quantifiers_by_id.contains_key(qid))
                    .collect::<HashMap<_, _>>();
                // classs -> (quantifier, position)
                let classes = class_equivalences
                    .iter()
                    .map(|((q, p), c)| (*c, (*q, *p)))
                    .into_group_map();

                for pred in predicates.iter() {
                    // not null constraint
                    {
                        let p = pred.borrow();
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

                    let p = deep_clone(pred);
                    let mut predicate_classes = BTreeSet::new();
                    let _ = p.borrow_mut().visit_mut(&mut |e| -> Result<(), ()> {
                        let mut class = None;
                        if let ExprType::ColumnReference(c) = &e.expr_type {
                            let qid = c.quantifier.borrow().id;
                            class = class_equivalences.get(&(qid, c.position));
                        }
                        // convert the column reference into a generic column with the id of
                        // the class for rewriting it later
                        if let Some(class) = class {
                            predicate_classes.insert(*class);
                            e.expr_type = ExprType::Column(*class);
                        }
                        Ok(())
                    });

                    let combinations = predicate_classes
                        .iter()
                        .map(|class| {
                            let v = classes.get(class).unwrap();
                            v.iter().map(move |v| (*class, *v)).collect::<Vec<_>>()
                        })
                        .multi_cartesian_product()
                        .map(|v| v.into_iter().collect::<HashMap<usize, (i32, usize)>>())
                        .collect::<Vec<_>>();

                    for mapping in combinations {
                        let p = deep_clone(&p);

                        let _ = p.borrow_mut().visit_mut(&mut |e| -> Result<(), ()> {
                            let mut cr = None;
                            if let ExprType::Column(c) = &e.expr_type {
                                cr = Some(mapping.get(c).expect("expected mapping for class"));
                            }
                            if let Some(cr) = cr {
                                e.expr_type = ExprType::ColumnReference(ColumnReference {
                                    quantifier: quantifiers_by_id.get(&cr.0).unwrap().clone(),
                                    position: cr.1,
                                });
                            }
                            Ok(())
                        });

                        self.new_predicates.push(p);
                    }
                }

                // note: insert the predicates in reliable order
                self.new_predicates.sort();
                self.new_predicates.dedup();
                self.new_predicates
                    .retain(|p| !p.borrow().is_true_predicate() && !predicates.contains(p));
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

/// Note: this rule is meant to be used within the same traversal as ConstraintPropagation.
/// A pass of PushDownPredicatesRules is needed afterwards for cleaning up redudant
/// predicates.
struct ConstraintLiftingRule {
    new_predicates: Vec<ExprRef>,
}

impl ConstraintLiftingRule {
    fn new() -> Self {
        Self {
            new_predicates: Vec::new(),
        }
    }

    /// Collect the predicates that can be lifted from boxes under `q` without
    /// extending projections.
    fn collect_liftable_predicates(q: &QuantifierRef, liftable_predicates: &mut Vec<ExprRef>) {
        let bq = q.borrow();
        let input_box = bq.input_box.clone();
        drop(bq);
        let input_box = input_box.borrow();
        let mut path = Vec::new();
        match &input_box.box_type {
            BoxType::Select(..) => {
                path.push(q.clone());
            }
            BoxType::Grouping(..) => {
                if let Some(iq) = input_box.first_quantifier() {
                    path.push(q.clone());
                    path.push(iq.clone());
                }
            }
            BoxType::OuterJoin => {
                path.push(q.clone());
                while let Some(iq) = path.last().cloned() {
                    let biq = iq.borrow();
                    let input_box = biq.input_box.borrow();
                    if let BoxType::OuterJoin = &input_box.box_type {
                        path.extend(
                            input_box
                                .quantifiers
                                .iter()
                                .filter(|q| {
                                    q.borrow().quantifier_type == QuantifierType::PreservedForeach
                                })
                                .cloned(),
                        );
                    } else {
                        break;
                    }
                }
            }
            BoxType::Union => {
                if let Some(fq) = input_box.first_quantifier() {
                    let predicates = input_box
                        .quantifiers
                        .iter()
                        // collect the predicates that are liftable from each quantifier
                        .map(|q| {
                            let mut v = Vec::new();
                            Self::collect_liftable_predicates(q, &mut v);
                            // put them all in terms of the first quantifier
                            if q.as_ptr() != fq.as_ptr() {
                                let mut to_replace = BTreeMap::new();
                                to_replace.insert(q.clone(), fq.clone());
                                let mut rule = ReplaceQuantifierRule {
                                    to_replace: &to_replace,
                                };
                                v = v
                                    .into_iter()
                                    .map(|mut e| {
                                        rewrite_engine::deep_apply_rule(&mut rule, &mut e);
                                        e
                                    })
                                    .collect();
                            }
                            v
                        })
                        // find the common predicates
                        .reduce(|mut a, b| {
                            a.retain(|x| b.iter().any(|y| x.borrow().is_equiv(&y.borrow())));
                            a
                        });
                    if let Some(predicates) = predicates {
                        // final lift through the ranging quantifier of the union
                        liftable_predicates.extend(
                            predicates
                                .into_iter()
                                .filter_map(|x| lift_expression(q, &x)),
                        );
                    }
                }
            }
            _ => {}
        }
        if let Some(last) = path.pop() {
            // @todo assert is select
            if let Some(predicates) = &last.borrow().input_box.borrow().predicates {
                for p in predicates.iter() {
                    let mut lifted_predicate = lift_expression(&last, &p);
                    while let Some(q) = path.pop() {
                        lifted_predicate = lifted_predicate.and_then(|p| lift_expression(&q, &p));
                    }
                    if let Some(lifted_predicate) = lifted_predicate {
                        liftable_predicates.push(lifted_predicate);
                    }
                }
            }
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for ConstraintLiftingRule {
    fn name(&self) -> &'static str {
        "ConstraintLiftingRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        let obj = obj.borrow();
        if let BoxType::Select(_) = &obj.box_type {
            for q in obj.quantifiers.iter() {
                let bq = q.borrow();
                if !bq.is_subquery() {
                    Self::collect_liftable_predicates(&q, &mut self.new_predicates);
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

/// This is a version of the E-to-F rule in the paper.
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
                                let q_ref = existential_quantifiers.into_iter().next().unwrap();
                                let q = q_ref.borrow();
                                let ib = q.input_box.borrow();
                                if ib.distinct_tuples() || ib.one_tuple_at_most() {
                                    return Some(q_ref.clone());
                                }
                            };
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

/// Remove a GROUP BY operator with a key that forms a unique key in the
/// input quantifier.
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
                // no aggregate function is used. note: could this be relaxed?
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
// FunctionalDependencies
//

/// Remove columns from GROUP KEY that functionally depend on other columns also in the GROUP KEY
struct FunctionalDependenciesRule {
    new_key: Option<Vec<KeyItem>>,
}

impl FunctionalDependenciesRule {
    fn new() -> Self {
        Self { new_key: None }
    }
}

impl rewrite_engine::Rule<BoxRef> for FunctionalDependenciesRule {
    fn name(&self) -> &'static str {
        "FunctionalDependenciesRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.new_key = None;
        let obj = obj.borrow();
        // note: this should be an assert
        if obj.quantifiers.len() == 1 {
            if let BoxType::Grouping(grouping) = &obj.box_type {
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
                let q = obj.quantifiers.iter().next().unwrap();
                let q = q.borrow();
                let b = q.input_box.borrow();
                // find the shortest unique key which all columns are contained by the
                // grouping key.
                let mut keys = b
                    .unique_keys
                    .iter()
                    .filter(|key| key.iter().all(|x| column_refs_in_key.contains(x)))
                    .sorted_by_key(|k| k.len());
                if let Some(key) = keys.next() {
                    self.new_key = Some(
                        grouping
                            .groups
                            .iter()
                            .filter(|x| {
                                let x = x.expr.borrow();
                                if let ExprType::ColumnReference(c) = &x.expr_type {
                                    if key.contains(&c.position) {
                                        return true;
                                    }
                                }
                                false
                            })
                            .cloned()
                            .collect::<Vec<_>>(),
                    );
                }
            }
        }
        self.new_key.is_some()
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let mut obj = obj.borrow_mut();
        if let BoxType::Grouping(grouping) = &mut obj.box_type {
            std::mem::swap(&mut grouping.groups, self.new_key.as_mut().unwrap());
            // note: we should recompute all the keys all the way up to the top box
            obj.recompute_unique_keys();
            self.new_key = None;
        } else {
            panic!("invalid action");
        }
    }
}

//
// MergeRule
//

/// Merges nested select boxes.
struct MergeRule {
    to_merge: QuantifierSet,
}

impl MergeRule {
    fn new() -> Self {
        Self {
            to_merge: BTreeSet::new(),
        }
    }

    fn add_quantifier_to_box(obj: &BoxRef, source_q: &QuantifierRef, new_q: &QuantifierRef) {
        if let BoxType::OuterJoin = &obj.borrow().box_type {
            // this is a 1-1 replacement, so the type must be preserved
            new_q.borrow_mut().quantifier_type = source_q.borrow_mut().quantifier_type;
        }
        add_quantifier_to_box(obj, new_q);
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
            // @todo this is best handled with a separate rule
            // BoxType::Union => {
            //     let to_replace = borrowed_obj.quantifiers.iter().filter_map(|q| {
            //         if let Some(iq) = q.borrow().input_box.borrow().is_dummy_select() {
            //             let biq = iq.borrow();
            //             let ib = biq.input_box.borrow();
            //             if let BoxType::Union = &ib.box_type {
            //                 if ib.distinct_operation == borrowed_obj.distinct_operation {
            //                     return Some((q, iq.clone()));
            //                 }
            //             }
            //         }
            //         None
            //     });
            // }
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
                        Self::add_quantifier_to_box(obj, &q, oq);
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
                        Self::add_quantifier_to_box(obj, &q, &new_q);
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

/// Remove un-referenced columns from the projection of intermediate boxes.
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
// EquivalentColumns
//

struct EquivalentColumnsRule {
    equivalent_columns: BTreeMap<QuantifierRef, HashMap<usize, usize>>,
}

impl EquivalentColumnsRule {
    fn new() -> Self {
        Self {
            equivalent_columns: BTreeMap::new(),
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for EquivalentColumnsRule {
    fn name(&self) -> &'static str {
        "EquivalentColumnsRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.equivalent_columns.clear();
        let bo = obj.borrow();
        for q in bo.quantifiers.iter() {
            let bq = q.borrow();
            let ib = bq.input_box.borrow();
            let classes = if ib.is_select() {
                if let Some(predicates) = &ib.predicates {
                    Some(compute_class_equivalence(predicates))
                } else {
                    None
                }
            } else {
                None
            };
            let mut eq_cols = HashMap::new();
            for i in 0..ib.columns.len() {
                if !eq_cols.contains_key(&i) {
                    let ie = ib.columns[i].expr.borrow();
                    for j in i + 1..ib.columns.len() {
                        let je = ib.columns[j].expr.borrow();
                        if ie.is_equiv(&je) {
                            eq_cols.insert(j, i);
                        } else if let Some(classes) = &classes {
                            //  select boxes use also equivalence classes
                            if let ExprType::ColumnReference(ic) = &ie.expr_type {
                                if let ExprType::ColumnReference(jc) = &je.expr_type {
                                    let ic = classes.get(&ic.to_desc());
                                    let ij = classes.get(&jc.to_desc());
                                    if ic.is_some() && ij.is_some() && ic.unwrap() == ij.unwrap() {
                                        eq_cols.insert(j, i);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if !eq_cols.is_empty() {
                self.equivalent_columns.insert(q.clone(), eq_cols);
            }
        }
        !self.equivalent_columns.is_empty()
    }
    fn action(&mut self, obj: &mut BoxRef) {
        // collect all column references under `obj` to be able to replace the
        // column references to the quantifiers being removed from within correlated
        // siblings.
        let mut column_references = BTreeMap::new();
        collect_column_references_recursively(obj.clone(), &mut column_references);
        for (q, eq_cols) in self.equivalent_columns.iter_mut() {
            if let Some(col_refs) = column_references.get(q) {
                for (old, new) in eq_cols {
                    if let Some(col_refs) = col_refs.get(old) {
                        for col_ref in col_refs {
                            let mut bc = col_ref.borrow_mut();
                            if let ExprType::ColumnReference(c) = &mut bc.expr_type {
                                c.position = *new;
                            } // panic?
                        }
                    }
                }
            }
        }
        self.equivalent_columns.clear();
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
        match &obj.box_type {
            BoxType::Select(s) => {
                if let Some(limit) = &s.limit {
                    let limit = limit.borrow();
                    if let ExprType::Literal(l) = &limit.expr_type {
                        match l {
                            Value::BigInt(0) => return true,
                            _ => {}
                        }
                    }
                }

                obj.predicates
                    .iter()
                    .any(|x| x.iter().any(|x| x.borrow().is_false_predicate()))
            }
            BoxType::Union => obj
                .quantifiers
                .iter()
                .any(|q| q.borrow().input_box.borrow().is_empty_box()),
            BoxType::OuterJoin => obj
                .predicates
                .iter()
                .any(|x| x.iter().any(|x| x.borrow().is_false_predicate())),
            _ => false,
        }
    }
    fn action(&mut self, obj_ref: &mut BoxRef) {
        let mut obj = obj_ref.borrow_mut();
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
            BoxType::Union => {
                let mut to_preserve: QuantifierSet = obj
                    .quantifiers
                    .iter()
                    .filter(|q| !q.borrow().input_box.borrow().is_empty_box())
                    .cloned()
                    .collect();
                match to_preserve.len() {
                    0 => {
                        obj.quantifiers.clear();
                        obj.box_type = BoxType::Select(Select::new());
                        obj.predicates = None;
                        for c in obj.columns.iter_mut() {
                            c.expr = make_ref(Expr::make_null());
                        }
                    }
                    _ => {
                        let old_first = obj.first_quantifier().expect("invalid union");

                        if !to_preserve.contains(&old_first) {
                            let new_first = to_preserve.iter().next().unwrap().clone();
                            let to_replace = {
                                let mut t = BTreeMap::new();
                                t.insert(old_first.clone(), new_first.clone());
                                t
                            };
                            let mut rule = ReplaceQuantifierRule {
                                to_replace: &to_replace,
                            };
                            let mut f = |e: &mut ExprRef| {
                                rewrite_engine::deep_apply_rule(&mut rule, e);
                            };
                            obj.visit_expressions(&mut f);
                        }
                        if to_preserve.len() == 1 {
                            obj.box_type = BoxType::Select(Select::new());
                        }
                        std::mem::swap(&mut obj.quantifiers, &mut to_preserve);
                    }
                }
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
                    | (BoxType::Select(_), QuantifierType::Existential)
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

            // subqueries must be referenced by at least one predicate
            if !original_p.borrow().is_existential_comparison() {
                obj.borrow_mut().remove_predicate(&original_p);
            }
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
                            // The predicate could be a correlated one, in which case I'm not
                            // sure modifying the sibling quantifier is correct. The plan for
                            // that case is to lift the predicate and then then remove the
                            // outer join once the predicate is in the right box.
                            if obj.quantifiers.contains(&c1.quantifier) {
                                let input_box = c1.quantifier.borrow().input_box.clone();
                                let input_box = input_box.borrow();
                                if let BoxType::OuterJoin = &input_box.box_type {
                                    if let Some(deref) = expr.dereference() {
                                        if let ExprType::ColumnReference(c2) =
                                            &deref.borrow().expr_type
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

struct OrderByRemovalRule {
    new_order_by: Option<Vec<KeyItem>>,
}

impl OrderByRemovalRule {
    fn new() -> Self {
        Self { new_order_by: None }
    }
}

impl rewrite_engine::Rule<BoxRef> for OrderByRemovalRule {
    fn name(&self) -> &'static str {
        "OrderByRemovalRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.new_order_by = None;
        let obj = obj.borrow();
        if let BoxType::Select(s) = &obj.box_type {
            if let Some(order_by) = &s.order_by {
                if !obj.columns.iter().any(|c| {
                    get_quantifiers(&c.expr)
                        .intersection(&obj.quantifiers)
                        .next()
                        .is_some()
                }) {
                    return true;
                }
                let new_order_by = order_by
                    .iter()
                    .filter(|k| {
                        get_quantifiers(&k.expr)
                            .intersection(&obj.quantifiers)
                            .next()
                            .is_some()
                    })
                    .cloned()
                    .collect::<Vec<_>>();
                if new_order_by.len() != order_by.len() {
                    if !new_order_by.is_empty() {
                        self.new_order_by = Some(new_order_by);
                    }
                    return true;
                }
            }
        }
        false
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let mut obj = obj.borrow_mut();
        if let BoxType::Select(s) = &mut obj.box_type {
            std::mem::swap(&mut s.order_by, &mut self.new_order_by);
            self.new_order_by = None;
        }
    }
}

/// Remove quantifiers pointing to the same box joined via a unqiue key.
struct RedundantJoinRule {
    to_replace: BTreeMap<QuantifierRef, QuantifierRef>,
}

impl RedundantJoinRule {
    fn new() -> Self {
        Self {
            to_replace: BTreeMap::new(),
        }
    }

    fn are_joined_via_unique_key(bo: &QGBox, q1: &QuantifierRef, q2: &QuantifierRef) -> bool {
        let bq1 = q1.borrow();
        let ib = bq1.input_box.borrow();
        for k in ib.unique_keys.iter() {
            if k.iter()
                .map(|i| {
                    let c1 = make_ref(Expr::make_column_ref(q1.clone(), *i));
                    let c2 = make_ref(Expr::make_column_ref(q2.clone(), *i));
                    let eq = make_ref(Expr::make_cmp(CmpOpType::Eq, c1, c2));
                    eq.borrow_mut().normalize();
                    eq
                })
                .all(|p| {
                    bo.predicates
                        .iter()
                        .any(|predicates| predicates.iter().any(|x| *x == p))
                })
            {
                return true;
            }
        }
        false
    }
}

impl rewrite_engine::Rule<BoxRef> for RedundantJoinRule {
    fn name(&self) -> &'static str {
        "RedundantJoinRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.to_replace.clear();

        let bo = obj.borrow();
        if let BoxType::Select(_) = &bo.box_type {
            let same_box = bo
                .quantifiers
                .iter()
                .filter(|q| q.borrow().quantifier_type == QuantifierType::Foreach)
                .filter(|q| q.borrow().input_box.borrow().unique_keys.len() > 0)
                .map(|q| (q.borrow().input_box.as_ptr(), q))
                .into_group_map();
            for (_, mut v) in same_box.into_iter().filter(|(_, v)| v.len() > 1) {
                v.sort();
                for i in 0..v.len() {
                    for j in i + 1..v.len() {
                        if !self.to_replace.contains_key(v[j]) {
                            if Self::are_joined_via_unique_key(&bo, v[i], v[j]) {
                                self.to_replace.insert(v[j].clone(), v[i].clone());
                            }
                        }
                    }
                }
            }
        }

        !self.to_replace.is_empty()
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let mut bo = obj.borrow_mut();
        let mut rule = ReplaceQuantifierRule {
            to_replace: &self.to_replace,
        };
        let mut f = |e: &mut ExprRef| {
            rewrite_engine::deep_apply_rule(&mut rule, e);
        };
        bo.visit_expressions(&mut f);
        for q in self.to_replace.keys() {
            bo.quantifiers.remove(q);
        }
        self.to_replace.clear();
    }
}

/// Remove redundant outer joins when the projection only contains
/// columns from the preserving side and each unique tuple from the
/// preserving side matches exactly one row from the non-presering
/// side.
struct RedundantOuterJoinRule {}

impl RedundantOuterJoinRule {
    fn new() -> Self {
        Self {}
    }
}

impl rewrite_engine::Rule<BoxRef> for RedundantOuterJoinRule {
    fn name(&self) -> &'static str {
        "RedundantOuterJoinRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        let bo = obj.borrow();
        if let BoxType::OuterJoin = &bo.box_type {
            let mut quantifiers = QuantifierSet::new();
            for c in bo.columns.iter() {
                collect_quantifiers(&mut quantifiers, &c.expr);
            }

            let preserving_q = bo
                .quantifiers
                .iter()
                .filter(|q| q.borrow().quantifier_type == QuantifierType::PreservedForeach)
                .next()
                .unwrap();
            let non_preserving_q = bo
                .quantifiers
                .iter()
                .filter(|q| q.borrow().quantifier_type == QuantifierType::Foreach)
                .next()
                .unwrap();
            if quantifiers.len() == 1 && quantifiers.contains(preserving_q) {
                if let Some(predicates) = &bo.predicates {
                    let classes = compute_class_equivalence(predicates);
                    let bnpq = non_preserving_q.borrow();
                    let bib = bnpq.input_box.borrow();

                    if bib
                        .unique_keys
                        .iter()
                        .any(|k| k.iter().all(|p| classes.contains_key(&(bnpq.id, *p))))
                    {
                        return true;
                    }
                }
            }
            if !quantifiers.contains(non_preserving_q) {
                // outer joins within an existential quantifier can be removed if no columns
                // from the non-preserving side are referenced
                return bo.ranging_quantifiers.len() > 0
                    && bo.ranging_quantifiers.iter().all(|q| {
                        if let Some(q) = q.upgrade() {
                            if let Some(p) = q.borrow().parent_box.upgrade() {
                                let p = p.borrow();
                                return p.ranging_quantifiers.len() > 0
                                    && p.ranging_quantifiers.iter().all(|q| {
                                        if let Some(q) = q.upgrade() {
                                            return q.borrow().quantifier_type
                                                == QuantifierType::Existential;
                                        }
                                        false
                                    });
                            }
                        }
                        false
                    });
            }
        }
        false
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let mut bo = obj.borrow_mut();
        bo.predicates = None;
        bo.box_type = BoxType::Select(Select::new());
        bo.quantifiers = bo
            .quantifiers
            .iter()
            .filter(|q| q.borrow().quantifier_type == QuantifierType::PreservedForeach)
            .map(|q| {
                q.borrow_mut().quantifier_type = QuantifierType::Foreach;
                q
            })
            .cloned()
            .collect();
    }
}

/// Convert scalar subqueries into join operands
struct ScalarToForeachRule {}

impl ScalarToForeachRule {
    fn new() -> Self {
        Self {}
    }

    fn is_column_ref_from(q: &Quantifier, p: &ExprRef) -> bool {
        if let ExprType::ColumnReference(c) = &p.borrow().expr_type {
            *c.quantifier.borrow() == *q
        } else {
            false
        }
    }

    fn nulls_are_rejected(q: &Quantifier) -> bool {
        let p = q.parent_box.upgrade();
        if let Some(p) = p {
            let p = p.borrow();
            if let BoxType::Select(_) = &p.box_type {
                if let Some(predicates) = &p.predicates {
                    for pred in predicates.iter() {
                        if Self::is_column_ref_from(q, pred) {
                            return true;
                        }
                        let pred = pred.borrow();
                        match &pred.expr_type {
                            ExprType::Cmp(_) => {
                                if pred
                                    .operands
                                    .as_ref()
                                    .expect("malformed expression")
                                    .iter()
                                    .any(|p| Self::is_column_ref_from(q, p))
                                {
                                    return true;
                                }
                            }
                            _ => {
                                if let Some(p) = pred.is_not_null() {
                                    return Self::is_column_ref_from(q, &p);
                                }
                            }
                        }
                    }
                }
            }
        }
        false
    }
}

impl rewrite_engine::Rule<BoxRef> for ScalarToForeachRule {
    fn name(&self) -> &'static str {
        "ScalarToForeachRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        let obj = obj.borrow();
        obj.one_tuple_at_most()
            && obj.ranging_quantifiers.len() > 0
            && obj.ranging_quantifiers.iter().all(|q| {
                let q = q.upgrade();
                if let Some(q) = q {
                    let q = q.borrow();
                    q.quantifier_type == QuantifierType::Scalar && Self::nulls_are_rejected(&q)
                } else {
                    false
                }
            })
    }
    fn action(&mut self, obj: &mut BoxRef) {
        let obj = obj.borrow();
        for q in obj.ranging_quantifiers.iter() {
            let q = q.upgrade();
            if let Some(q) = q {
                q.borrow_mut().quantifier_type = QuantifierType::Foreach;
            }
        }
    }
}

//
// FlattenJoin
//

struct FlattenJoinRule {
    to_pull: Vec<(BoxRef, QuantifierRef)>,
}

impl FlattenJoinRule {
    fn new() -> SingleTraversalRule {
        SingleTraversalRule::new(vec![
            Box::new(Self::new_internal()),
            Box::new(MergeRule::new()),
        ])
    }
    fn new_internal() -> Self {
        Self {
            to_pull: Vec::new(),
        }
    }
}

impl rewrite_engine::Rule<BoxRef> for FlattenJoinRule {
    fn name(&self) -> &'static str {
        "FlattenJoinRule"
    }
    fn apply_top_down(&self) -> bool {
        false
    }
    fn condition(&mut self, obj: &BoxRef) -> bool {
        self.to_pull.clear();
        let bo = obj.borrow();
        if let BoxType::Select(_) = &bo.box_type {
            self.to_pull.extend(bo.quantifiers.iter().filter_map(|q| {
                let bq = q.borrow();
                let ib = &bq.input_box;
                let bib = bq.input_box.borrow();
                if let BoxType::OuterJoin = &bib.box_type {
                    if let Some(q) = bib
                        .quantifiers
                        .iter()
                        .filter(|q| q.borrow().quantifier_type == QuantifierType::PreservedForeach)
                        .next()
                    {
                        return Some((ib.clone(), q.clone()));
                    }
                }
                None
            }));
        }
        !self.to_pull.is_empty()
    }
    fn action(&mut self, obj: &mut BoxRef) {
        loop {
            for (b, q) in self.to_pull.drain(..) {
                b.borrow_mut().quantifiers.remove(&q);
                q.borrow_mut().quantifier_type = QuantifierType::Foreach;
                add_quantifier_to_box(obj, &q);
            }
            if !self.condition(obj) {
                break;
            }
        }
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
        Box::new(EquivalentColumnsRule::new()),
        Box::new(ColumnRemovalRule::new()),
        Box::new(EmptyBoxesRule::new()),
        Box::new(ConstantLiftingRule::new()),
        Box::new(SemiJoinRemovalRule::new()),
        Box::new(GroupByRemovalRule::new()),
        Box::new(FunctionalDependenciesRule::new()),
        Box::new(PushDownPredicatesRule::new()),
        Box::new(ConstraintPropagationRule::new()),
        Box::new(OrderByRemovalRule::new()),
        Box::new(OuterToInnerJoinRule::new()),
        Box::new(RedundantJoinRule::new()),
        Box::new(RedundantOuterJoinRule::new()),
        Box::new(ScalarToForeachRule::new()),
        // cleanup
        Box::new(NormalizationRule::new()),
        Box::new(PushDownPredicatesRule::new()),
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
    use crate::ast;
    use crate::metadata::*;

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

    #[derive(PartialEq, Copy, Clone)]
    pub enum DumpMode {
        None,
        Final,
        Steps,
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
            dump: DumpMode,
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
                                if dump == DumpMode::Steps {
                                    output.push_str(
                                        &DotGenerator::new().generate(&model.borrow(), &label)?,
                                    );
                                }

                                Self::apply_rule(&model, rule)?;
                                label.push_str(&format!(" + {}", rule));
                            }
                        }
                        if dump != DumpMode::None {
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
                "ConstraintLifting" => Box::new(ConstraintLiftingRule::new()),
                "ConstraintPropagation" => Box::new(ConstraintPropagationRule::new()),
                "EmptyBoxes" => Box::new(EmptyBoxesRule::new()),
                "EquivalentColumns" => Box::new(EquivalentColumnsRule::new()),
                "FlattenJoin" => Box::new(FlattenJoinRule::new()),
                "FunctionalDependencies" => Box::new(FunctionalDependenciesRule::new()),
                "GroupByRemoval" => Box::new(GroupByRemovalRule::new()),
                "Merge" => Box::new(MergeRule::new()),
                "Normalization" => Box::new(NormalizationRule::new()),
                "OrderByRemoval" => Box::new(OrderByRemovalRule::new()),
                "OuterToInnerJoin" => Box::new(OuterToInnerJoinRule::new()),
                "PushDownPredicates" => Box::new(PushDownPredicatesRule::new()),
                "RedundantJoin" => Box::new(RedundantJoinRule::new()),
                "RedundantOuterJoin" => Box::new(RedundantOuterJoinRule::new()),
                "ScalarToForeach" => Box::new(ScalarToForeachRule::new()),
                "SemiJoinRemoval" => Box::new(SemiJoinRemovalRule::new()),
                _ => return Err(format!("invalid rule {}", rule)),
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
                    "query" => {
                        interpreter.process_query(&test_case.input[..], apply, DumpMode::Final)
                    }
                    "check" => {
                        interpreter.process_query(&test_case.input[..], apply, DumpMode::None)
                    }
                    "steps" => {
                        interpreter.process_query(&test_case.input[..], apply, DumpMode::Steps)
                    }
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
