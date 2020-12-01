use std::env;
use std::iter::*;

#[allow(dead_code)]
mod ast;
#[allow(dead_code)]
mod lexer;

// lexer

// syntax tree

// query graph model

#[allow(dead_code)]
mod qg {
    use std::cell::RefCell;
    use std::cmp::*;
    use std::collections::*;
    use std::rc::*;

    enum DataType {
        String,
        Integer,
        BigInt,
        Double,
    }

    struct ColumnMetadata {
        name: String,
        data_type: DataType,
    }

    struct TableMetadata {
        name: String,
        columns: Vec<ColumnMetadata>,
    }

    struct ColumnReference {
        data_type: DataType,
    }

    struct Expr {}

    impl Expr {}

    struct Column {
        name: String,
        expr: Rc<Expr>,
    }

    enum BoxType {
        Select,
        BaseTable,
    }

    struct QGBox {
        id: i32,
        box_type: BoxType,
        columns: Vec<Column>,
        quantifiers: BTreeSet<QuantifierRef>,
    }

    impl QGBox {
        fn new(id: i32, box_type: BoxType) -> Self {
            Self {
                id: id,
                box_type: box_type,
                columns: Vec::new(),
                quantifiers: BTreeSet::new(),
            }
        }
        fn add_quantifier(&mut self, q: QuantifierRef) {
            self.quantifiers.insert(q);
        }
        fn remove_quantifier(&mut self, q: &QuantifierRef) {
            self.quantifiers.remove(q);
        }
    }

    enum QuantifierType {
        Foreach,
        PreservedForeach,
        Existential,
        All,
    }

    struct Quantifier {
        id: i32,
        quantifier_type: QuantifierType,
        input_box: BoxRef,
        parent_box: Weak<RefCell<QGBox>>,
    }

    impl Quantifier {
        fn new(
            id: i32,
            quantifier_type: QuantifierType,
            input_box: BoxRef,
            parent_box: &BoxRef,
        ) -> Self {
            Self {
                id: id,
                quantifier_type: quantifier_type,
                input_box: input_box,
                parent_box: Rc::downgrade(parent_box),
            }
        }
    }

    struct Model {
        top_box: BoxRef,
    }

    impl Model {
        fn replace_top_box(&mut self, new_box: BoxRef) -> BoxRef {
            let other = Rc::clone(&self.top_box);
            self.top_box = new_box;
            other
        }
    }

    use crate::rewrite_engine;

    type BoxRef = Rc<RefCell<QGBox>>;
    type QuantifierRef = Rc<RefCell<Quantifier>>;

    struct EmptyRule {}

    impl rewrite_engine::Rule<BoxRef> for EmptyRule {
        fn name(&self) -> &'static str {
            "EmptyRule"
        }
        fn apply_to_down(&self) -> bool {
            false
        }
        fn condition(&mut self, _obj: &BoxRef) -> bool {
            true
        }
        fn action(&mut self, _obj: &mut BoxRef) -> Option<BoxRef> {
            None
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
        fn apply_to_down(&self) -> bool {
            false
        }
        fn condition(&mut self, obj: &BoxRef) -> bool {
            self.to_merge.clear();
            let borrowed_obj = obj.borrow();
            if let BoxType::Select = borrowed_obj.box_type {
                for q in &borrowed_obj.quantifiers {
                    let borrowed_q = q.borrow();
                    if let QuantifierType::Foreach = borrowed_q.quantifier_type {
                        if let BoxType::Select = borrowed_q.input_box.borrow().box_type {
                            self.to_merge.insert(Rc::clone(q));
                        }
                    }
                }
            }
            !self.to_merge.is_empty()
        }
        fn action(&mut self, obj: &mut BoxRef) -> Option<BoxRef> {
            let mut borrowed_obj = obj.borrow_mut();
            for q in &self.to_merge {
                for oq in &q.borrow().input_box.borrow().quantifiers {
                    borrowed_obj.add_quantifier(Rc::clone(oq));
                }
                borrowed_obj.remove_quantifier(q);
            }
            self.to_merge.clear();
            None
        }
    }

    type RuleT = dyn rewrite_engine::Rule<BoxRef>;
    type RuleBox = Box<RuleT>;

    fn apply_rules(m: &mut Model, rules: &mut Vec<RuleBox>) {
        for rule in rules.iter_mut() {
            let result = rewrite_engine::deep_apply_rule(&mut **rule, &mut m.top_box);
            if let Some(new_box) = result {
                m.replace_top_box(new_box);
            }
        }
    }

    impl rewrite_engine::Traverse<BoxRef> for BoxRef {
        fn descend_and_apply(rule: &mut dyn rewrite_engine::Rule<BoxRef>, target: &mut BoxRef) {
            for q in target.borrow_mut().quantifiers.iter() {
                let mut borrowed_q = q.borrow_mut();
                if let Some(c) = rewrite_engine::deep_apply_rule(rule, &mut borrowed_q.input_box) {
                    borrowed_q.input_box = c;
                }
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_empty_rule() {
            let top_box = Rc::new(RefCell::new(QGBox::new(0, BoxType::Select)));
            let mut m = Model { top_box };
            let rule = Box::new(EmptyRule {});
            let mut rules = Vec::<RuleBox>::new();
            rules.push(rule);
            apply_rules(&mut m, &mut rules);
        }

        #[test]
        fn test_merge_rule() {
            let top_box = Rc::new(RefCell::new(QGBox::new(0, BoxType::Select)));
            let nested_box = Rc::new(RefCell::new(QGBox::new(1, BoxType::Select)));
            let quantifier = Rc::new(RefCell::new(Quantifier::new(
                1,
                QuantifierType::Foreach,
                nested_box,
                &top_box,
            )));
            top_box.borrow_mut().add_quantifier(quantifier);
            let mut m = Model { top_box };
            let mut rule = MergeRule::new();
            assert_eq!(m.top_box.borrow().quantifiers.len(), 1);
            let result = rewrite_engine::deep_apply_rule(&mut rule, &mut m.top_box);
            if let Some(new_box) = result {
                m.replace_top_box(new_box);
            }
            assert_eq!(m.top_box.borrow().quantifiers.len(), 0);
        }

        #[test]
        fn test_merge_rule_deep_apply() {
            let top_box = Rc::new(RefCell::new(QGBox::new(0, BoxType::Select)));
            let nested_box1 = Rc::new(RefCell::new(QGBox::new(1, BoxType::Select)));
            let quantifier1 = Rc::new(RefCell::new(Quantifier::new(
                1,
                QuantifierType::Foreach,
                Rc::clone(&nested_box1),
                &top_box,
            )));
            let nested_box2 = Rc::new(RefCell::new(QGBox::new(1, BoxType::Select)));
            let quantifier2 = Rc::new(RefCell::new(Quantifier::new(
                1,
                QuantifierType::Foreach,
                nested_box2,
                &nested_box1,
            )));
            nested_box1.borrow_mut().add_quantifier(quantifier1);
            top_box.borrow_mut().add_quantifier(quantifier2);
            let mut m = Model { top_box };
            let mut rule = MergeRule::new();
            assert_eq!(m.top_box.borrow().quantifiers.len(), 1);
            let result = rewrite_engine::deep_apply_rule(&mut rule, &mut m.top_box);
            if let Some(new_box) = result {
                m.replace_top_box(new_box);
            }
            assert_eq!(m.top_box.borrow().quantifiers.len(), 0);
        }
    }
}

// rewrite engine
#[allow(dead_code)]
mod rewrite_engine {
    pub trait Rule<T> {
        fn name(&self) -> &'static str;
        fn apply_to_down(&self) -> bool;
        fn condition(&mut self, obj: &T) -> bool;
        fn action(&mut self, obj: &mut T) -> Option<T>;
        // @todo prune
    }

    pub trait Traverse<T> {
        fn descend_and_apply(rule: &mut dyn Rule<T>, target: &mut T);
    }

    fn apply_rule<T>(rule: &mut dyn Rule<T>, target: &mut T) -> Option<T> {
        if rule.condition(target) {
            rule.action(target)
        } else {
            None
        }
    }

    pub fn deep_apply_rule<T: Clone + Traverse<T>>(
        rule: &mut dyn Rule<T>,
        target: &mut T,
    ) -> Option<T> {
        if rule.apply_to_down() {
            T::descend_and_apply(rule, target);
        }
        let result = apply_rule(rule, target);
        match result {
            Some(mut c) => {
                if !rule.apply_to_down() {
                    T::descend_and_apply(rule, &mut c);
                }
                Some(c)
            }
            None => {
                if !rule.apply_to_down() {
                    T::descend_and_apply(rule, target);
                }
                None
            }
        }
    }
}

// optimizer

// plan generator

// execution engine

fn main() {
    let args: Vec<String> = env::args().collect();
    for arg in &args[1..] {
        println!("{:?}", arg);
        println!("{:?}", lexer::lex(&arg));
    }
}
