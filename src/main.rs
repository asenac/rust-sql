use std::env;
use std::iter::*;

// lexer

#[derive(Debug, Clone, PartialEq)]
pub enum Lexeme {
    Symbol(char),
    Number(u64),
    Keyword(String),
    Comment(String),
    Comma,
    Semicolon,
}

fn consume_number<T: Iterator<Item = char>>(iter: &mut Peekable<T>) -> u64 {
    let mut number: u64 = 0;
    while let Some(Ok(digit)) = iter.peek().map(|c| c.to_string().parse::<u64>()) {
        number = number * 10 + digit;
        iter.next();
    }
    number
}

fn consume_keyword<T: Iterator<Item = char>>(iter: &mut Peekable<T>) -> Result<String, String> {
    let mut keyword = String::new();

    while let Some(&c) = iter.peek() {
        match c {
            '0'..='9' | 'a'..='z' | 'A'..='Z' => {
                iter.next();
                for uc in c.to_uppercase() {
                    keyword.push(uc);
                }
            }
            _ => {
                break;
            }
        }
    }
    Ok(keyword)
}

fn lex(input: &str) -> Result<Vec<Lexeme>, String> {
    use Lexeme::*;

    let mut result = Vec::new();
    let mut it = input.chars().peekable();
    while let Some(&c) = it.peek() {
        match c {
            '0'..='9' => {
                let number = consume_number(&mut it);
                result.push(Number(number));
            }
            'a'..='z' | 'A'..='Z' => {
                let keyword = consume_keyword(&mut it)?;
                result.push(Keyword(keyword));
            }
            '*' | '+' | '-' | '/' => {
                it.next();
                result.push(Symbol(c));
            }
            ' ' | '\n' => {
                it.next();
            }
            ',' => {
                it.next();
                result.push(Comma);
            }
            ';' => {
                it.next();
                result.push(Semicolon);
            }
            _ => {
                return Err(format!("unexpected character {}", c));
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_consume_number() {
        let str_num = "123213 12-45";
        let mut it = str_num.chars().peekable();
        assert_eq!(consume_number(&mut it), 123213);
        assert_eq!(it.peek(), Some(&' '));
        it.next();
        assert_eq!(consume_number(&mut it), 12);
        assert_eq!(it.peek(), Some(&'-'));
        it.next();
        assert_eq!(consume_number(&mut it), 45);
        assert_eq!(it.peek(), None);
    }

    #[test]
    fn test_consume_keyword() {
        let str_input = "asenac12-45";
        let mut it = str_input.chars().peekable();
        assert_eq!(consume_keyword(&mut it), Ok(String::from("ASENAC12")));
        assert_eq!(it.peek(), Some(&'-'));
        it.next();
        assert_eq!(consume_keyword(&mut it), Ok(String::from("45")));
        assert_eq!(it.peek(), None);
    }

    #[test]
    fn test_lex() {
        use Lexeme::*;

        let str_num = String::from("123213 * 12-45 + ASENAC");
        let result = lex(&str_num);
        assert!(result.is_ok());
        let vec = result.unwrap();
        assert_eq!(vec.len(), 7);
        assert_eq!(vec[0], Number(123213));
        assert_eq!(vec[1], Symbol('*'));
        assert_eq!(vec[2], Number(12));
        assert_eq!(vec[3], Symbol('-'));
        assert_eq!(vec[4], Number(45));
        assert_eq!(vec[5], Symbol('+'));
        assert_eq!(vec[6], Keyword(String::from("ASENAC")));

        let bad_result = lex(&String::from("["));
        assert!(!bad_result.is_ok());
    }
}

// syntax tree

#[allow(dead_code)]
mod syn {
    use super::*;

    enum Statement {
        Select(Select),
        CreateTable(CreateTable),
    }

    struct Identifier {
        parts: Vec<String>,
    }

    struct Select {}

    enum TypeDef {
        String,
        Integer,
        BigInt,
        Double,
    }

    struct ColumnDef {
        name: String,
        data_type: TypeDef,
    }

    struct CreateTable {
        name: Identifier,
        columns: Vec<ColumnDef>,
    }

    struct Parser {}

    impl Parser {
        fn new() -> Parser {
            Parser {}
        }

        // parser
        fn parse(&self, input: &str) -> Result<Vec<Statement>, String> {
            match lex(input) {
                Err(c) => Err(c),
                Ok(tokens) => self.parse_statements(&tokens),
            }
        }

        fn parse_keyword(input: &Lexeme, keyword: &str) -> bool {
            if let Lexeme::Keyword(s) = input {
                return keyword == &s[..];
            }
            false
        }

        fn parse_symbol(input: &Lexeme, symbol: char) -> bool {
            if let Lexeme::Symbol(s) = input {
                return symbol == *s;
            }
            false
        }

        fn parse_select_body<'a, T: Iterator<Item = &'a Lexeme>>(
            &self,
            _iter: &mut Peekable<T>,
        ) -> Result<Select, String> {
            Ok(Select {})
        }

        fn parse_statements(&self, input: &Vec<Lexeme>) -> Result<Vec<Statement>, String> {
            let mut result: Vec<Statement> = Vec::new();
            let mut it = input.iter().peekable();
            while let Some(&c) = it.peek() {
                if Parser::parse_keyword(&c, &"SELECT") {
                    it.next();
                    result.push(Statement::Select(self.parse_select_body(&mut it)?));
                    continue;
                }
                if let Lexeme::Semicolon = c {
                    it.next();
                    continue;
                }
                return Err(format!("unexpected token {:?}", c));
            }
            Ok(result)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_parser() {
            let parser = Parser::new();
            let result = parser.parse("SELECT; SELECT; SELECT");
            assert!(result.is_ok());
        }
    }
}

// query graph model

#[allow(dead_code)]
mod qg {
    use std::cell::RefCell;
    use std::rc::*;
    use std::collections::*;
    use std::cmp::*;

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
                id: id, box_type: box_type, columns: Vec::new(), quantifiers: BTreeSet::new()
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
        fn new(id: i32, quantifier_type: QuantifierType, input_box: BoxRef, parent_box: &BoxRef) -> Self {
            Self {
                id: id, quantifier_type: quantifier_type, input_box : input_box, parent_box : Rc::downgrade(parent_box)
            }
        }
    }

    struct Model {
        top_box: BoxRef
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
        to_merge : BTreeSet<QuantifierRef>
    }

    impl MergeRule {
        fn new() -> Self {
            Self {
                to_merge : BTreeSet::new()
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
            let quantifier = Rc::new(RefCell::new(Quantifier::new(1, QuantifierType::Foreach, nested_box, &top_box)));
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
            let nested_box = Rc::new(RefCell::new(QGBox::new(1, BoxType::Select)));
            let quantifier = Rc::new(RefCell::new(Quantifier::new(1, QuantifierType::Foreach, nested_box, &top_box)));
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

    pub fn deep_apply_rule<T: Clone>(rule: &mut dyn Rule<T>, target: &mut T) -> Option<T> {
        if rule.apply_to_down() {
        }
        let result = apply_rule(rule, target);

        if !rule.apply_to_down() {
        }

        result
    }
}

// optimizer

// plan generator

// execution engine

fn main() {
    let args: Vec<String> = env::args().collect();
    for arg in &args[1..] {
        println!("{:?}", arg);
        println!("{:?}", lex(&arg));
    }
}
