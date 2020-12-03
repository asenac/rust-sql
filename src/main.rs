use std::env;
use std::iter::*;


// lexer
#[allow(dead_code)]
mod lexer;

// syntax tree and parser

#[allow(dead_code)]
mod ast;

// query graph model

#[allow(dead_code)]
mod qg {
    use std::cell::RefCell;
    use std::cmp::*;
    use std::collections::*;
    use std::rc::*;

    #[derive(Clone)]
    pub enum DataType {
        String,
        Integer,
        BigInt,
        Double,
    }

    #[derive(Clone)]
    pub struct ColumnMetadata {
        pub name: String,
        pub data_type: DataType,
    }

    #[derive(Clone)]
    pub struct TableMetadata {
        pub name: String,
        pub columns: Vec<ColumnMetadata>,
    }

    impl TableMetadata {
        pub fn new(name: &str) -> Self {
            Self {
                name: name.to_string(),
                columns: Vec::new()
            }
        }

        pub fn add_column(&mut self, name: &str) {
            self.columns.push(ColumnMetadata{name: name.to_string(), data_type: DataType::String});
        }
    }

    pub trait MetadataCatalog {
        fn get_table(&self, name: &str) -> Option<&TableMetadata>;
    }

    struct ColumnReference {
        quantifier: QuantifierRef,
        position: usize,
        data_type: DataType,
    }

    struct BaseColumn {
        parent_box: Weak<RefCell<QGBox>>,
        position: usize,
    }

    enum ExprType {
        BaseColumn(BaseColumn),
        ColumnReference(ColumnReference),
    }

    struct Expr {
        expr_type: ExprType,
        operands: Option<Vec<Box<Expr>>>
    }

    impl Expr {
        fn make_base_column(parent_box: &BoxRef, position: usize) -> Self {
            let base_col = BaseColumn {
                parent_box: Rc::downgrade(&parent_box),
                position: position
            };
            Self {
                expr_type: ExprType::BaseColumn(base_col),
                operands: None
            }
        }

        fn make_column_ref(quantifier: QuantifierRef, position: usize) -> Self {
            let col_ref = ColumnReference {
                quantifier: quantifier,
                position: position,
                data_type: DataType::String
            };
            Self {
                expr_type: ExprType::ColumnReference(col_ref),
                operands: None
            }
        }

        fn is_equiv(&self, o: &Self) -> bool {
            match (&self.expr_type, &o.expr_type) {
                (ExprType::ColumnReference(l), ExprType::ColumnReference(r)) => {
                    l.position == r.position && l.quantifier == r.quantifier
                }
                _ => {
                    false
                }
            }
        }
    }

    struct Column {
        name: Option<String>,
        expr: Box<Expr>,
    }

    enum BoxType {
        Select,
        BaseTable(TableMetadata),
    }

    struct QGBox {
        id: i32,
        box_type: BoxType,
        columns: Vec<Column>,
        quantifiers: BTreeSet<QuantifierRef>,
        predicates: Option<Vec<Box<Expr>>>,
    }

    impl QGBox {
        fn new(id: i32, box_type: BoxType) -> Self {
            Self {
                id: id,
                box_type: box_type,
                columns: Vec::new(),
                quantifiers: BTreeSet::new(),
                predicates: None
            }
        }
        fn add_quantifier(&mut self, q: QuantifierRef) {
            self.quantifiers.insert(q);
        }
        fn remove_quantifier(&mut self, q: &QuantifierRef) {
            self.quantifiers.remove(q);
        }
        fn add_column(&mut self, name: Option<String>, expr: Box<Expr>) {
            self.columns.push(Column{name : name, expr: expr});
        }
        fn add_predicate(&mut self, predicate: Box<Expr>) {
            if self.predicates.is_some() {
                self.predicates.as_mut().unwrap().push(predicate);
            } else {
                self.predicates = Some(vec![predicate]);
            }
        }
    }

    enum QuantifierType {
        Foreach,
        PreservedForeach,
        Existential,
        All,
        Scalar,
    }

    struct Quantifier {
        id: i32,
        quantifier_type: QuantifierType,
        input_box: BoxRef,
        parent_box: Weak<RefCell<QGBox>>,
        alias: Option<String>
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
                alias: None
            }
        }

        fn set_alias(&mut self, alias: String) {
            self.alias = Some(alias);
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
    }

    /// Generates a query graph model from the AST
    pub struct ModelGenerator<'a>{
        catalog: &'a dyn MetadataCatalog,
        next_box_id: i32,
        next_quantifier_id: i32
    }

    struct NameResolutionContext<'a> {
        owner_box: BoxRef,
        quantifiers: Vec<QuantifierRef>,
        parent_context: Option<&'a NameResolutionContext<'a>>
    }

    impl<'a> NameResolutionContext<'a> {
        fn new(owner_box: BoxRef, parent_context: Option<&'a Self>) -> Self {
            Self {
                owner_box: owner_box,
                quantifiers: Vec::new(),
                parent_context: parent_context
            }
        }

        fn add_quantifier(&mut self, q: &QuantifierRef) {
            self.quantifiers.push(Rc::clone(q))
        }

        /// adds all the quantifier from the given context into the current one
        fn merge_context(&mut self, o: Self) {
            for q in o.quantifiers {
                self.quantifiers.push(q);
            }
        }

        fn resolve_column(&self, table: Option<&str>, column: &str) -> Option<Box<Expr>> {
            if table.is_some() {
                let tn = table.unwrap();
                for q in &self.quantifiers {
                    // @todo case insensitive comparisons
                    if q.borrow().alias.is_some() && q.borrow().alias.as_ref().unwrap() == tn {
                        return self.resolve_column_in_quantifier(q, column);
                    }
                }
            } else {
                for q in &self.quantifiers {
                    let r = self.resolve_column_in_quantifier(q, column);
                    if r.is_some() {
                        return r;
                    }
                }
            }
            None
        }

        fn resolve_column_in_quantifier(&self, q: &QuantifierRef, column: &str) -> Option<Box<Expr>> {
            for (i, c) in q.borrow().input_box.borrow().columns.iter().enumerate() {
                // @todo case insensitive comparisons
                if c.name.is_some() && column == c.name.as_ref().unwrap() {
                    let column_ref = Expr::make_column_ref(Rc::clone(&q), i);
                    // @todo pull up column ref
                    return Some(Box::new(column_ref));
                }
            }
            None
        }
    }

    impl<'a> ModelGenerator<'a> {
        pub fn new(catalog: &'a dyn MetadataCatalog) -> Self {
            Self {
                catalog: catalog,
                // @todo move this to the model
                next_box_id: 0,
                next_quantifier_id: 0
            }
        }

        pub fn process(&mut self, select: &crate::ast::Select) -> Result<Model, String> {
            let top_box = self.process_select(select, None)?;
            let model = Model{ top_box };
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

        fn process_select(&mut self, select: &crate::ast::Select, parent_context: Option<&NameResolutionContext>) -> Result<BoxRef, String> {
            let select_box = Rc::new(RefCell::new(QGBox::new(self.get_box_id(), BoxType::Select)));
            let mut current_context = NameResolutionContext::new(Rc::clone(&select_box), parent_context);
            for join_item in &select.from_clause {
                let b = self.process_join_item(&join_item.join_item, &mut current_context)?;
                let mut q = Quantifier::new(self.get_quantifier_id(), QuantifierType::Foreach, b, &select_box);
                if join_item.alias.is_some() {
                    q.set_alias(join_item.alias.as_ref().unwrap().clone());
                }
                let q = Rc::new(RefCell::new(q));
                current_context.add_quantifier(&q);
                select_box.borrow_mut().add_quantifier(q);
            }
            if let Some(selection_list) = &select.selection_list {
                for item in selection_list {
                    self.add_subqueries(&select_box, &item.expr, &mut current_context)?;
                    let expr = self.process_expr(&item.expr, &current_context)?;
                    select_box.borrow_mut().add_column(item.alias.clone(), expr);
                }
            }
            if let Some(where_clause) = &select.where_clause {
                self.add_subqueries(&select_box, &where_clause, &mut current_context)?;
                let expr = self.process_expr(&where_clause, &current_context)?;
                    select_box.borrow_mut().add_predicate(expr);
            }
            Ok(select_box)
        }

        fn process_join_item(&mut self, item : &crate::ast::JoinItem, current_context : &mut NameResolutionContext) -> Result<BoxRef, String> {
            use crate::ast::JoinItem::*;
            match item {
                // the derived table should not see its siblings
                DerivedTable(s) => self.process_select(s, current_context.parent_context),
                TableRef(s) => {
                    // @todo suport for schemas and catalogs
                    let metadata = self.catalog.get_table(s.get_name());
                    if !metadata.is_some() {
                        return Err(format!("table {} not found", s.get_name()));
                    }
                    let metadata = metadata.unwrap();
                    // @todo avoid cloning the metadata. The catalog should return a ref counted instance
                    let base_table = BoxType::BaseTable(metadata.clone());
                    let table_box = Rc::new(RefCell::new(QGBox::new(self.get_box_id(), base_table)));
                    // add the columns of the table
                    for (i, c) in metadata.columns.iter().enumerate() {
                        table_box.borrow_mut().add_column(Some(c.name.clone()), Box::new(Expr::make_base_column(&table_box, i)));
                    }
                    Ok(table_box)
                }
                Join(_, l, r, on) => {
                    // @todo outer joins
                    let select_box = Rc::new(RefCell::new(QGBox::new(self.get_box_id(), BoxType::Select)));
                    let mut child_context = NameResolutionContext::new(Rc::clone(&select_box), current_context.parent_context);

                    // left term
                    let l_box = self.process_join_item(&l.join_item, &mut child_context)?;
                    let mut l_q = Quantifier::new(self.get_quantifier_id(), QuantifierType::Foreach, l_box, &select_box);
                    if l.alias.is_some() {
                        l_q.set_alias(l.alias.as_ref().unwrap().clone());
                    }
                    let l_q = Rc::new(RefCell::new(l_q));
                    child_context.add_quantifier(&l_q);
                    select_box.borrow_mut().add_quantifier(l_q);

                    // right term
                    let r_box = self.process_join_item(&r.join_item, &mut child_context)?;
                    let mut r_q = Quantifier::new(self.get_quantifier_id(), QuantifierType::Foreach, r_box, &select_box);
                    if r.alias.is_some() {
                        r_q.set_alias(r.alias.as_ref().unwrap().clone());
                    }
                    let r_q = Rc::new(RefCell::new(r_q));
                    child_context.add_quantifier(&r_q);
                    select_box.borrow_mut().add_quantifier(r_q);

                    if let Some(expr) = &on {
                        // subqueries in the ON clause should not see the siblings in the current context
                        self.add_subqueries(&select_box, expr, &mut child_context)?;
                    }

                    // merge the temporary context into the current one
                    current_context.merge_context(child_context);
                    Ok(select_box)
                }
                _ => Err(String::from("not implemented")),
            }
        }

        /// the suqbueries in the given expressions as quantifiers in the given select box
        fn add_subqueries(&mut self, select_box: &BoxRef, expr: &crate::ast::Expr, current_context : &mut NameResolutionContext) -> Result<(), String>{
            use crate::ast::Expr::*;
            for expr in expr.iter() {
                match expr {
                    ScalarSubquery(e) => {
                        let subquery_box = self.process_select(e, Some(current_context))?;
                        let q = Quantifier::new(self.get_quantifier_id(), QuantifierType::Scalar, subquery_box, &select_box);
                        select_box.borrow_mut().add_quantifier(Rc::new(RefCell::new(q)));
                    }
                    InSelect(_, e) | Exists(e) => {
                        let subquery_box = self.process_select(e, Some(current_context))?;
                        let q = Quantifier::new(self.get_quantifier_id(), QuantifierType::Existential, subquery_box, &select_box);
                        select_box.borrow_mut().add_quantifier(Rc::new(RefCell::new(q)));
                    }
                    _ => {}
                }
            }
            Ok(())
        }

        fn process_expr(&mut self, expr: &crate::ast::Expr, current_context : &NameResolutionContext) -> Result<Box<Expr>, String> {
            use crate::ast;
            match expr {
                ast::Expr::Reference(id) => {
                    let expr = current_context.resolve_column(id.get_qualifier_before_name(), &id.get_name());
                    if expr.is_some() {
                        return Ok(expr.unwrap());
                    }
                    Err(format!("column {} not found", id.get_name()))
                }
                _ => {
                    Err(String::from("expression not supported!"))
                }
            }
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

// interpreter

use std::collections::*;

struct FakeCatalog {
    tables : HashMap<String, qg::TableMetadata>
}

impl FakeCatalog {
    fn new() -> Self {
        Self {
            tables: HashMap::new()
        }
    }

    fn add_table(&mut self, table: qg::TableMetadata) {
        self.tables.insert(table.name.clone(), table);
    }
}

impl qg::MetadataCatalog for FakeCatalog
{
    fn get_table(&self, name: &str) -> Option<&qg::TableMetadata> {
        self.tables.get(name)
    }
}

/// simple interpreter to manually test the rewrite engine
struct Interpreter {
    catalog: FakeCatalog
}

impl Interpreter {
    pub fn new() -> Self {
        Self { catalog: FakeCatalog::new() }
    }

    pub fn process_line(&mut self, line: &str) -> Result<(), String> {
        let parser = ast::Parser::new();
        let result = parser.parse(line)?;
        for stmt in result {
            self.process_statement(&stmt)?;
        }
        Ok(())
    }

    fn process_statement(&mut self, stmt: &ast::Statement) -> Result<(), String> {
        use ast::Statement::*;
        match stmt {
            Select(e) => {
                let mut generator = qg::ModelGenerator::new(&self.catalog);
                generator.process(e)?;
            }
            CreateTable(c) => {
                let mut metadata = qg::TableMetadata::new(c.name.get_name());
                for c in &c.columns {
                    metadata.add_column(&c.name);
                }
                self.catalog.add_table(metadata);
            }
            _ => {
                return Err(format!("unsupported statement: {:?}", stmt));
            }
        }
        Ok(())
    }
}

use rustyline::error::ReadlineError;
use rustyline::Editor;

fn main() {
    let mut interpreter = Interpreter::new();
    let mut rl = Editor::<()>::new();
    if rl.load_history("history.txt").is_err() {
        println!("No previous history.");
    }
    loop {
        let readline = rl.readline("SQL> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                println!("Line: {}", line);
                let result = interpreter.process_line(&line);
                if result.is_err() {
                    println!("Error: {}", result.err().unwrap());
                }
            },
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break
            },
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break
            },
            Err(err) => {
                println!("Error: {:?}", err);
                break
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}
