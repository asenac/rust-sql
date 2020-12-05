// lexer
#[allow(dead_code)]
mod lexer;

// syntax tree and parser

#[allow(dead_code)]
mod ast;

// query graph model

#[allow(dead_code)]
mod qg {
    use std::fmt;
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

    #[derive(Clone)]
    struct ColumnReference {
        quantifier: QuantifierRef,
        position: usize,
        data_type: DataType,
    }

    #[derive(Clone)]
    struct BaseColumn {
        parent_box: Weak<RefCell<QGBox>>,
        position: usize,
    }

    #[derive(Clone)]
    enum ExprType {
        BaseColumn(BaseColumn),
        ColumnReference(ColumnReference),
        Parameter(u64),
        InList,
    }

    type ExprRef = Rc<RefCell<Expr>>;

    #[derive(Clone)]
    struct Expr {
        expr_type: ExprType,
        operands: Option<Vec<ExprRef>>
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

        fn make_parameter(index: u64) -> Self {
            Self {
                expr_type: ExprType::Parameter(index),
                operands: None
            }
        }

        fn make_in_list(term: ExprRef, list: Vec<ExprRef>) -> Self {
            let mut operands = vec![term];
            operands.extend(list);
            Self {
                expr_type: ExprType::InList,
                operands: Some(operands)
            }
        }

        fn is_equiv(&self, o: &Self) -> bool {
            match (&self.expr_type, &o.expr_type) {
                (ExprType::ColumnReference(l), ExprType::ColumnReference(r)) => {
                    l.position == r.position && l.quantifier == r.quantifier
                }
                (ExprType::Parameter(l), ExprType::Parameter(r)) => {
                    l == r
                }
                _ => {
                    false
                }
            }
        }

        fn dereference(&self) -> Option<ExprRef> {
            match &self.expr_type {
                ExprType::ColumnReference(c) => {
                    let q = c.quantifier.borrow();
                    let b = q.input_box.borrow();
                    Some(Rc::clone(&b.columns[c.position].expr))
                }
                _ => None
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
            }
        }
    }

    struct Column {
        name: Option<String>,
        expr: ExprRef,
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
        predicates: Option<Vec<ExprRef>>,
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
        /// use add_quantifier_to_box instead to properly set the parent box of the quantifier
        fn add_quantifier(&mut self, q: QuantifierRef) {
            self.quantifiers.insert(q);
        }
        fn remove_quantifier(&mut self, q: &QuantifierRef) {
            self.quantifiers.remove(q);
        }
        fn add_column(&mut self, name: Option<String>, expr: ExprRef) {
            self.columns.push(Column{name : name, expr: expr});
        }
        fn add_column_if_not_exists(&mut self, expr: Expr) -> usize {
            for (i, c) in self.columns.iter().enumerate() {
                if c.expr.borrow().is_equiv(&expr) {
                    return i;
                }
            }
            let pos = self.columns.len();
            self.columns.push(Column{name: None, expr: make_ref(expr)});
            pos
        }
        fn add_predicate(&mut self, predicate: ExprRef) {
            if self.predicates.is_some() {
                self.predicates.as_mut().unwrap().push(predicate);
            } else {
                self.predicates = Some(vec![predicate]);
            }
        }

        fn get_box_type_str(&self) -> &'static str {
            match self.box_type {
                BoxType::Select => "Select",
                BoxType::BaseTable(_) => "BaseTable",
            }
        }
    }

    fn add_quantifier_to_box(b: &BoxRef, q: &QuantifierRef) {
        let mut bb = b.borrow_mut();
        bb.add_quantifier(Rc::clone(q));
        let mut bq = q.borrow_mut();
        bq.parent_box = Rc::downgrade(&b);
    }

    enum QuantifierType {
        Foreach,
        PreservedForeach,
        Existential,
        All,
        Scalar,
    }

    impl fmt::Display for QuantifierType {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match &self {
                QuantifierType::Foreach => write!(f, "F"),
                QuantifierType::PreservedForeach => write!(f, "P"),
                QuantifierType::Existential => write!(f, "E"),
                QuantifierType::All => write!(f, "A"),
                QuantifierType::Scalar => write!(f, "S"),
            }
        }
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

        fn get_effective_name(&self) -> Option<String> {
            if self.alias.is_some() {
                return self.alias.clone();
            }
            let b = self.input_box.borrow();
            if let BoxType::BaseTable(t) = &b.box_type {
                return Some(t.name.clone());
            }
            return None
        }

        fn is_subquery(&self) -> bool {
            match &self.quantifier_type {
                QuantifierType::Existential | QuantifierType::Scalar => true,
                _ => false
            }
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

    fn make_ref<T>(t: T) -> Rc<RefCell<T>> {
        Rc::new(RefCell::new(t))
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
        parent_quantifiers: HashMap<i32, QuantifierRef>,
        subquery_quantifiers: Option<HashMap<*const crate::ast::Select, QuantifierRef>>,
        parent_context: Option<&'a NameResolutionContext<'a>>
    }

    impl<'a> NameResolutionContext<'a> {
        fn new(owner_box: BoxRef, parent_context: Option<&'a Self>) -> Self {
            Self {
                owner_box: owner_box,
                quantifiers: Vec::new(),
                parent_quantifiers: HashMap::new(),
                subquery_quantifiers: None,
                parent_context: parent_context
            }
        }

        fn add_quantifier(&mut self, q: &QuantifierRef) {
            self.parent_quantifiers.insert(q.borrow().input_box.borrow().id, Rc::clone(q));
            self.quantifiers.push(Rc::clone(q))
        }

        fn add_subquery_quantifier(&mut self, s: *const crate::ast::Select, q: &QuantifierRef) {
            if self.subquery_quantifiers.is_none() {
                self.subquery_quantifiers = Some(HashMap::new());
            }
            self.subquery_quantifiers.as_mut().unwrap().insert(s, Rc::clone(q));
        }

        fn get_subquery_quantifier(&self, s: *const crate::ast::Select) -> QuantifierRef {
            Rc::clone(self.subquery_quantifiers.as_ref().unwrap().get(&s).expect("bug"))
        }

        /// adds all the quantifier from the given context into the current one
        fn merge_quantifiers(&mut self, o: Self) {
            for q in o.quantifiers {
                self.quantifiers.push(q);
            }
            self.parent_quantifiers.extend(o.parent_quantifiers);
        }

        fn resolve_column(&self, table: Option<&str>, column: &str) -> Option<ExprRef> {
            if table.is_some() {
                let tn = table.unwrap();
                for q in &self.quantifiers {
                    // @todo case insensitive comparisons
                    let q_name = q.borrow().get_effective_name();
                    if q_name.is_some() && q_name.as_ref().unwrap() == tn {
                        return self.resolve_column_in_quantifier(q, column);
                    }
                }
            } else {
                for q in &self.quantifiers {
                    // @todo check for column name ambiguity
                    let r = self.resolve_column_in_quantifier(q, column);
                    if r.is_some() {
                        return r;
                    }
                }
            }
            None
        }

        fn resolve_column_in_quantifier(&self, q: &QuantifierRef, column: &str) -> Option<ExprRef> {
            for (i, c) in q.borrow().input_box.borrow().columns.iter().enumerate() {
                // @todo case insensitive comparisons
                if c.name.is_some() && column == c.name.as_ref().unwrap() {
                    let column_ref = Expr::make_column_ref(Rc::clone(&q), i);
                    let column_ref = self.pullup_column_ref(column_ref);
                    return Some(make_ref(column_ref));
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
                        let parent_q = self.parent_quantifiers.get(&parent_box_id).expect("must be a valid id");
                        c.position = parent_q.borrow().input_box.borrow_mut().add_column_if_not_exists(Expr::make_column_ref(Rc::clone(&c.quantifier), c.position));
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
            let select_box = make_ref(QGBox::new(self.get_box_id(), BoxType::Select));
            let mut current_context = NameResolutionContext::new(Rc::clone(&select_box), parent_context);
            for join_item in &select.from_clause {
                self.add_join_term_to_select_box(join_item, &select_box, &mut current_context)?
            }
            if let Some(selection_list) = &select.selection_list {
                for item in selection_list {
                    self.add_subqueries(&select_box, &item.expr, &mut current_context)?;
                    let expr = self.process_expr(&item.expr, &current_context)?;
                    select_box.borrow_mut().add_column(item.alias.clone(), expr);
                }
            } else {
                // add all columns from all quantifiers
                self.add_all_columns(&select_box);
            }
            if let Some(where_clause) = &select.where_clause {
                self.add_subqueries(&select_box, &where_clause, &mut current_context)?;
                let expr = self.process_expr(&where_clause, &current_context)?;
                select_box.borrow_mut().add_predicate(expr);
            }
            Ok(select_box)
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
                    select_box.borrow_mut().add_column(c.name.clone(), make_ref(expr));
                }
            }
        }

        /// adds a quantifier in the given select box with the result of parsing the given join term subtree
        fn add_join_term_to_select_box(&mut self, join_term: &crate::ast::JoinTerm, select_box: &BoxRef, current_context : &mut NameResolutionContext) -> Result<(), String> {
            let b = self.process_join_item(&join_term.join_item, current_context)?;
            let mut q = Quantifier::new(self.get_quantifier_id(), QuantifierType::Foreach, b, &select_box);
            if join_term.alias.is_some() {
                q.set_alias(join_term.alias.as_ref().unwrap().clone());
            }
            let q = make_ref(q);
            current_context.add_quantifier(&q);
            select_box.borrow_mut().add_quantifier(q);
            Ok(())
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
                    let table_box = make_ref(QGBox::new(self.get_box_id(), base_table));
                    // add the columns of the table
                    for (i, c) in metadata.columns.iter().enumerate() {
                        table_box.borrow_mut().add_column(Some(c.name.clone()), make_ref(Expr::make_base_column(&table_box, i)));
                    }
                    Ok(table_box)
                }
                Join(_, l, r, on) => {
                    // @todo outer joins
                    let select_box = make_ref(QGBox::new(self.get_box_id(), BoxType::Select));
                    let mut child_context = NameResolutionContext::new(Rc::clone(&select_box), current_context.parent_context);

                    self.add_join_term_to_select_box(l, &select_box, &mut child_context)?;
                    self.add_join_term_to_select_box(r, &select_box, &mut child_context)?;

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
                }
                // _ => Err(String::from("not implemented")),
            }
        }

        /// the suqbueries in the given expressions as quantifiers in the given select box
        fn add_subqueries(&mut self, select_box: &BoxRef, expr: &crate::ast::Expr, current_context : &mut NameResolutionContext) -> Result<(), String>{
            use crate::ast::Expr::*;
            for expr in expr.iter() {
                match expr {
                    ScalarSubquery(e) => {
                        let subquery_box = self.process_select(e, Some(current_context))?;
                        if subquery_box.borrow().columns.len() != 1 {
                            return Err(format!("scalar subqueries must project a single column"))
                        }
                        let q = Quantifier::new(self.get_quantifier_id(), QuantifierType::Scalar, subquery_box, &select_box);
                        let q = make_ref(q);
                        current_context.add_subquery_quantifier(e.as_ref() as *const crate::ast::Select, &q);
                        select_box.borrow_mut().add_quantifier(q);
                    }
                    InSelect(_, e) | Exists(e) => {
                        let subquery_box = self.process_select(e, Some(current_context))?;
                        let q = Quantifier::new(self.get_quantifier_id(), QuantifierType::Existential, subquery_box, &select_box);
                        let q = make_ref(q);
                        current_context.add_subquery_quantifier(e.as_ref() as *const crate::ast::Select, &q);
                        select_box.borrow_mut().add_quantifier(q);
                    }
                    _ => {}
                }
            }
            Ok(())
        }

        fn process_expr(&mut self, expr: &crate::ast::Expr, current_context : &NameResolutionContext) -> Result<ExprRef, String> {
            use crate::ast;
            match expr {
                ast::Expr::Reference(id) => {
                    let expr = current_context.resolve_column(id.get_qualifier_before_name(), &id.get_name());
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
                ast::Expr::ScalarSubquery(e) => {
                    Ok(make_ref(Expr::make_column_ref(current_context.get_subquery_quantifier(e.as_ref() as *const crate::ast::Select), 0)))
                }
                _ => {
                    Err(String::from("expression not supported!"))
                }
            }
        }
    }

    pub struct DotGenerator{
        output : String,
        indent: u32
    }

    impl DotGenerator {
        pub fn new() -> Self {
            Self{ output: String::new(), indent: 0 }
        }

        pub fn generate(mut self, m: &Model, sql_string: &str) -> Result<String, String> {
            self.new_line("digraph G {");
            self.inc();
            self.new_line("compound = true");
            self.new_line("lablejust = l");
            self.new_line(&format!("lable=\"{}\"", sql_string));
            self.new_line("node [ shape = box ]");

            let mut box_stack = vec![Rc::clone(&m.top_box)];
            let mut quantifiers = Vec::new();
            while let Some(b) = box_stack.pop() {
                let b = b.borrow();
                self.new_line(&format!("subgraph cluster{} {{", b.id));
                self.inc();
                self.new_line(&format!("label = \"Box{}:{}\"", b.id, b.get_box_type_str()));
                self.new_line(&format!("boxhead{} [ shape = record, label=\"{}\" ]", b.id, DotGenerator::get_box_head(&b)));

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
                    self.new_line(&format!("Q{0} [ label=\"Q{0}({1})\" ]", q.id, q.quantifier_type));
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
                    self.new_line(&format!("Q{0} -> boxhead{1} [ lhead = cluster{1} ]", q.id, q.input_box.borrow().id));
                }
            }

            self.dec();
            self.new_line("}");
            Ok(self.output)
        }

        fn get_box_head(b: &QGBox) -> String {
            let mut r  = String::new();
            for (i, c) in b.columns.iter().enumerate() {
                if r.len() > 0 {
                    r.push('|');
                }
                r.push_str(&format!("{}: {}", i, c.expr.borrow()));
                if let Some(c) = &c.name {
                    r.push_str(&format!(" AS {}", c));
                }
            }
            r
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
                for _ in 0..self.indent*4 {
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
        fn apply_top_down(&self) -> bool {
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
            for q in &self.to_merge {
                for oq in &q.borrow().input_box.borrow().quantifiers {
                    add_quantifier_to_box(obj, oq);
                }
                obj.borrow_mut().remove_quantifier(q);
            }
            self.to_merge.clear();
            None
        }
    }

    type RuleT = dyn rewrite_engine::Rule<BoxRef>;
    type RuleBox = Box<RuleT>;

    fn apply_rule(m: &mut Model, rule: &mut RuleBox) {
        let result = rewrite_engine::deep_apply_rule(&mut **rule, &mut m.top_box);
        if let Some(new_box) = result {
            m.replace_top_box(new_box);
        }
    }

    fn apply_rules(m: &mut Model, rules: &mut Vec<RuleBox>) {
        for rule in rules.iter_mut() {
            apply_rule(m, rule);
        }
    }

    pub fn rewrite_model(m: &mut Model) {
        let mut rule: RuleBox = Box::new(MergeRule::new());
        apply_rule(m, &mut rule);
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
            let top_box = make_ref(QGBox::new(0, BoxType::Select));
            let mut m = Model { top_box };
            let rule = Box::new(EmptyRule {});
            let mut rules = Vec::<RuleBox>::new();
            rules.push(rule);
            apply_rules(&mut m, &mut rules);
        }

        #[test]
        fn test_merge_rule() {
            let top_box = make_ref(QGBox::new(0, BoxType::Select));
            let nested_box = make_ref(QGBox::new(1, BoxType::Select));
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
            let result = rewrite_engine::deep_apply_rule(&mut rule, &mut m.top_box);
            if let Some(new_box) = result {
                m.replace_top_box(new_box);
            }
            assert_eq!(m.top_box.borrow().quantifiers.len(), 0);
        }

        #[test]
        fn test_merge_rule_deep_apply() {
            let top_box = make_ref(QGBox::new(0, BoxType::Select));
            let nested_box1 = make_ref(QGBox::new(1, BoxType::Select));
            let quantifier1 = make_ref(Quantifier::new(
                1,
                QuantifierType::Foreach,
                Rc::clone(&nested_box1),
                &top_box,
            ));
            let nested_box2 = make_ref(QGBox::new(1, BoxType::Select));
            let quantifier2 = make_ref(Quantifier::new(
                1,
                QuantifierType::Foreach,
                nested_box2,
                &nested_box1,
            ));
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
        fn apply_top_down(&self) -> bool;
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
        if !rule.apply_top_down() {
            T::descend_and_apply(rule, target);
        }
        let result = apply_rule(rule, target);
        match result {
            Some(mut c) => {
                if rule.apply_top_down() {
                    T::descend_and_apply(rule, &mut c);
                }
                Some(c)
            }
            None => {
                if rule.apply_top_down() {
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
            println!("{:?}", stmt);
            self.process_statement(&stmt)?;
        }
        Ok(())
    }

    fn process_statement(&mut self, stmt: &ast::Statement) -> Result<(), String> {
        use ast::Statement::*;
        match stmt {
            Select(e) => {
                let mut generator = qg::ModelGenerator::new(&self.catalog);
                let mut model = generator.process(e)?;
                let output = qg::DotGenerator::new().generate(&model, "@todo")?;
                println!("{}", output);

                qg::rewrite_model(&mut model);

                let output = qg::DotGenerator::new().generate(&model, "@todo")?;
                println!("{}", output);
            }
            CreateTable(c) => {
                let mut metadata = qg::TableMetadata::new(c.name.get_name());
                for c in &c.columns {
                    metadata.add_column(&c.name);
                }
                self.catalog.add_table(metadata);
            }
            // _ => return Err(format!("unsupported statement: {:?}", stmt)),
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
