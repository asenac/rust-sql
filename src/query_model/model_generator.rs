use crate::ast;
use crate::metadata::*;
use crate::query_model::{
    make_ref, BoxRef, BoxType, CmpOpType, Column, DistinctOperation, Expr, ExprRef, ExprType,
    Grouping, JoinType, KeyItem, LogicalExprType, Model, ModelRef, QGBox, Quantifier,
    QuantifierRef, QuantifierType, Select, Value,
};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Generates a query graph model from the AST
pub struct ModelGenerator<'a> {
    catalog: &'a dyn MetadataCatalog,
    model: ModelRef,
}

struct NameResolutionContext<'a> {
    owner_box: Option<BoxRef>,
    quantifiers: Vec<QuantifierRef>,
    subquery_quantifiers: Option<HashMap<*const ast::QueryBlock, QuantifierRef>>,
    ctes: Option<HashMap<String, BoxRef>>,
    parent_context: Option<&'a NameResolutionContext<'a>>,
}

impl<'a> NameResolutionContext<'a> {
    fn new(owner_box: BoxRef, parent_context: Option<&'a Self>) -> Self {
        Self {
            owner_box: Some(owner_box),
            quantifiers: Vec::new(),
            subquery_quantifiers: None,
            ctes: None,
            parent_context,
        }
    }

    fn for_ctes(parent_context: Option<&'a Self>) -> Self {
        Self {
            owner_box: None,
            quantifiers: Vec::new(),
            subquery_quantifiers: None,
            ctes: Some(HashMap::new()),
            parent_context,
        }
    }

    fn add_quantifier(&mut self, q: &QuantifierRef) {
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
                        return Err(format!("column {} is ambigous", column));
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
                    if parent_box_id
                        == self
                            .owner_box
                            .as_ref()
                            .expect("cannot pull up column")
                            .borrow()
                            .id
                    {
                        break;
                    }
                    let parent_q = {
                        let parent_box = parent_box.borrow();
                        assert!(parent_box.ranging_quantifiers.len() == 1);
                        parent_box.ranging_quantifiers[0]
                            .upgrade()
                            .expect("invalid ranging quantifier")
                    };
                    c.position = parent_q
                        .borrow()
                        .input_box
                        .borrow_mut()
                        .add_column_if_not_exists(Expr::make_column_ref(
                            Rc::clone(&c.quantifier),
                            c.position,
                        ));
                    c.quantifier = parent_q;
                }
                column_ref
            }
            _ => {
                panic!();
            }
        }
    }

    fn resolve_cte(&self, name: &str) -> Option<BoxRef> {
        if let Some(ctes) = &self.ctes {
            if let Some(cte) = ctes.get(name) {
                return Some(cte.clone());
            }
        }
        if let Some(parent) = self.parent_context {
            return parent.resolve_cte(name);
        }
        None
    }

    fn add_cte(&mut self, name: String, b: BoxRef) {
        self.ctes
            .as_mut()
            .expect("invalid CTE context")
            .insert(name, b);
    }
}

impl<'a> ModelGenerator<'a> {
    pub fn new(catalog: &'a dyn MetadataCatalog) -> Self {
        Self {
            catalog,
            model: Model::new(),
        }
    }

    pub fn process(mut self, quer_block: &ast::QueryBlock) -> Result<ModelRef, String> {
        let top_box = self.process_query_block(quer_block, None)?;
        self.model.borrow_mut().replace_top_box(top_box);
        Ok(self.model)
    }

    fn make_box(&mut self, box_type: BoxType) -> BoxRef {
        let model_ref = Rc::downgrade(&self.model);
        QGBox::new(
            model_ref,
            self.model.borrow_mut().ids.get_box_id(),
            box_type,
        )
    }

    fn make_select_box(&mut self) -> BoxRef {
        self.make_box(BoxType::Select(Select::new()))
    }

    fn make_outer_join_box(&mut self) -> BoxRef {
        self.make_box(BoxType::OuterJoin)
    }

    fn make_union_box(&mut self, distinct: bool, mut branches: Vec<BoxRef>) -> BoxRef {
        let union_box = self.make_box(BoxType::Union);
        {
            let mut union_mut = union_box.borrow_mut();
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
        Quantifier::new(
            self.model.borrow_mut().ids.get_quantifier_id(),
            QuantifierType::Foreach,
            input_box,
            &parent_box,
        )
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
        let mut current_context = NameResolutionContext::for_ctes(parent_context);
        if let Some(ctes) = &query_block.ctes {
            for cte in ctes.iter() {
                let mut select_box =
                    self.process_query_block(&cte.select, Some(&current_context))?;
                if let Some(columns) = &cte.columns {
                    if columns.len() != select_box.borrow().columns.len() {
                        return Err(format!("number of columns mismatch"));
                    }
                    let other_box = self.make_select_box();
                    let q = self.make_quantifier(select_box, &other_box);
                    other_box.borrow_mut().add_quantifier(Rc::clone(&q));
                    current_context.add_quantifier(&q);
                    for (i, c) in columns.iter().enumerate() {
                        let expr = Expr::make_column_ref(Rc::clone(&q), i);
                        other_box
                            .borrow_mut()
                            .add_column(Some(c.clone()), make_ref(expr));
                    }
                    self.add_unique_keys(&other_box);
                    select_box = other_box;
                }
                current_context.add_cte(cte.name.clone(), select_box);
            }
        }
        let result = self.process_query_block_body(query_block, Some(&current_context));
        result
    }

    fn process_query_block_body(
        &mut self,
        query_block: &ast::QueryBlock,
        parent_context: Option<&NameResolutionContext>,
    ) -> Result<BoxRef, String> {
        let mut current_box = self.make_select_box();
        let mut current_context =
            NameResolutionContext::new(Rc::clone(&current_box), parent_context);

        let input_box = self.process_query_block_source(&query_block.source, &current_context)?;
        let is_select = if let BoxType::Select(_) = &input_box.borrow().box_type {
            true
        } else {
            false
        };
        if is_select {
            current_box = input_box;
            current_context = NameResolutionContext::new(Rc::clone(&current_box), parent_context);
        } else {
            let q = self.make_quantifier(input_box, &current_box);
            current_box.borrow_mut().add_quantifier(Rc::clone(&q));
            current_context.add_quantifier(&q);

            self.add_all_columns(&current_box);
        }

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
            self.add_unique_keys(&current_box);

            let grouping_box = self.make_box(BoxType::Grouping(Grouping::new()));
            let q = self.make_quantifier(current_box, &grouping_box);
            grouping_box.borrow_mut().add_quantifier(Rc::clone(&q));
            // context for resolving the grouping keys
            current_context = NameResolutionContext::new(Rc::clone(&grouping_box), parent_context);
            current_context.add_quantifier(&q);
            let mut input_column_in_group_key = HashSet::new();
            for key in &grouping.groups {
                let expr = self.process_expr(&key.expr, &current_context)?;
                if let ExprType::ColumnReference(c) = &expr.borrow().expr_type {
                    input_column_in_group_key.insert(c.position);
                }
                let mut grouping_box = grouping_box.borrow_mut();
                grouping_box.add_column(None, expr.clone());
                grouping_box.add_group(KeyItem {
                    expr,
                    dir: key.direction,
                });
            }
            // Import all columns with functional dependencies. If all the elements in
            // unique key of the input box are present in the grouping key, then we can
            // add all the columns from the input box to the projection of the grouping
            // box.
            if q.borrow()
                .input_box
                .borrow()
                .unique_keys
                .iter()
                .any(|key| key.iter().all(|c| input_column_in_group_key.contains(c)))
            {
                for i in 0..q.borrow().input_box.borrow().columns.len() {
                    if !input_column_in_group_key.contains(&i) {
                        let expr = Expr::make_column_ref(Rc::clone(&q), i);
                        grouping_box.borrow_mut().add_column(None, make_ref(expr));
                    }
                }
            }

            // @todo this could part of a finalization step
            grouping_box.borrow_mut().recompute_unique_keys();

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

        // distinct property
        if select.distinct {
            let mut box_mut = current_box.borrow_mut();
            box_mut.distinct_operation = DistinctOperation::Enforce;
        }

        self.add_unique_keys(&current_box);

        Ok(current_box)
    }

    fn add_all_columns(&mut self, select_box: &BoxRef) {
        select_box.borrow_mut().add_all_columns();
    }

    fn add_unique_keys(&mut self, select_box: &BoxRef) {
        select_box.borrow_mut().recompute_unique_keys();
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
        } else if let ast::JoinItem::TableRef(s) = &join_term.join_item {
            q.borrow_mut().set_alias(s.get_name().to_string());
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
                if let Some(cte) = current_context.resolve_cte(&s.get_name()) {
                    return Ok(cte);
                }
                // @todo suport for schemas and catalogs
                let metadata = self.catalog.get_table(s.get_name())?;
                // @todo avoid cloning the metadata. The catalog should return a ref counted instance
                let base_table = BoxType::BaseTable(metadata.clone());
                let table_box = self.make_box(base_table);
                // add the columns of the table
                for (i, c) in metadata.columns.iter().enumerate() {
                    table_box.borrow_mut().add_column(
                        Some(c.name.clone()),
                        make_ref(Expr::make_base_column(&table_box, i)),
                    );
                }
                for index in metadata.indexes.iter() {
                    if index.unique {
                        table_box.borrow_mut().add_unique_key(index.columns.clone());
                    }
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
                self.add_unique_keys(&select_box);
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
                s.model.borrow_mut().ids.get_quantifier_id(),
                quantifier_type,
                subquery_box,
                &select_box,
            );
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
