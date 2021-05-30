use std::iter::*;

#[derive(Debug, Clone)]
pub enum Statement {
    Select(QueryBlock),
    Insert(Insert),
    Update(Update),
    Delete(Delete),
    CreateTable(CreateTable),
    CreateIndex(CreateIndex),
    CreateView(View),
    DropTable(DropTable),
}

#[derive(Debug, Clone)]
pub struct Identifier {
    parts: Vec<String>,
}

impl Identifier {
    pub fn new() -> Self {
        Self { parts: Vec::new() }
    }

    pub fn get_qualifier_before_name(&self) -> Option<&str> {
        if self.parts.len() > 1 {
            Some(&self.parts[self.parts.len() - 2])
        } else {
            None
        }
    }

    pub fn get_name(&self) -> &str {
        self.parts.last().unwrap()
    }
}

#[derive(Debug, Clone)]
pub struct SelectItem {
    pub expr: Expr,
    pub alias: Option<String>,
}

#[derive(Debug, Clone)]
pub enum JoinType {
    Inner,
    LeftOuter,
    RightOuter,
}

#[derive(Debug, Clone)]
pub enum JoinCond {
    On(Expr),
    Using(Vec<String>),
}

#[derive(Debug, Clone)]
pub enum JoinItem {
    TableRef(Identifier),
    Join(JoinType, Box<JoinTerm>, Box<JoinTerm>, Option<JoinCond>),
    DerivedTable(QueryBlock),
    Lateral(QueryBlock),
}

#[derive(Debug, Clone)]
pub struct JoinTerm {
    pub join_item: JoinItem,
    pub alias: Option<String>,
}

#[derive(Debug, Copy, Clone)]
pub enum Direction {
    Ascending,
    Descending,
}

#[derive(Debug, Clone)]
pub struct OrderByItem {
    pub expr: Expr,
    pub direction: Direction,
}

type OrderByClause = Vec<OrderByItem>;

#[derive(Debug, Clone)]
pub struct Grouping {
    pub groups: OrderByClause,
    pub having_clause: Option<Expr>,
}

#[derive(Debug, Clone)]
pub struct Select {
    pub selection_list: Option<Vec<SelectItem>>,
    pub from_clause: Vec<JoinTerm>,
    pub where_clause: Option<Expr>,
    pub grouping: Option<Grouping>,
    pub distinct: bool,
}

impl Select {
    fn new(distinct: bool) -> Self {
        Self {
            selection_list: None,
            from_clause: Vec::new(),
            where_clause: None,
            grouping: None,
            distinct,
        }
    }

    fn add_select_item(&mut self, item: SelectItem) {
        self.selection_list.get_or_insert_with(Vec::new).push(item);
    }
}

#[derive(Debug, Clone)]
pub struct Union {
    pub distinct: bool,
    pub left: Box<QueryBlockSource>,
    pub right: Box<QueryBlockSource>,
}

#[derive(Debug, Clone)]
pub enum QueryBlockSource {
    Select(Select),
    Union(Union),
    Except(Box<QueryBlockSource>, Box<QueryBlockSource>),
    Intersect(Box<QueryBlockSource>, Box<QueryBlockSource>),
}

#[derive(Debug, Clone)]
pub struct View {
    pub name: String,
    pub columns: Option<Vec<String>>,
    pub select: QueryBlock,
}

#[derive(Debug, Clone)]
pub struct QueryBlock {
    pub ctes: Option<Vec<View>>,
    pub source: QueryBlockSource,
    pub order_by_clause: Option<OrderByClause>,
    pub limit_clause: Option<Expr>,
}

impl QueryBlock {
    fn new(source: QueryBlockSource) -> Self {
        Self {
            ctes: None,
            source,
            order_by_clause: None,
            limit_clause: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Delete {
    pub target: Identifier,
    pub where_clause: Option<Expr>,
    pub limit_clause: Option<Expr>,
}

#[derive(Debug, Clone)]
pub struct Update {
    pub target: Identifier,
    pub assignments: Vec<Assignment>,
    pub where_clause: Option<Expr>,
    pub limit_clause: Option<Expr>,
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub name: String,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct Insert {
    pub target: Identifier,
    pub columns: Option<Vec<String>>,
    pub source: InsertSource,
}

#[derive(Debug, Clone)]
pub enum InsertSource {
    Values(Vec<Vec<Expr>>),
    Select(QueryBlock),
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryExprType {
    Eq,
    Neq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
}

#[derive(Debug, PartialEq, Clone)]
pub enum NaryExprType {
    And,
    Or,
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnaryExprType {
    Not,
}

#[derive(Debug, Clone)]
pub struct CaseExpr {
    pub case_branches: Vec<(Box<Expr>, Box<Expr>)>,
    pub else_branch: Option<Box<Expr>>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Parameter(u64),
    Reference(Identifier),
    NumericLiteral(i64),
    BooleanLiteral(bool),
    StringLiteral(String),
    Unary(UnaryExprType, Box<Expr>),
    Nary(NaryExprType, Vec<Box<Expr>>),
    Binary(BinaryExprType, Box<Expr>, Box<Expr>),
    ScalarSubquery(Box<QueryBlock>),
    Exists(Box<QueryBlock>),
    All(Box<QueryBlock>),
    Any(Box<QueryBlock>),
    InSelect(Box<Expr>, Box<QueryBlock>),
    InList(Box<Expr>, Vec<Box<Expr>>),
    FunctionCall(Identifier, Vec<Box<Expr>>),
    Case(CaseExpr),
    IsNull(Box<Expr>),
    Tuple(Vec<Box<Expr>>),
    Between(Box<Expr>, Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn iter(&self) -> ExprIterator {
        ExprIterator::new(self)
    }
}

pub struct ExprIterator<'a> {
    stack: Vec<&'a Expr>,
}

impl<'a> ExprIterator<'a> {
    fn new(expr: &'a Expr) -> Self {
        let stack = vec![expr];
        Self { stack }
    }
}

impl<'a> Iterator for ExprIterator<'a> {
    type Item = &'a Expr;
    fn next(&mut self) -> Option<Self::Item> {
        use Expr::*;
        if let Some(top) = self.stack.pop() {
            match top {
                Parameter(_) => {}
                Reference(_) => {}
                StringLiteral(_) | BooleanLiteral(_) | NumericLiteral(_) => {}
                ScalarSubquery(_) | Exists(_) | All(_) | Any(_) => {}
                FunctionCall(_, vec) => {
                    for e in vec.iter() {
                        self.stack.push(e);
                    }
                }
                InSelect(e, _) => {
                    self.stack.push(e);
                }
                InList(e, vec) => {
                    self.stack.push(e);
                    for e in vec.iter() {
                        self.stack.push(e);
                    }
                }
                IsNull(e) | Unary(_, e) => {
                    self.stack.push(e);
                }
                Binary(_, l, r) => {
                    self.stack.push(l);
                    self.stack.push(r);
                }
                Tuple(vec) | Nary(_, vec) => {
                    for e in vec.iter() {
                        self.stack.push(e);
                    }
                }
                Case(case_expr) => {
                    for (c, t) in case_expr.case_branches.iter() {
                        self.stack.push(c);
                        self.stack.push(t);
                    }
                    for e in case_expr.else_branch.iter() {
                        self.stack.push(e);
                    }
                }
                Between(a, b, c) => {
                    self.stack.push(a);
                    self.stack.push(b);
                    self.stack.push(c);
                }
            }
            Some(top)
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TypeDef {
    String,
    Integer,
    BigInt,
    Double,
}

#[derive(Debug, Clone)]
pub struct ColumnDef {
    pub name: String,
    pub data_type: TypeDef,
}

#[derive(Debug, Clone)]
pub struct CreateTable {
    pub name: Identifier,
    pub columns: Vec<ColumnDef>,
}

#[derive(Debug, Clone)]
pub struct CreateIndex {
    pub name: String,
    pub unique: bool,
    pub tablename: Identifier,
    pub columns: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct DropTable {
    pub name: Identifier,
}

pub struct Parser {}

use crate::lexer;

impl Parser {
    pub fn new() -> Self {
        Self {}
    }

    pub fn parse(&self, input: &str) -> Result<Vec<Statement>, String> {
        match lexer::lex(input) {
            Err(c) => Err(c),
            Ok(tokens) => {
                let parser = ParserImpl::new(input, tokens.iter().peekable());
                parser.parse_statements()
            }
        }
    }
}

struct ParserImpl<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>> {
    input: &'a str,
    it: Peekable<T>,
    parameter_index: u64,
}

macro_rules! parse_list {
    ($sel:ident $body:block) => {
        loop {
            $body;
            if !$sel.complete_substr_and_advance(",") {
                break;
            }
        }
    };
}

macro_rules! complete_keyword {
    ($sel:ident, $keyword:ident) => {
        $sel.complete_token_and_advance(&lexer::ReservedKeyword::$keyword)
    };
}
macro_rules! expect_keyword {
    ($sel:ident, $keyword:ident) => {
        $sel.expect_token_and_advance(&lexer::ReservedKeyword::$keyword)
    };
}

impl<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>> ParserImpl<'a, T> {
    fn new(input: &'a str, it: Peekable<T>) -> Self {
        Self {
            input,
            it,
            parameter_index: 0,
        }
    }

    fn parse_statements(mut self) -> Result<Vec<Statement>, String> {
        let mut result: Vec<Statement> = Vec::new();
        loop {
            if let Some(select) = self.parse_select()? {
                result.push(Statement::Select(select));
            } else if complete_keyword!(self, Insert) {
                expect_keyword!(self, Into)?;
                result.push(Statement::Insert(self.parse_insert_body()?));
            } else if complete_keyword!(self, Update) {
                result.push(Statement::Update(self.parse_update_body()?));
            } else if complete_keyword!(self, Delete) {
                expect_keyword!(self, From)?;
                result.push(Statement::Delete(self.parse_delete_body()?));
            } else if complete_keyword!(self, Create) {
                if complete_keyword!(self, Table) {
                    result.push(Statement::CreateTable(self.parse_create_table_body()?));
                } else if complete_keyword!(self, Index) {
                    result.push(Statement::CreateIndex(self.parse_create_index_body(false)?));
                } else if complete_keyword!(self, Unique) {
                    expect_keyword!(self, Index)?;
                    result.push(Statement::CreateIndex(self.parse_create_index_body(true)?));
                } else if complete_keyword!(self, View) {
                    result.push(Statement::CreateView(self.parse_view()?));
                } else {
                    return Err("invalid CREATE statement".to_string());
                }
            } else if complete_keyword!(self, Drop) {
                expect_keyword!(self, Table)?;
                result.push(Statement::DropTable(self.parse_drop_table_body()?));
            }
            if !self.complete_substr_and_advance(";") {
                break;
            }
        }
        if let Some(&c) = self.it.peek() {
            return Err(format!("unexpected token {:?}", c));
        }
        Ok(result)
    }

    // private methods

    fn get_error_context(&mut self) -> String {
        if let Some(&lexeme) = self.it.peek() {
            // @todo find line and offset
            return format!(", found '{}'", lexeme.substring);
        }
        String::from("")
    }

    fn complete_substr_and_advance(&mut self, symbol: &str) -> bool {
        if let Some(&lexeme) = self.it.peek() {
            if lexeme.substring == symbol {
                self.it.next();
                return true;
            }
        }
        false
    }

    fn expect_substr_and_advance(&mut self, symbol: &str) -> Result<(), String> {
        if self.complete_substr_and_advance(symbol) {
            Ok(())
        } else {
            Err(format!("expected '{}'{}", symbol, self.get_error_context()))
        }
    }

    fn complete_token_and_advance(&mut self, keyword: &lexer::ReservedKeyword) -> bool {
        if let Some(&lexeme) = self.it.peek() {
            if let lexer::LexemeType::ReservedKeyword(s) = &lexeme.type_ {
                if *keyword == *s {
                    self.it.next();
                    return true;
                }
            }
        }
        false
    }

    fn expect_token_and_advance(&mut self, keyword: &lexer::ReservedKeyword) -> Result<(), String> {
        if self.complete_token_and_advance(keyword) {
            Ok(())
        } else {
            Err(format!(
                "expected '{:?}'{}",
                keyword,
                self.get_error_context()
            ))
        }
    }

    fn parse_name(&mut self) -> Option<String> {
        if let Some(&lexeme) = self.it.peek() {
            if let lexer::LexemeType::Word(s) = &lexeme.type_ {
                self.it.next();
                return Some(s.clone());
            }
        }
        None
    }

    fn expect_name(&mut self) -> Result<String, String> {
        if let Some(c) = self.parse_name() {
            Ok(c)
        } else {
            Err(String::from("expected name"))
        }
    }

    fn parse_identifier(&mut self) -> Option<Identifier> {
        let mut identifier: Option<Identifier> = None;
        while let Some(part) = self.parse_name() {
            identifier
                .get_or_insert_with(Identifier::new)
                .parts
                .push(part);
            if !self.complete_substr_and_advance(".") {
                break;
            }
        }
        identifier
    }

    fn expect_identifier(&mut self) -> Result<Identifier, String> {
        if let Some(c) = self.parse_identifier() {
            Ok(c)
        } else {
            Err(String::from("expected identifier"))
        }
    }

    /// scalar subqueries are allowed within parenthesis
    fn parse_expr_within_parenthesis(&mut self) -> Result<Expr, String> {
        if let Some(select) = self.parse_select()? {
            Ok(Expr::ScalarSubquery(Box::new(select)))
        } else {
            let mut result = Vec::new();
            parse_list!(self {
                result.push(Box::new(self.parse_expr()?));
            });
            if result.len() == 1 {
                Ok(*result.pop().unwrap())
            } else {
                Ok(Expr::Tuple(result))
            }
        }
    }

    fn parse_expr_term(&mut self) -> Result<Expr, String> {
        if self.complete_substr_and_advance("(") {
            let result = self.parse_expr_within_parenthesis();
            self.expect_substr_and_advance(")")?;
            return result;
        } else if self.complete_substr_and_advance("?") {
            let result = Expr::Parameter(self.parameter_index);
            self.parameter_index += 1;
            return Ok(result);
        } else if complete_keyword!(self, Exists) {
            self.expect_substr_and_advance("(")?;
            let result = Expr::Exists(Box::new(self.expect_select()?));
            self.expect_substr_and_advance(")")?;
            return Ok(result);
        } else if complete_keyword!(self, True) {
            return Ok(Expr::BooleanLiteral(true));
        } else if complete_keyword!(self, False) {
            return Ok(Expr::BooleanLiteral(false));
        } else if complete_keyword!(self, Case) {
            let mut case_expr = CaseExpr {
                case_branches: Vec::new(),
                else_branch: None,
            };
            expect_keyword!(self, When)?;
            loop {
                let case = self.parse_expr()?;
                expect_keyword!(self, Then)?;
                let then = self.parse_expr()?;
                case_expr
                    .case_branches
                    .push((Box::new(case), Box::new(then)));
                if !complete_keyword!(self, When) {
                    break;
                }
            }
            if complete_keyword!(self, Else) {
                let else_branch = self.parse_expr()?;
                case_expr.else_branch = Some(Box::new(else_branch));
            }
            expect_keyword!(self, End)?;
            return Ok(Expr::Case(case_expr));
        } else if let Some(id) = self.parse_identifier() {
            if self.complete_substr_and_advance("(") {
                let mut params: Vec<Box<Expr>> = Vec::new();
                if !self.complete_substr_and_advance(")") {
                    parse_list! (self {
                        let param = self.parse_expr()?;
                        params.push(Box::new(param));
                    });
                    self.expect_substr_and_advance(")")?;
                }
                return Ok(Expr::FunctionCall(id, params));
            }
            return Ok(Expr::Reference(id));
        } else if let Some(&lexeme) = self.it.peek() {
            if lexeme.type_ == lexer::LexemeType::Number {
                self.it.next();
                let value = lexeme.substring.to_string().parse::<i64>();
                if value.is_err() {
                    return Err(format!("{}", value.err().unwrap()));
                }
                return Ok(Expr::NumericLiteral(value.unwrap()));
            } else {
                if lexeme.type_ == lexer::LexemeType::String {
                    self.it.next();
                    return Ok(Expr::StringLiteral(lexeme.substring.to_string()));
                }
            }
        }
        Err(String::from("invalid expression"))
    }

    /// handles IN-lists and IN SELECT expressions
    fn parse_expr_in(&mut self) -> Result<Expr, String> {
        let result = self.parse_expr_term()?;
        if complete_keyword!(self, In) {
            self.expect_substr_and_advance("(")?;
            if let Some(select) = self.parse_select()? {
                self.expect_substr_and_advance(")")?;
                Ok(Expr::InSelect(Box::new(result), Box::new(select)))
            } else {
                let mut terms = Vec::new();
                parse_list!(self {
                    let term = self.parse_expr()?;
                    terms.push(Box::new(term));
                });
                self.expect_substr_and_advance(")")?;
                Ok(Expr::InList(Box::new(result), terms))
            }
        } else if complete_keyword!(self, Is) {
            let not = complete_keyword!(self, Not);
            expect_keyword!(self, Null)?;
            if not {
                Ok(Expr::Unary(
                    UnaryExprType::Not,
                    Box::new(Expr::IsNull(Box::new(result))),
                ))
            } else {
                Ok(Expr::IsNull(Box::new(result)))
            }
        } else if complete_keyword!(self, Between) {
            let min = self.parse_expr_term()?;
            expect_keyword!(self, And)?;
            let max = self.parse_expr_term()?;
            Ok(Expr::Between(
                Box::new(result),
                Box::new(min),
                Box::new(max),
            ))
        } else {
            Ok(result)
        }
    }

    fn parse_expr_mult(&mut self) -> Result<Expr, String> {
        let op = |s: &mut Self| {
            if s.complete_substr_and_advance("*") {
                Some(NaryExprType::Mul)
            } else if s.complete_substr_and_advance("/") {
                Some(NaryExprType::Div)
            } else {
                None
            }
        };
        let term = |s: &mut Self| s.parse_expr_in();
        self.parse_nary_expr(&op, &term)
    }

    fn parse_expr_add(&mut self) -> Result<Expr, String> {
        let op = |s: &mut Self| {
            if s.complete_substr_and_advance("+") {
                Some(NaryExprType::Add)
            } else if s.complete_substr_and_advance("-") {
                Some(NaryExprType::Sub)
            } else {
                None
            }
        };
        let term = |s: &mut Self| s.parse_expr_mult();
        self.parse_nary_expr(&op, &term)
    }

    fn parse_expr_cmp(&mut self) -> Result<Expr, String> {
        let left = self.parse_expr_add()?;
        let op = {
            if self.complete_substr_and_advance("=") {
                Some(BinaryExprType::Eq)
            } else if self.complete_substr_and_advance("!=") {
                Some(BinaryExprType::Neq)
            } else if self.complete_substr_and_advance(">") {
                Some(BinaryExprType::Greater)
            } else if self.complete_substr_and_advance(">=") {
                Some(BinaryExprType::GreaterEq)
            } else if self.complete_substr_and_advance("<") {
                Some(BinaryExprType::Less)
            } else if self.complete_substr_and_advance("<=") {
                Some(BinaryExprType::LessEq)
            } else {
                None
            }
        };
        if op.is_none() {
            return Ok(left);
        }
        let right = {
            if complete_keyword!(self, All) {
                self.expect_substr_and_advance("(")?;
                let result = Expr::All(Box::new(self.expect_select()?));
                self.expect_substr_and_advance(")")?;
                result
            } else if complete_keyword!(self, Any) {
                self.expect_substr_and_advance("(")?;
                let result = Expr::Any(Box::new(self.expect_select()?));
                self.expect_substr_and_advance(")")?;
                result
            } else {
                self.parse_expr_add()?
            }
        };
        Ok(Expr::Binary(op.unwrap(), Box::new(left), Box::new(right)))
    }

    fn parse_expr_and(&mut self) -> Result<Expr, String> {
        let op = |s: &mut Self| {
            if complete_keyword!(s, And) {
                Some(NaryExprType::And)
            } else {
                None
            }
        };
        let term = |s: &mut Self| s.parse_expr_cmp();
        self.parse_nary_expr(&op, &term)
    }

    fn parse_expr_or(&mut self) -> Result<Expr, String> {
        let op = |s: &mut Self| {
            if complete_keyword!(s, Or) {
                Some(NaryExprType::Or)
            } else {
                None
            }
        };
        let term = |s: &mut Self| s.parse_expr_and();
        self.parse_nary_expr(&op, &term)
    }

    /// Parse any n-ary expression. op returns the operation type, term parses the terms of the expression
    fn parse_nary_expr<FOp, FTerm>(&mut self, op: &FOp, term: &FTerm) -> Result<Expr, String>
    where
        FOp: Fn(&mut Self) -> Option<NaryExprType>,
        FTerm: Fn(&mut Self) -> Result<Expr, String>,
    {
        let mut result: Option<Expr> = None;
        loop {
            let term: Expr = term(self)?;
            let op = op(self);
            let more = op.is_some();
            if result.is_none() {
                if !more {
                    return Ok(term);
                }
                result = Some(Expr::Nary(op.unwrap(), vec![Box::new(term)]));
            } else {
                let unwrapped = result.unwrap();
                if let Expr::Nary(o, mut vec) = unwrapped {
                    if op.is_none() || o == *op.as_ref().unwrap() {
                        vec.push(Box::new(term));
                        result = Some(Expr::Nary(o, vec));
                    } else {
                        result = Some(Expr::Nary(
                            op.unwrap(),
                            vec![Box::new(Expr::Nary(o, vec)), Box::new(term)],
                        ));
                    }
                } else {
                    panic!();
                }
            }
            if !more {
                break;
            }
        }
        Ok(result.unwrap())
    }

    /// Entry point for parsing expressions
    fn parse_expr(&mut self) -> Result<Expr, String> {
        self.parse_expr_or()
    }

    fn parse_join_item(&mut self) -> Result<JoinItem, String> {
        if let Some(c) = self.parse_identifier() {
            Ok(JoinItem::TableRef(c))
        } else if complete_keyword!(self, Lateral) {
            self.expect_substr_and_advance("(")?;
            let select = self.expect_select()?;
            self.expect_substr_and_advance(")")?;
            Ok(JoinItem::Lateral(select))
        } else if self.complete_substr_and_advance("(") {
            if let Some(select) = self.parse_select()? {
                self.expect_substr_and_advance(")")?;
                Ok(JoinItem::DerivedTable(select))
            } else {
                let join_term: JoinTerm = self.parse_join_tree()?;
                self.expect_substr_and_advance(")")?;
                Ok(join_term.join_item)
            }
        } else {
            Err(String::from("invalid join term"))
        }
    }

    fn parse_join_term(&mut self) -> Result<JoinTerm, String> {
        let join_item: JoinItem = self.parse_join_item()?;
        let alias: Option<String>;
        if complete_keyword!(self, As) {
            alias = self.parse_name();
            if !alias.is_some() {
                return Err(String::from("expected table alias"));
            }
        } else {
            // optional alias
            alias = self.parse_name();
        }
        Ok(JoinTerm { join_item, alias })
    }

    fn parse_join_tree(&mut self) -> Result<JoinTerm, String> {
        let mut left_item = self.parse_join_term()?;
        loop {
            let mut join_type: Option<JoinType> = None;
            if complete_keyword!(self, Left) {
                join_type = Some(JoinType::LeftOuter);
            } else if complete_keyword!(self, Right) {
                join_type = Some(JoinType::RightOuter);
            }
            if join_type.is_some() {
                // optional
                complete_keyword!(self, Outer);
                expect_keyword!(self, Join)?;
            } else {
                if complete_keyword!(self, Inner) {
                    expect_keyword!(self, Join)?;
                    join_type = Some(JoinType::Inner);
                } else if complete_keyword!(self, Join) {
                    join_type = Some(JoinType::Inner);
                }
            }
            if !join_type.is_some() {
                return Ok(left_item);
            }
            let right_item = self.parse_join_term()?;
            let mut join_cond = None;
            if complete_keyword!(self, On) {
                join_cond = Some(JoinCond::On(self.parse_expr()?));
            } else if complete_keyword!(self, Using) {
                if let Some(columns) = self.parse_column_list()? {
                    join_cond = Some(JoinCond::Using(columns));
                } else {
                    return Err(format!("expected column list for USING clause"));
                }
            }
            let join = JoinItem::Join(
                join_type.unwrap(),
                Box::new(left_item),
                Box::new(right_item),
                join_cond,
            );
            left_item = JoinTerm {
                join_item: join,
                alias: None,
            };
        }
    }

    fn parse_query_expression_body(&mut self) -> Result<Select, String> {
        let distinct = complete_keyword!(self, Distinct);
        let mut select = Select::new(distinct);
        if !self.complete_substr_and_advance("*") {
            parse_list!(self {
                let expr: Expr = self.parse_expr()?;
                let alias: Option<String>;
                if complete_keyword!(self, As) {
                    alias = self.parse_name();
                    if !alias.is_some() {
                        return Err(String::from("expected column alias"));
                    }
                } else {
                    // optional alias
                    alias = self.parse_name();
                }
                let select_item = SelectItem { expr, alias };
                select.add_select_item(select_item);
            });
        }

        // mandatory from clause
        expect_keyword!(self, From)?;
        parse_list!(self {
            let join_term: JoinTerm = self.parse_join_tree()?;
            select.from_clause.push(join_term);
        });

        // where clause
        select.where_clause = self.parse_where_clause()?;

        if complete_keyword!(self, Group) {
            expect_keyword!(self, By)?;
            select.grouping = Some(self.parse_group_by_body()?);
        }
        Ok(select)
    }

    fn parse_query_expression(&mut self) -> Result<Select, String> {
        expect_keyword!(self, Select)?;
        self.parse_query_expression_body()
    }

    fn expect_select(&mut self) -> Result<QueryBlock, String> {
        if let Some(select) = self.parse_select()? {
            Ok(select)
        } else {
            Err(format!("expected SELECT"))
        }
    }

    fn parse_column_list(&mut self) -> Result<Option<Vec<String>>, String> {
        if self.complete_substr_and_advance("(") {
            let mut cols = Vec::new();
            parse_list!(self {
                let col = self.expect_name()?;
                cols.push(col);
            });
            self.expect_substr_and_advance(")")?;
            Ok(Some(cols))
        } else {
            Ok(None)
        }
    }

    fn parse_view(&mut self) -> Result<View, String> {
        let name = self.expect_name()?;
        let columns = self.parse_column_list()?;
        expect_keyword!(self, As)?;
        let select = self.expect_select()?;
        Ok(View {
            name,
            columns,
            select,
        })
    }

    fn parse_select(&mut self) -> Result<Option<QueryBlock>, String> {
        let mut ctes = None;
        if complete_keyword!(self, With) {
            let mut views = Vec::new();
            parse_list!(self {
                let name = self.expect_name()?;
                let columns = self.parse_column_list()?;
                expect_keyword!(self, As)?;
                self.expect_substr_and_advance("(")?;
                let select = self.expect_select()?;
                self.expect_substr_and_advance(")")?;
                views.push(View{name, columns, select});
            });
            expect_keyword!(self, Select)?;
            ctes = Some(views);
        } else if !complete_keyword!(self, Select) {
            return Ok(None);
        }

        let mut select = self.parse_select_body()?;
        select.ctes = ctes;
        Ok(Some(select))
    }

    fn parse_select_body(&mut self) -> Result<QueryBlock, String> {
        let mut left = QueryBlockSource::Select(self.parse_query_expression_body()?);
        loop {
            if complete_keyword!(self, Union) {
                let all = complete_keyword!(self, All);
                if !all {
                    let _ = complete_keyword!(self, Distinct);
                }

                let right = QueryBlockSource::Select(self.parse_query_expression()?);
                left = QueryBlockSource::Union(Union {
                    distinct: !all,
                    left: Box::new(left),
                    right: Box::new(right),
                });
            } else if complete_keyword!(self, Except) {
                let right = QueryBlockSource::Select(self.parse_query_expression()?);
                left = QueryBlockSource::Except(Box::new(left), Box::new(right));
            } else if complete_keyword!(self, Intersect) {
                let right = QueryBlockSource::Select(self.parse_query_expression()?);
                left = QueryBlockSource::Intersect(Box::new(left), Box::new(right));
            } else {
                break;
            }
        }

        let mut query_block = QueryBlock::new(left);
        if complete_keyword!(self, Order) {
            expect_keyword!(self, By)?;
            query_block.order_by_clause = Some(self.parse_order_by_keys()?);
        }

        // limit clause
        query_block.limit_clause = self.parse_limit_clause()?;

        Ok(query_block)
    }

    fn parse_group_by_body(&mut self) -> Result<Grouping, String> {
        let keys = self.parse_order_by_keys()?;
        let mut having = None;
        if complete_keyword!(self, Having) {
            having = Some(self.parse_expr()?);
        }
        Ok(Grouping {
            groups: keys,
            having_clause: having,
        })
    }

    fn parse_order_by_keys(&mut self) -> Result<OrderByClause, String> {
        let mut clause = OrderByClause::new();
        parse_list!(self {
            let expr: Expr = self.parse_expr()?;
            let mut direction = Direction::Ascending;
            if complete_keyword!(self, Desc) {
                direction = Direction::Descending;
            } else {
                complete_keyword!(self, Asc);
            }
            clause.push(OrderByItem{expr, direction});
        });
        Ok(clause)
    }

    fn parse_delete_body(&mut self) -> Result<Delete, String> {
        let identifier = self.expect_identifier()?;
        let where_clause = self.parse_where_clause()?;
        let limit_clause = self.parse_limit_clause()?;
        Ok(Delete {
            target: identifier,
            where_clause,
            limit_clause,
        })
    }

    fn parse_insert_body(&mut self) -> Result<Insert, String> {
        let identifier = self.expect_identifier()?;
        let columns = self.parse_column_list()?;
        if complete_keyword!(self, Select) {
            let select = self.parse_select_body()?;
            Ok(Insert {
                target: identifier,
                columns,
                source: InsertSource::Select(select),
            })
        } else {
            expect_keyword!(self, Values)?;
            let mut rows = Vec::new();
            parse_list!(self {
                self.expect_substr_and_advance("(")?;
                let mut values = Vec::new();
                parse_list!(self {
                    let expr = self.parse_expr()?;
                    values.push(expr);
                });
                self.expect_substr_and_advance(")")?;
                rows.push(values);
            });
            Ok(Insert {
                target: identifier,
                columns,
                source: InsertSource::Values(rows),
            })
        }
    }

    fn parse_update_body(&mut self) -> Result<Update, String> {
        let target = self.expect_identifier()?;
        expect_keyword!(self, Set)?;
        let mut assignments = Vec::new();
        parse_list!(self {
            let col = self.expect_name()?;
            self.expect_substr_and_advance("=")?;
            let expr: Expr = self.parse_expr()?;
            assignments.push(Assignment{name: col, expr});
        });

        let where_clause = self.parse_where_clause()?;
        let limit_clause = self.parse_limit_clause()?;
        Ok(Update {
            target,
            assignments,
            where_clause,
            limit_clause,
        })
    }

    fn parse_where_clause(&mut self) -> Result<Option<Expr>, String> {
        let mut where_clause = None;
        if complete_keyword!(self, Where) {
            let expr: Expr = self.parse_expr()?;
            where_clause = Some(expr);
        }
        Ok(where_clause)
    }

    fn parse_limit_clause(&mut self) -> Result<Option<Expr>, String> {
        let mut limit_clause = None;
        if complete_keyword!(self, Limit) {
            let expr: Expr = self.parse_expr()?;
            limit_clause = Some(expr);
        }
        Ok(limit_clause)
    }

    fn parse_create_table_body(&mut self) -> Result<CreateTable, String> {
        let identifier = self.expect_identifier()?;
        self.expect_substr_and_advance("(")?;
        let mut columns = Vec::new();
        parse_list!(self {
            let name = self.expect_name()?;
            // @todo parse type
            columns.push(ColumnDef{name: name, data_type: TypeDef::String});
        });
        self.expect_substr_and_advance(")")?;
        Ok(CreateTable {
            name: identifier,
            columns,
        })
    }

    fn parse_drop_table_body(&mut self) -> Result<DropTable, String> {
        let identifier = self.expect_identifier()?;
        Ok(DropTable { name: identifier })
    }

    fn parse_create_index_body(&mut self, unique: bool) -> Result<CreateIndex, String> {
        let name = self.expect_name()?;
        expect_keyword!(self, On)?;

        let tablename = self.expect_identifier()?;

        self.expect_substr_and_advance("(")?;
        let mut columns = Vec::new();
        parse_list!(self {
            let name = self.expect_name()?;
            // @todo parse direction
            columns.push(name);
        });
        self.expect_substr_and_advance(")")?;

        Ok(CreateIndex {
            name,
            unique,
            tablename,
            columns,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_select() {
        let parser = Parser {};
        assert!(!parser.parse("select a from a").is_err());

        let test_valid_query = |q| {
            println!("{}", q);
            let result = parser.parse(q);
            println!("{:?}", result);
            assert!(result.is_ok());
        };

        let test_invalid_query = |q, t: Option<String>| {
            println!("{}", q);
            let result = parser.parse(q);
            println!("{:?}", result);
            assert!(result.is_err());
            if t.is_some() {
                assert_eq!(t.unwrap(), result.err().unwrap());
            }
        };

        test_valid_query("select * from a");
        test_valid_query("select a from a");
        test_valid_query("select a from a as b");
        test_valid_query("select a from a as b join c");
        test_valid_query("select a from a as b join c on a = 1");
        test_valid_query("select a from a b");
        test_valid_query("select a, b from a");
        test_valid_query("select a, b as c from a");
        test_valid_query("select a, b c from a");
        test_valid_query("select a from a where c");
        test_valid_query("select a from a limit c");
        test_valid_query("select a from a limit 1");
        test_valid_query("select a from a where a or b");
        test_valid_query("select a from a where a or b and c");
        test_valid_query("select a from a where a = 1");
        test_valid_query("select a from a where a = h or b = z and c = 1");
        test_valid_query("select a from a where a in (select b from b)");
        test_valid_query("select a from a where a = (select b from b)");
        test_valid_query("select a from a where a = ?");
        test_valid_query("select a from a where a in (1)");
        test_valid_query("select a from a where a in (1, 2)");
        test_valid_query("select a from a where a in (?, ?, ?, ?)");
        test_valid_query("select a from a where f1()");
        test_valid_query("select a from a where f1(?)");
        test_valid_query("select a from a where f1(?, ?, ?, ?)");
        test_valid_query("select a from a where exists(select 1 from b)");
        test_valid_query("select a from a where c = 1 order by a");
        test_valid_query("select a from a where c = 1 order by a, c desc");
        test_valid_query("select a from a where c = 1 order by a asc, c");
        test_valid_query("select a from a, lateral(select * from b where a = b)");
        test_valid_query("select a from a where (a, b) = (1, 2)");

        test_valid_query("insert into a values (1)");
        test_valid_query("insert into a(a) values (1)");
        test_valid_query("insert into a(a, b, c) values (1, 2, 3)");
        test_valid_query("insert into a select a from a");
        test_valid_query("delete from a");
        test_valid_query("delete from a where a = 1");
        test_valid_query("delete from a where a = 1 limit 10");

        test_invalid_query(
            "delete from a where a = 18446744073709551615",
            Some("number too large to fit in target type".to_string()),
        );
        test_invalid_query(
            "delete from a where a = 9223372036854775808",
            Some("number too large to fit in target type".to_string()),
        );
        test_valid_query("delete from a where a = 9223372036854775807");

        test_valid_query("select case when a = 1 then 1 end from a");
        test_valid_query("select case when a = 1 then 1 else 2 end from a");
        test_valid_query("select a from a where a between 1 and 2");
    }

    #[test]
    fn test_expr_iterator() {
        use std::collections::HashSet;

        let parser = Parser {};
        let result = parser.parse("select * from a where exists(select 1 from a) and a or b and c = 1 or z in (select a from a)");
        assert!(result.is_ok());
        let result = result.unwrap();
        assert_eq!(result.len(), 1);
        if let Statement::Select(s) = &result[0] {
            if let QueryBlockSource::Select(s) = &s.source {
                assert!(s.where_clause.is_some());
                let mut exprs = HashSet::new();
                for expr in s.where_clause.as_ref().unwrap().iter() {
                    exprs.insert(expr as *const Expr);
                    println!("{:?}", expr);
                }
            } else {
                assert!(false);
            }
        } else {
            assert!(false);
        }
    }
}
