use std::iter::*;

#[derive(Debug)]
pub enum Statement {
    Select(Select),
    Insert(Insert),
    Update(Update),
    Delete(Delete),
    CreateTable(CreateTable),
}

#[derive(Debug)]
pub struct Identifier {
    parts: Vec<String>,
}

impl Identifier {
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

#[derive(Debug)]
pub struct SelectItem {
    pub expr: Expr,
    pub alias: Option<String>,
}

#[derive(Debug)]
pub enum JoinType {
    Inner,
    LeftOuter,
    RightOuter,
}

#[derive(Debug)]
pub enum JoinItem {
    TableRef(Identifier),
    Join(JoinType, Box<JoinTerm>, Box<JoinTerm>, Option<Expr>),
    DerivedTable(Select),
    Lateral(Select),
}

#[derive(Debug)]
pub struct JoinTerm {
    pub join_item: JoinItem,
    pub alias: Option<String>,
}

#[derive(Debug, Copy, Clone)]
pub enum Direction {
    Ascending,
    Descending,
}

#[derive(Debug)]
pub struct OrderByItem {
    pub expr: Expr,
    pub direction: Direction,
}

type OrderByClause = Vec<OrderByItem>;

#[derive(Debug)]
pub struct Grouping {
    pub groups: OrderByClause,
    pub having_clause: Option<Expr>,
}

#[derive(Debug)]
pub struct Select {
    pub selection_list: Option<Vec<SelectItem>>,
    pub from_clause: Vec<JoinTerm>,
    pub where_clause: Option<Expr>,
    pub grouping: Option<Grouping>,
    pub order_by_clause: Option<OrderByClause>,
    pub limit_clause: Option<Expr>,
}

impl Select {
    fn new() -> Self {
        Self {
            selection_list: None,
            from_clause: Vec::new(),
            where_clause: None,
            grouping: None,
            order_by_clause: None,
            limit_clause: None,
        }
    }

    fn add_select_item(&mut self, item: SelectItem) {
        if self.selection_list.is_none() {
            self.selection_list = Some(Vec::new());
        }
        self.selection_list.as_mut().unwrap().push(item);
    }
}

#[derive(Debug)]
pub struct Delete {
    pub target: Identifier,
    pub where_clause: Option<Expr>,
    pub limit_clause: Option<Expr>,
}

#[derive(Debug)]
pub struct Update {
    pub target: Identifier,
    pub assignments: Vec<Assignment>,
    pub where_clause: Option<Expr>,
    pub limit_clause: Option<Expr>,
}

#[derive(Debug)]
pub struct Assignment {
    pub name: String,
    pub expr: Expr,
}

#[derive(Debug)]
pub struct Insert {
    pub target: Identifier,
    pub columns: Option<Vec<String>>,
    pub source: InsertSource,
}

#[derive(Debug)]
pub enum InsertSource {
    Values(Vec<Vec<Expr>>),
    Select(Select),
}

#[derive(Debug, PartialEq)]
pub enum BinaryExprType {
    Eq,
    Neq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
}

#[derive(Debug, PartialEq)]
pub enum NaryExprType {
    And,
    Or,
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug)]
pub struct CaseExpr {
    pub case_branches: Vec<(Box<Expr>, Box<Expr>)>,
    pub else_branch: Option<Box<Expr>>,
}

#[derive(Debug)]
pub enum Expr {
    Parameter(u64),
    Reference(Identifier),
    NumericLiteral(i64),
    BooleanLiteral(bool),
    Unary(Box<Expr>),
    Nary(NaryExprType, Vec<Box<Expr>>),
    Binary(BinaryExprType, Box<Expr>, Box<Expr>),
    ScalarSubquery(Box<Select>),
    Exists(Box<Select>),
    All(Box<Select>),
    Any(Box<Select>),
    InSelect(Box<Expr>, Box<Select>),
    InList(Box<Expr>, Vec<Box<Expr>>),
    FunctionCall(Identifier, Vec<Box<Expr>>),
    Case(CaseExpr),
    IsNull(Box<Expr>),
    Tuple(Vec<Box<Expr>>),
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
        Self { stack: stack }
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
                BooleanLiteral(_) | NumericLiteral(_) => {}
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
                IsNull(e) | Unary(e) => {
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
            }
            Some(top)
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TypeDef {
    String,
    Integer,
    BigInt,
    Double,
}

#[derive(Debug)]
pub struct ColumnDef {
    pub name: String,
    pub data_type: TypeDef,
}

#[derive(Debug)]
pub struct CreateTable {
    pub name: Identifier,
    pub columns: Vec<ColumnDef>,
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
        use lexer::*;

        let mut result: Vec<Statement> = Vec::new();
        loop {
            if complete_keyword!(self, Select) {
                result.push(Statement::Select(self.parse_select_body()?));
            } else if complete_keyword!(self, Insert) {
                self.expect_token_and_advance(&ReservedKeyword::Into)?;
                result.push(Statement::Insert(self.parse_insert_body()?));
            } else if complete_keyword!(self, Update) {
                result.push(Statement::Update(self.parse_update_body()?));
            } else if complete_keyword!(self, Delete) {
                self.expect_token_and_advance(&ReservedKeyword::From)?;
                result.push(Statement::Delete(self.parse_delete_body()?));
            } else if complete_keyword!(self, Create) {
                self.expect_token_and_advance(&ReservedKeyword::Table)?;
                result.push(Statement::CreateTable(self.parse_create_table_body()?));
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
            if !identifier.is_some() {
                identifier = Some(Identifier { parts: Vec::new() });
            }
            identifier.as_mut().unwrap().parts.push(part);
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
        if complete_keyword!(self, Select) {
            Ok(Expr::ScalarSubquery(Box::new(self.parse_select_body()?)))
        } else {
            let mut result = Vec::new();
            loop {
                result.push(Box::new(self.parse_expr()?));
                if !self.complete_substr_and_advance(",") {
                    break;
                }
            }
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
            self.expect_token_and_advance(&lexer::ReservedKeyword::Select)?;
            let result = Expr::Exists(Box::new(self.parse_select_body()?));
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
            }
        }
        Err(String::from("invalid expression"))
    }

    /// handles IN-lists and IN SELECT expressions
    fn parse_expr_in(&mut self) -> Result<Expr, String> {
        let result = self.parse_expr_term()?;
        if complete_keyword!(self, In) {
            self.expect_substr_and_advance("(")?;
            if complete_keyword!(self, Select) {
                let select = self.parse_select_body()?;
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
            expect_keyword!(self, Null)?;
            Ok(Expr::IsNull(Box::new(result)))
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
            if self.complete_token_and_advance(&lexer::ReservedKeyword::All) {
                self.expect_substr_and_advance("(")?;
                self.expect_token_and_advance(&lexer::ReservedKeyword::Select)?;
                let result = Expr::All(Box::new(self.parse_select_body()?));
                self.expect_substr_and_advance(")")?;
                result
            } else if self.complete_token_and_advance(&lexer::ReservedKeyword::Any) {
                self.expect_substr_and_advance("(")?;
                self.expect_token_and_advance(&lexer::ReservedKeyword::Select)?;
                let result = Expr::Any(Box::new(self.parse_select_body()?));
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
            if s.complete_token_and_advance(&lexer::ReservedKeyword::And) {
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
            if s.complete_token_and_advance(&lexer::ReservedKeyword::Or) {
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
        // @todo parse JoinItem::Join
        if let Some(c) = self.parse_identifier() {
            Ok(JoinItem::TableRef(c))
        } else if self.complete_token_and_advance(&lexer::ReservedKeyword::Lateral) {
            self.expect_substr_and_advance("(")?;
            self.expect_token_and_advance(&lexer::ReservedKeyword::Select)?;
            let select = self.parse_select_body()?;
            self.expect_substr_and_advance(")")?;
            Ok(JoinItem::Lateral(select))
        } else if self.complete_substr_and_advance("(") {
            self.expect_token_and_advance(&lexer::ReservedKeyword::Select)?;
            let select = self.parse_select_body()?;
            self.expect_substr_and_advance(")")?;
            Ok(JoinItem::DerivedTable(select))
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
                self.expect_token_and_advance(&lexer::ReservedKeyword::Join)?;
            } else {
                if complete_keyword!(self, Inner) {
                    self.expect_token_and_advance(&lexer::ReservedKeyword::Join)?;
                    join_type = Some(JoinType::Inner);
                } else if complete_keyword!(self, Join) {
                    join_type = Some(JoinType::Inner);
                }
            }
            if !join_type.is_some() {
                return Ok(left_item);
            }
            let right_item = self.parse_join_term()?;
            let mut on_clause: Option<Expr> = None;
            if complete_keyword!(self, On) {
                on_clause = Some(self.parse_expr()?);
            }
            let join = JoinItem::Join(
                join_type.unwrap(),
                Box::new(left_item),
                Box::new(right_item),
                on_clause,
            );
            left_item = JoinTerm {
                join_item: join,
                alias: None,
            };
        }
    }

    fn parse_select_body(&mut self) -> Result<Select, String> {
        let mut select = Select::new();
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
        self.expect_token_and_advance(&lexer::ReservedKeyword::From)?;
        parse_list!(self {
            let join_term: JoinTerm = self.parse_join_tree()?;
            select.from_clause.push(join_term);
        });

        // where clause
        select.where_clause = self.parse_where_clause()?;

        if complete_keyword!(self, Group) {
            self.expect_token_and_advance(&lexer::ReservedKeyword::By)?;
            select.grouping = Some(self.parse_group_by_body()?);
        }

        if complete_keyword!(self, Order) {
            self.expect_token_and_advance(&lexer::ReservedKeyword::By)?;
            select.order_by_clause = Some(self.parse_order_by_keys()?);
        }

        // limit clause
        select.limit_clause = self.parse_limit_clause()?;

        Ok(select)
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
        let mut columns: Option<Vec<String>> = None;
        if self.complete_substr_and_advance("(") {
            let mut cols = Vec::new();
            parse_list!(self {
                let name = self.expect_name()?;
                cols.push(name);
            });
            self.expect_substr_and_advance(")")?;
            columns = Some(cols);
        }
        if complete_keyword!(self, Select) {
            let select = self.parse_select_body()?;
            Ok(Insert {
                target: identifier,
                columns,
                source: InsertSource::Select(select),
            })
        } else {
            self.expect_token_and_advance(&lexer::ReservedKeyword::Values)?;
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
        self.expect_token_and_advance(&lexer::ReservedKeyword::Set)?;
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
            assert!(s.where_clause.is_some());
            let mut exprs = HashSet::new();
            for expr in s.where_clause.as_ref().unwrap().iter() {
                exprs.insert(expr as *const Expr);
                println!("{:?}", expr);
            }
        } else {
            assert!(false);
        }
    }
}
