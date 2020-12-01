use std::iter::*;

#[derive(Debug)]
pub enum Statement {
    Select(Select),
    CreateTable(CreateTable),
}

#[derive(Debug)]
pub struct Identifier {
    parts: Vec<String>,
}

#[derive(Debug)]
pub struct SelectItem {
    expr: Expr,
    alias: Option<String>,
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
    Join(JoinType, Box<JoinTerm>, Box<JoinTerm>),
    DerivedTable(Select),
}

#[derive(Debug)]
pub struct JoinTerm {
    join_item: JoinItem,
    alias: Option<String>,
}

#[derive(Debug)]
pub struct Select {
    selection_list: Option<Vec<SelectItem>>,
    from_clause: Vec<JoinTerm>,
    where_clause: Option<Expr>,
    limit_clause: Option<Expr>,
}

impl Select {
    fn new() -> Self {
        Self {
            selection_list: None,
            from_clause: Vec::new(),
            where_clause: None,
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
pub enum Expr {
    Reference(Identifier),
    Unary(Box<Expr>),
    Binary(Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub enum TypeDef {
    String,
    Integer,
    BigInt,
    Double,
}

#[derive(Debug)]
pub struct ColumnDef {
    name: String,
    data_type: TypeDef,
}

#[derive(Debug)]
pub struct CreateTable {
    name: Identifier,
    columns: Vec<ColumnDef>,
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
                let mut parser = ParserImpl::new(input, tokens.iter().peekable());
                parser.parse_statements()
            }
        }
    }
}

struct ParserImpl<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>> {
    input: &'a str,
    it: Peekable<T>,
}

impl<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>> ParserImpl<'a, T> {
    fn new(input: &'a str, it: Peekable<T>) -> Self {
        Self { input, it }
    }

    fn parse_statements(&mut self) -> Result<Vec<Statement>, String> {
        use lexer::*;

        let mut result: Vec<Statement> = Vec::new();
        while let Some(&c) = self.it.peek() {
            if self.complete_token_and_advance(&ReservedKeyword::Select) {
                result.push(Statement::Select(self.parse_select_body()?));
            } else {
                return Err(format!("unexpected token {:?}", c));
            }
        }
        Ok(result)
    }

    // private methods

    fn get_error_context(&mut self) -> String {
        if let Some(&lexeme) = self.it.peek() {
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
            Err(format!("expected '{:?}'{}", keyword, self.get_error_context()))
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

    fn parse_expr(&mut self) -> Result<Expr, String> {
        if self.complete_substr_and_advance("(") {
            let result = self.parse_expr();
            self.expect_substr_and_advance(")")?;
            result
        } else if let Some(id) = self.parse_identifier() {
            Ok(Expr::Reference(id))
        } else {
            Err(String::from("invalid expression"))
        }
    }

    fn parse_join_item(&mut self) -> Result<JoinItem, String> {
        // @todo parse JoinItem::Join
        if let Some(c) = self.parse_identifier() {
            Ok(JoinItem::TableRef(c))
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
        if self.complete_token_and_advance(&lexer::ReservedKeyword::As) {
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

    fn parse_select_body(&mut self) -> Result<Select, String> {
        let mut select = Select::new();
        if !self.complete_substr_and_advance("*") {
            loop {
                let expr: Expr = self.parse_expr()?;
                let alias: Option<String>;
                if self.complete_token_and_advance(&lexer::ReservedKeyword::As) {
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
                if !self.complete_substr_and_advance(",") {
                    break;
                }
            }
        }

        // mandatory from clause
        self.expect_token_and_advance(&lexer::ReservedKeyword::From)?;
        loop {
            let join_term: JoinTerm = self.parse_join_term()?;
            select.from_clause.push(join_term);
            if !self.complete_substr_and_advance(",") {
                break;
            }
        }

        // where clause
        if self.complete_token_and_advance(&lexer::ReservedKeyword::Where) {
            let expr: Expr = self.parse_expr()?;
            select.where_clause = Some(expr);
        }

        // limit clause
        if self.complete_token_and_advance(&lexer::ReservedKeyword::Limit) {
            let expr: Expr = self.parse_expr()?;
            select.limit_clause = Some(expr);
        }

        Ok(select)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_select() {
        let parser = Parser {};
        assert!(!parser.parse("select a from a").is_err());

        println!("{:?}", parser.parse("select a from a"));
        println!("{:?}", parser.parse("select a, b from a"));
        println!("{:?}", parser.parse("select a, b as c from a"));
        println!("{:?}", parser.parse("select a, b c from a"));
        println!("{:?}", parser.parse("select a from a where c"));
    }
}
