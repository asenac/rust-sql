use std::iter::*;

pub enum Statement {
    Select(Select),
    CreateTable(CreateTable),
}

pub struct Identifier {
    parts: Vec<String>,
}

pub struct SelectItem {
    expr: Expr,
    alias: Option<String>
}

pub enum JoinType {
    Inner, LeftOuter, RightOuter
}

pub enum JoinItem {
    TableRef(Identifier),
    Join(JoinType, Box<JoinTerm>, Box<JoinTerm>),
    DerivedTable(Select)
}

pub struct JoinTerm {
    join_item: JoinItem,
    alias: Option<String>
}

pub struct Select {
    selection_list: Option<Vec<SelectItem>>,
    from_clause: Vec<JoinTerm>,
    where_clause: Option<Expr>,
    limit_clause: Option<Expr>
}

impl Select {
    fn new() -> Self {
        Self {
            selection_list: None,
            from_clause: Vec::new(),
            where_clause: None,
            limit_clause: None
        }
    }

    fn add_select_item(&mut self, item: SelectItem) {
        if self.selection_list.is_none() {
            self.selection_list = Some(Vec::new());
        }
        self.selection_list.as_mut().unwrap().push(item);
    }
}

pub enum Expr {
    Reference(Identifier),
    Unary(Box<Expr>),
    Binary(Box<Expr>, Box<Expr>)
}

pub enum TypeDef {
    String,
    Integer,
    BigInt,
    Double,
}

pub struct ColumnDef {
    name: String,
    data_type: TypeDef,
}

pub struct CreateTable {
    name: Identifier,
    columns: Vec<ColumnDef>,
}

pub struct Parser {}

use crate::lexer;

impl Parser {

    pub fn new() -> Parser {
        Parser {}
    }

    // parser
    pub fn parse(&self, input: &str) -> Result<Vec<Statement>, String> {
        match lexer::lex(input) {
            Err(c) => Err(c),
            Ok(tokens) => self.parse_statements(&tokens),
        }
    }

    // private methods

    fn complete_substr_and_advance<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>,
        symbol: &str
    ) -> bool {
        if let Some(&lexeme) = it.peek() {
            if lexeme.substring == symbol {
                it.next();
                return true;
            }
        }
        false
    }

    fn expect_substr_and_advance<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>,
        symbol: &str
    ) -> Result<(), String> {
        if self.complete_substr_and_advance(it, symbol) {
            Ok(())
        } else {
            Err(format!("expected '{}'", symbol))
        }
    }

    fn complete_token_and_advance<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>,
        keyword: &lexer::ReservedKeyword
    ) -> bool {
        if let Some(&lexeme) = it.peek() {
            if let lexer::LexemeType::ReservedKeyword(s) = &lexeme.type_ {
                if *keyword == *s {
                    it.next();
                    return true;
                }
            }
        }
        false
    }

    fn expect_token_and_advance<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>,
        keyword: &lexer::ReservedKeyword
    ) -> Result<(), String> {
        if self.complete_token_and_advance(it, keyword) {
            Ok(())
        } else {
            Err(format!("expected '{:?}'", keyword))
        }
    }

    fn parse_name<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>
    ) -> Option<String> {
        if let Some(&lexeme) = it.peek() {
            if let lexer::LexemeType::Word(s) = &lexeme.type_ {
                return Some(s.clone());
            }
        }
        None
    }

    fn parse_identifier<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>
    ) -> Option<Identifier> {
        let mut identifier : Option<Identifier> = None;
        while let Some(part) = self.parse_name(it) {
            if !identifier.is_some() {
                identifier = Some(Identifier{parts: Vec::new()});
            }
            identifier.as_mut().unwrap().parts.push(part);
            if !self.complete_substr_and_advance(it, ".") {
                break;
            }
        }
        identifier
    }

    fn parse_expr<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>
    ) -> Result<Expr, String> {
        if self.complete_substr_and_advance(it, "(") {
            let result = self.parse_expr(it);
            self.expect_substr_and_advance(it, ")")?;
            result
        } else if let Some(id) = self.parse_identifier(it) {
            Ok(Expr::Reference(id))
        } else {
            Err(String::from("invalid expression"))
        }
    }

    fn parse_join_item<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>
    ) -> Result<JoinItem, String> {
        // @todo parse JoinItem::Join
        if let Some(c) = self.parse_identifier(it) {
            Ok(JoinItem::TableRef(c))
        } else if self.complete_substr_and_advance(it, "(") {
            self.expect_token_and_advance(it, &lexer::ReservedKeyword::Select)?;
            let select = self.parse_select_body(it)?;
            self.expect_substr_and_advance(it, ")")?;
            Ok(JoinItem::DerivedTable(select))
        } else {
            Err(String::from("invalid join term"))
        }
    }

    fn parse_join_term<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>
    ) -> Result<JoinTerm, String> {
        let join_item : JoinItem = self.parse_join_item(it)?;
        let mut alias : Option<String> = None;
        if self.complete_token_and_advance(it, &lexer::ReservedKeyword::As) {
            alias = self.parse_name(it);
            if !alias.is_some() {
                return Err(String::from("expected table alias"));
            }
        }
        Ok(JoinTerm{join_item, alias})
    }

    fn parse_select_body<'a, T: Iterator<Item = &'a lexer::Lexeme<'a>>>(
        &self,
        it : &mut Peekable<T>
    ) -> Result<Select, String> {
        let mut select = Select::new();
        if !self.complete_substr_and_advance(it, "*") {
            loop {
                let expr : Expr = self.parse_expr(it)?;
                let mut alias : Option<String> = None;
                if self.complete_token_and_advance(it, &lexer::ReservedKeyword::As) {
                    alias = self.parse_name(it);
                    if !alias.is_some() {
                        return Err(String::from("expected column alias"));
                    }
                }
                let select_item = SelectItem{expr, alias};
                select.add_select_item(select_item);
                if !self.complete_substr_and_advance(it, ",") {
                    break;
                }
            }
        }

        // mandatory from clause
        self.expect_token_and_advance(it, &lexer::ReservedKeyword::From)?;
        loop {
            let join_term : JoinTerm = self.parse_join_term(it)?;
            select.from_clause.push(join_term);
            if !self.complete_substr_and_advance(it, ",") {
                break;
            }
        }

        // where clause
        if self.complete_token_and_advance(it, &lexer::ReservedKeyword::Where) {
            let expr : Expr = self.parse_expr(it)?;
            select.where_clause = Some(expr);
        }

        // limit clause
        if self.complete_token_and_advance(it, &lexer::ReservedKeyword::Limit) {
            let expr : Expr = self.parse_expr(it)?;
            select.limit_clause = Some(expr);
        }

        Ok(select)
    }

    fn parse_statements(&self, input: &Vec<lexer::Lexeme>) -> Result<Vec<Statement>, String> {
        use lexer::*;

        let mut result: Vec<Statement> = Vec::new();
        let mut it = input.iter().peekable();
        while let Some(&c) = it.peek() {
            if self.complete_token_and_advance(&mut it, &ReservedKeyword::Select) {
                result.push(Statement::Select(self.parse_select_body(&mut it)?));
            } else {
                return Err(format!("unexpected token {:?}", c));
            }
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_select() {
        let parser = Parser{};
        assert!(parser.parse("select a from a").is_err());
        println!("{}", parser.parse("select a from a").err().unwrap())
    }
}
