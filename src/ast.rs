use crate::lexer::*;

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
    join_term: JoinItem,
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
    Reference(String),
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

impl Parser {
    pub fn new() -> Parser {
        Parser {}
    }

    // parser
    pub fn parse(&self, input: &str) -> Result<Vec<Statement>, String> {
        match lex(input) {
            Err(c) => Err(c),
            Ok(tokens) => self.parse_statements(&tokens),
        }
    }

    fn parse_statements(&self, input: &Vec<Lexeme>) -> Result<Vec<Statement>, String> {
        let mut result: Vec<Statement> = Vec::new();
        let mut it = input.iter().peekable();
        while let Some(&c) = it.peek() {
            return Err(format!("unexpected token {:?}", c));
        }
        Ok(result)
    }
}
