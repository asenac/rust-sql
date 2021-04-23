use std::iter::*;

#[derive(Debug, PartialEq)]
pub enum ReservedKeyword {
    All,
    And,
    As,
    Asc,
    By,
    Case,
    Create,
    Delete,
    Desc,
    Else,
    End,
    Exists,
    False,
    Group,
    Having,
    In,
    Inner,
    Insert,
    Int,
    Into,
    Is,
    From,
    Join,
    Left,
    Limit,
    Not,
    Null,
    On,
    Or,
    Order,
    Outer,
    Right,
    Select,
    Set,
    Table,
    Then,
    True,
    Union,
    Update,
    Values,
    When,
    Where,
}

#[derive(Debug, PartialEq)]
pub enum LexemeType {
    Comma,
    Comment,
    Dot,
    Number,
    Semicolon,
    Symbol,
    Word(String),
    ReservedKeyword(ReservedKeyword),
}

#[derive(Debug)]
pub struct Lexeme<'a> {
    pub type_: LexemeType,
    pub substring: &'a str,
    pub offset: usize,
}

fn consume_number<T: Iterator<Item = (usize, char)>>(iter: &mut Peekable<T>) -> usize {
    let mut len: usize = 0;
    while let Some(&(_, c)) = iter.peek() {
        match c {
            '0'..='9' => {
                iter.next();
                len += 1;
            }
            _ => {
                break;
            }
        }
    }
    len
}

fn consume_word<T: Iterator<Item = (usize, char)>>(iter: &mut Peekable<T>) -> usize {
    let mut len: usize = 0;
    while let Some(&(_, c)) = iter.peek() {
        match c {
            '0'..='9' | 'a'..='z' | 'A'..='Z' | '_' => {
                iter.next();
                len += 1;
            }
            _ => {
                break;
            }
        }
    }
    len
}

fn get_reserved_keyword(input: &str) -> Option<ReservedKeyword> {
    use ReservedKeyword::*;
    match input {
        "AND" => Some(And),
        "AS" => Some(As),
        "ASC" => Some(Asc),
        "BY" => Some(By),
        "CASE" => Some(Case),
        "CREATE" => Some(Create),
        "DELETE" => Some(Delete),
        "DESC" => Some(Desc),
        "ELSE" => Some(Else),
        "END" => Some(End),
        "EXISTS" => Some(Exists),
        "FALSE" => Some(False),
        "GROUP" => Some(Group),
        "HAVING" => Some(Having),
        "IN" => Some(In),
        "INNER" => Some(Inner),
        "INSERT" => Some(Insert),
        "INT" => Some(Int),
        "INTO" => Some(Into),
        "IS" => Some(Is),
        "FROM" => Some(From),
        "JOIN" => Some(Join),
        "LEFT" => Some(Left),
        "LIMIT" => Some(Limit),
        "NOT" => Some(Not),
        "NULL" => Some(Null),
        "ON" => Some(On),
        "OR" => Some(Or),
        "ORDER" => Some(Order),
        "OUTER" => Some(Outer),
        "RIGHT" => Some(Right),
        "SELECT" => Some(Select),
        "SET" => Some(Set),
        "TABLE" => Some(Table),
        "THEN" => Some(Then),
        "TRUE" => Some(True),
        "UPDATE" => Some(Update),
        "VALUES" => Some(Values),
        "WHEN" => Some(When),
        "WHERE" => Some(Where),
        _ => None,
    }
}

fn build_word<'a>(input: &'a str) -> LexemeType {
    let uppercase = input.to_uppercase().to_string();
    let reserved_keyword = get_reserved_keyword(&uppercase);
    if let Some(c) = reserved_keyword {
        LexemeType::ReservedKeyword(c)
    } else {
        LexemeType::Word(uppercase)
    }
}

pub fn lex<'a>(input: &'a str) -> Result<Vec<Lexeme<'a>>, String> {
    use LexemeType::*;

    let mut result = Vec::new();
    let mut it = input.chars().enumerate().peekable();
    while let Some(&(i, c)) = it.peek() {
        match c {
            '0'..='9' => {
                let len = consume_number(&mut it);
                result.push(Lexeme {
                    type_: Number,
                    substring: &input[i..i + len],
                    offset: i,
                });
            }
            'a'..='z' | 'A'..='Z' => {
                let len = consume_word(&mut it);
                let substring = &input[i..i + len];
                result.push(Lexeme {
                    type_: build_word(substring),
                    substring: substring,
                    offset: i,
                });
            }
            '*' | '+' | '-' | '/' | '=' | '(' | ')' | '?' | '<' | '>' | '!' => {
                let len = symbol_length(&mut it)?;
                result.push(Lexeme {
                    type_: Symbol,
                    substring: &input[i..i + len],
                    offset: i,
                });
            }
            ' ' | '\n' => {
                it.next();
            }
            ',' => {
                it.next();
                let len = 1;
                result.push(Lexeme {
                    type_: Comma,
                    substring: &input[i..i + len],
                    offset: i,
                });
            }
            ';' => {
                it.next();
                let len = 1;
                result.push(Lexeme {
                    type_: Semicolon,
                    substring: &input[i..i + len],
                    offset: i,
                });
            }
            '.' => {
                it.next();
                let len = 1;
                result.push(Lexeme {
                    type_: Dot,
                    substring: &input[i..i + len],
                    offset: i,
                });
            }
            _ => {
                return Err(format!("unexpected character {}", c));
            }
        }
    }
    Ok(result)
}

fn symbol_length<T: Iterator<Item = (usize, char)>>(it: &mut Peekable<T>) -> Result<usize, String> {
    let mut len: usize = 1;
    let (_, c) = *it.peek().unwrap();
    it.next();
    if let Some((_, n)) = it.peek() {
        match (c, n) {
            ('>', '=') | ('<', '=') | ('!', '=') => {
                it.next();
                len = len + 1;
            }
            ('!', _) => {
                return Err(format!("unexpected character {}", n));
            }
            _ => (),
        }
    }
    Ok(len)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_consume_number() {
        let str_num = "123213 12-45";
        let mut it = str_num.chars().enumerate().peekable();
        assert_eq!(consume_number(&mut it), 6);
        assert_eq!(it.peek(), Some(&(6, ' ')));
        it.next();
        assert_eq!(consume_number(&mut it), 2);
        assert_eq!(it.peek(), Some(&(9, '-')));
        it.next();
        assert_eq!(consume_number(&mut it), 2);
        assert_eq!(it.peek(), None);
    }

    #[test]
    fn test_lex() {
        use LexemeType::*;

        let result = lex("123213 * 12-45 + ASENAC");
        assert!(result.is_ok());
        let vec = result.unwrap();
        assert_eq!(vec.len(), 7);
        assert_eq!(vec[0].type_, Number);
        assert_eq!(vec[1].type_, Symbol);
        assert_eq!(vec[2].type_, Number);
        assert_eq!(vec[3].type_, Symbol);
        assert_eq!(vec[4].type_, Number);
        assert_eq!(vec[5].type_, Symbol);
        assert_eq!(vec[6].type_, Word(String::from("ASENAC")));
    }

    #[test]
    fn test_symbols() {
        let result = lex("!= >= > < <= =");
        println!("{:?}", result);
    }
}
