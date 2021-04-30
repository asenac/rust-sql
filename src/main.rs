// lexer
#[allow(dead_code)]
mod lexer;

// syntax tree and parser
#[allow(dead_code)]
mod ast;

// system metadata
#[allow(dead_code)]
mod metadata;

// query graph model
#[allow(dead_code)]
mod query_model;

// rewrite engine
#[allow(dead_code)]
mod rewrite_engine;

// optimizer

// plan generator

// execution engine

// interpreter

use std::io::Write;
use std::process::{Child, Command, Stdio};

struct Pager {
    child: Child,
}

impl Pager {
    pub fn new(command: String) -> Self {
        let child = Command::new(command).stdin(Stdio::piped()).spawn().unwrap();
        Self { child }
    }

    pub fn sendln(&self, line: String) {
        self.child
            .stdin
            .as_ref()
            .unwrap()
            .write(line.as_bytes())
            .unwrap();
    }

    pub fn wait(&mut self) {
        let _ = self.child.wait();
    }
}

impl Drop for Pager {
    fn drop(&mut self) {
        let _ = self.child.kill();
    }
}

/// simple interpreter to manually test the rewrite engine
struct Interpreter {
    catalog: metadata::FakeCatalog,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            catalog: metadata::FakeCatalog::new(),
        }
    }

    pub fn process_line(&mut self, line: &str) -> Result<(), String> {
        let parser = ast::Parser::new();
        let result = parser.parse(line)?;
        for stmt in result {
            println!("{:?}", stmt);
            // @todo pass substring
            self.process_statement(&stmt, line)?;
        }
        Ok(())
    }

    fn process_statement(&mut self, stmt: &ast::Statement, line: &str) -> Result<(), String> {
        use ast::Statement::*;
        match stmt {
            Select(e) => {
                let mut pager = Pager::new("magic-pager.sh".to_string());
                let mut generator = query_model::ModelGenerator::new(&self.catalog);
                let mut model = generator.process(e)?;
                let output = query_model::DotGenerator::new()
                    .generate(&model, format!("{} (before rewrites)", line).as_str())?;
                pager.sendln(output);

                query_model::rewrite_model(&mut model);

                let output = query_model::DotGenerator::new()
                    .generate(&model, format!("{} (after rewrites)", line).as_str())?;
                pager.sendln(output);
                pager.wait();
            }
            CreateTable(c) => {
                let mut metadata = metadata::TableMetadata::new(c.name.get_name());
                for c in &c.columns {
                    metadata.add_column(&c.name);
                }
                self.catalog.add_table(metadata);
            }
            _ => return Err(format!("unsupported statement: {:?}", stmt)),
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
        let readline = rl.readline("RS-SQL> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                println!("Line: {}", line);
                let result = interpreter.process_line(&line);
                if result.is_err() {
                    println!("Error: {}", result.err().unwrap());
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}
