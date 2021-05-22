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
mod interpreter;

use rustyline::error::ReadlineError;
use rustyline::Editor;

fn main() {
    let mut interpreter = interpreter::Interpreter::new();
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
