use metadata::FromCreateStatement;

use crate::ast;
use crate::metadata;
use crate::metadata::MetadataCatalog;
use crate::query_model;

use std::io::Write;
use std::process::{Child, Command, Stdio};

trait Pager {
    fn sendln(&self, line: String);

    fn wait(&mut self);
}

pub struct PagerProcess {
    child: Child,
}

impl PagerProcess {
    pub fn new(command: String) -> Self {
        let child = Command::new(command).stdin(Stdio::piped()).spawn().unwrap();
        Self { child }
    }
}

impl Pager for PagerProcess {
    fn sendln(&self, line: String) {
        self.child
            .stdin
            .as_ref()
            .unwrap()
            .write(line.as_bytes())
            .unwrap();
    }

    fn wait(&mut self) {
        let _ = self.child.wait();
    }
}

impl Drop for PagerProcess {
    fn drop(&mut self) {
        let _ = self.child.kill();
    }
}

/// simple interpreter to manually test the rewrite engine
pub struct Interpreter {
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
                let mut pager = PagerProcess::new("magic-pager.sh".to_string());
                let generator = query_model::ModelGenerator::new(&self.catalog);
                let model = generator.process(e)?;
                let output = query_model::DotGenerator::new().generate(
                    &model.borrow(),
                    format!("{} (before rewrites)", line).as_str(),
                )?;
                pager.sendln(output);

                query_model::rewrite_model(&model);

                let output = query_model::DotGenerator::new().generate(
                    &model.borrow(),
                    format!("{} (after rewrites)", line).as_str(),
                )?;
                pager.sendln(output);
                pager.wait();
            }
            CreateTable(c) => {
                self.catalog
                    .add_table(metadata::TableMetadata::from_create(c));
            }
            DropTable(c) => {
                let table = self.catalog.get_table(c.name.get_name())?.clone();
                self.catalog.drop_table(&table);
            }
            CreateIndex(c) => {
                let table = self.catalog.get_table(c.tablename.get_name())?;
                let mut cloned = table.clone();
                let mut columns = Vec::new();
                for ic in c.columns.iter() {
                    let mut idx = None;
                    for (i, tc) in cloned.columns.iter().enumerate() {
                        if tc.name == *ic {
                            idx = Some(i);
                            break;
                        }
                    }
                    if let Some(i) = idx {
                        columns.push(i);
                    } else {
                        return Err(format!("column {} not found", ic));
                    }
                }
                cloned.indexes.push(metadata::Index {
                    name: c.name.clone(),
                    unique: c.unique,
                    columns,
                });
                self.catalog.add_table(cloned);
            }
            _ => return Err(format!("unsupported statement: {:?}", stmt)),
        }
        Ok(())
    }
}
