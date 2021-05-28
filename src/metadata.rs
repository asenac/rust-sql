use crate::ast;
use std::collections::*;

#[derive(Clone, Debug)]
pub enum DataType {
    String,
    Integer,
    BigInt,
    Double,
}

#[derive(Clone, Debug)]
pub struct ColumnMetadata {
    pub name: String,
    pub data_type: DataType,
}

#[derive(Clone, Debug)]
pub struct TableMetadata {
    pub name: String,
    pub columns: Vec<ColumnMetadata>,
    pub indexes: Vec<Index>,
}

impl TableMetadata {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            columns: Vec::new(),
            indexes: Vec::new(),
        }
    }

    pub fn add_column(&mut self, name: &str) {
        self.columns.push(ColumnMetadata {
            name: name.to_string(),
            data_type: DataType::String,
        });
    }
}

#[derive(Clone, Debug)]
pub struct Index {
    pub name: String,
    pub unique: bool,
    pub columns: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct View {
    pub name: String,
    pub columns: Option<Vec<String>>,
    pub select: ast::QueryBlock,
}

#[derive(Clone, Debug)]
pub enum CatalogItem {
    Table(TableMetadata),
    View(View),
}

/// interface for resolving metadata definitions
pub trait MetadataCatalog {
    fn find_table(&self, name: &str) -> Option<&TableMetadata>;

    fn get_table(&self, name: &str) -> Result<&TableMetadata, String> {
        if let Some(table) = self.find_table(name) {
            Ok(table)
        } else {
            Err(format!("table {} not found", name))
        }
    }
}

/// fake metadata catalog used for testing
pub struct FakeCatalog {
    tables: HashMap<String, TableMetadata>,
}

impl FakeCatalog {
    pub fn new() -> Self {
        Self {
            tables: HashMap::new(),
        }
    }

    pub fn add_table(&mut self, table: TableMetadata) {
        self.tables.insert(table.name.clone(), table);
    }

    pub fn drop_table(&mut self, table: &TableMetadata) {
        self.tables.remove(&table.name);
    }
}

impl MetadataCatalog for FakeCatalog {
    fn find_table(&self, name: &str) -> Option<&TableMetadata> {
        self.tables.get(name)
    }
}

pub trait FromCreateStatement<N> {
    fn from_create(node: &N) -> Self;
}

impl FromCreateStatement<ast::CreateTable> for TableMetadata {
    fn from_create(c: &ast::CreateTable) -> Self {
        let mut metadata = Self::new(c.name.get_name());
        for c in &c.columns {
            metadata.add_column(&c.name);
        }
        metadata
    }
}

impl FromCreateStatement<ast::View> for View {
    fn from_create(c: &ast::View) -> Self {
        View {
            name: c.name.clone(),
            columns: c.columns.clone(),
            select: c.select.clone(),
        }
    }
}
