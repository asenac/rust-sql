use std::collections::*;

#[derive(Clone)]
pub enum DataType {
    String,
    Integer,
    BigInt,
    Double,
}

#[derive(Clone)]
pub struct ColumnMetadata {
    pub name: String,
    pub data_type: DataType,
}

#[derive(Clone)]
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

#[derive(Clone)]
pub struct Index {
    pub name: String,
    pub unique: bool,
    pub columns: Vec<usize>,
}

/// interface for resolving metadata definitions
pub trait MetadataCatalog {
    fn get_table(&self, name: &str) -> Option<&TableMetadata>;
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
    fn get_table(&self, name: &str) -> Option<&TableMetadata> {
        self.tables.get(name)
    }
}
