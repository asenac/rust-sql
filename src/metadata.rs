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
}

impl TableMetadata {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            columns: Vec::new(),
        }
    }

    pub fn add_column(&mut self, name: &str) {
        self.columns.push(ColumnMetadata {
            name: name.to_string(),
            data_type: DataType::String,
        });
    }
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
}

impl MetadataCatalog for FakeCatalog {
    fn get_table(&self, name: &str) -> Option<&TableMetadata> {
        self.tables.get(name)
    }
}
