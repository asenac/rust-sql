type Res<T> = Result<T, String>;

pub trait Transaction {
    fn commit(self) -> Res<()>;
    fn rollback(self) -> Res<()>;
}

pub trait StorageEngine {
    fn start_transaction(&mut self) -> Res<Box<dyn Transaction>>;
}

//
// Persy as storage engine
//
use persy::{Persy,Config};

pub struct PersyStorageEngine {
    engine: Persy,
}

fn error_to_string<T>(r: Result<T, persy::PersyError>) -> Result<T, String> {
    if r.is_ok() {
        Ok(r.unwrap())
    } else {
        Err(format!("{}", r.err().unwrap()))
    }
}

impl StorageEngine for PersyStorageEngine {
    fn start_transaction(&mut self) -> Res<Box<dyn Transaction>> {
        let tx = error_to_string(self.engine.begin())?;
        Ok(Box::new(PersyTransaction{tx: tx}))
    }
}

pub struct PersyTransaction {
    tx: persy::Transaction
}

impl Transaction for PersyTransaction {
    fn commit(self) -> Res<()> {
        let prepared = error_to_string(self.tx.prepare())?;
        error_to_string(prepared.commit())
    }
    fn rollback(self) -> Res<()> {
        error_to_string(self.tx.rollback())
    }
}
