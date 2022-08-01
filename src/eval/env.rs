#![allow(dead_code)]

use std::{cell::RefCell, collections::HashMap};
use super::object::Object;

pub struct Environment {
    idents: RefCell<HashMap<String, Object>>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment { idents: RefCell::new(HashMap::new()) }
    }

    pub fn reg(&self, name: String, obj: Object) {
        self.idents.borrow_mut().insert(name, obj);
    }

    pub fn get(&self, name: &String) -> Option<Object> {
        Some(self.idents.borrow().get(name)?.clone())
    }
}
