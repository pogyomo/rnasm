use derive_new::new;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use crate::object::Object;

#[derive(new)]
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct SymbolTable {
    #[new(default)]
    table: HashMap<String, Rc<RefCell<Symbol>>>,
}

impl SymbolTable {
    /// Add symbol to symbol table with value. If the symbol already
    /// exist, return true.
    pub fn add(&mut self, name: String, value: Rc<Object>) -> bool {
        let symbol = Symbol::new(value);
        self.table.insert(name, Rc::new(RefCell::new(symbol))).is_some()
    } 

    /// Get name-associated symbol.
    pub fn get(&mut self, name: &str) -> Option<Rc<RefCell<Symbol>>> {
        Some(Rc::clone(self.table.get(name)?))
    }
}

#[derive(new)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    pub value: Rc<Object>,
    #[new(default)]
    childs: HashMap<String, Rc<Object>>,
}

impl Symbol {
    /// Add child to this symbol with value. If the child already
    /// exist, return true.
    pub fn add(&mut self, name: String, value: Rc<Object>) -> bool {
        self.childs.insert(name, value).is_some()
    }

    /// Get the child's value.
    pub fn get(&self, name: &str) -> Option<Rc<Object>> {
        Some(Rc::clone(self.childs.get(name)?))
    }
}
