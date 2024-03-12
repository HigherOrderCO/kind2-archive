use crate::{*};

use std::collections::BTreeMap;
use std::collections::BTreeSet;

mod compile;
mod parse;
mod show;

// <book> ::=
//   USE | use <alias> <book>
//   ADT | <adt> <book>
//   ANN | <name> : <term> = <term> <book>
//   DEF | <name> = <term> <book>
//   END | <eof>
#[derive(Clone, Debug)]
pub struct Book {
  pub defs: BTreeMap<String, Term>,
  pub fids: BTreeMap<String, u64>,
}

// Shadows a name on the uses map
pub fn shadow(key: &str, uses: &Uses) -> Uses {
  let mut uses = uses.clone();
  uses.insert(key.to_string(), key.to_string());
  return uses;
}

// Maps short names ("cons") to full names ("Data.List.cons")
pub type Uses = im::HashMap<String, String>;

impl Book {

  // Creates an empty book
  pub fn new() -> Self {
    Book {
      defs: BTreeMap::new(),
      fids: BTreeMap::new(),
    }
  }

  // Creates a book, loading a term, its dependencies, and stdlib
  pub fn boot(name: &str) -> Result<Self, String> {
    let mut book = Book::new();
    book.load(name)?;
    book.load("String")?;
    book.load("String.cons")?;
    book.load("String.nil")?;
    book.load("Nat")?;
    book.load("Nat.succ")?;
    book.load("Nat.zero")?;
    return Ok(book);
  }

  // Handles an unbound definition
  pub fn handle_unbound(&self, file: &str, name: &str) -> Result<(), String> {
    return Err(format!("ERROR\n- unbound: '{}'\n- on_file: {}", name, file));
  }

  // Same as load, mutably adding to a 'book'
  pub fn load(&mut self, name: &str) -> Result<(), String> {
    if !self.defs.contains_key(name) {
      // Parses a file into a new book
      let file = format!("./{}.kind2", name);
      let text = std::fs::read_to_string(&file).map_err(|_| format!("Could not read file: {}", file))?;
      let fid  = self.get_file_id(&file);
      let defs = KindParser::new(&text).parse_book(name, fid)?;
      // Merges new book into book
      for (def_name, def_value) in &defs.defs {
        self.defs.insert(def_name.clone(), def_value.clone());
      }
      // Finds dependencies and loads them
      for (_, def_term) in defs.defs.into_iter() {
        let mut dependencies = BTreeSet::new();
        def_term.get_free_vars(im::Vector::new(), &mut dependencies);
        for ref_name in dependencies {
          if let Err(_) = self.load(&ref_name) {
            self.handle_unbound(&file, &ref_name)?;
          }
        }
      }
    }
    return Ok(());
  }

  // Gets a file id from its name
  pub fn get_file_id(&mut self, name: &str) -> u64 {
    if let Some(id) = self.fids.get(name) {
      *id
    } else {
      let id = self.fids.len() as u64 + 1;
      self.fids.insert(name.to_string(), id);
      id
    }
  }

  // Gets a file name from its id (FIXME: asymptotics)
  pub fn get_file_name(&self, id: u64) -> Option<String> {
    for (name, &fid) in &self.fids {
      if fid == id {
        return Some(name.clone());
      }
    }
    None
  }

}
