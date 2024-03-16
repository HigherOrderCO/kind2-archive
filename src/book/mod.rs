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

// Maps short names ("cons") to full names ("List/cons")
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
  pub fn boot(base: &str, name: &str) -> Result<Self, String> {
    let mut book = Book::new();
    book.load(base, name)?;
    book.load(base, "String")?;
    book.load(base, "String/cons")?;
    book.load(base, "String/nil")?;
    book.load(base, "Nat")?;
    book.load(base, "Nat/succ")?;
    book.load(base, "Nat/zero")?;
    book.expand_implicits();
    return Ok(book);
  }

  // Handles an unbound definition
  pub fn handle_unbound(&self, file: &str, name: &str) -> Result<(), String> {
    return Err(format!("ERROR\n- unbound: '{}'\n- on_file: {}", name, file));
  }

  // Same as load, mutably adding to a 'book'
  pub fn load(&mut self, base: &str, name: &str) -> Result<(), String> {
    let name = name.trim_end_matches('/'); // last "/" is not part of name
    if !self.defs.contains_key(name) {
      // Parses a file into a new book
      let file = format!("{}/{}.kind2", base, name);
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
          if let Err(_) = self.load(&base, &ref_name) {
            self.handle_unbound(&file, &ref_name)?;
          }
        }
      }
    }
    return Ok(());
  }

  // Desugars all definitions
  pub fn expand_implicits(&mut self) {
    // Creates a map with the implicit count of each top-level definition
    let mut implicit_count = BTreeMap::new();
    for (name, term) in self.defs.iter() {
      implicit_count.insert(name.clone(), term.count_implicits());
    }
    // Expands implicit calls of each top-level definition in the book
    for def in self.defs.iter_mut() {
      def.1.expand_implicits(im::Vector::new(), &implicit_count);
    }
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
