use crate::{*};

use std::collections::BTreeMap;
use std::collections::BTreeSet;

mod parse;
mod show;
mod to_hvm1;

// <book> ::=
//   DEF_ANN | <name> : <term> = <term> <book>
//   DEF_VAL | <name> = <term> <book>
//   END     | <eof>
#[derive(Clone, Debug)]
pub struct Book {
  pub defs: BTreeMap<String, Term>,
  pub fids: BTreeMap<String, u64>,
}

impl Book {

  pub fn new() -> Self {
    Book {
      defs: BTreeMap::new(),
      fids: BTreeMap::new(),
    }
  }
  
  pub fn load(name: &str) -> Result<Self, String> {
    fn load_go(name: &str, book: &mut Book) -> Result<(), String> {
      //println!("... {}", name);
      if !book.defs.contains_key(name) {
        let file = format!("./{}.kind2", name);
        let text = std::fs::read_to_string(&file).map_err(|_| format!("Could not read file: {}", file))?;
        let fid  = book.get_file_id(&file);
        //println!("... parsing: {}", name);
        let defs = KindParser::new(&text).parse_book(fid)?;
        //println!("... parsed: {}", name);
        for (def_name, def_value) in &defs.defs {
          book.defs.insert(def_name.clone(), def_value.clone());
        }
        //println!("laoding deps for: {}", name);
        for (_, def_term) in defs.defs.into_iter() {
          let mut dependencies = BTreeSet::new();
          def_term.get_free_vars(im::Vector::new(), &mut dependencies);
          //println!("{} deps: {:?}", name, dependencies);
          for ref_name in dependencies {
            load_go(&ref_name, book)?;
          }
        }
      }
      return Ok(());
    }
    let mut book = Book::new();
    load_go(name, &mut book)?;
    load_go("String", &mut book)?;
    load_go("String.cons", &mut book)?;
    load_go("String.nil", &mut book)?;
    //println!("DONE!");
    Ok(book)
  }

  pub fn get_file_id(&mut self, name: &str) -> u64 {
    if let Some(id) = self.fids.get(name) {
      *id
    } else {
      let id = self.fids.len() as u64 + 1;
      self.fids.insert(name.to_string(), id);
      id
    }
  }

  // FIXME: asymptotics
  pub fn get_file_name(&self, id: u64) -> Option<String> {
    for (name, &fid) in &self.fids {
      if fid == id {
        return Some(name.clone());
      }
    }
    None
  }

}
