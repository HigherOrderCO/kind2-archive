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
      for (def_name, def_term) in defs.defs.into_iter() {
        let mut dependencies = BTreeSet::new();
        def_term.get_free_vars(im::Vector::new(), &mut dependencies);
        for ref_name in dependencies {
          if let Err(_) = self.load(&base, &ref_name) {
            // If `ref_name` is an unbound constructor of the ADT `def_term`,
            // we can generate it.
            let maybe_ctr = Term::constructor_code((&def_name, &def_term), &ref_name);

            if let Some(ctr_code) = maybe_ctr {
              let file_name = format!("{}.kind2", ref_name.trim_end_matches('/'));
              let file_path = std::path::Path::new(&file_name);
              let err = || format!("ERROR: could not create file for generated constructor {ref_name}");

              // Create folder structure
              std::fs::create_dir_all(file_path.parent().ok_or_else(err)?).map_err(|_| err())?;
              // Write constructor to its own file.
              // It rewrites the file if it already exists.
              // TODO: If the ADT definition does not type check, the wrong constructor
              //       is still written to its own file. What should I do in this case?
              std::fs::write(&file_name, ctr_code).map_err(|_| err())?;

              self.load(&base, &ref_name)?;
              continue;
            }

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

#[cfg(test)]
mod tests {
  use crate::*;

  #[test]
  /// Test if construction generation matches book
  fn constructor_generation() {
    let book_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("book");
    let book = Book::boot(&book_dir.to_string_lossy(), "Test").unwrap();

    for (_, term) in book.defs.iter() {
      fn extract_adt(t: &Term) -> &Term {
        match t {
          Term::Lam { bod, .. } => extract_adt(bod),
          Term::Ann { val, .. } => extract_adt(val),
          Term::Src { val, .. } => extract_adt(val),
          // Found ADT
          Term::Slf { .. } => t,
          // Couldn't find ADT
          _ => t,
        }
      }

      if let Some(adt) = extract_adt(term).as_adt() {
        let full_name = |adt_name: &str, ctr_name: &str| format!("{adt_name}/{ctr_name}");

        let ctrs: Vec<(&str, &Term)> = adt
          .ctrs
          .iter()
          .map(|ctr| (ctr.name.as_ref(), &book.defs[&full_name(&adt.name, &ctr.name)]))
          .collect();

        for (ctr_name, ctr_term) in ctrs {
          println!("{ctr_name} = {}", ctr_term.show());

          let ctr_ref = full_name(&adt.name, ctr_name);
          let gen_code = Term::constructor_code((&adt.name, term), &ctr_ref).unwrap();
          let gen_term = KindParser::new(&gen_code).parse_def(0, &im::HashMap::new()).unwrap().1;

          // TODO: deal with cases like this:
          // assertion `left == right` failed
          //   left: "λn ~λP λsucc λzero (succ n)"
          //  right: "λpred ~λP λsucc λzero (succ pred)"
          assert_eq!(ctr_term.show(), gen_term.show());
        }
      }
    }
  }
}
