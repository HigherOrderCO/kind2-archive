use crate::{*};

use std::collections::BTreeMap;
use std::collections::BTreeSet;

impl<'i> KindParser<'i> {

  pub fn parse_def(&mut self, fid: u64) -> Result<(String, Term), String> {

    // Top-level datatype
    if self.peek_many(5) == Some("data ") {
      let adt = self.parse_adt(fid)?;
      let mut typ = Term::Set;
      let mut val = Term::new_adt(&adt);
      for (idx_nam, idx_typ) in adt.idxs.iter().rev() {
        typ = Term::All { nam: idx_nam.clone(), inp: Box::new(idx_typ.clone()), bod: Box::new(typ) };
        val = Term::Lam { nam: idx_nam.clone(), bod: Box::new(val) };
      }
      for par_nam in adt.pars.iter().rev() {
        typ = Term::All { nam: par_nam.clone(), inp: Box::new(Term::Set), bod: Box::new(typ) };
        val = Term::Lam { nam: par_nam.clone(), bod: Box::new(val) };
      }
      //println!("NAM: {}", adt.name);
      //println!("TYP: {}", typ.show());
      //println!("VAL: {}", val.show());
      return Ok((adt.name, Term::Ann { chk: false, val: Box::new(val), typ: Box::new(typ) }));
    }

    // Top level definition
    self.skip_trivia();
    let nam = self.parse_name()?;
    self.skip_trivia();

    // Type annotation (optional)
    if self.peek_one() == Some(':') {
      self.consume(":")?;
      let typ = self.parse_term(fid)?;
      self.consume("=")?;
      let val = self.parse_term(fid)?;
      return Ok((nam, Term::Ann { chk: false, val: Box::new(val), typ: Box::new(typ) }));
    }

    // Value (mandatory)
    self.consume("=")?;
    let val = self.parse_term(fid)?;

    return Ok((nam, val));
  }

  pub fn parse_book(&mut self, fid: u64) -> Result<Book, String> {
    let mut book = Book::new();
    while *self.index() < self.input().len() {
      let (name, term) = self.parse_def(fid)?;
      book.defs.insert(name, term);
      self.skip_trivia();
    }
    Ok(book)
  }

}
