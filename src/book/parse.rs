use crate::{*};

use std::collections::BTreeMap;
use std::collections::BTreeSet;

impl<'i> KindParser<'i> {

  // Parses a top-level use-declaration
  fn parse_use(&mut self, fid: u64, nam: String, uses: &mut Uses) -> Result<(), String> {
    self.skip_trivia();
    let add = self.parse_name()?;
    self.skip_trivia();
    let nam = format!("{}{}", nam, add);
    if self.peek_one() == Some('{') {
      self.consume("{")?;
      self.skip_trivia();
      loop {
        self.parse_use(fid, nam.clone(), uses)?;
        self.skip_trivia();
        match self.peek_one() {
          Some(',') => { self.consume(",")?; continue; }
          Some('}') => { self.consume("}")?; break; }
          _         => { return self.expected("comma (`,`) or semicolon (`;`)"); }
        }
      }
    } else {
      let pts = nam.split('.').collect::<Vec<&str>>();
      let key = pts.last().unwrap().to_string();
      //println!("use {} ~> {}", key, nam);
      uses.insert(key, nam);
    }
    return Ok(());
  }

  // Parses many top-level use-declarations
  fn parse_uses(&mut self, fid: u64) -> Result<Uses, String> {
    let mut uses = im::HashMap::new();
    self.skip_trivia();
    while self.peek_many(4) == Some("use ") {
      self.consume("use")?;
      self.parse_use(fid, String::new(), &mut uses)?;
      self.skip_trivia();
    }
    return Ok(uses);
  }

  // Parses a top-level definition (datatype or term)
  pub fn parse_def(&mut self, fid: u64, uses: &Uses) -> Result<(String, Term), String> {
    // Top-level datatype
    if self.peek_many(5) == Some("data ") {
      let adt = self.parse_adt(fid, uses)?;
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
    let nam = uses.get(&nam).unwrap_or(&nam).to_string();
    self.skip_trivia();

    // Parameters (optional)
    let mut pars = vec![];
    while self.peek_one().map_or(false, |c| c.is_ascii_alphabetic()) {
      let par = self.parse_name()?;
      self.skip_trivia();
      pars.push(par);
    }

    // Arguments (optional)
    let mut args = vec![];
    while self.peek_one() == Some('(') {
      self.consume("(")?;
      let arg_name = self.parse_name()?;
      self.consume(":")?;
      let arg_type = self.parse_term(fid, uses)?;
      self.consume(")")?;
      args.push((arg_name, arg_type));
      self.skip_trivia();
    }

    // Type annotation (optional)
    let mut typ;
    if self.peek_one() == Some(':') {
      self.consume(":")?;
      typ = self.parse_term(fid, uses)?;
    } else {
      typ = Term::Met {};
    }

    // Value (mandatory)
    self.consume("=")?;
    let mut val = self.parse_term(fid, uses)?;

    // Adds arguments to val/typ
    for (arg_nam, arg_typ) in args.iter().rev() {
      typ = Term::All { nam: arg_nam.clone(), inp: Box::new(arg_typ.clone()), bod: Box::new(typ.clone()) };
      val = Term::Lam { nam: arg_nam.clone(), bod: Box::new(val.clone()) };
    }

    // Adds parameters to val/typ
    for par in pars.iter().rev() {
      typ = Term::All { nam: par.clone(), inp: Box::new(Term::Met{}), bod: Box::new(typ.clone()) };
      val = Term::Lam { nam: par.clone(), bod: Box::new(val.clone()) };
    }

    //println!("- def: {}", nam);
    //println!("- typ: {}", typ.show());
    //println!("- val: {}", val.show());

    return Ok((nam, Term::Ann { chk: false, val: Box::new(val), typ: Box::new(typ) }));
  }

  pub fn parse_book(&mut self, name: &str, fid: u64) -> Result<Book, String> {
    let mut book = Book::new();
    let mut uses = self.parse_uses(fid)?;
    // Adds the default 'use Path.to.file'
    uses.insert(name.split('.').last().unwrap().to_string(), name.to_string());
    while *self.index() < self.input().len() {
      let (name, term) = self.parse_def(fid, &mut uses)?;
      book.defs.insert(name, term);
      self.skip_trivia();
    }
    Ok(book)
  }

}
