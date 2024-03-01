use crate::{*};

use std::collections::BTreeMap;
use std::collections::BTreeSet;

impl<'i> KindParser<'i> {

  pub fn parse_def(&mut self, fid: u64) -> Result<(String, Term), String> {
    self.skip_trivia();
    let nam = self.parse_name()?;
    self.skip_trivia();
    if self.peek_one() == Some(':') {
      self.consume(":")?;
      let typ = self.parse_term(fid)?;
      self.consume("=")?;
      let val = self.parse_term(fid)?;
      Ok((nam, Term::Ann { val: Box::new(val), typ: Box::new(typ) }))
    } else {
      self.consume("=")?;
      let val = self.parse_term(fid)?;
      Ok((nam, val))
    }
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
