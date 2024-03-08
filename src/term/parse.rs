use crate::{*};

impl<'i> KindParser<'i> {

  pub fn parse_oper(&mut self) -> Result<Oper, String> {
    self.skip_trivia();
    match self.peek_one() {
      Some('+') => { self.advance_one(); Ok(Oper::Add) }
      Some('-') => { self.advance_one(); Ok(Oper::Sub) }
      Some('*') => { self.advance_one(); Ok(Oper::Mul) }
      Some('/') => { self.advance_one(); Ok(Oper::Div) }
      Some('%') => { self.advance_one(); Ok(Oper::Mod) }
      Some('=') => { self.consume("==")?; Ok(Oper::Eq) }
      Some('!') => { self.consume("!=")?; Ok(Oper::Ne) }
      Some('<') => {
        match self.peek_many(2) {
          Some("<=") => { self.advance_many(2); Ok(Oper::Lte) }
          Some("<<") => { self.advance_many(2); Ok(Oper::Lsh) }
          _ => { self.advance_one(); Ok(Oper::Lt) }
        }
      }
      Some('>') => {
        match self.peek_many(2) {
          Some(">=") => { self.advance_many(2); Ok(Oper::Gte) }
          Some(">>") => { self.advance_many(2); Ok(Oper::Rsh) }
          _ => { self.advance_one(); Ok(Oper::Gt) }
        }
      }
      Some('&') => { self.advance_one(); Ok(Oper::And) }
      Some('|') => { self.advance_one(); Ok(Oper::Or) }
      Some('^') => { self.advance_one(); Ok(Oper::Xor) }
      _ => self.expected("operator"),
    }
  }

  pub fn parse_term(&mut self, fid: u64) -> Result<Term, String> {
    self.skip_trivia();
    match self.peek_one() {
      Some('∀') => {
        let ini = *self.index() as u64;
        self.consume("∀")?;
        self.consume("(")?;
        let nam = self.parse_name()?;
        self.consume(":")?;
        let inp = Box::new(self.parse_term(fid)?);
        self.consume(")")?;
        let bod = Box::new(self.parse_term(fid)?);
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::All { nam, inp, bod }) })
      }
      Some('λ') => {
        let ini = *self.index() as u64;
        self.consume("λ")?;
        let nam = self.parse_name()?;
        let bod = Box::new(self.parse_term(fid)?);
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Lam { nam, bod }) })
      }
      Some('(') => {
        let ini = *self.index() as u64;
        self.consume("(")?;
        let fun = Box::new(self.parse_term(fid)?);
        let mut args = Vec::new();
        while self.peek_one() != Some(')') {
          args.push(Box::new(self.parse_term(fid)?));
          self.skip_trivia();
        }
        self.consume(")")?;
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        let mut app = fun;
        for arg in args {
          app = Box::new(Term::App { fun: app, arg });
        }
        Ok(Term::Src { src, val: app })
      }
      Some('{') => {
        let ini = *self.index() as u64;
        self.consume("{")?;
        let val = Box::new(self.parse_term(fid)?);
        self.consume(":")?;
        let typ = Box::new(self.parse_term(fid)?);
        self.consume("}")?;
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Ann { chk: true, val, typ }) })
      }
      Some('$') => {
        let ini = *self.index() as u64;
        self.consume("$")?;
        self.consume("(")?;
        let nam = self.parse_name()?;
        self.consume(":")?;
        let typ = Box::new(self.parse_term(fid)?);
        self.consume(")")?;
        let bod = Box::new(self.parse_term(fid)?);
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Slf { nam, typ, bod }) })
      }
      Some('~') => {
        let ini = *self.index() as u64;
        self.consume("~")?;
        let val = Box::new(self.parse_term(fid)?);
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Ins { val }) })
      }
      Some('*') => {
        let ini = *self.index() as u64;
        self.consume("*")?;
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Set) })
      }
      Some('#') => {
        let ini = *self.index() as u64;
        self.consume("#")?;
        match self.peek_one() {
          Some('U') => {
            self.consume("U60")?;
            let end = *self.index() as u64;
            let src = Src::new(fid, ini, end);
            Ok(Term::Src { src, val: Box::new(Term::U60) })
          }
          Some('(') => {
            self.consume("(")?;
            let opr = self.parse_oper()?;
            let fst = Box::new(self.parse_term(fid)?);
            let snd = Box::new(self.parse_term(fid)?);
            self.consume(")")?;
            let end = *self.index() as u64;
            let src = Src::new(fid, ini, end);
            Ok(Term::Src { src, val: Box::new(Term::Op2 { opr, fst, snd }) })
          }
          Some('m') => {
            self.consume("match")?;
            let nam = self.parse_name()?;
            self.consume("=")?;
            let x = Box::new(self.parse_term(fid)?);
            self.consume("{")?;
            self.consume("#0")?;
            self.consume(":")?;
            let z = Box::new(self.parse_term(fid)?);
            self.consume("#+")?;
            self.consume(":")?;
            let s = Box::new(self.parse_term(fid)?);
            self.consume("}")?;
            self.consume(":")?;
            let p = Box::new(self.parse_term(fid)?);
            let end = *self.index() as u64;
            let src = Src::new(fid, ini, end);
            Ok(Term::Src { src, val: Box::new(Term::Mat { nam, x, z, s, p }) })
          }
          Some(_) => {
            let val = self.parse_u64()?;
            let end = *self.index() as u64;
            let src = Src::new(fid, ini, end);
            Ok(Term::Src { src, val: Box::new(Term::Num { val }) })
          }
          _ => {
            self.expected("numeric-expression")
          }
        }
      }
      Some('?') => {
        let ini = *self.index() as u64;
        self.consume("?")?;
        let nam = self.parse_name()?;
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Hol { nam }) })
      }
      Some('_') => {
        let ini = *self.index() as u64;
        self.consume("_")?;
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Met {}) })
      }
      Some('\'') => {
        let ini = *self.index() as u64;
        let chr = self.parse_quoted_char()?;
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Num { val: chr as u64 }) })
      }
      Some('"') => {
        let ini = *self.index() as u64;
        let txt = self.parse_quoted_string()?;
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Txt { txt }) })
      }
      _ => {
        if self.peek_many(4) == Some("let ") {
          let ini = *self.index() as u64;
          self.advance_many(4);
          let nam = self.parse_name()?;
          self.consume("=")?;
          let val = Box::new(self.parse_term(fid)?);
          let bod = Box::new(self.parse_term(fid)?);
          let end = *self.index() as u64;
          let src = Src::new(fid, ini, end);
          Ok(Term::Src { src, val: Box::new(Term::Let { nam, val, bod }) })
        } else if self.peek_many(4) == Some("use ") {
          let ini = *self.index() as u64;
          self.advance_many(4);
          let nam = self.parse_name()?;
          self.consume("=")?;
          let val = Box::new(self.parse_term(fid)?);
          let bod = Box::new(self.parse_term(fid)?);
          let end = *self.index() as u64;
          let src = Src::new(fid, ini, end);
          Ok(Term::Src { src, val: Box::new(Term::Use { nam, val, bod }) })
        } else {
          let ini = *self.index() as u64;
          let nam = self.parse_name()?;
          let end = *self.index() as u64;
          let src = Src::new(fid, ini, end);
          Ok(Term::Src { src, val: Box::new(Term::Var { nam }) })
        }
      }
    }
  }

}
