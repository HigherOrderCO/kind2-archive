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

  pub fn parse_term(&mut self, fid: u64, uses: &Uses) -> Result<Term, String> {
    self.skip_trivia();
    //println!("parsing ||{}", self.input[self.index..].replace("\n",""));

    // ALL ::= ∀(<name>: <term>) <term>
    if self.starts_with("∀") {
      let ini = *self.index() as u64;
      self.consume("∀")?;
      self.consume("(")?;
      let nam = self.parse_name()?;
      self.consume(":")?;
      let inp = Box::new(self.parse_term(fid, uses)?);
      self.consume(")")?;
      let bod = Box::new(self.parse_term(fid, &shadow(&nam, uses))?);
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::All { nam, inp, bod }) });
    }

    // LAM ::= λ<name> <term>
    if self.starts_with("λ") {
      let ini = *self.index() as u64;
      self.consume("λ")?;
      let nam = self.parse_name()?;
      let bod = Box::new(self.parse_term(fid, &shadow(&nam, uses))?);
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Lam { nam, bod }) });
    }

    // APP ::= (<term> <term>)
    if self.starts_with("(") {
      let ini = *self.index() as u64;
      self.consume("(")?;
      let fun = Box::new(self.parse_term(fid, uses)?);
      let mut args = Vec::new();
      while self.peek_one() != Some(')') {
        args.push(Box::new(self.parse_term(fid, uses)?));
        self.skip_trivia();
      }
      self.consume(")")?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      let mut app = fun;
      for arg in args {
        app = Box::new(Term::App { fun: app, arg });
      }
      return Ok(Term::Src { src, val: app });
    }

    // ANN ::= {<term>: <term>}
    if self.starts_with("{") {
      let ini = *self.index() as u64;
      self.consume("{")?;
      let val = Box::new(self.parse_term(fid, uses)?);
      self.consume(":")?;
      let typ = Box::new(self.parse_term(fid, uses)?);
      self.consume("}")?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Ann { chk: true, val, typ }) });
    }

    // SLF ::= $(<name>: <term>) <term>
    if self.starts_with("$") {
      let ini = *self.index() as u64;
      self.consume("$")?;
      self.consume("(")?;
      let nam = self.parse_name()?;
      self.consume(":")?;
      let typ = Box::new(self.parse_term(fid, uses)?);
      self.consume(")")?;
      let bod = Box::new(self.parse_term(fid, &shadow(&nam, uses))?);
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Slf { nam, typ, bod }) });
    }

    // INS ::= ~<term>
    if self.starts_with("~") {
      let ini = *self.index() as u64;
      self.consume("~")?;
      let val = Box::new(self.parse_term(fid, uses)?);
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Ins { val }) });
    }

    // SET ::= *
    if self.starts_with("*") {
      let ini = *self.index() as u64;
      self.consume("*")?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Set) });
    }

    // U60 ::= #U60
    if self.starts_with("#U60") {
      let ini = *self.index() as u64;
      self.consume("#U60")?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::U60) });
    }

    // OP2 ::= #(<oper> <term> <term>)
    if self.starts_with("#(") {
      let ini = *self.index() as u64;
      self.consume("#(")?;
      let opr = self.parse_oper()?;
      let fst = Box::new(self.parse_term(fid, uses)?);
      let snd = Box::new(self.parse_term(fid, uses)?);
      self.consume(")")?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Op2 { opr, fst, snd }) });
    }

    // MAT ::= #match <name> = <term> { #0: <term>; #+: <term> }: <term>
    // - The matched term is optional. Defaults to `Var { nam: <name> }`.
    // - The return type is optional. Defaults to `Met {}`.
    if self.starts_with("#match") {
      let ini = *self.index() as u64;
      self.consume("#match")?;
      let nam = self.parse_name()?;
      self.skip_trivia();
      let x = if self.peek_one() == Some('=') {
        self.consume("=")?;
        Box::new(self.parse_term(fid, uses)?)
      } else {
        Box::new(Term::Var { nam: nam.clone() })
      };
      self.consume("{")?;
      self.consume("#0")?;
      self.consume(":")?;
      let z = Box::new(self.parse_term(fid, uses)?);
      self.consume("#+")?;
      self.consume(":")?;
      let s = Box::new(self.parse_term(fid, &shadow(&format!("{}-1",nam), uses))?);
      self.consume("}")?;
      let p = if self.peek_one() == Some(':') {
        self.consume(":")?;
        Box::new(self.parse_term(fid, &shadow(&nam, uses))?)
      } else {
        Box::new(Term::Met {})
      };
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Mat { nam, x, z, s, p }) });
    }

    // NUM ::= #<uint>
    if self.starts_with("#") {
      let ini = *self.index() as u64;
      self.advance_one();
      let val = self.parse_u64()?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Num { val }) });
    }

    // HOL ::= ?<name>
    if self.starts_with("?") {
      let ini = *self.index() as u64;
      self.advance_one();
      let nam = self.parse_name()?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Hol { nam }) });
    }

    // MET ::= _
    if self.starts_with("_") {
      let ini = *self.index() as u64;
      self.advance_one();
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Met {}) });
    }

    // TXT ::= "<string>"
    if self.starts_with("\"") {
      let ini = *self.index() as u64;
      let txt = self.parse_quoted_string()?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Txt { txt }) });
    }

    // LET ::= let <name> = <term> <term>
    if self.starts_with("let ") {
      let ini = *self.index() as u64;
      self.consume("let ")?;
      let nam = self.parse_name()?;
      self.consume("=")?;
      let val = Box::new(self.parse_term(fid, uses)?);
      let bod = Box::new(self.parse_term(fid, &shadow(&nam, uses))?);
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Let { nam, val, bod }) });
    }

    // USE ::= use <name> = <term> <term>
    if self.starts_with("use ") {
      let ini = *self.index() as u64;
      self.consume("use ")?;
      let nam = self.parse_name()?;
      self.consume("=")?;
      let val = Box::new(self.parse_term(fid, uses)?);
      let bod = Box::new(self.parse_term(fid, &shadow(&nam, uses))?);
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Use { nam, val, bod }) });
    }

    // CHR ::= '<char>'
    if self.starts_with("'") {
      let ini = *self.index() as u64;
      let chr = self.parse_quoted_char()?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Num { val: chr as u64 }) });
    }

    // LST ::= [ <term> , ... ]
    if self.starts_with("[") {
      let ini = *self.index() as u64;
      let lst = self.parse_list(fid, uses)?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      let val = Box::new(Term::new_list(&lst));
      return Ok(Term::Src { src, val });
    }

    // NAT ::= <uint>
    if self.peek_one().map_or(false, |c| c.is_ascii_digit()) {
      let ini = *self.index() as u64;
      let nat = self.parse_u64()?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      let val = Box::new(Term::new_nat(nat));
      return Ok(Term::Src { src, val });
    }

    // ADT ::= data <name> <name> ... (<name> : <term>) ...
    // | <name> (<name> : <term>) ... : (<Type> <Params> ... <term> ...)
    // | ...
    if self.starts_with("data ") {
      let ini = *self.index() as u64;
      let adt = self.parse_adt(fid, uses)?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::new_adt(&adt)) });
    }

    // MAT ::= match <name> = <term> { <name> : <term> <...> }: <term>
    if self.starts_with("match ") {
      let ini = *self.index() as u64;
      let mch = self.parse_match(fid, uses)?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Mch { mch: Box::new(mch) }) });
      //return Ok(Term::Src { src, val: Box::new(Term::new_match(&mch)) });
    }

    // VAR ::= <name>
    let ini = *self.index() as u64;
    let old = self.parse_name()?;
    let nam = uses.get(&old).unwrap_or(&old).to_string();
    //if old != nam { println!("{} -> {}", old, nam); }
    let end = *self.index() as u64;
    let src = Src::new(fid, ini, end);
    return Ok(Term::Src { src, val: Box::new(Term::Var { nam }) });

  }

  // Parses a name that can be aliased (via the 'uses' map)
  //pub fn parse_nick(&mut self, uses: &Uses) -> Result<String, String> {
    //let nam = self.parse_name()?;
    //Ok(uses.get(&nam).cloned().unwrap_or(nam))
  //}

}
