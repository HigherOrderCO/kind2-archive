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
    //println!("parsing ||{}", self.input[self.index..].replace("\n",""));

    // ALL ::= ∀(<name>: <term>) <term>
    if self.starts_with("∀") {
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
      return Ok(Term::Src { src, val: Box::new(Term::All { nam, inp, bod }) });
    }

    // LAM ::= λ<name> <term>
    if self.starts_with("λ") {
      let ini = *self.index() as u64;
      self.consume("λ")?;
      let nam = self.parse_name()?;
      let bod = Box::new(self.parse_term(fid)?);
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Lam { nam, bod }) });
    }

    // APP ::= (<term> <term>)
    if self.starts_with("(") {
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
      return Ok(Term::Src { src, val: app });
    }

    // ANN ::= {<term>: <term>}
    if self.starts_with("{") {
      let ini = *self.index() as u64;
      self.consume("{")?;
      let val = Box::new(self.parse_term(fid)?);
      self.consume(":")?;
      let typ = Box::new(self.parse_term(fid)?);
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
      let typ = Box::new(self.parse_term(fid)?);
      self.consume(")")?;
      let bod = Box::new(self.parse_term(fid)?);
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Slf { nam, typ, bod }) });
    }

    // INS ::= ~<term>
    if self.starts_with("~") {
      let ini = *self.index() as u64;
      self.consume("~")?;
      let val = Box::new(self.parse_term(fid)?);
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
      let fst = Box::new(self.parse_term(fid)?);
      let snd = Box::new(self.parse_term(fid)?);
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
        Box::new(self.parse_term(fid)?)
      } else {
        Box::new(Term::Var { nam: nam.clone() })
      };
      self.consume("{")?;
      self.consume("#0")?;
      self.consume(":")?;
      let z = Box::new(self.parse_term(fid)?);
      self.consume("#+")?;
      self.consume(":")?;
      let s = Box::new(self.parse_term(fid)?);
      self.consume("}")?;
      let p = if self.peek_one() == Some(':') {
        self.consume(":")?;
        Box::new(self.parse_term(fid)?)
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
      let val = Box::new(self.parse_term(fid)?);
      let bod = Box::new(self.parse_term(fid)?);
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
      let val = Box::new(self.parse_term(fid)?);
      let bod = Box::new(self.parse_term(fid)?);
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
      self.consume("[")?;
      let mut list = Vec::new();
      while self.peek_one() != Some(']') {
        list.push(Box::new(self.parse_term(fid)?));
        self.skip_trivia();
        if self.peek_one() == Some(',') {
          self.consume(",")?;
        }
      }
      self.consume("]")?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      let val = Box::new(Term::new_list(&crate::sugar::list::List { vals: list }));
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

    // Let's now create the ADT parse.
    // ADT ::= data <name> <name> ... (<name> : <term>) ...
    // | <name> (<name> : <term>) ... : (<Type> <Params> ... <term> ...)
    // | ...
    if self.starts_with("data ") {
      let ini = *self.index() as u64;
      self.consume("data ")?;
      let name = self.parse_name()?;
      let mut pars = Vec::new();
      let mut idxs = Vec::new();
      // Parses ADT parameters (if any)
      self.skip_trivia();
      while self.peek_one().map_or(false, |c| c.is_ascii_alphabetic()) {
        let par = self.parse_name()?;
        self.skip_trivia();
        pars.push(par);
      }
      // Parses ADT fields
      while self.peek_one() == Some('(') {
        self.consume("(")?;
        let idx_name = self.parse_name()?;
        self.consume(":")?;
        let idx_type = self.parse_term(fid)?;
        self.consume(")")?;
        idxs.push((idx_name, idx_type));
        self.skip_trivia();
      }
      // Parses ADT constructors
      let mut ctrs = Vec::new();
      self.skip_trivia();
      while self.peek_one() == Some('|') {
        self.consume("|")?;
        let ctr_name = self.parse_name()?;
        let mut flds = Vec::new();
        // Parses constructor fields
        self.skip_trivia();
        while self.peek_one() == Some('(') {
          self.consume("(")?;
          let fld_name = self.parse_name()?;
          self.consume(":")?;
          let fld_type = self.parse_term(fid)?;
          self.consume(")")?;
          flds.push((fld_name, fld_type));
          self.skip_trivia();
        }
        // Parses constructor return
        self.consume(":")?;
        let mut ctr_indices = Vec::new();
        self.consume("(")?;
        // Parses the type (must be fixed, equal to 'name')
        self.consume(&name)?;
        // Parses each parameter (must be fixed, equal to 'pars')
        for par in &pars {
          self.consume(par)?;
        }
        // Parses the indices
        while self.peek_one() != Some(')') {
          let ctr_index = self.parse_term(fid)?;
          ctr_indices.push(ctr_index);
          self.skip_trivia();
        }
        self.consume(")")?;
        ctrs.push(sugar::adt::Constructor { name: ctr_name, flds, idxs: ctr_indices });
        self.skip_trivia();
      }
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      let adt = sugar::adt::ADT { name, pars, idxs, ctrs };
      return Ok(Term::Src { src, val: Box::new(Term::new_adt(adt)) });
    }

    // MAT ::= match <name> = <term> { <name> : <term> <...> }: <term>
    // The ADT match syntax is similar to the numeric match syntax, including the same optionals,
    // but it allows any number of <name>:<term> cases. Also, similarly to the List syntax, there
    // is no built-in "Mat" syntax on the Term type, so we must convert it to an applicative form:
    //   match x = val {
    //     List.cons: x.head
    //     List.nil: #0
    //   }: #U60
    // Would be converted to:
    //   (~val _ (λx.head λx.tail x.tail) 0)
    // Which is the same as:
    //   (APP (APP (APP (INS (VAR "val")) MET) (LAM "x.head" (LAM "x.tail" (VAR "x.head")))) (NUM 0))
    // Note that, in our notation, fields are NOT written by the user. For example, this is WRONG:
    //   match x = val {
    //     (List.cons head tail): head
    //     List.nil: #0
    //   }: #U60
    // Instead, we write only the constructors, and infer the fields from the datatype. To make
    // this possible, we need to FIND the datatype that is currently matched. To do so, we get the
    // first constructor name, remove the last `.part` (ex: `Foo.Bar.Tic.tac` will become
    // `Foo.Bar.Tic`), and call the function `ADT::load(name: &str) -> ADT`. This will return a
    // struct including the type's constructors and fields. We can then use it to create the
    // lambdas when desugaring. For example, in the case above, the `λx.head` and `λx.tail` lambdas
    // were created on the `List.cons` case, because the matched name is `x`, and the cons
    // constructor has a `head` and a `tail` field.
    // (TODO)

    // VAR ::= <name>
    let ini = *self.index() as u64;
    let nam = self.parse_name()?;
    let end = *self.index() as u64;
    let src = Src::new(fid, ini, end);
    return Ok(Term::Src { src, val: Box::new(Term::Var { nam }) });

  }

}
