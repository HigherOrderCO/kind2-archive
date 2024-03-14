use crate::{*};

impl<'i> KindParser<'i> {

  pub fn parse_oper(&mut self) -> Result<Oper, String> {
    self.skip_trivia();
    if self.peek_one() == Some('+') {
      self.consume("+")?;
      return Ok(Oper::Add);
    }
    if self.peek_one() == Some('-') {
      self.consume("-")?;
      return Ok(Oper::Sub);
    }
    if self.peek_one() == Some('*') {
      self.consume("*")?;
      return Ok(Oper::Mul);
    } 
    if self.peek_one() == Some('/') {
      self.consume("/")?;
      return Ok(Oper::Div);
    }
    if self.peek_one() == Some('%') {
      self.consume("%")?;
      return Ok(Oper::Mod);
    }
    if self.peek_many(2) == Some("==") {
      self.consume("==")?;
      return Ok(Oper::Eq);
    }
    if self.peek_many(2) == Some("!=") {
      self.consume("!=")?;
      return Ok(Oper::Ne); 
    }
    if self.peek_many(2) == Some("<=") {
      self.consume("<=")?;
      return Ok(Oper::Lte);
    }
    if self.peek_many(2) == Some("<<") {
      self.consume("<<")?;
      return Ok(Oper::Lsh);
    }
    if self.peek_one() == Some('<') { 
      self.consume("<")?;
      return Ok(Oper::Lt);
    }
    if self.peek_many(2) == Some(">=") {
      self.consume(">=")?;
      return Ok(Oper::Gte); 
    }
    if self.peek_many(2) == Some(">>") {
      self.consume(">>")?;
      return Ok(Oper::Rsh);
    }
    if self.peek_one() == Some('>') {
      self.consume(">")?;
      return Ok(Oper::Gt);
    }
    if self.peek_one() == Some('&') {
      self.consume("&")?;
      return Ok(Oper::And);
    }
    if self.peek_one() == Some('|') {
      self.consume("|")?;
      return Ok(Oper::Or);
    } 
    if self.peek_one() == Some('^') {
      self.consume("^")?;
      return Ok(Oper::Xor);
    }
    self.expected("operator")
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
      // Annotated
      if self.peek_one() == Some('(') {
        self.consume("(")?;
        let nam = self.parse_name()?;
        self.consume(":")?;
        let typ = Box::new(self.parse_term(fid, uses)?);
        self.consume(")")?;
        let bod = Box::new(self.parse_term(fid, &shadow(&nam, uses))?);
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        let typ = Box::new(Term::All { nam: nam.clone(), inp: typ, bod: Box::new(Term::Met {}) });
        let val = Box::new(Term::Lam { nam: nam.clone(), bod });
        let val = Box::new(Term::Ann { chk: true, typ, val });
        return Ok(Term::Src { src, val });
      }
      //λ(x: A) B
      //-----------------
      //{λx B: ∀(x: A) _}
      // Untyped
      let nam = self.parse_name()?;
      let bod = Box::new(self.parse_term(fid, &shadow(&nam, uses))?);
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Lam { nam, bod }) });
    }

    // RFL ::= (=)
    if self.starts_with("{=}") {
      let ini = *self.index() as u64;
      self.consume("{=}")?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src {
        src,
        val: Box::new(Term::App {
          fun: Box::new(Term::App {
            fun: Box::new(Term::Var { nam: "Equal.refl".to_string() }),
            arg: Box::new(Term::Met {}),
          }),
          arg: Box::new(Term::Met {}),
        })
      });
    }

    // OP2 ::= (<oper> <term> <term>)
    // APP ::= (<term> <term> ...)
    if self.starts_with("(") {
      let ini = *self.index() as u64;
      self.consume("(")?;
      // Operation
      if let Some(oper) = self.peek_one() {
        if "+-*/%=&|<>!^".contains(oper) {
          let opr = self.parse_oper()?;
          let fst = Box::new(self.parse_term(fid, uses)?);
          let snd = Box::new(self.parse_term(fid, uses)?);
          self.consume(")")?;
          let end = *self.index() as u64;
          let src = Src::new(fid, ini, end);
          return Ok(Term::Src { src, val: Box::new(Term::Op2 { opr, fst, snd }) });
        }
      }
      // Application
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

    // ANN ::= {<term> : <term>}
    // EQL ::= {<term> = <term>}
    if self.starts_with("{") {
      let ini = *self.index() as u64;
      self.consume("{")?;
      let val = Box::new(self.parse_term(fid, uses)?);
      self.skip_trivia();
      if self.peek_one() == Some(':') {
        self.consume(":")?;
        let chk = true;
        let typ = Box::new(self.parse_term(fid, uses)?);
        self.consume("}")?;
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        return Ok(Term::Src { src, val: Box::new(Term::Ann { chk, val, typ }) });
      } else if self.peek_one() == Some('=') {
        self.consume("=")?;
        let cmp = Box::new(self.parse_term(fid, uses)?);
        self.consume("}")?;
        let end = *self.index() as u64;
        let src = Src::new(fid, ini, end);
        let eql = Equal { a: *val, b: *cmp };
        return Ok(Term::Src { src, val: Box::new(Term::new_equal(&eql)) });
      } else {
        return self.expected("':' or '=' after '{'");
      }
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

    // SWI ::= switch <name> = <term> { 0: <term>; +: <term> }: <term>
    // - The matched term is optional. Defaults to `Var { nam: <name> }`.
    // - The return type is optional. Defaults to `Met {}`.
    // - Consecutive numbers can be chained, as a syntax sugar. Example:
    //   switch x = expr {
    //     0: ... zero case ...
    //     1: ... one case ...
    //     2: ... two case ...
    //     _: ... >=3 case, with access to x-3 ...
    //   }: return_type
    // Is desugared to:
    //   switch x = expr {
    //     0: ... zero case ...
    //     _: switch x = x-1 {
    //       0: ... one case ...
    //       _: switch x = x-2 {
    //         0: ... two case ...
    //         _: ... >=3 case, with access to x-3 ...
    //       }: _
    //     }:_
    //   }: return_type
    if self.starts_with("switch ") {
      let ini = *self.index() as u64;
      self.consume("switch ")?;
      let nam = self.parse_name()?;
      self.skip_trivia();
      let x = if self.peek_one() == Some('=') {
        self.consume("=")?;
        Box::new(self.parse_term(fid, uses)?)
      } else {
        Box::new(Term::Var { nam: nam.clone() })
      };
      self.consume("{")?;
      let mut cases = Vec::new();
      while self.peek_one() != Some('}') {
        if self.peek_one() == Some('_') {
          self.consume("_:")?;
          let body = Box::new(self.parse_term(fid, &shadow(&format!("{}-{}",nam,cases.len()), uses))?);
          cases.push(body);
          break;
        } else {
          self.consume(&format!("{}:", cases.len()))?;
          let body = Box::new(self.parse_term(fid, uses)?);
          cases.push(body);
          self.skip_trivia();
        }
      }
      self.consume("}")?;
      let p = if self.peek_one() == Some(':') {
        self.consume(":")?;
        Box::new(self.parse_term(fid, &shadow(&nam, uses))?)
      } else {
        Box::new(Term::Met {})
      };
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      // Desugars a long switch into a nested chain of switches
      let mut val = cases.pop().unwrap();
      val = Box::new(Term::Use {
        nam: format!("{}-{}", nam, cases.len()),
        val: Box::new(Term::Var { nam: format!("{}-1", nam) }),
        bod: val,
      });
      for i in (0..(cases.len())).rev() {
        let x = Box::new(Term::Var { nam: format!("{}-1", nam.clone()) });
        let z = cases[i].clone();
        let s = val;
        let p = Box::new(Term::Met {});
        val = Box::new(Term::Swi { nam: nam.clone(), x, z, s, p });
      }
      val = Box::new(Term::Swi { nam, x, z: cases[0].clone(), s: val, p });
      return Ok(Term::Src { src, val });
    }

    // NAT ::= #<uint>
    if self.starts_with("#") {
      let ini = *self.index() as u64;
      self.advance_one();
      let val = self.parse_u64()?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      let val = Box::new(Term::new_nat(val));
      return Ok(Term::Src { src, val });
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

    // NUM ::= <uint>
    if self.peek_one().map_or(false, |c| c.is_ascii_digit()) {
      let ini = *self.index() as u64;
      let val = self.parse_u64()?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      let val = Box::new(Term::Num { val });
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

    // MCH ::= match <name> = <term> { <name> : <term> <...> }: <term>
    if self.starts_with("match ") {
      let ini = *self.index() as u64;
      let mch = self.parse_match(fid, uses)?;
      let end = *self.index() as u64;
      let src = Src::new(fid, ini, end);
      return Ok(Term::Src { src, val: Box::new(Term::Mch { mch: Box::new(mch) }) });
    }

    // VAR ::= <name>
    let ini = *self.index() as u64;
    let old = self.parse_name()?;
    let nam = uses.get(&old).unwrap_or(&old).to_string();
    let end = *self.index() as u64;
    let src = Src::new(fid, ini, end);
    let val = if nam == "U60" {
      Box::new(Term::U60)
    } else {
      Box::new(Term::Var { nam })
    };
    return Ok(Term::Src { src, val });

  }

}
