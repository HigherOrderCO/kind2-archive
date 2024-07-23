use crate::{*};

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
      let pts = nam.split('/').collect::<Vec<&str>>();
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
        typ = Term::All { era: false, nam: idx_nam.clone(), inp: Box::new(idx_typ.clone()), bod: Box::new(typ) };
        val = Term::Lam { era: false, nam: idx_nam.clone(), bod: Box::new(val) };
      }
      for (par_nam, par_typ) in adt.pars.iter().rev() {
        typ = Term::All { era: false, nam: par_nam.clone(), inp: Box::new(par_typ.clone()), bod: Box::new(typ) };
        val = Term::Lam { era: false, nam: par_nam.clone(), bod: Box::new(val) };
      }
      //println!("NAM: {}", adt.name);
      //println!("TYP: {}", typ.show());
      //println!("VAL: {}", val.show());
      return Ok((adt.name, Term::Ann { chk: false, val: Box::new(val), typ: Box::new(typ) }));
    }

    // Top level definition
    self.skip_trivia();
    let nam = self.parse_name()?;
    // FIXME: this breaks definitions of terms with a name equivalent to one that has been imported.
    let nam = uses.get(&nam).unwrap_or(&nam).to_string();
    self.skip_trivia();

    // Arguments (optional)
    let mut args = im::Vector::new();
    let mut uses = uses.clone();
    while self.peek_one() == Some('<') || self.peek_one() == Some('(') || self.peek_one() == Some('~') || self.peek_one() == Some('-') {
      let implicit = self.peek_one() == Some('<') || self.peek_one() == Some('~');
      let closing = self.peek_one() == Some('<') || self.peek_one() == Some('(');
      if closing {
        self.consume(if implicit { "<" } else { "(" })?;
      } else {
        self.consume(if implicit { "~" } else { "-" })?;
      }
      let arg_name = self.parse_name()?;
      self.skip_trivia();
      let arg_type = if self.peek_one() == Some(':') {
        self.consume(":")?;
        self.parse_term(fid, &uses)?
      } else {
        Term::Met {}
      };
      if closing {
        self.consume(if implicit { ">" } else { ")" })?;
      }
      uses = shadow(&arg_name, &uses);
      args.push_back((implicit, arg_name, arg_type));
      self.skip_trivia();
    }

    // Type annotation (optional)
    let mut typ;
    let ann;
    if self.peek_one() == Some(':') {
      self.consume(":")?;
      typ = self.parse_term(fid, &uses)?;
      ann = true;
    } else {
      typ = Term::Met {};
      ann = false;
    }

    // Optional '=' sign
    self.skip_trivia();
    if self.peek_one() == Some('=') {
      self.consume("=")?;
      self.skip_trivia();
    }

    let mut val = self.parse_term(fid, &uses)?;

    //println!("PARSING {}", nam);

    // Adds lambdas/foralls for each argument
    typ.add_alls(args.clone());
    val.add_lams(args.clone());

    // Removes syntax-sugars from the AST
    typ.desugar();
    val.desugar();

    //println!("{}", nam);
    //println!(": {}", typ.show());
    //println!("= {}", val.show());
    //println!("");

    return Ok((nam, Term::Ann { chk: !ann, val: Box::new(val), typ: Box::new(typ) }));
  }

  // Parses a whole file into a book.
  pub fn parse_book(&mut self, name: &str, fid: u64) -> Result<Book, String> {
    let mut book = Book::new();
    // Parses all top-level 'use' declarations.
    let mut uses = self.parse_uses(fid)?;
    // Each file has an implicit 'use Path.to.file'. We add it here:
    uses.insert(name.split('/').last().unwrap().to_string(), name.to_string());
    // Parses all definitions.
    while *self.index() < self.input().len() {
      let (name, term) = self.parse_def(fid, &mut uses)?;
      book.defs.insert(name, term);
      self.skip_trivia();
    }
    Ok(book)
  }

}

impl Term {

  // Wraps a Lam around this term.
  fn add_lam(&mut self, era: bool, arg: &str) {
    *self = Term::Lam {
      era: era,
      nam: arg.to_string(),
      bod: Box::new(std::mem::replace(self, Term::Met {})),
    };
  }

  // Wraps many lams around this term. Linearizes when possible.
  fn add_lams(&mut self, args: im::Vector<(bool,String,Term)>) {
    for (era, nam, _) in args.iter().rev() {
      self.add_lam(*era, &nam);
    }

    // NOTE: match-passthrough removed due to problems. For example:
    // U48.if (x: U48) (P: *) (t: P) (f: P) : P = switch x { 0: t _: f }
    // This wouldn't check, because 'P' is moved inside, becoming a different 'P'.
    // I think automatic behaviors like this are dangerous and should be avoided.

    //// Passes through Src
    //if let Term::Src { val, .. } = self {
      //val.add_lams(args);
      //return;
    //}
    //// Passes through Ann
    //if let Term::Ann { val, .. } = self {
      //val.add_lams(args);
      //return;
    //}
    //// Linearizes a numeric pattern match
    //if let Term::Swi { nam, z, s, p, .. } = self {
      //if args.len() >= 1 && args[0].1 == *nam {
        //let (head, tail) = args.split_at(1);
        //z.add_lams(tail.clone());
        //s.add_lams(tail.clone());
        //p.add_alls(tail.clone());
        //self.add_lam(head[0].0, &head[0].1);
        //return;
      //}
    //}
    //// Linearizes a user-defined ADT match
    //if let Term::Mch { mch } = self {
      //if !mch.fold {
        //let Match { name, cses, moti, .. } = &mut **mch;
        //if args.len() >= 1 && args[0].1 == *name {
          //let (head, tail) = args.split_at(1);
          //for (_, cse) in cses {
            //cse.add_lams(tail.clone());
          //}
          //moti.as_mut().map(|x| x.add_alls(tail.clone()));
          //self.add_lam(head[0].0, &head[0].1);
          //return;
        //}
      //}
    //}
    //// Prepend remaining lambdas
    //if args.len() > 0 {
      //let (head, tail) = args.split_at(1);
      //self.add_lam(head[0].0, &head[0].1);
      //if let Term::Lam { era: _, nam: _, bod } = self {
        //bod.add_lams(tail.clone());
      //} else {
        //unreachable!();
      //}
    //}
  
  }

  // Wraps an All around this term.
  fn add_all(&mut self, era: bool, arg: &str, typ: &Term) {
    *self = Term::All {
      era: era,
      nam: arg.to_string(),
      inp: Box::new(typ.clone()),
      bod: Box::new(std::mem::replace(self, Term::Met {})),
    };
  }

  // Wraps many Lams around this term.
  fn add_alls(&mut self, args: im::Vector<(bool,String,Term)>) {
    for (era, nam, typ) in args.iter().rev() {
      self.add_all(*era, &nam, typ);
    }
  }

}
