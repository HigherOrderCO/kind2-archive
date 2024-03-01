#![allow(dead_code)]

use TSPL::Parser;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::env;
use std::fs::File;
use std::io::Write;
use std::process::Command;
use highlight_error::highlight_error;
//use std::fmt;

#[derive(Clone, Copy)]
enum Oper {
  Add , Sub , Mul , Div ,
  Mod , Eq  , Ne  , Lt  ,
  Gt  , Lte , Gte , And ,
  Or  , Xor , Lsh , Rsh ,
}

// Term variables use Bruijn Levels.
#[derive(Clone)]
enum Term {
  All { nam: String, inp: Box<Term>, bod: Box<Term> },
  Lam { nam: String, bod: Box<Term> },
  App { fun: Box<Term>, arg: Box<Term> },
  Ann { val: Box<Term>, typ: Box<Term> },
  Slf { nam: String, typ: Box<Term>, bod: Box<Term> },
  Ins { val: Box<Term> },
  Set,
  U60,
  Num { val: u64 },
  Op2 { opr: Oper, fst: Box<Term>, snd: Box<Term> },
  Mat { nam: String, x: Box<Term>, z: Box<Term>, s: Box<Term>, p: Box<Term> },
  Txt { txt: String },
  Let { nam: String, val: Box<Term>, bod: Box<Term> },
  Var { nam: String },
  Hol { nam: String },
  Met {},
  Src { src: u64, val: Box<Term> },
}

struct Book {
  defs: BTreeMap<String, Term>,
  fids: BTreeMap<String, u64>,
}

fn name(numb: usize) -> String {
  let mut name = String::new();
  let mut numb = numb as i64;
  loop {
    name.insert(0, ((97 + (numb % 26)) as u8) as char);
    numb = numb / 26 - 1;
    if numb < 0 { break; }
  }
  name
}

pub fn new_src(fid: u64, ini: u64, end: u64) -> u64 {
  (fid << 40) | (ini << 20) | end
}

pub fn src_fid(src: u64) -> u64 {
  src >> 40
}

pub fn src_ini(src: u64) -> u64 {
  (src >> 20) & 0xFFFFF
}

pub fn src_end(src: u64) -> u64 {
  src & 0xFFFFF
}

pub fn cons<A>(vector: &im::Vector<A>, value: A) -> im::Vector<A> where A: Clone {
  let mut new_vector = vector.clone();
  new_vector.push_back(value);
  new_vector
}

impl Oper {
  fn show(&self) -> &'static str {
    match self {
      Oper::Add => "+",
      Oper::Sub => "-",
      Oper::Mul => "*",
      Oper::Div => "/",
      Oper::Mod => "%",
      Oper::Eq  => "==",
      Oper::Ne  => "!=",
      Oper::Lt  => "<",
      Oper::Gt  => ">",
      Oper::Lte => "<=",
      Oper::Gte => ">=",
      Oper::And => "&",
      Oper::Or  => "|",
      Oper::Xor => "^",
      Oper::Lsh => "<<",
      Oper::Rsh => ">>",
    }
  }

  fn to_hvm1(&self) -> &'static str {
    match self {
      Oper::Add => "ADD",
      Oper::Sub => "SUB",
      Oper::Mul => "MUL",
      Oper::Div => "DIV",
      Oper::Mod => "MOD",
      Oper::Eq  => "EQ",
      Oper::Ne  => "NE",
      Oper::Lt  => "LT",
      Oper::Gt  => "GT",
      Oper::Lte => "LTE",
      Oper::Gte => "GTE",
      Oper::And => "AND",
      Oper::Or  => "OR",
      Oper::Xor => "XOR",
      Oper::Lsh => "LSH",
      Oper::Rsh => "RSH",
    }
  }
}

impl Term {
  fn show(&self) -> String {
    match self {
      Term::All { nam, inp, bod } => format!("∀({}: {}) {}", nam, inp.show(), bod.show()),
      Term::Lam { nam, bod } => format!("λ{} {}", nam, bod.show()),
      Term::App { fun, arg } => format!("({} {})", fun.show(), arg.show()),
      Term::Ann { val, typ } => format!("{{{}: {}}}", val.show(), typ.show()),
      Term::Slf { nam, typ, bod } => format!("$({}: {}) {}", nam, typ.show(), bod.show()),
      Term::Ins { val } => format!("~{}", val.show()),
      Term::Set => "*".to_string(),
      Term::U60 => "#U60".to_string(),
      Term::Num { val } => format!("#{}", val),
      Term::Op2 { opr, fst, snd } => format!("#({} {} {})", opr.show(), fst.show(), snd.show()),
      Term::Mat { nam, x, z, s, p } => format!("#match {} = {} {{ #0: {}; #+: {} }}: {}", nam, x.show(), z.show(), s.show(), p.show()),
      Term::Txt { txt } => format!("\"{}\"", txt),
      Term::Let { nam, val, bod } => format!("let {} = {} in {}", nam, val.show(), bod.show()),
      Term::Hol { nam } => format!("?{}", nam),
      Term::Met {} => format!("_"),
      Term::Var { nam } => nam.clone(),
      Term::Src { src: _, val } => val.show(),
    }
  }

  fn to_hvm1(&self, env: im::Vector<String>, met: &mut usize) -> String {
    fn binder(name: &str) -> String {
      format!("x{}", name.replace("-", "._."))
    }
    match self {
      Term::All { nam, inp, bod } => format!("(All \"{}\" {} λ{} {})", nam, inp.to_hvm1(env.clone(),met), binder(nam), bod.to_hvm1(cons(&env, nam.clone()),met)),
      Term::Lam { nam, bod } => format!("(Lam \"{}\" λ{} {})", nam, binder(nam), bod.to_hvm1(cons(&env, nam.clone()),met)),
      Term::App { fun, arg } => format!("(App {} {})", fun.to_hvm1(env.clone(),met), arg.to_hvm1(env.clone(),met)),
      Term::Ann { val, typ } => format!("(Ann {} {})", val.to_hvm1(env.clone(),met), typ.to_hvm1(env.clone(),met)),
      Term::Slf { nam, typ, bod } => format!("(Slf \"{}\" {} λ{} {})", nam, typ.to_hvm1(env.clone(),met), binder(nam), bod.to_hvm1(cons(&env, nam.clone()),met)),
      Term::Ins { val } => format!("(Ins {})", val.to_hvm1(env.clone(),met)),
      Term::Set => "(Set)".to_string(),
      Term::U60 => "(U60)".to_string(),
      Term::Num { val } => format!("(Num {})", val),
      Term::Op2 { opr, fst, snd } => format!("(Op2 {} {} {})", opr.to_hvm1(), fst.to_hvm1(env.clone(),met), snd.to_hvm1(env.clone(),met)),
      Term::Mat { nam, x, z, s, p } => format!("(Mat \"{}\" {} {} λ{} {} λ{} {})", nam, x.to_hvm1(env.clone(),met), z.to_hvm1(env.clone(),met), binder(&format!("{}-1",nam)), s.to_hvm1(cons(&env, format!("{}-1",nam)),met), binder(nam), p.to_hvm1(cons(&env, nam.clone()),met)),
      Term::Txt { txt } => format!("(Txt \"{}\")", txt),
      Term::Let { nam, val, bod } => format!("(Let \"{}\" {} λ{} {})", nam, val.to_hvm1(env.clone(),met), binder(nam), bod.to_hvm1(cons(&env, nam.clone()),met)),
      Term::Hol { nam } => format!("(Hol \"{}\" [{}])", nam, env.iter().map(|n| binder(n)).collect::<Vec<_>>().join(",")),
      Term::Met {} => { let n = *met; *met += 1; format!("(Met \"{}\" {})", n, format!("_{}",n)) },
      Term::Var { nam } => if env.contains(nam) { format!("{}", binder(nam)) } else { format!("(Book.{})", nam) },
      Term::Src { src, val } => format!("(Src {} {})", src, val.to_hvm1(env,met)),
    }
  }

  fn get_free_vars(&self, env: im::Vector<String>, free_vars: &mut BTreeSet<String>) {
    match self {
      Term::All { nam, inp, bod } => {
        inp.get_free_vars(env.clone(), free_vars);
        bod.get_free_vars(cons(&env, nam.clone()), free_vars);
      },
      Term::Lam { nam, bod } => {
        bod.get_free_vars(cons(&env, nam.clone()), free_vars);
      },
      Term::App { fun, arg } => {
        fun.get_free_vars(env.clone(), free_vars);
        arg.get_free_vars(env.clone(), free_vars);
      },
      Term::Ann { val, typ } => {
        val.get_free_vars(env.clone(), free_vars);
        typ.get_free_vars(env.clone(), free_vars);
      },
      Term::Slf { nam, typ, bod } => {
        typ.get_free_vars(env.clone(), free_vars);
        bod.get_free_vars(cons(&env, nam.clone()), free_vars);
      },
      Term::Ins { val } => {
        val.get_free_vars(env.clone(), free_vars);
      },
      Term::Set => {},
      Term::U60 => {},
      Term::Num { val: _ } => {},
      Term::Op2 { opr: _, fst, snd } => {
        fst.get_free_vars(env.clone(), free_vars);
        snd.get_free_vars(env.clone(), free_vars);
      },
      Term::Mat { nam, x, z, s, p } => {
        x.get_free_vars(env.clone(), free_vars);
        z.get_free_vars(env.clone(), free_vars);
        s.get_free_vars(cons(&env, format!("{}-1",nam)), free_vars);
        p.get_free_vars(cons(&env, nam.clone()), free_vars);
      },
      Term::Txt { txt: _ } => {},
      Term::Let { nam, val, bod } => {
        val.get_free_vars(env.clone(), free_vars);
        bod.get_free_vars(cons(&env, nam.clone()), free_vars);
      },
      Term::Hol { nam: _ } => {},
      Term::Met {} => {},
      Term::Src { src: _, val } => {
        val.get_free_vars(env, free_vars);
      },
      Term::Var { nam } => {
        if !env.contains(nam) {
          free_vars.insert(nam.clone());
        }
      },
    }
  }

  fn count_metas(&self) -> usize {
    match self {
      Term::All { nam: _, inp, bod } => { inp.count_metas() + bod.count_metas() }
      Term::Lam { nam: _, bod } => { bod.count_metas() },
      Term::App { fun, arg } => { fun.count_metas() + arg.count_metas() },
      Term::Ann { val, typ } => { val.count_metas() + typ.count_metas() },
      Term::Slf { nam: _, typ, bod } => { typ.count_metas() + bod.count_metas() },
      Term::Ins { val } => { val.count_metas() },
      Term::Set => 0,
      Term::U60 => 0,
      Term::Num { val: _ } => 0,
      Term::Op2 { opr: _, fst, snd } => { fst.count_metas() + snd.count_metas() },
      Term::Mat { nam: _, x, z, s, p } => { x.count_metas() + z.count_metas() + s.count_metas() + p.count_metas() },
      Term::Txt { txt: _ } => 0,
      Term::Let { nam: _, val, bod } => { val.count_metas() + bod.count_metas() },
      Term::Hol { nam: _ } => 0,
      Term::Met {} => 1,
      Term::Var { nam: _ } => 0,
      Term::Src { src: _, val } => { val.count_metas() }
    }
  }

}

TSPL::new_parser!(KindParser);

impl<'i> KindParser<'i> {
  fn parse_oper(&mut self) -> Result<Oper, String> {
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

  fn parse_term(&mut self, fid: u64) -> Result<Term, String> {
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
        let src = new_src(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::All { nam, inp, bod }) })
      }
      Some('λ') => {
        let ini = *self.index() as u64;
        self.consume("λ")?;
        let nam = self.parse_name()?;
        let bod = Box::new(self.parse_term(fid)?);
        let end = *self.index() as u64;
        let src = new_src(fid, ini, end);
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
        let src = new_src(fid, ini, end);
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
        let src = new_src(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Ann { val, typ }) })
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
        let src = new_src(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Slf { nam, typ, bod }) })
      }
      Some('~') => {
        let ini = *self.index() as u64;
        self.consume("~")?;
        let val = Box::new(self.parse_term(fid)?);
        let end = *self.index() as u64;
        let src = new_src(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Ins { val }) })
      }
      Some('*') => {
        let ini = *self.index() as u64;
        self.consume("*")?;
        let end = *self.index() as u64;
        let src = new_src(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Set) })
      }
      Some('#') => {
        let ini = *self.index() as u64;
        self.consume("#")?;
        match self.peek_one() {
          Some('U') => {
            self.consume("U60")?;
            let end = *self.index() as u64;
            let src = new_src(fid, ini, end);
            Ok(Term::Src { src, val: Box::new(Term::U60) })
          }
          Some('(') => {
            self.consume("(")?;
            let opr = self.parse_oper()?;
            let fst = Box::new(self.parse_term(fid)?);
            let snd = Box::new(self.parse_term(fid)?);
            self.consume(")")?;
            let end = *self.index() as u64;
            let src = new_src(fid, ini, end);
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
            let src = new_src(fid, ini, end);
            Ok(Term::Src { src, val: Box::new(Term::Mat { nam, x, z, s, p }) })
          }
          Some(_) => {
            let val = self.parse_u64()?;
            let end = *self.index() as u64;
            let src = new_src(fid, ini, end);
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
        let src = new_src(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Hol { nam }) })
      }
      Some('_') => {
        let ini = *self.index() as u64;
        self.consume("_")?;
        let end = *self.index() as u64;
        let src = new_src(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Met {}) })
      }
      Some('\'') => {
        let ini = *self.index() as u64;
        let chr = self.parse_quoted_char()?;
        let end = *self.index() as u64;
        let src = new_src(fid, ini, end);
        Ok(Term::Src { src, val: Box::new(Term::Num { val: chr as u64 }) })
      }
      Some('"') => {
        let ini = *self.index() as u64;
        let txt = self.parse_quoted_string()?;
        let end = *self.index() as u64;
        let src = new_src(fid, ini, end);
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
          let src = new_src(fid, ini, end);
          Ok(Term::Src { src, val: Box::new(Term::Let { nam, val, bod }) })
        } else {
          let ini = *self.index() as u64;
          let nam = self.parse_name()?;
          let end = *self.index() as u64;
          let src = new_src(fid, ini, end);
          Ok(Term::Src { src, val: Box::new(Term::Var { nam }) })
        }
      }
    }
  }
  
  fn parse_def(&mut self, fid: u64) -> Result<(String, Term), String> {
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

  fn parse_book(&mut self, fid: u64) -> Result<Book, String> {
    let mut book = Book::new();
    while *self.index() < self.input().len() {
      let (name, term) = self.parse_def(fid)?;
      book.defs.insert(name, term);
      self.skip_trivia();
    }
    Ok(book)
  }

}

impl Book {
  fn new() -> Self {
    Book {
      defs: BTreeMap::new(),
      fids: BTreeMap::new(),
    }
  }
  
  fn to_hvm1(&self) -> String {
    let mut used = BTreeSet::new();
    let mut code = String::new();
    for (name, term) in &self.defs {
      let metas = term.count_metas();
      let mut lams = String::new();
      for i in 0 .. term.count_metas() {
        lams = format!("{} λ_{}", lams, i);
      }
      let subs = (0 .. metas).map(|h| format!("(Pair \"{}\" None)", h)).collect::<Vec<_>>().join(",");
      code.push_str(&format!("Book.{} = (Ref \"{}\" [{}] {}{})\n", name, name, subs, lams, term.to_hvm1(im::Vector::new(), &mut 0)));
      used.insert(name.clone());
    }
    code
  }

  fn show(&self) -> String {
    let mut book_str = String::new();
    for (name, term) in &self.defs {
      book_str.push_str(&format!("{} = {}\n", name, term.show()));
    }
    book_str
  }

  fn load(name: &str) -> Result<Self, String> {
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

  fn get_file_id(&mut self, name: &str) -> u64 {
    if let Some(id) = self.fids.get(name) {
      *id
    } else {
      let id = self.fids.len() as u64 + 1;
      self.fids.insert(name.to_string(), id);
      id
    }
  }

  // FIXME: asymptotics
  fn get_file_name(&self, id: u64) -> Option<String> {
    for (name, &fid) in &self.fids {
      if fid == id {
        return Some(name.clone());
      }
    }
    None
  }

  fn inject_sources(&self, input: &str) -> Result<String, String> {
    let mut result = input.to_string();
    let ini_sym = "##LOC{";
    let end_sym = "}LOC##";
    while let (Some(ini), Some(end)) = (result.find(ini_sym), result.find(end_sym)) {
      let got = &result[ini + ini_sym.len()..end];
      let loc = got.parse::<u64>().map_err(|_| "Failed to parse location")?;
      let fid = src_fid(loc);
      let ini = src_ini(loc) as usize;
      let end = src_end(loc) as usize;
      if loc == 0 {
        result = result.replace(&format!("{}{}{}", ini_sym, got, end_sym), "");
      } else if let Some(file_name) = self.get_file_name(fid) {
        let source_file = std::fs::read_to_string(&file_name).map_err(|_| "Failed to read source file")?;
        let context_str = highlight_error(ini, end, &source_file);
        let context_str = format!("\x1b[4m{}\x1b[0m\n{}", file_name, context_str);
        result = result.replace(&format!("{}{}{}", ini_sym, got, end_sym), &context_str);
      } else {
        return Err("File ID not found".to_string());
      }
    }
    Ok(result)
  }

}

//fn run() -> Result<(), String> {
  //let book = Book::load("Nat")?;
  //println!("{}", book.show());
  //println!("{}", book.to_hvm1());
  //return Ok(());
//}

//fn main() {
  //if let Err(e) = run() {
    //eprintln!("{}", e);
  //}
//}


fn generate_check_hvm1(book: &Book, command: &str, arg: &str) -> String {
  //let used_defs = book.defs.keys().collect::<Vec<_>>().iter().map(|name| format!("(Pair \"{}\" Book.{})", name, name)).collect::<Vec<_>>().join(" ");
  let kind_hvm1 = include_str!("./kind2.hvm1");
  let book_hvm1 = book.to_hvm1();
  let main_hvm1 = match command {
    "check" => format!("Main = (API.check Book.{})\n", arg),
    //"check" => format!("Main = (API.check.many [{}])\n", used_defs),
    "run"   => format!("Main = (API.normal Book.{})\n", arg),
    _       => panic!("invalid command"),
  };
  let hvm1_code = format!("{}\n{}\n{}", kind_hvm1, book_hvm1, main_hvm1);
  return hvm1_code;
}

fn main() {
  let args: Vec<String> = env::args().collect();

  if args.len() < 3 {
    show_help();
  }

  let cmd = &args[1];
  let arg = &args[2];

  //println!("loading");
  match cmd.as_str() {
    "check" | "run" => {
      match Book::load(arg) {
        Ok(book) => {
          //println!("loaded!");
          let check_hvm1 = generate_check_hvm1(&book, cmd, arg);

          // Saves it to a file.
          let mut file = File::create(".check.hvm1").expect("Failed to create '.check.hvm1'.");
          file.write_all(check_hvm1.as_bytes()).expect("Failed to write '.check.hvm1'.");

          let output = Command::new("hvm1").arg("run").arg("-t").arg("1").arg("-c").arg("-f").arg(".check.hvm1").arg("(Main)").output().expect("Failed to execute command");
          //let stdout : Result<String,String> = Ok(format!("{}", String::from_utf8_lossy(&output.stdout)));
          let stdout = book.inject_sources(&format!("{}", String::from_utf8_lossy(&output.stdout)));
          let stderr = String::from_utf8_lossy(&output.stderr);

          match stdout {
            //Ok(output) => println!("{}", output.replace("(ERRORS_FOUND)","")),
            Ok(output) => println!("{}", output),
            Err(error) => eprintln!("{}", error),
          }

          if !output.stderr.is_empty() {
            eprintln!("{}", stderr);
          }
        },
        Err(e) => {
          eprintln!("{}", e);
          std::process::exit(1);
        },
      }
    },
    _ => {
      show_help();
    },
  }
}

fn show_help() {
  eprintln!("Usage: kind2 [check|run] <name>");
  std::process::exit(1);
}
