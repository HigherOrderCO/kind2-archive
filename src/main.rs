#![allow(dead_code)]

use TSPL::Parser;
use std::collections::HashMap;
use std::collections::HashSet;
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
  Slf { nam: String, bod: Box<Term> },
  Ins { val: Box<Term> },
  Set,
  U60,
  Num { val: u64 },
  Op2 { opr: Oper, fst: Box<Term>, snd: Box<Term> },
  Mat { nam: String, x: Box<Term>, z: Box<Term>, s: Box<Term>, p: Box<Term> },
  Txt { txt: String },
  Let { nam: String, val: Box<Term>, bod: Box<Term> },
  Hol { nam: String },
  Var { nam: String },
}

struct Book {
  defs: HashMap<String, Term>,
}

// NOT USED ANYMORE
//fn name(numb: usize) -> String {
  //let mut name = String::new();
  //let mut numb = numb as i64;
  //loop {
    //name.insert(0, ((97 + (numb % 26)) as u8) as char);
    //numb = numb / 26 - 1;
    //if numb < 0 { break; }
  //}
  //name
//}

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
      Term::Slf { nam, bod } => format!("${} {}", nam, bod.show()),
      Term::Ins { val } => format!("~{}", val.show()),
      Term::Set => "*".to_string(),
      Term::U60 => "#U60".to_string(),
      Term::Num { val } => format!("#{}", val),
      Term::Op2 { opr, fst, snd } => format!("#({} {} {})", opr.show(), fst.show(), snd.show()),
      Term::Mat { nam, x, z, s, p } => format!("#match {} = {} {{ #0: {}; #+: {} }}: {}", nam, x.show(), z.show(), s.show(), p.show()),
      Term::Txt { txt } => format!("\"{}\"", txt),
      Term::Let { nam, val, bod } => format!("let {} = {} in {}", nam, val.show(), bod.show()),
      Term::Hol { nam } => format!("?{}", nam),
      Term::Var { nam } => nam.clone(),
    }
  }

  fn to_hvm1(&self, env: im::Vector<String>) -> String {
    match self {
      Term::All { nam, inp, bod } => format!("(All \"{}\" {} λ{} {})", nam, inp.to_hvm1(env.clone()), nam, bod.to_hvm1(cons(&env, nam.clone()))),
      Term::Lam { nam, bod } => format!("(Lam \"{}\" λ{} {})", nam, nam, bod.to_hvm1(cons(&env, nam.clone()))),
      Term::App { fun, arg } => format!("(App {} {})", fun.to_hvm1(env.clone()), arg.to_hvm1(env.clone())),
      Term::Ann { val, typ } => format!("(Ann {} {})", val.to_hvm1(env.clone()), typ.to_hvm1(env.clone())),
      Term::Slf { nam, bod } => format!("(Slf \"{}\" λ{} {})", nam, nam, bod.to_hvm1(cons(&env, nam.clone()))),
      Term::Ins { val } => format!("(Ins {})", val.to_hvm1(env.clone())),
      Term::Set => "(Set)".to_string(),
      Term::U60 => "(U60)".to_string(),
      Term::Num { val } => format!("(Num {})", val),
      Term::Op2 { opr, fst, snd } => format!("(Op2 {} {} {})", opr.to_hvm1(), fst.to_hvm1(env.clone()), snd.to_hvm1(env.clone())),
      Term::Mat { nam, x, z, s, p } => format!("(Mat \"{}\" {} {} λ{} {} λ{} {})", nam, x.to_hvm1(env.clone()), z.to_hvm1(env.clone()), nam, s.to_hvm1(cons(&env, nam.clone())), nam, p.to_hvm1(cons(&env, nam.clone()))),
      Term::Txt { txt } => format!("(Txt \"{}\")", txt),
      Term::Let { nam, val, bod } => format!("(Let \"{}\" {} λ{} {})", nam, val.to_hvm1(env.clone()), nam, bod.to_hvm1(cons(&env, nam.clone()))),
      Term::Hol { nam } => format!("(Hol \"{}\" [{}])", nam, env.iter().map(|n| format!("\"{}\"", n)).collect::<Vec<_>>().join(",")),
      Term::Var { nam } => if env.contains(nam) { nam.clone() } else { format!("(Book.{})", nam) },
    }
  }

  fn get_free_vars(&self, env: im::Vector<String>, free: &mut HashSet<String>) {
    match self {
      Term::All { nam, inp, bod } => {
        inp.get_free_vars(env.clone(), free);
        bod.get_free_vars(cons(&env, nam.clone()), free);
      },
      Term::Lam { nam, bod } => {
        bod.get_free_vars(cons(&env, nam.clone()), free);
      },
      Term::App { fun, arg } => {
        fun.get_free_vars(env.clone(), free);
        arg.get_free_vars(env.clone(), free);
      },
      Term::Ann { val, typ } => {
        val.get_free_vars(env.clone(), free);
        typ.get_free_vars(env.clone(), free);
      },
      Term::Slf { nam, bod } => {
        bod.get_free_vars(cons(&env, nam.clone()), free);
      },
      Term::Ins { val } => {
        val.get_free_vars(env.clone(), free);
      },
      Term::Set => {},
      Term::U60 => {},
      Term::Num { val: _ } => {},
      Term::Op2 { opr: _, fst, snd } => {
        fst.get_free_vars(env.clone(), free);
        snd.get_free_vars(env.clone(), free);
      },
      Term::Mat { nam, x, z, s, p } => {
        x.get_free_vars(env.clone(), free);
        z.get_free_vars(env.clone(), free);
        s.get_free_vars(cons(&env, nam.clone()), free);
        p.get_free_vars(cons(&env, nam.clone()), free);
      },
      Term::Txt { txt: _ } => {},
      Term::Let { nam, val, bod } => {
        val.get_free_vars(env.clone(), free);
        bod.get_free_vars(cons(&env, nam.clone()), free);
      },
      Term::Hol { nam: _ } => {},
      Term::Var { nam } => {
        if !env.contains(nam) {
          free.insert(nam.clone());
        }
      },
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
      Some('=') => { self.consume("=")?; Ok(Oper::Eq) }
      Some('!') => { self.consume("!=")?; Ok(Oper::Ne) }
      Some('<') => {
        match self.peek_many(2) {
          Some("<=") => { self.advance_many(2); Ok(Oper::Lte) }
          _ => { self.advance_one(); Ok(Oper::Lt) }
        }
      }
      Some('>') => {
        match self.peek_many(2) {
          Some(">=") => { self.advance_many(2); Ok(Oper::Gte) }
          _ => { self.advance_one(); Ok(Oper::Gt) }
        }
      }
      Some('&') => { self.advance_one(); Ok(Oper::And) }
      Some('|') => { self.advance_one(); Ok(Oper::Or) }
      Some('^') => { self.advance_one(); Ok(Oper::Xor) }
      Some('l') => { self.consume("<<")?; Ok(Oper::Lsh) }
      Some('r') => { self.consume(">>")?; Ok(Oper::Rsh) }
      _ => self.expected("operator"),
    }
  }
  
  fn parse_term(&mut self) -> Result<Term, String> {
    self.skip_trivia();
    match self.peek_one() {
      Some('∀') => {
        self.consume("∀")?;
        self.consume("(")?;
        let nam = self.parse_name()?;
        self.consume(":")?;
        let inp = Box::new(self.parse_term()?);
        self.consume(")")?;
        let bod = Box::new(self.parse_term()?);
        Ok(Term::All { nam, inp, bod })
      }
      Some('λ') => {
        self.consume("λ")?;
        let nam = self.parse_name()?;
        let bod = Box::new(self.parse_term()?);
        Ok(Term::Lam { nam, bod })
      }
      Some('(') => {
        self.consume("(")?;
        let fun = Box::new(self.parse_term()?);
        let mut args = Vec::new();
        while self.peek_one() != Some(')') {
          args.push(Box::new(self.parse_term()?));
        }
        self.consume(")")?;
        let mut app = fun;
        for arg in args {
          app = Box::new(Term::App { fun: app, arg });
        }
        Ok(*app)
      }
      Some('{') => {
        self.consume("{")?;
        let val = Box::new(self.parse_term()?);
        self.consume(":")?;
        let typ = Box::new(self.parse_term()?);
        self.consume("}")?;
        Ok(Term::Ann { val, typ })
      }
      Some('$') => {
        self.consume("$")?;
        let nam = self.parse_name()?;
        let bod = Box::new(self.parse_term()?);
        Ok(Term::Slf { nam, bod })
      }
      Some('~') => {
        self.consume("~")?;
        let val = Box::new(self.parse_term()?);
        Ok(Term::Ins { val })
      }
      Some('*') => {
        self.consume("*")?;
        Ok(Term::Set)
      }
      Some('#') => {
        self.consume("#")?;
        match self.peek_one() {
          Some('U') => {
            self.consume("U60")?;
            Ok(Term::U60)
          }
          Some('(') => {
            self.consume("(")?;
            let opr = self.parse_oper()?;
            let fst = Box::new(self.parse_term()?);
            let snd = Box::new(self.parse_term()?);
            self.consume(")")?;
            Ok(Term::Op2 { opr, fst, snd })
          }
          Some('m') => {
            self.consume("match")?;
            let nam = self.parse_name()?;
            self.consume("=")?;
            let x = Box::new(self.parse_term()?);
            self.consume("{")?;
            self.consume("#0")?;
            self.consume(":")?;
            let z = Box::new(self.parse_term()?);
            self.consume("#+")?;
            self.consume(":")?;
            let s = Box::new(self.parse_term()?);
            self.consume("}")?;
            self.consume(":")?;
            let p = Box::new(self.parse_term()?);
            Ok(Term::Mat { nam, x, z, s, p })
          }
          Some(_) => {
            let val = self.parse_u64()?;
            Ok(Term::Num { val })
          }
          _ => {
            self.expected("numeric-expression")
          }
        }
      }
      Some('?') => {
        self.consume("?")?;
        let nam = self.parse_name()?;
        Ok(Term::Hol { nam })
      }
      Some('\'') => {
        let chr = self.parse_quoted_char()?;
        Ok(Term::Num { val: chr as u64 })
      }
      Some('"') => {
        let txt = self.parse_quoted_string()?;
        Ok(Term::Txt { txt })
      }
      _ => {
        if self.peek_many(4) == Some("let ") {
          self.advance_many(4);
          let nam = self.parse_name()?;
          self.consume("=")?;
          let val = Box::new(self.parse_term()?);
          let bod = Box::new(self.parse_term()?);
          Ok(Term::Let { nam, val, bod })
        } else {
          let nam = self.parse_name()?;
          Ok(Term::Var { nam })
        }
      }
    }
  }

  fn parse_def(&mut self) -> Result<(String, Term), String> {
    let nam = self.parse_name()?;
    self.skip_trivia();
    if self.peek_one() == Some(':') {
      self.consume(":")?;
      let typ = self.parse_term()?;
      self.consume("=")?;
      let val = self.parse_term()?;
      Ok((nam, Term::Ann { val: Box::new(val), typ: Box::new(typ) }))
    } else {
      self.consume("=")?;
      let val = self.parse_term()?;
      Ok((nam, val))
    }
  }

  fn parse_book(&mut self) -> Result<Book, String> {
    let mut book = Book::new();
    while *self.index() < self.input().len() {
      let (name, term) = self.parse_def()?;
      book.defs.insert(name, term);
      self.skip_trivia();
    }
    Ok(book)
  }

}

impl Book {
  fn new() -> Self {
    Book {
      defs: HashMap::new(),
    }
  }
  
  fn to_hvm1(&self) -> String {
    let mut used = HashSet::new();
    let mut code = String::new();
    for (name, term) in &self.defs {
      code.push_str(&format!("Book.{} = (Ref \"{}\" {})\n", name, name, term.to_hvm1(im::Vector::new())));
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

  fn load_file(filename: &str) -> Result<Self, String> {
    std::fs::read_to_string(filename)
      .map_err(|_| format!("Could not read file: {}", filename))
      .and_then(|contents| KindParser::new(&contents).parse_book())
  }

  fn load(name: &str) -> Result<Self, String> {
    fn load_term(name: &str, book: &mut Book) -> Result<(), String> {
      if !book.defs.contains_key(name) {
        let file = format!("./book/{}.kind2", name);
        let text = std::fs::read_to_string(&file).map_err(|_| format!("Could not read file: {}", file))?;
        let defs = KindParser::new(&text).parse_book()?;
        for (def_name, def_term) in &defs.defs {
          book.defs.insert(def_name.clone(), def_term.clone());
        }
        for (_, def_term) in defs.defs.into_iter() {
          let mut dependencies = HashSet::new();
          def_term.get_free_vars(im::Vector::new(), &mut dependencies);
          for ref_name in dependencies {
            load_term(&ref_name, book)?;
          }
        }
      }
      return Ok(());
    }
    let mut book = Book::new();
    load_term(name, &mut book)?;
    Ok(book)
  }

}

fn run() -> Result<(), String> {
  let book = Book::load("Bool")?;
  //let book = KindParser::new("f : * = ∀(a: *) λf λx (ID (f (f a b c)))").parse_book()?;
  println!("{}", book.show());
  println!("{}", book.to_hvm1());
  return Ok(());
}

fn main() {
  if let Err(e) = run() {
    eprintln!("{}", e);
  }
}
