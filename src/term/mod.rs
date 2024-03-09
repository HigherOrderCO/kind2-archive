use crate::{*};
use std::collections::BTreeSet;

pub mod compile;
pub mod format;
pub mod parse;
pub mod sugar;

#[derive(Clone, Copy, Debug)]
pub enum Oper {
  Add , Sub , Mul , Div ,
  Mod , Eq  , Ne  , Lt  ,
  Gt  , Lte , Gte , And ,
  Or  , Xor , Lsh , Rsh ,
}

#[derive(Clone, Debug)]
pub struct Src {
  pub ini: u64,
  pub end: u64,
  pub fid: u64,
}

// <term> ::=
//   ALL | ∀(<name>: <term>) <term>
//   LAM | λ<name> <term>
//   APP | (<term> <term>)
//   ANN | {<term>: <term>}
//   SLF | $(<name>: <term>) <term>
//   INS | ~<term>
//   SET | *
//   U60 | #U60
//   NUM | #<uint>
//   OP2 | #(<oper> <term> <term>)
//   MAT | #match <name> = <term> { #0: <term>; #+: <term> }: <term>
//   HOL | ?<name>
//   MET | _
//   CHR | '<char>'
//   STR | "<string>"
//   LET | let <name> = <term> <term>
//   VAR | <name>
#[derive(Clone, Debug)]
pub enum Term {
  All { nam: String, inp: Box<Term>, bod: Box<Term> },
  Lam { nam: String, bod: Box<Term> },
  App { fun: Box<Term>, arg: Box<Term> },
  Ann { chk: bool, val: Box<Term>, typ: Box<Term> },
  Slf { nam: String, typ: Box<Term>, bod: Box<Term> },
  Ins { val: Box<Term> },
  Set,
  U60,
  Num { val: u64 },
  Op2 { opr: Oper, fst: Box<Term>, snd: Box<Term> },
  Mat { nam: String, x: Box<Term>, z: Box<Term>, s: Box<Term>, p: Box<Term> },
  Let { nam: String, val: Box<Term>, bod: Box<Term> },
  Use { nam: String, val: Box<Term>, bod: Box<Term> },
  Var { nam: String },
  Hol { nam: String },
  Met {},
  Src { src: Src, val: Box<Term> },
  Nat { nat: u64 },
  Txt { txt: String },
}

impl Src {
  pub fn new(fid: u64, ini: u64, end: u64) -> Self {
    Src { ini, end, fid }
  }

  pub fn to_u64(&self) -> u64 {
    (self.fid << 40) | (self.ini << 20) | self.end
  }

  pub fn from_u64(src: u64) -> Self {
    let fid = src >> 40;
    let ini = (src >> 20) & 0xFFFFF;
    let end = src & 0xFFFFF;
    Src { ini, end, fid }
  }
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

pub fn cons<A>(vector: &im::Vector<A>, value: A) -> im::Vector<A> where A: Clone {
  let mut new_vector = vector.clone();
  new_vector.push_back(value);
  new_vector
}

impl Oper {
  pub fn show(&self) -> String {
    return self.format().flatten(None);
  }
}

impl Term {

  pub fn show(&self) -> String {
    return self.format().flatten(None);
  }

  pub fn get_free_vars(&self, env: im::Vector<String>, free_vars: &mut BTreeSet<String>) {
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
      Term::Ann { chk: _, val, typ } => {
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
      Term::Nat { nat: _ } => {},
      Term::Txt { txt: _ } => {},
      Term::Let { nam, val, bod } => {
        val.get_free_vars(env.clone(), free_vars);
        bod.get_free_vars(cons(&env, nam.clone()), free_vars);
      },
      Term::Use { nam, val, bod } => {
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

  pub fn count_metas(&self) -> usize {
    match self {
      Term::All { inp, bod, .. } => {
        let inp = inp.count_metas();
        let bod = bod.count_metas();
        inp + bod
      },
      Term::Lam { bod, .. } => {
        let bod = bod.count_metas();
        bod
      },
      Term::App { fun, arg } => {
        let fun = fun.count_metas();
        let arg = arg.count_metas();
        fun + arg
      },
      Term::Ann { chk: _, val, typ } => {
        let val = val.count_metas();
        let typ = typ.count_metas();
        val + typ
      },
      Term::Slf { typ, bod, .. } => {
        let typ = typ.count_metas();
        let bod = bod.count_metas();
        typ + bod
      },
      Term::Ins { val } => {
        let val = val.count_metas();
        val
      },
      Term::Set => {
        0
      },
      Term::U60 => {
        0
      },
      Term::Num { .. } => {
        0
      },
      Term::Op2 { fst, snd, .. } => {
        let fst = fst.count_metas();
        let snd = snd.count_metas();
        fst + snd
      },
      Term::Mat { x, z, s, p, .. } => {
        let x = x.count_metas();
        let z = z.count_metas();
        let s = s.count_metas();
        let p = p.count_metas();
        x + z + s + p
      },
      Term::Nat { .. } => {
        0
      },
      Term::Txt { .. } => {
        0
      },
      Term::Let { val, bod, .. } => {
        let val = val.count_metas();
        let bod = bod.count_metas();
        val + bod
      },
      Term::Use { val, bod, .. } => {
        let val = val.count_metas();
        let bod = bod.count_metas();
        val + bod
      },
      Term::Hol { .. } => {
        0
      },
      Term::Met { .. } => {
        1
      },
      Term::Var { .. } => {
        0
      },
      Term::Src { val, .. } => {
        let val = val.count_metas();
        val
      },
    }
  }

  pub fn clean(&self) -> Term {
    match self {
      Term::All { nam, inp, bod } => {
        Term::All {
          nam: nam.clone(),
          inp: Box::new(inp.clean()),
          bod: Box::new(bod.clean()),
        }
      },
      Term::Lam { nam, bod } => {
        Term::Lam {
          nam: nam.clone(),
          bod: Box::new(bod.clean()),
        }
      },
      Term::App { fun, arg } => {
        Term::App {
          fun: Box::new(fun.clean()),
          arg: Box::new(arg.clean()),
        }
      },
      Term::Ann { chk, val, typ } => {
        Term::Ann {
          chk: *chk,
          val: Box::new(val.clean()),
          typ: Box::new(typ.clean()),
        }
      },
      Term::Slf { nam, typ, bod } => {
        Term::Slf {
          nam: nam.clone(),
          typ: Box::new(typ.clean()),
          bod: Box::new(bod.clean()),
        }
      },
      Term::Ins { val } => {
        Term::Ins {
          val: Box::new(val.clean()),
        }
      },
      Term::Set => {
        Term::Set
      },
      Term::U60 => {
        Term::U60
      },
      Term::Num { val } => {
        Term::Num { val: *val }
      },
      Term::Op2 { opr, fst, snd } => {
        Term::Op2 {
          opr: *opr,
          fst: Box::new(fst.clean()),
          snd: Box::new(snd.clean()),
        }
      },
      Term::Mat { nam, x, z, s, p } => {
        Term::Mat {
          nam: nam.clone(),
          x: Box::new(x.clean()),
          z: Box::new(z.clean()),
          s: Box::new(s.clean()),
          p: Box::new(p.clean()),
        }
      },
      Term::Nat { nat } => {
        Term::Nat { nat: *nat }
      },
      Term::Txt { txt } => {
        Term::Txt { txt: txt.clone() }
      },
      Term::Let { nam, val, bod } => {
        Term::Let {
          nam: nam.clone(),
          val: Box::new(val.clean()),
          bod: Box::new(bod.clean()),
        }
      },
      Term::Use { nam, val, bod } => {
        Term::Use {
          nam: nam.clone(),
          val: Box::new(val.clean()),
          bod: Box::new(bod.clean()),
        }
      },
      Term::Var { nam } => {
        Term::Var { nam: nam.clone() }
      },
      Term::Hol { nam } => {
        Term::Hol { nam: nam.clone() }
      },
      Term::Met {} => {
        Term::Met {}
      },
      Term::Src { src: _, val } => {
        val.clean()
      },
    }
  }

}
