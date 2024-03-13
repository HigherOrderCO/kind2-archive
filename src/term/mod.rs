//./../sugar/mod.rs//

use crate::{*};
use std::collections::BTreeSet;

pub mod compile;
pub mod parse;
pub mod show;

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
  // Syntax Sugars that are NOT compiled
  Mch { mch: Box<Match> },
  // Syntax Sugars that are compiled
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

impl Term {

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
      Term::Mch { .. } => {
        unreachable!()
      },
    }
  }

  // Adds lambdas to a term, linearizing matches
  //fn add_lams(lams: &mut im::Vector<String>, term: Term) -> Term {
    //if let Term::Src { src, val } = term {
      //return Term::Src { src, val: add_lams(lams, val) }
    //}
    //if let Term::Mat { .. } = term {
      //todo!()
    //}
    //if let Term::Mch { mch } = term {
    //  if let Some((head,tail)) = lams.split() {
        //let adt  = mch.adt;
        //let name = mch.name;
        //let expr = mch.expr;
        //let cses = mch.cses.map(|nm,x| (nm, add_lams(x, tail)));
        //let moti = mch.moti;
        //return Term::lam {
          //nam: head,
          //bod: Term::Mch { mch: Match { adt, name, expr, cses, moti } }
        //};
      //}
    //}
    //if let Some((head, tail)) = lams.split() {
      //return Term::Lam {
        //nam: head,
        //bod: add_lams(tail, term),
      //}
    //}
    //return term;
  //}

  // TODO: the commented function above is a draft. It has many errors and missing parts. Its goal
  // is to prepend lambdas to a term, passing through matches if possible. For example:
  //   add_lams(["x", "y", "z"], match x { foo: 0, bar: match y { foo: 1, bar: z } })
  // Would result in:
  //   λx match x { foo: λy λz 0, bar: λy match y { foo: λz 1, bar: λz z } }
  // TASK: Write the COMPLETE version of the function below. Add lots of comments.
  // NOTE: Mat and Mch are different constructs. Mat is a numeric pattern match that works only for
  // the U60 type in special. It has a zero/succ case. Mch is a general pattern match that works
  // for any user-defined inductive datatype. It can have an arbitrary number of cases. Both
  // versions must be handled correct by the add_lams fn.

  //Here is the complete add_lams function:

  // Adds lambdas to a term, linearizing matches
  //fn add_lams(&self, lams: &mut im::Vector<String>) -> Term {
    //match self {
      //// Passes through Src, recursing on the inner value
      //Term::Src { src, val } => {
        //let val = Box::new(val.add_lams(lams));
        //Term::Src { src: *src, val }
      //},
      //// Handles a numeric pattern match
      //Term::Mat { nam, x, z, s, p } => {
        //// Prepends a lambda for the matched variable
        //if let Some((head, tail)) = lams.split_first() {
          //let nam = nam.clone();
          //let x = Box::new(x.add_lams(tail));
          //let z = Box::new(z.add_lams(tail));
          //let s = Box::new(s.add_lams(tail));
          //let p = Box::new(p.add_lams(tail));
          //Term::Lam {
            //nam: head.clone(), 
            //bod: Box::new(Term::Mat { nam, x, z, s, p }),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //},
      //// Handles a user-defined ADT match
      //Term::Mch { mch } => {
        //// Prepends a lambda for the matched variable  
        //if let Some((head, tail)) = lams.split_first() {
          //let adt = mch.adt.clone();
          //let name = mch.name.clone();
          //let expr = Box::new(mch.expr.add_lams(tail));
          //let cses = mch.cses.iter().map(|(nm, term)| {
            //(nm.clone(), term.add_lams(tail))
          //}).collect();
          //let moti = mch.moti.as_ref().map(|term| term.add_lams(tail));
          //Term::Lam {
            //nam: head.clone(),
            //bod: Box::new(Term::Mch { 
              //mch: Box::new(Match { adt, name, expr, cses, moti }),
            //}),
          //}
        //} else {
          //// No more lambdas to add, clone self  
          //self.clone()
        //}
      //},
      //// For all other terms, prepend a lambda if possible 
      //term => {
        //if let Some((head, tail)) = lams.split_first() {
          //Term::Lam {
            //nam: head.clone(),
            //bod: Box::new(term.add_lams(tail)),  
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()  
        //}
      //}
    //}
  //}

  // The split_first function seems to not exist on im::Vector. It does have a split_at method though:
  //pub fn split_at(self, index: usize) -> (Self, Self)
  //Split a vector at a given index.
  //Split a vector at a given index, consuming the vector and returning a pair of the left hand side and the right hand side of the split.
  //Time: O(log n)
  //Examples
  //let mut vec = vector![1, 2, 3, 7, 8, 9];
  //let (left, right) = vec.split_at(3);
  //assert_eq!(vector![1, 2, 3], left);
  //assert_eq!(vector![7, 8, 9], right);

  // Fix your implementation to use it.

  // Adds lambdas to a term, linearizing matches
  //fn add_lams(&self, lams: im::Vector<String>) -> Term {
    //match self {
      //// Passes through Src, recursing on the inner value
      //Term::Src { src, val } => {
        //let val = Box::new(val.add_lams(lams.clone()));
        //Term::Src { src: *src, val }
      //},
      //// Handles a numeric pattern match
      //Term::Mat { nam, x, z, s, p } => {
        //// Prepends a lambda for the matched variable
        //if let Some((head, tail)) = lams.split_at(1) {
          //let nam = nam.clone();
          //let x = Box::new(x.add_lams(tail.clone()));
          //let z = Box::new(z.add_lams(tail.clone()));
          //let s = Box::new(s.add_lams(tail.clone()));
          //let p = Box::new(p.add_lams(tail));
          //Term::Lam {
            //nam: head[0].clone(), 
            //bod: Box::new(Term::Mat { nam, x, z, s, p }),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //},
      //// Handles a user-defined ADT match   
      //Term::Mch { mch } => {
        //// Prepends a lambda for the matched variable
        //if let Some((head, tail)) = lams.split_at(1) {
          //let adt = mch.adt.clone();
          //let name = mch.name.clone();
          //let expr = Box::new(mch.expr.add_lams(tail.clone()));
          //let cses = mch.cses.iter().map(|(nm, term)| {
            //(nm.clone(), term.add_lams(tail.clone()))
          //}).collect();
          //let moti = mch.moti.as_ref().map(|term| term.add_lams(tail));
          //Term::Lam {
            //nam: head[0].clone(),
            //bod: Box::new(Term::Mch { 
              //mch: Box::new(Match { adt, name, expr, cses, moti }),
            //}),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}        
      //},
      //// For all other terms, prepend a lambda if possible
      //term => {
        //if let Some((head, tail)) = lams.split_at(1) {
          //Term::Lam {
            //nam: head[0].clone(),
            //bod: Box::new(term.add_lams(tail)),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //}
    //}
  //}

   //Compiling kind2 v0.1.0 (/Users/v/vic/dev/kind2)
//error[E0308]: mismatched types
   //--> src/term/mod.rs:298:16
    //|
//298 |         if let Some((head, tail)) = lams.split_at(1) {
    //|                ^^^^^^^^^^^^^^^^^^   ---------------- this expression has type `(Vector<String>, Vector<String>)`
    //|                |
    //|                expected `(Vector<String>, Vector<String>)`, found `Option<_>`
    //|
    //= note: expected tuple `(Vector<String>, Vector<String>)`
                //found enum `Option<_>`

//error[E0308]: mismatched types
   //--> src/term/mod.rs:316:16
    //|
//316 |         if let Some((head, tail)) = lams.split_at(1) {
    //|                ^^^^^^^^^^^^^^^^^^   ---------------- this expression has type `(Vector<String>, Vector<String>)`
    //|                |
    //|                expected `(Vector<String>, Vector<String>)`, found `Option<_>`
    //|
    //= note: expected tuple `(Vector<String>, Vector<String>)`
                //found enum `Option<_>`

//error[E0308]: mismatched types
   //--> src/term/mod.rs:327:48
    //|
//327 |               mch: Box::new(Match { adt, name, expr, cses, moti }),
    //|                                                ^^^^ expected `Term`, found `Box<Term>`
    //|
    //= note: expected enum `term::Term`
             //found struct `Box<term::Term>`
//help: consider unboxing the value
    //|
//327 |               mch: Box::new(Match { adt, name, expr: *expr, cses, moti }),
    //|                                                +++++++

//error[E0308]: mismatched types
   //--> src/term/mod.rs:337:16
    //|
//337 |         if let Some((head, tail)) = lams.split_at(1) {
    //|                ^^^^^^^^^^^^^^^^^^   ---------------- this expression has type `(Vector<String>, Vector<String>)`
    //|                |
    //|                expected `(Vector<String>, Vector<String>)`, found `Option<_>`
    //|
    //= note: expected tuple `(Vector<String>, Vector<String>)`
                //found enum `Option<_>`

//For more information about this error, try `rustc --explain E0308`.
//error: could not compile `kind2` (bin "kind2") due to 4 previous errors
//RUST_BACKTRACE=1 cargo run  0.10s user 0.04s system 96% cpu 0.148 total

  // There are many errors in your implementation. Fix them.

  // Adds lambdas to a term, linearizing matches
  //fn add_lams(&self, lams: im::Vector<String>) -> Term {
    //match self {
      //// Passes through Src, recursing on the inner value
      //Term::Src { src, val } => {
        //let val = Box::new(val.add_lams(lams.clone()));
        //Term::Src { src: src.clone(), val }
      //},
      //// Handles a numeric pattern match
      //Term::Mat { nam, x, z, s, p } => {
        //// Prepends a lambda for the matched variable
        //if let (head, tail) = lams.split_at(1) {
          //let nam = nam.clone();
          //let x = Box::new(x.add_lams(tail.clone()));
          //let z = Box::new(z.add_lams(tail.clone()));
          //let s = Box::new(s.add_lams(tail.clone()));
          //let p = Box::new(p.add_lams(tail));
          //Term::Lam {
            //nam: head[0].clone(), 
            //bod: Box::new(Term::Mat { nam, x, z, s, p }),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //},
      //// Handles a user-defined ADT match   
      //Term::Mch { mch } => {
        //// Prepends a lambda for the matched variable
        //if let (head, tail) = lams.split_at(1) {
          //let adt = mch.adt.clone();
          //let name = mch.name.clone();
          //let expr = mch.expr.add_lams(tail.clone());
          //let cses = mch.cses.iter().map(|(nm, term)| {
            //(nm.clone(), term.add_lams(tail.clone()))
          //}).collect();
          //let moti = mch.moti.as_ref().map(|term| term.add_lams(tail));
          //Term::Lam {
            //nam: head[0].clone(),
            //bod: Box::new(Term::Mch { 
              //mch: Box::new(Match { adt, name, expr, cses, moti }),
            //}),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}        
      //},
      //// For all other terms, prepend a lambda if possible
      //term => {
        //if let (head, tail) = lams.split_at(1) {
          //Term::Lam {
            //nam: head[0].clone(),
            //bod: Box::new(term.add_lams(tail)),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //}
    //}
  //}

   //Compiling kind2 v0.1.0 (/Users/v/vic/dev/kind2)
//warning: irrefutable `if let` pattern
   //--> src/term/mod.rs:414:12
    //|
//414 |         if let (head, tail) = lams.split_at(1) {
    //|            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    //|
    //= note: this pattern will always match, so the `if let` is useless
    //= help: consider replacing the `if let` with a `let`
    //= note: `#[warn(irrefutable_let_patterns)]` on by default

//warning: irrefutable `if let` pattern
   //--> src/term/mod.rs:432:12
    //|
//432 |         if let (head, tail) = lams.split_at(1) {
    //|            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    //|
    //= note: this pattern will always match, so the `if let` is useless
    //= help: consider replacing the `if let` with a `let`

//warning: irrefutable `if let` pattern
   //--> src/term/mod.rs:453:12
    //|
//453 |         if let (head, tail) = lams.split_at(1) {
    //|            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    //|
    //= note: this pattern will always match, so the `if let` is useless
    //= help: consider replacing the `if let` with a `let`

//warning: function cannot return without recursing
   //--> src/term/mod.rs:404:3
    //|
//404 |   fn add_lams(&self, lams: im::Vector<String>) -> Term {
    //|   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ cannot return without recursing
//...
//408 |         let val = Box::new(val.add_lams(lams.clone()));
    //|                            -------------------------- recursive call site
//...
//416 |           let x = Box::new(x.add_lams(tail.clone()));
    //|                            ------------------------ recursive call site
//...
//435 |           let expr = mch.expr.add_lams(tail.clone());
    //|                      ------------------------------- recursive call site
//...
//456 |             bod: Box::new(term.add_lams(tail)),
    //|                           ------------------- recursive call site
    //|
    //= help: a `loop` may express intention better if this is on purpose
    //= note: `#[warn(unconditional_recursion)]` on by default

  // There are still some errors, including an infinite loop, it seems.
  // You probably need to check the len(), since split_at doesn't return an Option.
  // Fix it:

  // Adds lambdas to a term, linearizing matches
  //fn add_lams(&self, lams: im::Vector<String>) -> Term {
    //match self {
      //// Passes through Src, recursing on the inner value
      //Term::Src { src, val } => {
        //let val = Box::new(val.add_lams(lams.clone()));
        //Term::Src { src: src.clone(), val }
      //},
      //// Handles a numeric pattern match
      //Term::Mat { nam, x, z, s, p } => {
        //// Prepends a lambda for the matched variable
        //if lams.len() >= 1 {
          //let (head, tail) = lams.split_at(1);
          //let nam = nam.clone();
          //let x = Box::new(x.add_lams(tail.clone()));
          //let z = Box::new(z.add_lams(tail.clone()));
          //let s = Box::new(s.add_lams(tail.clone()));
          //let p = Box::new(p.add_lams(tail));
          //Term::Lam {
            //nam: head[0].clone(), 
            //bod: Box::new(Term::Mat { nam, x, z, s, p }),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //},
      //// Handles a user-defined ADT match   
      //Term::Mch { mch } => {
        //// Prepends a lambda for the matched variable
        //if lams.len() >= 1 {
          //let (head, tail) = lams.split_at(1);  
          //let adt = mch.adt.clone();
          //let name = mch.name.clone();
          //let expr = mch.expr.add_lams(tail.clone());
          //let cses = mch.cses.iter().map(|(nm, term)| {
            //(nm.clone(), term.add_lams(tail.clone()))
          //}).collect();
          //let moti = mch.moti.as_ref().map(|term| term.add_lams(tail));
          //Term::Lam {
            //nam: head[0].clone(),
            //bod: Box::new(Term::Mch { 
              //mch: Box::new(Match { adt, name, expr, cses, moti }),
            //}),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}        
      //},
      //// For all other terms, prepend a lambda if possible
      //term => {
        //if lams.len() >= 1 {
          //let (head, tail) = lams.split_at(1);
          //Term::Lam {
            //nam: head[0].clone(),
            //bod: Box::new(term.add_lams(tail)),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //}
    //}
  //}

  // I apologize, but the function above is still wrong. It should only append a lambda on the Mtch
  // case when the matched variable name is the same as the lams head. Otherwise, it should just
  // fallback to the "for all other terms..." case. Fix it:

  // Adds lambdas to a term, linearizing matches
  //fn add_lams(&self, lams: im::Vector<String>) -> Term {
    //match self {
      //// Passes through Src, recursing on the inner value
      //Term::Src { src, val } => {
        //let val = Box::new(val.add_lams(lams.clone()));
        //Term::Src { src: src.clone(), val }
      //},
      //// Handles a numeric pattern match
      //Term::Mat { nam, x, z, s, p } => {
        //// Prepends a lambda for the matched variable
        //if lams.len() >= 1 {
          //let (head, tail) = lams.split_at(1);
          //let nam = nam.clone();
          //let x = Box::new(x.add_lams(tail.clone()));
          //let z = Box::new(z.add_lams(tail.clone()));
          //let s = Box::new(s.add_lams(tail.clone()));
          //let p = Box::new(p.add_lams(tail));
          //Term::Lam {
            //nam: head[0].clone(), 
            //bod: Box::new(Term::Mat { nam, x, z, s, p }),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //},
      //// Handles a user-defined ADT match   
      //Term::Mch { mch } => {
        //// Prepends a lambda for the matched variable if it matches the head of lams
        //if lams.len() >= 1 && lams[0] == mch.name {  
          //let (head, tail) = lams.split_at(1);
          //let adt = mch.adt.clone();
          //let name = mch.name.clone();
          //let expr = mch.expr.add_lams(tail.clone());
          //let cses = mch.cses.iter().map(|(nm, term)| {
            //(nm.clone(), term.add_lams(tail.clone()))
          //}).collect();
          //let moti = mch.moti.as_ref().map(|term| term.add_lams(tail));
          //Term::Lam {
            //nam: head[0].clone(),
            //bod: Box::new(Term::Mch { 
              //mch: Box::new(Match { adt, name, expr, cses, moti }),
            //}),
          //}
        //} else {
          //// Fallback to the default case for other terms
          //if lams.len() >= 1 {
            //let (head, tail) = lams.split_at(1);
            //Term::Lam {
              //nam: head[0].clone(),
              //bod: Box::new(self.add_lams(tail)),
            //}
          //} else {
            //// No more lambdas to add, clone self
            //self.clone()
          //}
        //}        
      //},
      //// For all other terms, prepend a lambda if possible
      //term => {
        //if lams.len() >= 1 {
          //let (head, tail) = lams.split_at(1);
          //Term::Lam {
            //nam: head[0].clone(),
            //bod: Box::new(term.add_lams(tail)),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //}
    //}
  //}

  // You forgot to add the name check on the Mat case. Also, your code became repetitive. Refactor
  // the form of the function to avoid redundant code.

  // Adds lambdas to a term, linearizing matches
  //fn add_lams(&self, lams: im::Vector<String>) -> Term {
    //match self {
      //// Passes through Src, recursing on the inner value
      //Term::Src { src, val } => {
        //let val = Box::new(val.add_lams(lams.clone()));
        //Term::Src { src: src.clone(), val }
      //},
      //// Handles a numeric or user-defined pattern match
      //Term::Mat { nam, x, z, s, p } | Term::Mch { mch: Match { name, expr, cses, moti, .. } } => {
        //if lams.len() >= 1 && lams[0] == nam || lams.len() >= 1 && lams[0] == name {
          //let (head, tail) = lams.split_at(1);
          //match self {
            //Term::Mat { nam, x, z, s, p } => {
              //let nam = nam.clone();
              //let x = Box::new(x.add_lams(tail.clone()));
              //let z = Box::new(z.add_lams(tail.clone()));
              //let s = Box::new(s.add_lams(tail.clone()));
              //let p = Box::new(p.add_lams(tail));
              //Term::Lam { 
                //nam: head[0].clone(),
                //bod: Box::new(Term::Mat { nam, x, z, s, p }),
              //}
            //},
            //Term::Mch { mch: Match { adt, name, expr, cses, moti } } => {
              //let adt = adt.clone();
              //let name = name.clone();
              //let expr = expr.add_lams(tail.clone());
              //let cses = cses.iter().map(|(nm, term)| {
                //(nm.clone(), term.add_lams(tail.clone()))  
              //}).collect();
              //let moti = moti.as_ref().map(|term| term.add_lams(tail));
              //Term::Lam {
                //nam: head[0].clone(),
                //bod: Box::new(Term::Mch {
                  //mch: Box::new(Match { adt, name, expr, cses, moti }),  
                //}),
              //}
            //},
            //_ => unreachable!(),
          //}
        //} else {
          //self.clone()  
        //}
      //},
      //// For all other terms, prepend a lambda if possible
      //term => {
        //if lams.len() >= 1 {
          //let (head, tail) = lams.split_at(1);
          //Term::Lam {
            //nam: head[0].clone(),
            //bod: Box::new(term.add_lams(tail)),
          //}
        //} else {
          //// No more lambdas to add, clone self
          //self.clone()
        //}
      //}
    //}
  //}

  // Sorry but I really don't like the style of this function, with the merged mat/mch. I believe
  // it would look better if you just made a chain if `if let ... = self` instead of a single
  // `match self` right on the beginning. That way, you could early return when there is something
  // to do, and just let it fall to the end of the function otherwise, where the "other terms"
  // logic occurs. Does that make sense? Can you try?

  // Recurses through the term, desugaring Mch constructors
  pub fn desugar(&mut self) {
    match self {
      // Desugars the Mch constructor using sugar::new_match
      Term::Mch { mch } => {
        *self = Term::new_match(&mch);
        self.desugar();
      },
      // Recurses on subterms for all other constructors
      Term::All { nam: _, inp, bod } => {
        inp.desugar();
        bod.desugar();
      },
      Term::Lam { nam: _, bod } => {
        bod.desugar();
      },
      Term::App { fun, arg } => {
        fun.desugar();
        arg.desugar();
      },
      Term::Ann { chk: _, val, typ } => {
        val.desugar();
        typ.desugar();
      },
      Term::Slf { nam: _, typ, bod } => {
        typ.desugar();
        bod.desugar();
      },
      Term::Ins { val } => {
        val.desugar();
      },
      Term::Op2 { opr: _, fst, snd } => {
        fst.desugar();
        snd.desugar();
      },
      Term::Mat { nam: _, x, z, s, p } => {
        x.desugar();
        z.desugar();
        s.desugar(); 
        p.desugar();
      },
      Term::Let { nam: _, val, bod } => {
        val.desugar();
        bod.desugar();
      },
      Term::Use { nam: _, val, bod } => {
        val.desugar();
        bod.desugar();
      },
      Term::Src { src: _, val } => {
        val.desugar();
      },
      // Base cases, do nothing
      Term::Set => {},
      Term::U60 => {},
      Term::Num { val: _ } => {},
      Term::Nat { nat: _ } => {},
      Term::Txt { txt: _ } => {},
      Term::Var { nam: _ } => {},
      Term::Hol { nam: _ } => {},
      Term::Met {} => {},
    }
  }

  //pub fn count_metas(&self) -> usize {
    //match self {
      //Term::All { inp, bod, .. } => {
        //let inp = inp.count_metas();
        //let bod = bod.count_metas();
        //inp + bod
      //},
      //Term::Lam { bod, .. } => {
        //let bod = bod.count_metas();
        //bod
      //},
      //Term::App { fun, arg } => {
        //let fun = fun.count_metas();
        //let arg = arg.count_metas();
        //fun + arg
      //},
      //Term::Ann { chk: _, val, typ } => {
        //let val = val.count_metas();
        //let typ = typ.count_metas();
        //val + typ
      //},
      //Term::Slf { typ, bod, .. } => {
        //let typ = typ.count_metas();
        //let bod = bod.count_metas();
        //typ + bod
      //},
      //Term::Ins { val } => {
        //let val = val.count_metas();
        //val
      //},
      //Term::Set => {
        //0
      //},
      //Term::U60 => {
        //0
      //},
      //Term::Num { .. } => {
        //0
      //},
      //Term::Op2 { fst, snd, .. } => {
        //let fst = fst.count_metas();
        //let snd = snd.count_metas();
        //fst + snd
      //},
      //Term::Mat { x, z, s, p, .. } => {
        //let x = x.count_metas();
        //let z = z.count_metas();
        //let s = s.count_metas();
        //let p = p.count_metas();
        //x + z + s + p
      //},
      //Term::Nat { .. } => {
        //0
      //},
      //Term::Txt { .. } => {
        //0
      //},
      //Term::Let { val, bod, .. } => {
        //let val = val.count_metas();
        //let bod = bod.count_metas();
        //val + bod
      //},
      //Term::Use { val, bod, .. } => {
        //let val = val.count_metas();
        //let bod = bod.count_metas();
        //val + bod
      //},
      //Term::Hol { .. } => {
        //0
      //},
      //Term::Met { .. } => {
        //1
      //},
      //Term::Var { .. } => {
        //0
      //},
      //Term::Src { val, .. } => {
        //let val = val.count_metas();
        //val
      //},
      //Term::Mch { .. } => {
        //unreachable!()
      //},
    //}
  //}

  //pub fn clean(&self) -> Term {
    //match self {
      //Term::All { nam, inp, bod } => {
        //Term::All {
          //nam: nam.clone(),
          //inp: Box::new(inp.clean()),
          //bod: Box::new(bod.clean()),
        //}
      //},
      //Term::Lam { nam, bod } => {
        //Term::Lam {
          //nam: nam.clone(),
          //bod: Box::new(bod.clean()),
        //}
      //},
      //Term::App { fun, arg } => {
        //Term::App {
          //fun: Box::new(fun.clean()),
          //arg: Box::new(arg.clean()),
        //}
      //},
      //Term::Ann { chk, val, typ } => {
        //Term::Ann {
          //chk: *chk,
          //val: Box::new(val.clean()),
          //typ: Box::new(typ.clean()),
        //}
      //},
      //Term::Slf { nam, typ, bod } => {
        //Term::Slf {
          //nam: nam.clone(),
          //typ: Box::new(typ.clean()),
          //bod: Box::new(bod.clean()),
        //}
      //},
      //Term::Ins { val } => {
        //Term::Ins {
          //val: Box::new(val.clean()),
        //}
      //},
      //Term::Set => {
        //Term::Set
      //},
      //Term::U60 => {
        //Term::U60
      //},
      //Term::Num { val } => {
        //Term::Num { val: *val }
      //},
      //Term::Op2 { opr, fst, snd } => {
        //Term::Op2 {
          //opr: *opr,
          //fst: Box::new(fst.clean()),
          //snd: Box::new(snd.clean()),
        //}
      //},
      //Term::Mat { nam, x, z, s, p } => {
        //Term::Mat {
          //nam: nam.clone(),
          //x: Box::new(x.clean()),
          //z: Box::new(z.clean()),
          //s: Box::new(s.clean()),
          //p: Box::new(p.clean()),
        //}
      //},
      //Term::Nat { nat } => {
        //Term::Nat { nat: *nat }
      //},
      //Term::Txt { txt } => {
        //Term::Txt { txt: txt.clone() }
      //},
      //Term::Let { nam, val, bod } => {
        //Term::Let {
          //nam: nam.clone(),
          //val: Box::new(val.clean()),
          //bod: Box::new(bod.clean()),
        //}
      //},
      //Term::Use { nam, val, bod } => {
        //Term::Use {
          //nam: nam.clone(),
          //val: Box::new(val.clean()),
          //bod: Box::new(bod.clean()),
        //}
      //},
      //Term::Var { nam } => {
        //Term::Var { nam: nam.clone() }
      //},
      //Term::Hol { nam } => {
        //Term::Hol { nam: nam.clone() }
      //},
      //Term::Met {} => {
        //Term::Met {}
      //},
      //Term::Src { src: _, val } => {
        //val.clean()
      //},
      //Term::Mch { .. } => {
        //unreachable!()
      //},
    //}
  //}

}
