use crate::{*};

//./../term/mod.rs//

// A List.
#[derive(Debug, Clone)]
pub struct List {
  pub vals: Vec<Box<Term>>,
}

// An Algebraic Data Type (ADT).
#[derive(Debug, Clone)]
pub struct ADT {
  pub name: String,
  pub pars: Vec<String>, // parameters
  pub idxs: Vec<(String,Term)>, // indices
  pub ctrs: Vec<Constructor>, // constructors
}

#[derive(Debug, Clone)]
pub struct Constructor {
  pub name: String, // constructor name
  pub flds: Vec<(String,Term)>, // constructor fields
  pub idxs: Vec<Term>, // constructor type indices
}

// NOTE: we've just added the 'with' field to the 'match' sugar.
// We must now refactor some functions to enable it.
#[derive(Debug, Clone)]
pub struct Match {
  pub adt: String, // datatype
  pub name: String, // scrutinee name
  pub expr: Term, // structinee expression
  pub with: Vec<(String,Term)>, // terms to move in
  pub cses: Vec<(String,Term)>, // matched cases
  pub moti: Option<Term>, // motive
}

// Examples:
// 
// The Vector type:
//
//   data Vector A (len: Nat)
//   | nil : (Vector A zero)
//   | cons (len: Nat) (head: A) (tail: (Vector A len)) : (Vector A (succ len))
//
// Has the following λ-encoding:
//
//   Vector
//   : ∀(A: *) ∀(len: Nat) *
//   = λA λlen
//     $(self: (Vector A len))
//     ∀(P: ∀(len: Nat) ∀(x: (Vector A len)) *)
//     ∀(cons: ∀(len: Nat) ∀(head: A) ∀(tail: (Vector A len)) (P (Nat.succ len) (Vector.cons A len head tail)))
//     ∀(nil: (P 0 (Vector.nil A)))
//     (P len self)
//
// And is represented on Rust as:
//
//   let vector = ADT {
//     name: "Vector".to_string(),
//     pars: vec!["A".to_string()],
//     idxs: vec![("len".to_string(), Term::Var { nam: "Nat".to_string() })],
//     ctrs: vec![
//       Constructor {
//         name: "nil".to_string(),
//         flds: vec![],
//         idxs: vec![
//           Term::Var { nam: "A".to_string() },
//           Term::Var { nam: "zero".to_string() },
//         ],
//       },
//       Constructor { 
//         name: "cons".to_string(),
//         flds: vec![
//           ("len".to_string(), Term::Var { nam: "Nat".to_string() }),
//           ("head".to_string(), Term::Var { nam: "A".to_string() }),
//           ("tail".to_string(), Term::App {
//             fun: Box::new(Term::App {
//               fun: Box::new(Term::Var { nam: "Vector".to_string() }),
//               arg: Box::new(Term::Var { nam: "A".to_string() }),
//             }),
//             arg: Box::new(Term::Var { nam: "len".to_string() }),
//           }),        
//         ],
//         idxs: vec![
//           Term::Var { nam: "A".to_string() },
//           Term::App {
//             fun: Box::new(Term::Var { nam: "succ".to_string() }),
//             arg: Box::new(Term::Var { nam: "len".to_string() }),
//           },
//         ],
//       },
//     ],
//   };
//
// A pattern-match is represented as: 
//
//   match name = expr with (a: A) (b: B) ... {
//     ADT.foo: ...
//     ADT.bar: ...
//   }: motive
//
// Note:
// 1. The `= expr` can be omitted. Will default to `Var { name }`.
// 2. The `: motive` can be omitted. Will default to `Met {}`.
// 3. The ADT is obtained from the 'ADT.ctr' cases.
// 4. If there are no cases, ADT is defaulted to 'Empty'.
// 5. The 'with' clause is optional.
//
// The 'with' clause moves outer vars inwards, linearizing them. For example:
//   let a = (f y)
//   match x {
//     tic: a
//     tac: a
//   }
// Would, normally, cause 'a' to be *cloned*. This has two problems:
// 1. Cloning can have large efficiency costs in some runtimes, such as the HVM.
// 2. If 'x' occurs in the type of 'a', it won't get specialized, blocking proofs.
// The 'with' clause allows us to solve both issues. For example:
//   let a = (f y)
//   match x with a {
//     tic: a
//     tac: a
//   }
// This expression is desugared as:
//   let a = (f y)
//   let b = (g y)
//   ({(match x with (a: A) (b: B) ... {
//     tic: λa a
//     tac: λa a
//   }): ∀(a: A) ∀(b: B) _} a b)
// Or, in raw terms, the 'match_expr' is changed to:
//   (APP (APP (ANN match_expr (ALL "a" A (ALL "b" B ... MET))) a) b)

// Nat
// ---

impl Term {

  // Interprets as a Nat:
  // - (Nat.succ (Nat.succ ... Nat.zero))
  // Patterns:
  // - (SUCC pred) ::= (App (Var "Nat.succ") pred)
  // - ZERO        ::= (Var "Nat.zero")
  pub fn as_nat(&self) -> Option<u64> {
    let mut nat = 0;
    let mut term = self;
    loop {
      match term {
        Term::App { fun, arg } => {
          if let Term::Var { nam } = &**fun {
            if nam == "Nat.succ" {
              nat += 1;
              term = arg;
              continue;
            }
          }
          return None;
        },
        Term::Var { nam } if nam == "Nat.zero" => {
          return Some(nat);
        },
        _ => {
          return None;
        }
      }
    }
  }

  // Nats have a dedicated term, for type-checking efficiency
  pub fn new_nat(nat: u64) -> Term {
    Term::Nat { nat }
  }

}

// List
// ----

impl Term {

  // Interprets as a list:
  // - (((List.cons _) x) (((List.cons _) y) ... (List.nil _)))
  // Patterns:
  // - (CONS head tail) ::= (App (App (App (Var "List.cons") Met) head) tail)
  // - NIL              ::= (App (Var "List.nil") Met)
  pub fn as_list(&self) -> Option<List> {
    let mut vals = Vec::new();
    let mut term = self;
    loop {
      match term {
        Term::App { fun, arg } => {
          if let Term::App { fun: cons, arg: head } = &**fun {
            if let Term::App { fun: cons_fun, arg: _ } = &**cons {
              if let Term::Var { nam } = &**cons_fun {
                if nam == "List.cons" {
                  vals.push(head.clone());
                  term = arg;
                  continue;
                }
              }
            }
          }
          if let Term::Var { nam } = &**fun {
            if nam == "List.nil" {
              return Some(List { vals });
            }
          }
          return None;
        },
        _ => return None,
      }
    }
  }

  // Builds a chain of applications of List.cons and List.nil from a Vec<Box<Term>>
  pub fn new_list(list: &List) -> Term {
    let mut term = Term::App {
      fun: Box::new(Term::Var { nam: "List.nil".to_string() }),
      arg: Box::new(Term::Met {}),
    };
    for item in (&list.vals).into_iter().rev() {
      term = Term::App {
        fun: Box::new(Term::App {
          fun: Box::new(Term::App {
            fun: Box::new(Term::Var { nam: "List.cons".to_string() }),
            arg: Box::new(Term::Met {}),
          }),
          arg: item.clone(),
        }),
        arg: Box::new(term),
      };
    }
    term
  }

}

// ADT
// ---

impl Term {

  // Interprets a λ-encoded Algebraic Data Type definition as an ADT struct.
  pub fn as_adt(&self) -> Option<ADT> {

    let name: String;
    let pvar: String;

    let mut pars: Vec<String> = Vec::new();
    let mut idxs: Vec<(String,Term)> = Vec::new();
    let mut ctrs: Vec<Constructor> = Vec::new();
    let mut term = self;

    // Skips the Slf: `$(self: (TY P0 P1 ... I0 I1 ...))`
    if let Term::Slf { nam: _, typ: _, bod } = term {
      term = bod;
    } else {
      return None;
    }

    // Reads the motive: `∀(P: ∀(I0: I0.TY) ∀(I1: I1.TY) ... ∀(x: (TY P0 P1 ... I0 I1 ...)) *).`
    if let Term::All { nam, inp, bod } = term {
      // Gets the motive name
      pvar = nam.clone();

      // Gets the motive type
      let mut moti = &**inp;

      // Reads each motive index
      while let Term::All { nam, inp: idx_inp, bod: idx_bod } = moti {
        if let Term::All { .. } = &**idx_bod {
          idxs.push((nam.clone(), *idx_inp.clone()));
          moti = idx_bod;
        } else {
          break;
        }
      }

      // Skips the witness
      if let Term::All { nam: _, inp: wit_inp, bod: wit_bod } = moti {

        // Here, the witness has form '(TY P0 P1 ... I0 I1 ...)'
        let mut wit_inp = wit_inp;

        // Skips the wit's indices (outermost Apps)
        for _ in 0 .. idxs.len() {
          if let Term::App { fun: wit_inp_fun, arg: _ } = &**wit_inp {
            wit_inp = wit_inp_fun;
          } else {
            return None;
          }
        }

        // Collects the wit's parameters (remaining Apps)
        while let Term::App { fun: wit_inp_fun, arg: wit_inp_arg } = &**wit_inp {
          if let Term::Var { nam: parameter } = &**wit_inp_arg {
            pars.push(parameter.to_string());
            wit_inp = wit_inp_fun;
          } else {
            return None;
          }
        }

        // Extracts the type name
        if let Term::Var { nam } = &**wit_inp {
          name = nam.clone();
        } else {
          return None;
        }
        moti = &wit_bod;
      } else {
        return None;
      }

      // Checks if the motive ends in Set
      if let Term::Set = moti {
        // Correct.
      } else {
        return None;
      }

      term = bod;
    } else {
      return None;
    }

    // Reads each constructor: `∀(C0: ∀(C0_F0: C0_F0.TY) ∀(C0_F1: C0_F1.TY) ... (P I0 I1 ... (TY.C0 P0 P1 ... C0_F0 C0_F1 ...)))`
    while let Term::All { nam, inp, bod } = term {
      let mut flds: Vec<(String,Term)> = Vec::new();
      let mut ctyp: &Term = &**inp;

      // Reads each field
      while let Term::All { nam, inp, bod } = ctyp {
        flds.push((nam.clone(), *inp.clone()));
        ctyp = bod;
      }

      // Now, the ctyp will be in the form (P I0 I1 ... (Ctr P0 P1 ... F0 F1 ...))
      
      // Skips the outermost application
      if let Term::App { fun: ctyp_fun, arg: _ } = ctyp {
        ctyp = ctyp_fun;
      } else {
        return None;
      }

      // Collects constructor indices until we reach the pattern head P
      let mut ctr_idxs: Vec<Term> = Vec::new();
      while let Term::App { fun: fun_app, arg: arg_app } = ctyp {
        ctr_idxs.push(*arg_app.clone());
        ctyp = fun_app;
      }

      // Checks if the pattern fun is `pvar`
      if let Term::Var { nam } = ctyp {
        if nam != &pvar {
          return None;
        }
      } else {
        return None;
      }
      
      ctr_idxs.reverse();
      ctrs.push(Constructor { name: nam.clone(), flds, idxs: ctr_idxs });
      
      term = bod;
    }

    return Some(ADT { name, pars, idxs, ctrs });
  }

  // Builds a λ-encoded Algebraic Data Type definition from an ADT struct.
  pub fn new_adt(adt: &ADT) -> Term {
    // 1. Builds the self type: (Type P0 P1 ... I0 I1 ...)
    
    // Starts with the type name
    let mut self_type = Term::Var { nam: adt.name.clone() };

    // Then appends each type parameter
    for par in adt.pars.iter().rev() {
      self_type = Term::App { fun: Box::new(self_type), arg: Box::new(Term::Var { nam: par.clone() }) };
    }

    // And finally appends each index
    for (idx_name, _) in adt.idxs.iter().rev() {
      self_type = Term::App { fun: Box::new(self_type), arg: Box::new(Term::Var { nam: idx_name.clone() }) };
    }

    // 2. Builds the motive type: ∀(I0: I0.TY) ∀(I1: I1.TY) ... ∀(x: (Type P0 P1 ... I0 I1 ...)) *
    
    // Starts with the witness type: ∀(x: (Type P0 P1 ... I0 I1 ...)) *
    let mut motive_type = Term::All {
      nam: "x".to_string(),
      inp: Box::new(self_type.clone()),
      bod: Box::new(Term::Set),
    };

    // Then prepends each index type
    for (idx_name, idx_type) in adt.idxs.iter().rev() {
      motive_type = Term::All {
        nam: idx_name.clone(),
        inp: Box::new(idx_type.clone()),
        bod: Box::new(motive_type),
      };
    }
    
    // 3. Builds the final term, starting with the self application: (P I0 I1 ... self)
    let mut term = Term::Var { nam: "P".to_string() };

    // Applies the motive to each index
    for (idx_name, _) in adt.idxs.iter() {
      term = Term::App {
        fun: Box::new(term),
        arg: Box::new(Term::Var { nam: idx_name.clone() }),
      };
    }

    // And applies it to the witness (self)
    term = Term::App {
      fun: Box::new(term),
      arg: Box::new(Term::Var { nam: "self".to_string() }),
    };

    // 4. Prepends each constructor: ∀(C0: ∀(C0_F0: C0_F0.TY) ∀(C0_F1: C0_F1.TY) ... (P C0_I0 C0_I1 ... (Type.C0 P0 P1 ... C0_F0 C0_F1 ...)))
    for ctr in adt.ctrs.iter().rev() {
      // Builds the constructor application: (P C0_I0 C0_I1 ... (Type.C0 P0 P1 ... C0_F0 C0_F1 ...))
      let mut ctr_term = Term::Var { nam: "P".to_string() };

      // Applies the motive to each constructor index
      for idx in ctr.idxs.iter().rev() {
        ctr_term = Term::App {
          fun: Box::new(ctr_term),
          arg: Box::new(idx.clone()),
        };
      }

      // Builds the constructor type: (Type.C0 P0 P1 ... C0_F0 C0_F1 ...)
      let mut ctr_type = Term::Var { nam: format!("{}.{}", adt.name, ctr.name) };

      // For each type parameter
      for par in adt.pars.iter() {
        ctr_type = Term::App {
          fun: Box::new(ctr_type),
          arg: Box::new(Term::Var { nam: par.clone() }),
        };
      }

      // And for each field
      for (fld_name, _fld_type) in ctr.flds.iter() {
        ctr_type = Term::App {
          fun: Box::new(ctr_type),
          arg: Box::new(Term::Var { nam: fld_name.clone() }),
        };
      }

      // Wraps the constructor type with the application
      ctr_term = Term::App {
        fun: Box::new(ctr_term),
        arg: Box::new(ctr_type),
      };

      // Finally, quantifies each field
      for (fld_name, fld_type) in ctr.flds.iter().rev() {
        ctr_term = Term::All {
          nam: fld_name.clone(),
          inp: Box::new(fld_type.clone()),
          bod: Box::new(ctr_term),
        };
      }

      // And quantifies the constructor
      term = Term::All {
        nam: ctr.name.clone(), 
        inp: Box::new(ctr_term),
        bod: Box::new(term),
      };
    }

    // 5 Quantifies the motive
    term = Term::All {
      nam: "P".to_string(),
      inp: Box::new(motive_type),
      bod: Box::new(term),
    };

    // 6. Wraps everything with a self annotation
    term = Term::Slf {
      nam: "self".to_string(),
      typ: Box::new(self_type),
      bod: Box::new(term),
    };

    //println!("RESULT:\n{:#?}", term.format());
    //println!("PARSED:\n{}", term.format().flatten(Some(80)));

    return term;
  }

  // Builds a λ-encoded pattern-match. For example, the expression:
  //   match x = (f arg) with (a: A) (b: B) {
  //     Vector.cons: (U60.add x.head (sum x.tail))
  //     Vector.nil: #0
  //   }: #U60
  // Is converted to:
  //   use x.P = λx.len λx ∀(a: A) ∀(b: B) #U60
  //   use x.cons = λx.head λx.tail λa λb ((U60.add x.head) (sum x.tail))
  //   use x.nil = λx.len λa λb #0
  //   (({(((~(f arg) x.P) x.cons) x.nil): ∀(a: A) ∀(b: B) _} a) b)
  pub fn new_match(mat: &Match) -> Term {
    let adt = ADT::load(&mat.adt).expect(&format!("Cannot load datatype '{}'", &mat.adt));

    let mut term: Term;

    // 1. Create the motive's term
    let mut motive;
    if let Some(moti) = &mat.moti {
      // Creates the first lambda: 'λx <motive>'
      motive = Term::Lam {
        nam: mat.name.clone(),
        bod: Box::new(moti.clone()),
      };
      // Creates a lambda for each index: 'λindices ... λx <motive>'
      for (idx_name, _) in adt.idxs.iter().rev() {
        motive = Term::Lam {
          nam: idx_name.clone(),
          bod: Box::new(motive),
        };
      }
      // Creates a forall for each moved value: 'λindices ... λx ∀(a: A) ... <motive>'
      for (nam, typ) in mat.with.iter().rev() {
        motive = Term::All {
          nam: nam.clone(),
          inp: Box::new(typ.clone()),
          bod: Box::new(motive),
        };
      }
    } else {
      // If there is no explicit motive, default to a metavar
      motive = Term::Met {};
    }

    // 2. Create each constructor's term
    let mut ctrs: Vec<Term> = Vec::new();
    for ctr in &adt.ctrs {
      // Find this constructor's case
      let found = mat.cses.iter().find(|(case_name, _)| {
        return case_name == &format!("{}.{}", adt.name, ctr.name);
      });
      if let Some((_, case_term)) = found {
        // If it is present...
        let mut ctr_term = case_term.clone();
        // Adds moved value lambdas
        for (nam, _) in mat.with.iter().rev() {
          ctr_term = Term::Lam {
            nam: nam.clone(),
            bod: Box::new(ctr_term),
          };
        }
        // Adds field lambdas
        for (fld_name, _) in ctr.flds.iter().rev() {
          ctr_term = Term::Lam {
            nam: format!("{}.{}", mat.name, fld_name.clone()),
            bod: Box::new(ctr_term),
          };
        }
        ctrs.push(ctr_term);
      } else {
        // Otherwise, show an error. TODO: improve the error reporting here
        println!("Missing case for constructor '{}' on {} match.", ctr.name, mat.adt);
        std::process::exit(0);
      }
    }

    // 3. Wrap Ins around term
    term = Term::Ins {
      val: Box::new(mat.expr.clone())
    };

    // 4. Apply the motive, making a Var for it
    term = Term::App {
      fun: Box::new(term),
      arg: Box::new(Term::Var { nam: format!("{}.P", mat.name) }),
    };

    // 5. Apply each constructor (by name)
    for ctr in &adt.ctrs {
      term = Term::App {
        fun: Box::new(term),
        arg: Box::new(Term::Var { nam: format!("{}.{}", mat.name, ctr.name) }),
      };
    }

    // 6. Annotates with the moved var foralls
    if mat.with.len() > 0 {
      let mut ann_type = Term::Met {};
      for (nam, typ) in mat.with.iter().rev() {
        ann_type = Term::All {
          nam: nam.clone(),
          inp: Box::new(typ.clone()),
          bod: Box::new(ann_type),
        };
      }
      term = Term::Ann {
        val: Box::new(term),
        typ: Box::new(ann_type),
        chk: true,
      };
    }

    // 7. Applies each moved var
    for (nam, _) in mat.with.iter() {
      term = Term::App {
        fun: Box::new(term),
        arg: Box::new(Term::Var { nam: nam.clone() }),
      };  
    }

    // 8. Create the local 'use' definition for each term
    for (i,ctr) in adt.ctrs.iter().enumerate().rev() {
      term = Term::Use {
        nam: format!("{}.{}", mat.name, ctr.name),
        val: Box::new(ctrs[i].clone()),
        bod: Box::new(term)
      };
    }

    // 9. Create the local 'use' definition for the motive
    term = Term::Use {
      nam: format!("{}.P", mat.name),
      val: Box::new(motive),
      bod: Box::new(term)
    };

    //println!("PARSED:\n{}", term.show());

    // 10. Return 'term'
    return term;
  }

}

impl ADT {
  
  // Loads an ADT from its λ-encoded file.
  pub fn load(name: &str) -> Result<ADT, String> {
    let book = Book::boot(name)?;
    if let Some(term) = book.defs.get(name) {
      let mut term = term.clone();
      // Skips Anns, Lams, Srcs
      loop {
        match term {
          Term::Ann { val, .. } => { term = *val; }
          Term::Lam { bod, .. } => { term = *bod; }
          Term::Src { val, .. } => { term = *val; }
          _ => { break; }
        }
      }
      //println!("{}", term.format().flatten(Some(800)));
      return term.as_adt().ok_or_else(|| format!("Failed to interpret '{}' as an ADT.", name))
    } else {
      Err(format!("Cannot find definition for type '{}'.", name))
    }
  }

}


impl List {
  
  pub fn format(&self) -> Box<Show> {
    if self.vals.len() == 0 {
      return Show::text("[]");
    } else {
      return Show::call("", vec![
        Show::text("["),
        Show::pile(", ", self.vals.iter().map(|x| x.format_go()).collect()),
        Show::text("]"),
      ]);
    }
  }

}

impl ADT {
  
  pub fn format(&self) -> Box<Show> {

    // ADT head: `data Name <params> <indices>`
    let mut adt_head = vec![];
    adt_head.push(Show::text("data"));
    adt_head.push(Show::text(&self.name));
    for par in self.pars.iter() {
      adt_head.push(Show::text(par));
    }
    for (nam,typ) in self.idxs.iter() {
      adt_head.push(Show::call("", vec![
        Show::glue("", vec![Show::text("("), Show::text(nam), Show::text(": ")]),
        typ.format_go(),
        Show::text(")"),
      ]));
    }

    // ADT tail: constructors
    let mut adt_tail = vec![];
    for ctr in &self.ctrs {
      let mut adt_ctr = vec![];
      // Constructor head: name
      adt_ctr.push(Show::glue("", vec![
        Show::line(),
        Show::text("| "),
        Show::text(&ctr.name),
      ]));
      // Constructor body: fields
      for (nam,typ) in ctr.flds.iter() {
        adt_ctr.push(Show::call("", vec![
          Show::glue("", vec![
            Show::text("("),
            Show::text(nam),
            Show::text(": "),
          ]),
          typ.format_go(),
          Show::text(")"),  
        ]));
      }
      // Constructor tail: return
      adt_ctr.push(Show::glue(" ", vec![
        Show::text(":"),
        Show::call(" ", {
          let mut ret_typ = vec![];
          ret_typ.push(Show::text(&format!("({}", &self.name)));
          for par in &self.pars {
            ret_typ.push(Show::text(par));
          }
          for idx in &ctr.idxs {
            ret_typ.push(idx.format_go());
          }
          ret_typ.push(Show::text(")"));
          ret_typ
        })
      ]));
      adt_tail.push(Show::call(" ", adt_ctr));
    }

    return Show::glue(" ", vec![
      Show::glue(" ", adt_head),
      Show::glue(" ", adt_tail),
    ]);
  }

}

// Parser
// ------

impl Match {

  pub fn format(&self) -> Box<Show> {
    Show::pile(" ", vec![
      Show::glue(" ", vec![
        Show::text("match"),
        Show::text(&self.name),
        Show::text("="),
        self.expr.format_go(),  
      ]),
      Show::glue(" ", vec![
        Show::text("{"),
        Show::pile("; ", self.cses.iter().map(|(name,term)| {
          Show::glue(" ", vec![
            Show::text(name),
            Show::text(":"),
            term.format_go(),
          ])
        }).collect()),
      ]),
      if let Some(moti) = &self.moti {
        Show::glue(" ", vec![
          Show::text(":"),
          moti.format_go()
        ])
      } else {
        Show::text("")
      }
    ])
  }

}

impl<'i> KindParser<'i> {

  pub fn parse_list(&mut self, fid: u64, uses: &Uses) -> Result<crate::sugar::List, String> {
    self.consume("[")?;
    let mut vals = Vec::new();
    while self.peek_one() != Some(']') {
      vals.push(Box::new(self.parse_term(fid, uses)?));
      self.skip_trivia();
      if self.peek_one() == Some(',') {
        self.consume(",")?;
      }
    }
    self.consume("]")?;
    return Ok(crate::sugar::List { vals });
  }

  // FIXME: handle shadowing
  pub fn parse_adt(&mut self, fid: u64, uses: &Uses) -> Result<crate::sugar::ADT, String> {
    self.consume("data ")?;
    let name = self.parse_name()?;
    let mut pars = Vec::new();
    let mut idxs = Vec::new();
    let mut uses = uses.clone();
    // Parses ADT parameters (if any)
    self.skip_trivia();
    while self.peek_one().map_or(false, |c| c.is_ascii_alphabetic()) {
      let par = self.parse_name()?;
      self.skip_trivia();
      uses = shadow(&par, &uses);
      pars.push(par);
    }
    // Parses ADT fields
    while self.peek_one() == Some('(') {
      self.consume("(")?;
      let idx_name = self.parse_name()?;
      self.consume(":")?;
      let idx_type = self.parse_term(fid, &uses)?;
      self.consume(")")?;
      uses = shadow(&idx_name, &uses);
      idxs.push((idx_name, idx_type));
      self.skip_trivia();
    }
    // Parses ADT constructors
    let mut ctrs = Vec::new();
    self.skip_trivia();
    while self.peek_one() == Some('|') {
      self.consume("|")?;
      let ctr_name = self.parse_name()?;
      let mut uses = uses.clone();
      let mut flds = Vec::new();
      // Parses constructor fields
      self.skip_trivia();
      while self.peek_one() == Some('(') {
        self.consume("(")?;
        let fld_name = self.parse_name()?;
        self.consume(":")?;
        let fld_type = self.parse_term(fid, &uses)?;
        self.consume(")")?;
        uses = shadow(&fld_name, &uses);
        flds.push((fld_name, fld_type));
        self.skip_trivia();
      }
      // Parses constructor return
      self.skip_trivia();
      let mut ctr_indices = Vec::new();
      // Annotated
      if self.peek_one() == Some(':') {
        self.consume(":")?;
        self.skip_trivia();
        // Call
        if self.peek_one() == Some('(') {
          self.consume("(")?;
          // Parses the type (must be fixed, equal to 'name')
          self.consume(&name)?;
          // Parses each parameter (must be fixed, equal to 'pars')
          for par in &pars {
            self.consume(par)?;
          }
          // Parses the indices
          while self.peek_one() != Some(')') {
            let ctr_index = self.parse_term(fid, &uses)?;
            ctr_indices.push(ctr_index);
            self.skip_trivia();
          }
          self.consume(")")?;
        // Non-call
        } else {
          // Parses the type (must be fixed, equal to 'name')
          self.consume(&name)?;
        }
      // Non-annotated
      } else {
        if idxs.len() > 0 {
          return self.expected("annotation for indexed type");
        }
      }
      ctrs.push(sugar::Constructor { name: ctr_name, flds, idxs: ctr_indices });
      self.skip_trivia();
    }
    return Ok(sugar::ADT { name, pars, idxs, ctrs });
  }

  // MAT ::= match <name> = <term> { <name> : <term> <...> }: <term>
  // The ADT match syntax is similar to the numeric match syntax, including the same optionals,
  // but it allows any number of <name>:<term> cases. Also, similarly to the List syntax, there
  // is no built-in "Mat" syntax on the Term type, so we must convert it to an applicative form:
  //   match x:
  //     List.cons: x.head
  //     List.nil: #0
  //   : #U60
  // Would be converted to:
  //   (~val _ (λx.head λx.tail x.tail) 0)
  // Which is the same as:
  //   (APP (APP (APP (INS (VAR "val")) MET) (LAM "x.head" (LAM "x.tail" (VAR "x.head")))) (NUM 0))
  // FIXME: handle shadowing
  pub fn parse_match(&mut self, fid: u64, uses: &Uses) -> Result<Match, String> {
    // Parses the header: 'match <name> = <expr>'
    self.consume("match ")?;
    let name = self.parse_name()?;
    self.skip_trivia();
    let expr = if self.peek_one() == Some('=') { 
      self.consume("=")?;
      self.parse_term(fid, uses)?
    } else {
      Term::Var { nam: name.clone() }  
    };
    // Parses the with clause: 'with (a: A) (b: B) ...'
    let mut with = Vec::new();
    self.skip_trivia();
    if self.peek_many(5) == Some("with ") {
      self.consume("with")?;
      self.skip_trivia();  
      while self.peek_one() == Some('(') {
        self.consume("(")?;
        let mov_name = self.parse_name()?;  
        self.consume(":")?;
        let mov_type = self.parse_term(fid, uses)?;
        self.consume(")")?;
        with.push((mov_name, mov_type));
        self.skip_trivia();
      }
    }
    self.skip_trivia();
    // Parses the cases: '{ Type.constructor: value ... }'
    self.consume("{")?;
    let mut adt = "Empty".to_string();
    let mut cses = Vec::new();
    while self.peek_one() != Some('}') {
      let cse_name = self.parse_name()?;
      let cse_name = uses.get(&cse_name).unwrap_or(&cse_name).to_string();
      // Infers the local ADT name
      let adt_name = {
        let pts = cse_name.split('.').collect::<Vec<&str>>();
        if pts.len() < 2 {
          return self.expected(&format!("valid constructor (did you forget 'TypeName.' before '{}'?)", cse_name));
        } else {
          pts[..pts.len() - 1].join(".")
        }
      };
      // Sets the global ADT name
      if adt == "Empty" {
        adt = adt_name.clone();
      } else if adt != adt_name {
        return self.expected(&format!("{}.constructor", adt));
      }
      // Finds this case's constructor
      let cnm = cse_name.split('.').last().unwrap().to_string();
      let ctr = ADT::load(&adt).ok().and_then(|adt| adt.ctrs.iter().find(|ctr| ctr.name == cnm).cloned());
      if ctr.is_none() {
        return self.expected(&format!("a valid constructor ({}.{} doesn't exit)", adt_name, cnm));
      }
      // Shadows this constructor's field variables
      let mut uses = uses.clone();
      for (fld_name, _) in &ctr.unwrap().flds {
        uses = shadow(&format!("{}.{}", name, fld_name), &uses);
      }
      // Parses the return value
      self.consume(":")?;
      let cse_body = self.parse_term(fid, &uses)?;
      cses.push((cse_name, cse_body));
      self.skip_trivia();
    }
    self.consume("}")?;
    // Parses the motive: ': return_type'
    let moti = if self.peek_one() == Some(':') {
      self.consume(":")?;
      Some(self.parse_term(fid, uses)?)
    } else {
      None
    };
    return Ok(Match { adt, name, expr, with, cses, moti });
  }

}
