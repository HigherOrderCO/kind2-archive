use crate::{*};

//./../mod.rs//
//./../parse.rs//
//./mod.rs//
//./list.rs//
//./nat.rs//

// An Algebraic Data Type (ADT).
#[derive(Debug)]
pub struct ADT {
  pub name: String,
  pub pars: Vec<String>, // parameters
  pub idxs: Vec<(String,Term)>, // indices
  pub ctrs: Vec<Constructor>, // constructors
}

#[derive(Debug)]
pub struct Constructor {
  pub name: String, // constructor name
  pub flds: Vec<(String,Term)>, // constructor fields
  //pub rtyp: Term, // constructor type; NOTE: refactored. now, instead of storing `rtyp=(Vec A 0)`, we store just `idxs=[0]`, for ex.
  pub idxs: Vec<Term>, // constructor type indices
}

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
  pub fn new_adt(adt: ADT) -> Term {
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
    //
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

    println!("PARSED:\n{}", term.format().flatten(Some(80)));

    return term;
  }

}

impl ADT {
  
  // Loads an ADT from its λ-encoded file.
  pub fn load(name: &str) -> Result<ADT, String> {
    let book = Book::load(name)?;
    if let Some(term) = book.defs.get(name) {
      let mut term = &term.clean();
      // Skips all Anns
      while let Term::Ann { val, .. } = term {
        term = val;
      }
      // Skips all Lams
      while let Term::Lam { bod, .. } = term {
        term = bod;
      }
      //println!("{}", term.format().flatten(Some(800)));
      return term.as_adt().ok_or_else(|| format!("Failed to interpret '{}' as an ADT.", name))
    } else {
      Err(format!("Cannot find definition for type '{}'.", name))
    }
  }

}
