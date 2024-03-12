use crate::{*};

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

