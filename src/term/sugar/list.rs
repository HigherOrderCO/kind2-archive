use crate::{*};

// Lists
#[derive(Debug)]
pub struct List {
  pub vals: Vec<Box<Term>>,
}

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


