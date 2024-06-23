use crate::{*};

impl Book {

  pub fn to_hvm2(&self) -> String {
    let mut code = String::new();
    for (name, term) in &self.defs {
      code.push_str(&format!("{} = {}\n", Term::to_hvm2_name(name), term.to_hvm2()));
    }
    code
  }

  pub fn to_kindc(&self) -> String {
    let mut code = String::new();
    for (name, term) in &self.defs {
      code.push_str(&format!("{} = {};\n", name, term.to_kindc(&mut 0)));
    }
    code
  }
}
