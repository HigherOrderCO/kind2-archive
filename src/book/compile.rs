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
    let mut meta = 0;
    for (name, term) in &self.defs {
      code.push_str(&format!("{} = {};\n", name, term.to_kindc(im::Vector::new(), &mut meta)));
    }
    code
  }

  pub fn to_js(&self) -> String {
    let mut code = String::new();
    for (name, term) in &self.defs {
      code.push_str(&format!("const {} = {};\n", Term::to_js_name(name), term.to_js()));
    }
    code
  }
}
