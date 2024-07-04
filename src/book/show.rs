use std::fmt::Display;

use crate::*;

impl Book {
  pub fn show(&self) -> String {
    self.to_string()
  }
}

impl Display for Book {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for (i, (name, term)) in self.defs.iter().enumerate() {
      write!(f, "{name}")?;

      if let Term::Ann { chk: _, val, typ } = term {
        write!(f, ": {typ} = {val}")?;
      } else {
        write!(f, " = {term}")?;
      }

      if i < self.defs.len() - 1 {
        writeln!(f)?;
        writeln!(f)?;
      }
    }

    Ok(())
  }
}
