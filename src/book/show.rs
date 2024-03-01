use crate::{*};

impl Book {

  pub fn show(&self) -> String {
    let mut book_str = String::new();
    for (name, term) in &self.defs {
      book_str.push_str(&format!("{} = {}\n", name, term.show()));
    }
    book_str
  }

}
