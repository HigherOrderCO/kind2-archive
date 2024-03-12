use crate::{*};

impl Book {

  pub fn show(&self) -> String {
    return self.format().flatten(None);
  }

  pub fn format_def(&self, name: &str, term: &Term) -> Box<Show> {
    match term {
      Term::Ann { chk: _, val, typ } => {
        Show::glue("", vec![
          Show::text(name),
          Show::line(),
          Show::glue("", vec![
            Show::text(": "),
            Show::inc(),
            typ.format(),
            Show::dec(),
          ]),
          Show::line(),
          Show::glue("", vec![
            Show::text("= "),
            Show::inc(),
            val.format(),
            Show::dec(),
          ]),
        ])
      },
      val => {
        Show::glue("", vec![
          Show::text(name),
          Show::line(),
          Show::glue("", vec![
            Show::text("="),
            Show::inc(),
            val.format(),
            Show::dec(),
          ]),
        ])
      }
    }
  }

  pub fn format(&self) -> Box<Show> {
    Show::glue("", self.defs.iter().map(|(name, term)| {
      Show::glue("", vec![
        self.format_def(&name, term),
        Show::line(),
        Show::line(),
      ])
    }).collect())
  }

}
