use crate::{*};

//./mod.rs//

impl Book {

  pub fn format_def(&self, name: &str, term: &Term) -> Box<Form> {
    match term {
      Term::Ann { chk: _, val, typ } => {
        Form::glue("", vec![
          Form::text(name),
          Form::line(),
          Form::glue("", vec![
            Form::text(": "),
            Form::inc(),
            typ.format(),
            Form::dec(),
          ]),
          Form::line(),
          Form::glue("", vec![
            Form::text("= "),
            Form::inc(),
            val.format(),
            Form::dec(),
          ]),
        ])
      },
      val => {
        Form::glue("", vec![
          Form::text(name),
          Form::line(),
          Form::glue("", vec![
            Form::text("="),
            Form::inc(),
            val.format(),
            Form::dec(),
          ]),
        ])
      }
    }
  }

  pub fn format(&self) -> Box<Form> {
    Form::glue("", self.defs.iter().map(|(name, term)| {
      Form::glue("", vec![
        self.format_def(&name, term),
        Form::line(),
        Form::line(),
      ])
    }).collect())
  }

}
