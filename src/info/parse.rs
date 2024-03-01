use crate::{*};

impl<'i> KindParser<'i> {

  pub fn parse_info(&mut self) -> Result<Info, String> {
    self.skip_trivia();
    match self.peek_one() {
      Some('#') => {
        self.consume("#")?;
        match self.peek_one() {
          Some('f') => {
            self.consume("found")?;
            self.consume("{")?;
            let nam = self.parse_name()?;
            let typ = self.parse_term(0)?;
            self.consume("[")?;
            let mut ctx = Vec::new();
            while self.peek_one() != Some(']') {
              ctx.push(self.parse_term(0)?);
              self.skip_trivia();
            }
            self.consume("]")?;
            self.consume("}")?;
            Ok(Info::Found { nam, typ, ctx })
          }
          Some('e') => {
            self.consume("error")?;
            self.consume("{")?;
            let exp = self.parse_term(0)?;
            let det = self.parse_term(0)?;
            let bad = self.parse_term(0)?;
            let src = Src::from_u64(self.parse_u64()?);
            self.consume("}")?;
            Ok(Info::Error {
              exp: exp,
              det: det,
              bad: bad,
              src: src,
            })
          }
          Some('s') => {
            self.consume("solve")?;
            self.consume("{")?;
            let nam = self.parse_name()?;
            let val = self.parse_term(0)?;
            self.consume("}")?;
            Ok(Info::Solve { nam, val })
          }
          Some('v') => {
            self.consume("vague")?;
            self.consume("{")?;
            let nam = self.parse_name()?;
            self.consume("}")?;
            Ok(Info::Vague { nam })
          }
          _ => self.expected("info type (solve, found, error)"),
        }
      }
      _ => self.expected("# (start of info)"),
    }
  }
  
  pub fn parse_infos(&mut self) -> Result<Vec<Info>, String> {
    let mut infos = Vec::new();
    while *self.index() < self.input().len() {
      let parsed_info = self.parse_info();
      match parsed_info {
        Ok(msg) => {
          infos.push(msg);
          self.skip_trivia();
        }
        Err(_) => {
          break;
        }
      }
    }
    Ok(infos)
  }

}
