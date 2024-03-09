use crate::Term;

// Example:
//   ["(" "foo" "arg0" "arg1" "arg2" ")"]
// Call:
//   (
//     foo
//     arg0
//     arg1
//     arg2
//   )
// Pile:
//   (
//   foo
//   arg0
//   arg1
//   arg2
//   )
// Glue:
//   (foo arg0 arg1 arg2)
#[derive(Debug, Clone, Copy)]
pub enum Style {
  Call,
  Pile,
  Glue,
}

// A Form is a pre-format string of trees
#[derive(Debug)]
pub enum Form {
  Many { style: Style, join: String, child: Vec<Box<Form>> }, // combines many texts
  Text { value: String }, // inserts a text
  Line, // causes a line break, indenting the next line
  Inc, // increments the indentation level
  Dec, // decrements the indentation level
}

impl Form {
  // Allocs a new Text node from a string slice.
  pub fn text(txt: &str) -> Box<Form> {
    Box::new(Form::Text { value: txt.to_string() })
  }

  // Allocs a new Many node.
  pub fn many(style: Style, join: &str, child: Vec<Box<Form>>) -> Box<Form> {
    Box::new(Form::Many { style: style, join: join.to_string(), child: child })
  }

  // Allocs a new Call with given children.
  pub fn call(join: &str, child: Vec<Box<Form>>) -> Box<Form> {
    Form::many(Style::Call, join, child)
  }

  // Allocs a new Pile with given children.
  pub fn pile(join: &str, child: Vec<Box<Form>>) -> Box<Form> {
    Form::many(Style::Pile, join, child)
  }

  // Allocs a new Glue with given children.
  pub fn glue(join: &str, child: Vec<Box<Form>>) -> Box<Form> {
    Form::many(Style::Glue, join, child)
  }
    
  // Allocs a new Line node.
  pub fn line() -> Box<Form> {
    Box::new(Form::Line)
  }

  // Allocs a new Inc node.
  pub fn inc() -> Box<Form> {
    Box::new(Form::Inc)
  }

  // Allocs a new Dec node.
  pub fn dec() -> Box<Form> {
    Box::new(Form::Dec)
  }

  // Flattens the Form structure into a string, respecting indentation and width limits.
  pub fn flatten(&self, lim: Option<usize>) -> String {
    let mut out = String::new();
    if let Some(lim) = lim {
      self.flatten_into(&mut out, true, &mut 0, lim);
    } else {
      self.flatten_into(&mut out, false, &mut 0, 0);
    }
    out
  }

  // Helper function.
  pub fn flatten_into(&self, out: &mut String, fmt: bool, tab: &mut usize, lim: usize) {
    match self {
      Form::Many { style, join, child } => {
        match style {
          Style::Call => {
            let add_lines = fmt && Form::no_lines(&child) && self.width(lim) >= lim;
            for (i, c) in child.iter().enumerate() {
              if add_lines && i > 0 && i < child.len() - 1 {
                Form::Inc.flatten_into(out, fmt, tab, lim);
              }
              if add_lines && i > 0 {
                Form::Line.flatten_into(out, fmt, tab, lim);
              }
              if !add_lines && i > 0 && i < child.len() - 1 {
                out.push_str(&join);
              }
              c.flatten_into(out, fmt, tab, lim);
              if add_lines && i > 0 && i < child.len() - 1 {
                Form::Dec.flatten_into(out, fmt, tab, lim);
              }
            }
          },
          Style::Pile => {
            let add_lines = fmt && Form::no_lines(&child) && self.width(lim) >= lim;
            for (i, c) in child.iter().enumerate() {
              if add_lines && i > 0 {
                Form::Line.flatten_into(out, fmt, tab, lim);
              }
              if !add_lines && i > 0 {
                out.push_str(&join);
              }
              c.flatten_into(out, fmt, tab, lim);
            }
          },
          Style::Glue => {
            for (i, c) in child.iter().enumerate() {
              if i > 0 {
                out.push_str(&join);
              }
              c.flatten_into(out, fmt, tab, lim);
            }
          },
        }
      },
      Form::Text { value } => {
        out.push_str(value)
      },
      Form::Line => {
        if fmt {
          out.push('\n');
          out.push_str(&"  ".repeat(*tab));
        } else {
          out.push_str("; ");
        }
      },
      Form::Inc => {
        *tab += 1
      },
      Form::Dec => {
        *tab -= 1
      },
    }
  }

  // Sums the width of all children ropes, up to a limit.
  fn width(&self, lim: usize) -> usize {
    let mut total_width = 0;
    match self {
      Form::Text { value } => {
        total_width += value.len();
      },
      Form::Many { join, child, .. } => {
        for (i, child) in child.iter().enumerate() {
          if i > 0 {
            total_width += join.len();
          }
          total_width += child.width(lim);
          if total_width >= lim {
            break;
          }
        }
      },
      _ => {},
    }
    total_width.min(lim)
  }

  // Checks if there is no `Line` in a vector of ropes.
  fn no_lines(child: &Vec<Box<Form>>) -> bool {
    for child in child {
      if let Form::Line = **child {
        return false;
      }
    }
    return true;
  }

}
