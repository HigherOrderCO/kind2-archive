#!/usr/bin/env ts-node

// TODO: move the parser to HVM

// ICC: Parser, Stringifier and CLI
// ================================

// List
// ----

type List<A> =
  | { tag: "Cons"; head: A; tail: List<A> }
  | { tag: "Nil"; };

// Constructors
const Cons = <A>(head: A, tail: List<A>): List<A> => ({ tag: "Cons", head, tail });
const Nil  = <A>(): List<A>                       => ({ tag: "Nil" });

// Term
// ----

type Term =
  | { $: "All"; nam: string; inp: Term; bod: (x:Term)=> Term } // ∀(x: inp) bod
  | { $: "Lam"; nam: string; bod: (x:Term)=> Term } // λx bod
  | { $: "App"; fun: Term; arg: Term } // (fun arg)
  | { $: "Ann"; val: Term; typ: Term } // {val:typ}
  | { $: "Slf"; nam: string; bod: (x:Term)=> Term } // $x bod
  | { $: "Ins"; val: Term } // ~val
  | { $: "Set" } // *
  | { $: "U60" } // #U60
  | { $: "Num"; val: BigInt } // #num
  | { $: "Op2"; opr: string; fst: Term; snd: Term } // #(<opr> fst snd)
  | { $: "Mat"; nam: string; x: Term; z: Term; s: (x:Term) => Term; p: (x: Term) => Term } // #match k = x { zero: z; succ: s }: p
  | { $: "Txt"; txt: string } // "text"
  | { $: "Ref"; nam: string; val?: Term }
  | { $: "Let"; nam: string; val: Term; bod: (x:Term)=> Term }
  | { $: "Hol"; nam: string }
  | { $: "Var"; nam: string; idx: number };

// Constructors
export const All = (nam: string, inp: Term, bod: (x:Term)=> Term): Term => ({ $: "All", nam, inp, bod });
export const Lam = (nam: string, bod: (x:Term)=> Term): Term => ({ $: "Lam", nam, bod });
export const App = (fun: Term, arg: Term): Term => ({ $: "App", fun, arg });
export const Ann = (val: Term, typ: Term): Term => ({ $: "Ann", val, typ });
export const Slf = (nam: string, bod: (x:Term)=> Term): Term => ({ $: "Slf", nam, bod });
export const Ins = (val: Term): Term => ({ $: "Ins", val });
export const Set = (): Term => ({ $: "Set" });
export const U60 = (): Term => ({ $: "U60" });
export const Num = (val: BigInt): Term => ({ $: "Num", val });
export const Op2 = (opr: string, fst: Term, snd: Term): Term => ({ $: "Op2", opr, fst, snd });
export const Mat = (nam: string, x: Term, z: Term, s: (x:Term) => Term, p: (x:Term) => Term): Term => ({ $: "Mat", nam, x, z, s, p });
export const Txt = (txt: string): Term => ({ $: "Txt", txt });
export const Ref = (nam: string, val?: Term): Term => ({ $: "Ref", nam, val });
export const Let = (nam: string, val: Term, bod: (x:Term)=> Term): Term => ({ $: "Let", nam, val, bod });
export const Hol = (nam: string): Term => ({ $: "Hol", nam });
export const Var = (nam: string, idx: number): Term => ({ $: "Var", nam, idx });

// Book
// ----

type Book = {[name: string]: Term};

// Stringifier
// -----------

export const name = (numb: number): string => {
  let name = '';
  do {
    name = String.fromCharCode(97 + (numb % 26)) + name;
    numb = Math.floor(numb / 26) - 1;
  } while (numb >= 0);
  return name;
}

export const context = (numb: number): string => {
  var names = [];
  for (var i = 0; i < numb; ++i) {
    names.push(name(i));
  }
  return "["+names.join(",")+"]";
}

const compile_oper = (opr: string): string => {
  switch (opr) {
    case "+"  : return "ADD";
    case "-"  : return "SUB";
    case "*"  : return "MUL";
    case "/"  : return "DIV";
    case "%"  : return "MOD";
    case "==" : return "EQ";
    case "!=" : return "NE";
    case "<"  : return "LT";
    case ">"  : return "GT";
    case "<=" : return "LTE";
    case ">=" : return "GTE";
    case "&"  : return "AND";
    case "|"  : return "OR";
    case "^"  : return "XOR";
    case "<<" : return "LSH";
    case ">>" : return "RSH";
    default: throw new Error("Unknown operator: " + opr);
  }
};

export const compile = (term: Term, used_refs: any, dep: number = 0): string => {
  switch (term.$) {
    case "All": return `(All "${term.nam}" ${compile(term.inp, used_refs, dep)} λ${name(dep)} ${compile(term.bod(Var(term.nam,dep)), used_refs, dep + 1)})`;
    case "Lam": return `(Lam "${term.nam}" λ${name(dep)} ${compile(term.bod(Var(term.nam,dep)), used_refs, dep + 1)})`;
    case "App": return `(App ${compile(term.fun, used_refs, dep)} ${compile(term.arg, used_refs, dep)})`;
    case "Ann": return `(Ann ${compile(term.val, used_refs, dep)} ${compile(term.typ, used_refs, dep)})`;
    case "Slf": return `(Slf "${term.nam}" λ${name(dep)} ${compile(term.bod(Var(term.nam,dep)), used_refs, dep + 1)})`;
    case "Ins": return `(Ins ${compile(term.val, used_refs, dep)})`;
    case "Set": return `(Set)`;
    case "U60": return `(U60)`;
    case "Num": return `(Num ${term.val.toString()})`;
    case "Op2": return `(Op2 ${compile_oper(term.opr)} ${compile(term.fst, used_refs, dep)} ${compile(term.snd, used_refs, dep)})`;
    case "Mat": return `(Mat "${term.nam}" ${compile(term.x, used_refs, dep)} ${compile(term.z, used_refs, dep)} λ${name(dep)} ${compile(term.s(Var(term.nam,dep)), used_refs, dep + 1)} λ${name(dep)} ${compile(term.p(Var(term.nam,dep)), used_refs, dep + 1)})`;
    case "Txt": return `(Txt \`${term.txt}\`)`;
    case "Hol": return `(Hol "${term.nam}" ${context(dep)})`;
    case "Var": return name(term.idx);
    case "Ref": return (used_refs[term.nam] = 1), ("Book." + term.nam);
    case "Let": return `(Let "${term.nam}" ${compile(term.val, used_refs, dep)} λ${name(dep)} ${compile(term.bod(Var(term.nam,dep)), used_refs, dep + 1)})`;
  }
};

// Parser
// ------

export type Scope = List<[string, Term]>;

export function find<A>(list: Scope, nam: string): Term {
  switch (list.tag) {
    case "Cons": return list.head[0] === nam ? list.head[1] : find(list.tail, nam);
    case "Nil" : return Ref(nam);
  }
}

export function skip(code: string): string {
  while (true) {
    if (code.slice(0, 2) === "//") {
      do { code = code.slice(1); } while (code.length != 0 && code[0] != "\n");
      continue;
    }
    if (code[0] === "\n" || code[0] === " ") {
      code = code.slice(1);
      continue;
    }
    break;
  }
  return code;
}

export function is_name_char(c: string): boolean {
  return /[a-zA-Z0-9_.-]/.test(c);
}

export function is_oper_char(c: string): boolean {
  return /[+\-*/%<>=&|^!~]/.test(c);
}

export function parse_word(is_letter: (c: string) => boolean, code: string): [string, string] {
  code = skip(code);
  var name = "";
  while (is_letter(code[0]||"")) {
    name = name + code[0];
    code = code.slice(1);
  }
  return [code, name];
}

export function parse_name(code: string): [string, string] {
  return parse_word(is_name_char, code);
}

export function parse_oper(code: string): [string, string] {
  return parse_word(is_oper_char, code);
}

export function parse_text(code: string, text: string): [string, null] {
  code = skip(code);
  if (text === "") {
    return [code, null];
  } else if (code[0] === text[0]) {
    return parse_text(code.slice(1), text.slice(1));
  } else {
    throw "parse error";
  }
}

export function parse_term(code: string): [string, (ctx: Scope) => Term] {
  code = skip(code);
  // ALL: `∀(x: A) B[x]` -SUGAR
  if (code[0] === "∀") {
    var [code, nam] = parse_name(code.slice(2));
    var [code, _  ] = parse_text(code, ":");
    var [code, inp] = parse_term(code);
    var [code, _  ] = parse_text(code, ")");
    var [code, bod] = parse_term(code);
    return [code, ctx => All(nam, inp(ctx), x => bod(Cons([nam, x], ctx)))];
  }
  // LAM: `λx f`
  if (code[0] === "λ") {
    var [code, nam] = parse_name(code.slice(1));
    var [code, bod] = parse_term(code);
    return [code, ctx => Lam(nam, x => bod(Cons([nam, x], ctx)))];
  }
  // APP: `(f x y z ...)`
  if (code[0] === "(") {
    var [code, fun] = parse_term(code.slice(1));
    var args: ((ctx: Scope) => Term)[] = [];
    while (code[0] !== ")") {
      var [code, arg] = parse_term(code);
      args.push(arg);
      code = skip(code);
    }
    var [code, _] = parse_text(code, ")");
    return [code, ctx => args.reduce((f, x) => App(f, x(ctx)), fun(ctx))];
  }
  // ANN: `{x : T}`
  if (code[0] === "{") {
    var [code, val] = parse_term(code.slice(1));
    var [code, _  ] = parse_text(code, ":");
    var [code, typ] = parse_term(code);
    var [code, _  ] = parse_text(code, "}");
    return [code, ctx => Ann(val(ctx), typ(ctx))];
  }
  // SLF: `$x T`
  if (code[0] === "$") {
    var [code, nam] = parse_name(code.slice(1));
    var [code, bod] = parse_term(code);
    return [code, ctx => Slf(nam, x => bod(Cons([nam, x], ctx)))];
  }
  // INS: `~x`
  if (code[0] === "~") {
    var [code, val] = parse_term(code.slice(1));
    return [code, ctx => Ins(val(ctx))];
  }
  // SET: `*`
  if (code[0] === "*") {
    return [code.slice(1), ctx => Set()];
  }
  // LET: `let x = A in B`
  if (code.slice(0,4) === "let ") {
    var [code, nam] = parse_name(code.slice(4));
    var [code, _  ] = parse_text(code, "=");
    var [code, val] = parse_term(code);
    var [code, bod] = parse_term(code);
    return [code, ctx => Let(nam, val(ctx), x => bod(Cons([nam, x], ctx)))];
  }
  // U60: `#U60`
  if (code.slice(0,4) === "#U60") {
    return [code.slice(4), ctx => U60()];
  }
  // OP2: `#(<opr> fst snd)`
  if (code.slice(0,2) === "#(") {
    var [code, opr] = parse_oper(code.slice(2));
    var [code, fst] = parse_term(code);
    var [code, snd] = parse_term(code);
    var [code, _]   = parse_text(code, ")");
    return [code, ctx => Op2(opr, fst(ctx), snd(ctx))];
  }
  // MAT: `#match x = val { #0: z; #+: s }: p`
  if (code.slice(0,7) === "#match ") {
    var [code, nam] = parse_name(code.slice(7));
    var [code, _  ] = parse_text(code, "=");
    var [code, x]   = parse_term(code);
    var [code, _  ] = parse_text(code, "{");
    var [code, _  ] = parse_text(code, "#0:");
    var [code, z]   = parse_term(code);
    var [code, _  ] = parse_text(code, "#+:");
    var [code, s]   = parse_term(code);
    var [code, _  ] = parse_text(code, "}");
    var [code, _  ] = parse_text(code, ":");
    var [code, p]   = parse_term(code);
    return [code, ctx => Mat(nam, x(ctx), z(ctx), k => s(Cons([nam+"-1", k], ctx)), k => p(Cons([nam, k], ctx)))];
  }
  // NUM: `#num`
  if (code[0] === "#") {
    var [code, num] = parse_name(code.slice(1));
    return [code, ctx => Num(BigInt(num))];
  }
  // CHR: `'a'` -- char syntax sugar
  if (code[0] === "'") {
    var [code, chr] = [code.slice(2), code[1]];
    var [code, _]   = parse_text(code, "'");
    return [code, ctx => Num(BigInt(chr.charCodeAt(0)))];
  }
  // STR: `"text"` -- string syntax sugar
  if (code[0] === "\"" || code[0] === "`") {
    var str = "";
    var end = code[0];
    code = code.slice(1);
    while (code[0] !== end) {
      str += code[0];
      code = code.slice(1);
    }
    code = code.slice(1);
    return [code, ctx => Txt(str)];
  }
  // HOL: `?name`
  if (code[0] === "?") {
    var [code, nam] = parse_name(code.slice(1));
    return [code, ctx => Hol(nam)];
  }
  // VAR: `name`
  var [code, nam] = parse_name(code);
  if (nam.length > 0) {
    return [code, ctx => find(ctx, nam)];
  }
  throw "parse error";
}

export function do_parse_term(code: string): Term {
  return parse_term(code)[1](Nil());
}

export function parse_def(code: string): [string, {nam: string, val: Term}] {
  var [code, nam] = parse_name(skip(code));
  if (skip(code)[0] === ":") {
    var [code, _  ] = parse_text(code, ":");
    var [code, typ] = parse_term(code);
    var [code, _  ] = parse_text(code, "=");
    var [code, val] = parse_term(code);
    return [code, {nam: nam, val: Ann(val(Nil()), typ(Nil()))}];
  } else {
    var [code, _  ] = parse_text(code, "=");
    var [code, val] = parse_term(code);
    return [code, {nam: nam, val: val(Nil())}];
  }
}

export function parse_book(code: string): Book {
  var book : Book = {};
  while (code.length > 0) {
    var [code, def] = parse_def(code);
    book[def.nam] = def.val;
    code = skip(code);
  }
  return book;
}

export function do_parse_book(code: string): Book {
  return parse_book(code);
}

// CLI
// ---

import * as fs from "fs";
import { execSync } from "child_process";

export function main() {
  // Loads Kind's HVM checker.
  var kind2_hvm1 = fs.readFileSync(__dirname + "/kind2.hvm1", "utf8");

  // Loads all local ".kind2" files.
  const code = fs.readdirSync(".")
    .filter(file => file.endsWith(".kind2"))
    .map(file => fs.readFileSync("./"+file, "utf8"))
    .join("\n");

  // Parses into book.
  const book = do_parse_book(code);

  // Compiles book to hvm1.
  //var book_hvm1 = "Names = [" + Object.keys(book).map(x => '"'+x+'"').join(",") + "]\n";
  //var ref_count = 0;
  var used_refs = {};
  var book_hvm1 = "";
  for (let name in book) {
    book_hvm1 += "Book." + name + " = (Ref \"" + name + "\" " + compile(book[name], used_refs) + ")\n";
  }

  // Checks for unbound definitions
  for (var ref_name in used_refs) {
    if (!book[ref_name]) {
      throw "Unbound definition: " + ref_name;
    }
  }

  // Gets arguments.
  const args = process.argv.slice(2);
  const func = args[0];
  const name = args[1];

  // Creates main.
  var main_hvm1 = "";
  switch (func) {
    case "check": {
      main_hvm1 = "Main = (Checker Book." + name + ")\n";
      break;
    }
    case "run": {
      main_hvm1 = "Main = (Normalizer Book." + name + ")\n";
      break;
    }
    default: {
      console.log("Usage: kind2 [check|run] <name>");
    }
  }

  // Generates the 'kind2.hvm1' file.
  var checker_hvm1 = [kind2_hvm1, book_hvm1, main_hvm1].join("\n\n");

  // Saves locally.
  fs.writeFileSync("./.kind2.hvm1", checker_hvm1);

  // Runs 'hvm1 kind2.hvm1 -s -L -1'

  //const output = execSync("hvm1 run .kind2.hvm1 -s -L -1").toString();

  //for (let name in book) {
    //console.log("Checking: " + name);

    const output = execSync("hvm1 run -t 1 -c -f .kind2.hvm1 \"(Main)\"").toString();
    //const output = execSync(`hvm1 run -t 1 -c -f .kind2.hvm1 "(Checker Book.${name})"`).toString();
    try {
      var check_text = output.slice(output.indexOf("[["), output.indexOf("RWTS")).trim();
      var stats_text = output.slice(output.indexOf("RWTS"));
      var [logs, check] = JSON.parse(check_text);
      logs.reverse();
      for (var log of logs) {
        console.log(log);
      }
      console.log(check ? "Check!" : "Error.");
      console.log("");
      console.log(stats_text);
    } catch (e) {
      console.log(output);
    }

  //}

};

main();
