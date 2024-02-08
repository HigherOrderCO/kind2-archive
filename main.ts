#!/usr/bin/env ts-node

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

// NEW TERM TYPE
type Term =
  | { $: "All"; inp: Term; bod: (x:Term)=> Term } // ∀(x: inp) bod
  | { $: "Lam"; bod: (x:Term)=> Term } // λx bod
  | { $: "App"; fun: Term; arg: Term } // (fun arg)
  | { $: "Ann"; val: Term; typ: Term } // {val:typ}
  | { $: "Slf"; bod: (x:Term)=> Term } // $x bod
  | { $: "Ins"; val: Term } // ~val
  | { $: "Set" } // *
  | { $: "Ref"; nam: string; val?: Term }
  | { $: "Var"; idx: number };

// Constructors
export const All = (inp: Term, bod: (x:Term)=> Term): Term => ({ $: "All", inp, bod });
export const Lam = (bod: (x:Term)=> Term): Term => ({ $: "Lam", bod });
export const App = (fun: Term, arg: Term): Term => ({ $: "App", fun, arg });
export const Ann = (val: Term, typ: Term): Term => ({ $: "Ann", val, typ });
export const Slf = (bod: (x:Term)=> Term): Term => ({ $: "Slf", bod });
export const Ins = (val: Term): Term => ({ $: "Ins", val });
export const Set = (): Term => ({ $: "Set" });
export const Ref = (nam: string, val?: Term): Term => ({ $: "Ref", nam, val });
export const Var = (idx: number): Term => ({ $: "Var", idx });

// Book
// ----

type Book = {[name: string]: Term};

// Stringifier
// -----------

export const num_to_name = (num: number): string => {
  var nam = "";
  while (num >= 26) {
    nam += String.fromCharCode("a".charCodeAt(0) + (num % 26));
    num = Math.floor(num / 26);
  }
  nam += String.fromCharCode("a".charCodeAt(0) + num);
  return nam.split("").reverse().join("");
};

export const name = (numb: number): string => {
  let name = '';
  do {
    name = String.fromCharCode(97 + (numb % 26)) + name;
    numb = Math.floor(numb / 26) - 1;
  } while (numb >= 0);
  return name;
}

export const show = (term: Term, dep: number = 0): string => {
  switch (term.$) {
    case "All": return `∀(${name(dep)}: ${show(term.inp, dep)}) ${show(term.bod(Var(dep)), dep + 1)}`;
    case "Lam": return `λ${name(dep)} ${show(term.bod(Var(dep)), dep + 1)}`;
    case "App": return `(${show(term.fun, dep)} ${show(term.arg, dep)})`;
    case "Ann": return `{${show(term.val, dep)} : ${show(term.typ, dep)}}`;
    case "Slf": return `${name(dep)} ${show(term.bod(Var(dep)), dep + 1)}`;
    case "Ins": return `~${show(term.val, dep)}`;
    case "Set": return `*`;
    case "Var": return term.idx === -1 ? "*" : name(term.idx);
    case "Ref": return term.nam;
  }
};

export const compile = (term: Term, dep: number = 0): string => {
  switch (term.$) {
    case "All": return `(All ${compile(term.inp, dep)} λ${name(dep)} ${compile(term.bod(Var(dep)), dep + 1)})`;
    case "Lam": return `(Lam λ${name(dep)} ${compile(term.bod(Var(dep)), dep + 1)})`;
    case "App": return `(App ${compile(term.fun, dep)} ${compile(term.arg, dep)})`;
    case "Ann": return `(Ann ${compile(term.val, dep)} ${compile(term.typ, dep)})`;
    case "Slf": return `(Slf λ${name(dep)} ${compile(term.bod(Var(dep)), dep + 1)})`;
    case "Ins": return `(Ins ${compile(term.val, dep)})`;
    case "Set": return `(Set)`;
    case "Var": return name(term.idx);
    case "Ref": return "T_" + term.nam;
  }
};

// Parser
// ------

export type Scope = List<[string, Term]>;

export function num_to_str(num: number): string {
  let txt = '';
  num += 1;
  while (num > 0) {
    txt += String.fromCharCode(((num-1) % 26) + 'a'.charCodeAt(0));
    num  = Math.floor((num-1) / 26);
  }
  return txt.split('').reverse().join('');
}

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
  return /[a-zA-Z0-9_.]/.test(c);
}

export function parse_name(code: string): [string, string] {
  code = skip(code);
  var name = "";
  while (is_name_char(code[0]||"")) {
    name = name + code[0];
    code = code.slice(1);
  }
  return [code, name];
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
    var [code, __ ] = parse_text(code, ")");
    var [code, bod] = parse_term(code);
    return [code, ctx => All(inp(ctx), x => bod(Cons([nam, x], ctx)))];
  }
  // LAM: `λx f`
  if (code[0] === "λ") {
    var [code, nam] = parse_name(code.slice(1));
    var [code, bod] = parse_term(code);
    return [code, ctx => Lam(x => bod(Cons([nam, x], ctx)))];
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
    return [code, ctx => Slf(x => bod(Cons([nam, x], ctx)))];
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
  var book_hvm1 = "";
  for (let name in book) {
    book_hvm1 += "T_" + name + " = (Ref \"" + name + "\" " + compile(book[name]) + ")\n";
  }

  // Gets arguments.
  const args = process.argv.slice(2);
  const func = args[0];
  const name = args[1];

  // Creates main.
  var main_hvm1 = "";
  switch (func) {
    case "check": {
      main_hvm1 = "Main = (Checker T_" + name + ")\n";
      break;
    }
    case "run": {
      main_hvm1 = "Main = (Normalizer T_" + name + ")\n";
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
  const output = execSync("hvm1 run -t 1 -c -f .kind2.hvm1 \"(Main)\"").toString();
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

};

main();
