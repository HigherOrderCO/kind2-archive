import { execSync } from 'child_process';
import * as fs from 'fs';

type Book = {[name:string]: string};

export function run(expr: string): string {
  var command = `hvm1 run -t 1 -c -f bootstrap.hvm1 '${expr}'`;
  try {
    const output = execSync(command).toString();
    return output;
  } catch (error) {
    throw error;
  }
}

export function str(result: string): string {
  return result.slice(1,-1).trim();
}

export function get_refs(code: string): [string] {
  return JSON.parse(run(`(Strs.view ((Book.Kind.Book.get_refs) ((Book.Kind.Book.parse) (Str \`${code}\`))))`).trim());
}

export function to_hvm(code: string): string {
  return str(run(`(Str.view ((Book.Kind.Book.to_hvm) ((Book.Kind.Book.parse) (Str \`${code}\`))))`).trim());
}

export function load_file(file: string): string {
  return fs.readFileSync("./book/"+file, "utf8");
}

export function load(name: string, book: Book = {}): Book {
  console.log("loading", name);
  book[name] = load_file(name + ".kind2");
  var refs = get_refs(book[name]);
  for (var ref of refs) {
    if (!book[ref]) {
      load(ref, book);
    }
  }
  return book;
}


console.log(load("Bool", {}));
