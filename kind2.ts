import { execSync } from 'child_process';
import * as fs from 'fs';

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

export function load(name: string): string {
  return fs.readFileSync("./book/"+name+".kind2", "utf8");
}

export function get_refs(code: string): string {
  return run(`(Strs.view ((Book.Kind.Book.get_refs) ((Book.Kind.Book.parse) (Str \`${code}\`))))`).trim();
}

export function to_hvm(code: string): string {
  return str(run(`(Str.view ((Book.Kind.Book.to_hvm) ((Book.Kind.Book.parse) (Str \`${code}\`))))`).trim());
}

console.log(get_refs(`plus2 = λx (Nat.succ (Nat.succ x))`));
