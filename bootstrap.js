// Bootstrap by compiling ALL book/ functions to a single HVM1 file.

const fs = require('fs');
const { execSync } = require('child_process');
const path = require('path');

const bookDir = './book';
const outputFilePath = './bootstrap.hvm1';
let outputs = [];

fs.readdirSync(bookDir).forEach(file => {
  if (path.extname(file) === '.kind2') {
    try {
      const filePath = path.join(bookDir, file);
      const fileContent = fs.readFileSync(filePath, 'utf8');
      const compileString = `_compile : String = (Kind.Book.to_hvm (Kind.Book.parse \`${fileContent}\`))`;
      const compileFilePath = path.join(bookDir, '_compile.kind2');
      fs.writeFileSync(compileFilePath, compileString);
      console.log("COMPILING", filePath);
      const command = `kind2 run _compile`;
      const result = execSync(command, { cwd: bookDir }).toString().trim().slice(1,-1);
      console.log(result);
      outputs.push(result);
    } catch (e) {
      console.log(e);
    }
  }
});

// Loads prelude
var prelude = fs.readFileSync("./book/Kind.Book.to_hvm.prelude", "utf8");
const lines = prelude.split("\n");
lines.shift();
lines.pop();
var prelude = lines.join("\n");

const finalOutput = prelude + "\n" + outputs.join('\n');
fs.writeFileSync(outputFilePath, finalOutput);
