const fs = require('fs');
const path = require('path');

// Read all .kind2 files in the current directory
fs.readdir('.', (err, files) => {
  if (err) {
    console.error('Error reading directory:', err);
    return;
  }

  files.filter(file => file.endsWith('.kind2')).forEach(file => {
    // Construct new path by replacing dots with slashes, except for the extension
    const newName = file.slice(0, -6).replace(/\./g, '/') + file.slice(-6);
    const newPath = path.join('.', newName);
    const newDir = path.dirname(newPath);

    // Create the directory structure if it doesn't exist
    fs.mkdir(newDir, { recursive: true }, (err) => {
      if (err) {
        console.error('Error creating directories:', err);
        return;
      }

      // Move the file to the new location
      fs.rename(file, newPath, (err) => {
        if (err) {
          console.error('Error moving file:', err);
        }
      });
    });
  });
});
