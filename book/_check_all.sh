#for file in $(ls *.kind2 | grep -v '^_'); do
  #echo "checking ${file}"
  #kind2 check "${file%.*}"
#done

# TODO: make this script check all kind2 files recursively, not just top-dir ones

#!/bin/bash

find . -name "*.kind2" -not -name "_*" | while read -r file; do
  echo "checking ${file}"
  kind2 check "${file%.*}"
done
