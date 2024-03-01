for file in $(ls *.kind2 | grep -v '^_'); do
  echo "checking ${file}"
  kind2 check "${file%.*}"
done
