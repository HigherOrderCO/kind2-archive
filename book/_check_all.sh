for file in *.kind2; do
  echo "checking ${file}"
  kind2 check "${file%.*}"
done
