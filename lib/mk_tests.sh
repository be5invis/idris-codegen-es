for f in tests/*.idr
do
  echo compiling $f
  rm ${f%%.idr}.ibc 2>/dev/null
  idris -p js  --codegen js $f  -o ${f%%.idr}.js
done
