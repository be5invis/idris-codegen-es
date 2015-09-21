for f in tests/*.idr
do
  rm ${f%%.idr}.ibc
  idris -p js  --codegen js $f  -o ${f%%.idr}
done
