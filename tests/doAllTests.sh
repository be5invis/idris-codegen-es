export IDRISJS_OPTIM=Y
for f in *.idr
do
  echo $f
  idris --codegen js -p effects -p js $f -o ${f%%.idr}.js
  res=$(node ${f%%.idr}.js)
  pred=$(cat ${f%%.idr}.testres)
  echo "   res:" $res
  if [[ "$res" == "$pred" ]]
  then
    echo "   OK"
  else
    echo "   KO"
  fi
done
