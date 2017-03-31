export IDRISJS_OPTIM=$1
export IDRISJS_DEBUG=$2
idris --codegen js -p effects -p js ex0.idr -o ex0.js
idris --codegen js -p effects -p js todo.idr -o todo.js

