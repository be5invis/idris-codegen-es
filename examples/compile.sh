export IDRISJS_OPTIM=$2
export IDRISJS_DEBUG=$3
idris -p js -p effects -p contrib --codegen js  $1 -o ${1%%.idr}.js
