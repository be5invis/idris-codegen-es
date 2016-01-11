# idrisjs
Js ffis for idris.
Due to some dificulties with the default js backend this lib uses its own js backend.

###To build
```shell
cabal install
cd lib
idris --install js.ipkg
```

###Compilation example:
```shell
cd examples
idris --codegen js -p js todo.idr -o todo.js
```
then open todo.html
