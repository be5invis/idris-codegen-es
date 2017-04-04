# idrisjs
Js libraries for idris.
Due to some dificulties with the default js backend this lib uses its own js backend. This backend is compatible with the default js IO type JS_IO, hence they are interchangeable. The test t8.idr shows the troubles with the idris default backend.

### To build
```shell
cabal install
cd lib
idris --install js.ipkg
```

### Compilation example:
```shell
cd examples
idris --codegen js -p js todo.idr -o todo.js
```
then open todo.html

### Documentation
The only documentation available right now is the idris generated doc
```shell
cd lib
idris --mkdoc js.ipkg
```
Open a github issue to discuss anything related to this project. 
