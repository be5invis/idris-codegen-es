# idris-codegen-es

Optimized JavaScript codegen for Idris.

Originally based on the codegen in https://github.com/rbarreiro/idrisjs.

Objective:

 - Fast & reasonable JS output.
 - Compatible with official JS FFI.

To build:

```bash
stack build
```

To test: with [Ava](https://github.com/avajs/ava) and [JS Bindings](https://github.com/rbarreiro/idrisjs) installed,

```bash
npm install
npm test
```
