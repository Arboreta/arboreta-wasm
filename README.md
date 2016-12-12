# Arboreta WebAssembly components

Common Lisp tooling for [WebAssembly](http://webassembly.org) in the Arboreta environment. Far future goals include a native debugger for the browser target and progressive compatability of sbcl code.

arboret-wasm requires the [WASM Binary Toolkit](https://github.com/WebAssembly/wabt)

# Installation
run "sbcl --core image.ccl --script test-server.lisp" against a sbcl image with the package requirements found in test-server.lisp to compile an executable Hunchentoot site at localhost:8004 serving /output/out.wasm


# Roadmap

* basic VM layout (see [OCaml implementation](https://github.com/WebAssembly/spec) )
* CL parser
* wasm generator
* further bootstrapping CL repl
* wasm runtime debugger in Arboreta
