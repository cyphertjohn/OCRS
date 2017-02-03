all: examples

examples: main.ml test.ml
	ocamlfind ocamlopt -linkpkg -package ocrs -o main main.ml
	ocamlfind ocamlopt -linkpkg -package ocrs -o test test.ml


clean:
	rm test main *o *cmi *cmx
