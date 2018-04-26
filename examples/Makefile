all: examples

examples: main.ml test.ml
	ocamlfind ocamlopt -linkpkg -package ocrs -o main main.ml
	ocamlfind ocamlopt -linkpkg -package ocrs -o test test.ml
	ocamlfind ocamlopt -linkpkg -package ocrs -o unit_mult_test unit_mult_test.ml


clean:
	rm test main unit_mult_test *o *cmi *cmx
