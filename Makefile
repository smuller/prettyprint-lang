all: lexer.mll parser.mly types.ml test.ml
	ocamllex lexer.mll
	ocamlyacc -v parser.mly
#	ocamlc -g -o test types.ml parser.mli lexer.ml parser.ml unify.ml context.ml typecheck.ml test.ml
	ocamlc -c -rectypes types.ml
	ocamlc -c -rectypes parser.mli
	ocamlc -c -rectypes lexer.ml
	ocamlc -c -rectypes parser.ml
#	ocamlc -c -rectypes print.ml
	#ocamlfind ocamlc -package z3 -c -rectypes unifyz3.ml
	#ocamlc -c -rectypes context.ml
	ocamlfind ocamlc -g -rectypes -package z3 -linkpkg -o test types.ml parser.mli lexer.ml parser.ml print.ml unifyz3.ml context.ml typecheck.ml test.ml

clean:
	rm *.cmo
	rm *.cmi

full-clean: clean
	rm lexer.ml
	rm parser.ml
	rm parser.mli
