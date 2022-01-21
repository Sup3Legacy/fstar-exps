all: tuto1

tuto1:
	fstar --odir fstar_out --codegen OCaml tuto1.fst --extract 'Tuto1';
	ocamlbuild fstar_out/Tuto1.native -package fstarlib,batteries;
	_build/fstar_out/Tuto1.native;

compil:
	fstar --record_hints --use_hints --odir fstar_out --codegen OCaml compil.fst --extract 'Compil';
	ocamlbuild fstar_out/Compil.native -package fstarlib,batteries;
	_build/fstar_out/Compil.native;