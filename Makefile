all:
	ocamlbuild -cflags -warn-error,+26 -use-ocamlfind -package qcheck lCheck.cmo

clean:
	ocamlbuild -clean
