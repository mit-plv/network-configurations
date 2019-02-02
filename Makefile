.PHONY: coq clean

COQC=coqc -q -Q bbv/theories bbv
OCAMLC=ocamlfind ocamlopt -g -thread -I src/ -package openflow,openflow.async -linkpkg

all : coq install compile-ocaml

coq:
	$(MAKE) -C bbv && $(COQC) src/NetworkConfigurations

install:
	opam pin openflow 0.9.1

compile-ocaml:
	mkdir -p out && $(OCAMLC) -o out/openflow_controller src/example_entries.mli src/example_entries.ml src/openflow_controller.ml

clean:
	$(MAKE) -C bbv clean; rm -f *.vo *.glob .*.aux src/*.vo src/*.glob src/*.aux src/*.cmi src/*.cmx src/*.o src/example_entries.*; rm -rf out
