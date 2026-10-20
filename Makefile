# Rocq 9.0.1 / OCaml 5.2.1
OCAMLOPT = ocamlfind ocamlopt -package str -linkpkg
all: Makefile.coq
	$(MAKE) -f Makefile.coq
	$(OCAMLOPT) devote.mli devote.ml tally.ml devote_main.ml -o devote_main
	$(OCAMLOPT) devote.mli devote.ml tally.ml votes.ml recount.ml -o recount
	$(OCAMLOPT) devote.mli devote.ml tally.ml random_cycles.ml -o random_cycles
	$(OCAMLOPT) devote.mli devote.ml tally.ml devotee_diff.ml -o devotee_diff
	$(OCAMLOPT) devote.mli devote.ml tally.ml certify.ml -o certify
	$(OCAMLOPT) devote.mli devote.ml tally.ml votes.ml audit.ml -o audit
Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq
recount: all
	./recount
clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf devote_main recount random_cycles devotee_diff certify audit devote.ml devote.mli *.cm* *.o
.PHONY: all clean recount
