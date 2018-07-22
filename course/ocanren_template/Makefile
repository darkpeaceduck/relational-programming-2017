OCAMLC = ocamlc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
SOURCES = tests.ml
CAMLP5 = -pp "camlp5o -I `ocamlfind -query ocanren.syntax` -I `ocamlfind -query GT.syntax` pa_minikanren.cmo pa_gt.cmo -L `ocamlfind -query GT.syntax`"
PXFLAGS = $(CAMLP5)
BFLAGS = -rectypes -I `ocamlfind -query GT` -I `ocamlfind -query ocanren` -I `ocamlfind -query checked`
OFLAGS = $(BFLAGS)

all: .depend tests.opt

.depend: $(SOURCES)
	$(OCAMLDEP) $(PXFLAGS) *.ml > .depend

tests.opt: $(SOURCES:.ml=.cmx)
	$(OCAMLOPT) -o tests.opt $(OFLAGS) GT.cmxa unix.cmxa MiniKanren.cmxa $(SOURCES:.ml=.cmx)

tests.byte: $(SOURCES:.ml=.cmo)
	$(OCAMLC) -o tests.byte $(BFLAGS) GT.cma unix.cma MiniKanren.cma $(SOURCES:.ml=.cmo)

clean:
	rm -Rf *.cmi *.cmo *.cmx *.annot *.o

-include .depend
# generic rules

###############
%.cmi: %.mli
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

# Note: cmi <- mli should go first
%.cmi: %.ml
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

%.cmo: %.ml
	$(OCAMLC) -c $(BFLAGS) $(PXFLAGS) $<

%.o: %.ml
	$(OCAMLOPT) -c $(OFLAGS) $(STATIC) $(PXFLAGS) $<

%.cmx: %.ml
	$(OCAMLOPT) -c $(OFLAGS) $(STATIC) $(PXFLAGS) $<

