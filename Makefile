.PHONY: coq clean

COQC=coqc -q -Q bbv/theories bbv

coq:
	$(MAKE) -C bbv; $(COQC) NetworkConfigurations

clean:
	rm -f *.vo *.glob .*.aux
