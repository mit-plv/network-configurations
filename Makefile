.PHONY: coq clean

COQC=coqc -q -Q bbv/theories bbv

coq:
	$(COQC) NetworkConfigurations

clean:
	rm -f *.vo *.glob .*.aux
