.PHONY: coq clean

COQC=coqc -q

coq:
	$(COQC) NetworkConfigurations

clean:
	rm -f *.vo *.glob .*.aux
