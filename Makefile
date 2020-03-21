.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Group.v

clean:
	rm -f *.vo *.vok *.vos *.glob
