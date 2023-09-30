all: Makefile.coq
	+make -C coq -f Makefile.coq all

coq/Syntax.v: coq/cbpv.sig
	as2-exe -p Coq -i coq/cbpv.sig > coq/Syntax.v

coq/CBN/CBN.v: coq/CBN/cbn.sig
	as2-exe -p Coq -i coq/CBN/cbn.sig > coq/CBN/CBN.v

coq/CBV/CBV.v: coq/CBV/cbv.sig
	as2-exe -p Coq -i coq/CBV/cbv.sig > coq/CBV/CBV.v

html: Makefile.coq
	+make -C coq -f Makefile.coq html

clean: Makefile.coq
	+make -C coq -f Makefile.coq clean
	rm -f coq/Makefile.coq
	rm -f coq/Makefile.coq.conf
	rm -f website/*html

Makefile.coq: coq/_CoqProject
	cd coq && coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all html clean

website: Makefile.coq
	+make -C coq -f Makefile.coq html
	mv coq/html/*html website
	rm -rf coq/html
