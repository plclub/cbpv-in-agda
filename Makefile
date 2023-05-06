all: Makefile.coq
	+make -C coq -f Makefile.coq all

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
