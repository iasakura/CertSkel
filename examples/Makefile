.PHONY: all

all: extracted Makefile.coq
	make -f Makefile.coq

extracted:
	mkdir extracted

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
