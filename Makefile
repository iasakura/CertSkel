.PHONY: cpdtlib tlc all

all: tlc cpdtlib Makefile.coq
	make -f Makefile.coq

./external/cpdtlib/Makefile:
	git submodule update --init

./external/tlc/GNUmakefile:
	git submodule update --init

cpdtlib: ./external/cpdtlib/Makefile
	make -C ./external/cpdtlib

tlc: ./external/tlc/GNUmakefile
	make -C ./external/tlc

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

examples: all tlc cpdtlib
	make -C examples
