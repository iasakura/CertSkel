.PHONY: cpdtlib tlc all

all: tlc cpdtlib Makefile.coq
	make -f Makefile.coq

./external/cpdtlib/Makefile:
	git submodule update --init

./external/tlc/GNUmakefile:
	git submodule update --init

cpdtlib: ./external/cpdtlib/Makefile
	cd ./external/cpdtlib && make

tlc: ./external/tlc/GNUmakefile
	cd ./external/tlc/ && make

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
