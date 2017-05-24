.PHONY: cpdtlib tlc all
default: all

./external/cpdtlib:
	git submodule update --init

./external/tlc:
	git submodule update --init

cpdtlib: ./external/cpdtlib
	cd ./external/cpdtlib && make

tlc: ./external/tlc
	cd ./external/tlc/ && make

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

all: tlc cpdtlib Makefile.coq
	make -f Makefile.coq

