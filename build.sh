#!/usr/bin/zsh

dirs=(GPUCSL TypedIR Compiler CertSkel)

pushd cpdtlib; make || exit 1; popd;
pushd tlc; make || exit 1; popd;

for d in $dirs;
do
    pushd $d;
    coq_makefile -f _CoqProject -f Make -o Makefile
    make -j8 || exit 1; 
    popd
done
