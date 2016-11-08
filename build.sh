#!/usr/bin/zsh

dirs=(GPUCSL TypedIR Compiler CertSkel Examples)

for d in $dirs;
do
    pushd $d;
    coq_makefile -f _CoqProject -f Make -o Makefile
    make || exit 1; 
    popd
done
