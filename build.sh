#!/usr/bin/zsh

dirs=(GPUCSL GPUVeLib Skeletons CompilerProof)

for d in $dirs;
do
    pushd $d;
    coq_makefile -f _CoqProject -f Make -o Makefile
    make; 
    popd
done
