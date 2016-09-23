#!/usr/bin/zsh

dirs=(GPUCSL GPUVeLib Skeletons CompilerProof)

for d in $dirs;
do
    pushd $d; make; popd
done
