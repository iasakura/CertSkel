Require Import TypedTerm Monad Host DepList CUDALib Compiler Correctness CodeGenM.

Theorem compile_prog_ok GA ty ntrd nblk (p : Skel.AS GA ty) :
  let M := compile_prog ntrd nblk p in
  sat_FC M nil ("__main", {|fs_tag := Hfun; fs_params := |})
