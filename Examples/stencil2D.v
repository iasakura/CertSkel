Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Require Import Compiler Ext Extract Host CompilerProof LibTactics.
Open Scope Z_scope.

Definition stencil (dim : list (Z * Z)) (xs : list Z) : comp (list Z) :=
  mapM (fun i =>
          do! dim <- nth_error dim 0 in
          let dx := fst dim in
          let dy := snd dim in
          let ix := i mod dx in
          let iy := i / dx in
          do! nv <- if iy =? dy - 1 then ret 0 else nth_error xs (ix + (iy + 1) * dx) in
          do! wv <- if ix =? 0 then ret 0 else nth_error xs ((ix - 1) + iy * dx) in
          do! cv <- nth_error xs i in
          do! ev <- if ix =? dx - 1 then ret 0 else nth_error xs ((ix + 1) + iy * dx) in
          do! sv <- if i =? 0 then ret 0 else nth_error xs (ix + (iy - 1) * dx) in
          ret (nv + wv + cv + ev + sv))
       (seq 0 (len xs)).

Definition stencil_GPGPU :
  {p : GModule | @equivGC (Skel.TZ :: Skel.TTup Skel.TZ Skel.TZ :: nil) Skel.TZ stencil p}.
Proof.
  unfold stencil.
  reifyFunc.
  apply compileOk.
  repeat constructor.
Defined.