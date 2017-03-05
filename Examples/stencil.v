Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Require Import Compiler Ext Extract Host CompilerProof LibTactics.
Open Scope Z_scope.

Definition stencil (xs : list Z) : comp (list Z) :=
  mapM (fun i =>
          do! l <- if i =? 0 then ret 0 else nth_error xs (i - 1) in
          do! c <- nth_error xs i in
          do! r <- if i =? len xs - 1 then ret 0 else nth_error xs (i + 1) in
          ret (l + c + r))
       (seq 0 (len xs)).

Definition map0 (xs : list Z) : comp (list Z) :=
  mapM (fun _ => ret 0%Z) xs.

Definition stencil_GPGPU :
  {p : GModule | @equivGC (Skel.TZ :: nil) Skel.TZ stencil p}.
Proof.
  unfold stencil.
  reifyFunc.
  apply compileOk.
  repeat constructor.
Defined.