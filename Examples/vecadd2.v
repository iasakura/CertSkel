Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Require Import Compiler Ext Extract Host CompilerProof LibTactics.
Open Scope Z_scope.

Definition vecadd2 (xs ys : list Z) : comp (list Z) :=
  mapM (fun xy => ret (fst xy + snd xy))
       (zip xs ys).

Definition vecadd2_GPGPU:
  {p : GModule | @equivGC (Skel.TZ :: Skel.TZ :: nil) Skel.TZ vecadd2 p}.
Proof.
  unfold vecadd2.
  reifyFunc.
  apply compileOk.
  repeat constructor.
Defined.

Definition res := 
  save_to_file (`vecadd2_GPGPU) 
               "./vecadd2.cu".

Cd "extracted".

Separate Extraction res.