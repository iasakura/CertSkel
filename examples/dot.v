Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Require Import Compiler Ext Extract Host CompilerProof LibTactics.
Open Scope Z_scope.

Definition dot (xs ys : list Z) : comp (list Z)
  := do! t <- mapM (fun xy => ret (fst xy + snd xy)) (zip xs ys) : comp _ in
     do! t <- reduceM (fun x y => ret (x + y)) t in
     ret t.

Definition min_idx_GPGPU :
  {p : GModule | @equivGC (Skel.TZ :: Skel.TZ :: nil) (Skel.TZ) dot p}.
Proof.
  unfold dot; simpl.
  reifyFunc.
  apply compileOk.
  repeat econstructor; simpl.
  - intros; omega.
  - intros; omega.
Defined.

Definition res := save_to_file (`min_idx_GPGPU) "./dot.cu".

Cd "extracted".

Separate Extraction res.