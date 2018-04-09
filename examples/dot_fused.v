Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Require Import Compiler Ext Extract Host CompilerProof Fusion LibTactics.
Open Scope Z_scope.

Require Import DepList.
Import Skel.

Definition dot_fused_IR : AS (TZ :: TZ :: nil) TZ :=
  ALet _ _ _ (
    Reduce _ _  (F2 _ TZ TZ TZ (EBin _ _ _ _ _ Eplus (EVar _ _ _ (HNext HFirst)) (EVar _ _ _ HFirst)))
      (DArr _ _ (F1 _ TZ TZ (EBin _ _ _ _ _ Emult 
                                  (EA _ _ _ (HNext HFirst) (EVar _ _ _ HFirst) )
                                  (EA _ _ _ HFirst (EVar _ _ _ HFirst)))) (LLen _ _ HFirst))
  ) (
  ARet _ _ HFirst).

Definition dot (xs ys : list Z) : comp (list Z)
  := do! t <- mapM (fun xy => ret (fst xy * snd xy)) (zip xs ys) in
     reduceM (fun x y => ret (x + y)) t.

Definition dot_fused_GPGPU :
  {p : GModule | @equivGC (Skel.TZ :: Skel.TZ :: nil) (Skel.TZ) dot p}.
Proof.
  unfold dot; simpl.
  reifyFunc.
  eapply equivIC_weaken.
  { introv Heq; applys (>>simple_fusion_correct Heq).
    repeat econstructor; simpl.
    - intros; omega.
    - intros; omega. }
  unfold simple_fusion; simpl.
  unfold fuse_f1, body_of_func1, lift_sexp; simpl.
  apply compileOk.
  repeat econstructor; simpl.
  - intros; omega.
  - intros; omega.
Defined.

Goal False.
  pose (asDenote _ _ dot_fused_IR) as D.
  simpl in D.
Abort.

Definition res := save_to_file (`dot_fused_GPGPU) "./dot_fused.cu".

Cd "extracted".

Separate Extraction res.