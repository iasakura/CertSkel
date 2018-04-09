Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Require Import Compiler Ext Extract Host CompilerProof Fusion LibTactics.
Open Scope Z_scope.

Require Import DepList.
Import Skel.

Definition dot (xs ys : list Z) : comp (list Z)
  := do! t <- mapM (fun xy => ret (fst xy * snd xy)) (zip xs ys) in
     reduceM (fun x y => ret (x + y)) t.

Definition dot_fused_GPGPU :
  {p : GModule | @equivGC (Skel.TZ :: Skel.TZ :: nil) (Skel.TZ) dot p}.
Proof.
  unfold dot; simpl.
  (* Reification *)
  reifyFunc.
  eapply equivIC_weaken.
  { (* Fusion transformation *)
    introv Heq; applys (>>simple_fusion_correct Heq).
    (* Currently, my fusion transformation also requires algebraic properties of reduce function... *)
    repeat econstructor; simpl.
    - intros; omega.
    - intros; omega. }
  (* GPGPU code generation *)
  apply compileOk.
  repeat econstructor; simpl.
  - intros; omega.
  - intros; omega.
Defined.

Definition res := save_to_file (`dot_fused_GPGPU) "./dot_fused.cu".

Cd "extracted".

Separate Extraction res.