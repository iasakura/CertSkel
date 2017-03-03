Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Require Import Compiler Ext Extract Host CompilerProof LibTactics.
Open Scope Z_scope.

Definition min_idx (arr : list Z) : comp (list (Z * Z))
  := reduceM
       (fun x y => if (fst x) <? (fst y) then ret x
                   else if (fst y) <? (fst x) then ret y
                   else if (snd x) <? (snd y) then ret x
                   else if (snd y) <? (snd x) then ret y
                   else ret x)
       (zip arr (seq 0 (len arr))).

Definition min_idx_GPGPU :
  {p : GModule | equivGC1 (min_idx : list (Skel.typDenote Skel.TZ) ->
                                     comp (list (Skel.typDenote (Skel.TTup Skel.TZ Skel.TZ))))
                          p}.
Proof.
  unfold min_idx; simpl.
  reifyFunc.
  apply compileOk.
  repeat econstructor; simpl.
  - introv; repeat lazymatch goal with
            | [|- context [(?X <? ?Y)%Z]] => destruct (Z.ltb_spec0 X Y)
            end; eauto; try omega.
    destruct x, y; simpl in *; f_equal; try omega.
  - introv; repeat lazymatch goal with
            | [|- context [(?X <? ?Y)%Z]] =>
              let H := fresh in
              destruct (Z.ltb_spec0 X Y) as [H | H];
              revert H
            end; eauto; intros; try omega.
Defined.

Definition res := save_to_file (`min_idx_GPGPU) "./min_idx.cu".
Print Assumptions min_idx_GPGPU.

Cd "extracted".

Separate Extraction res.