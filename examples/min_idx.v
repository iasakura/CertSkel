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
  {p : GModule | @equivGC (Skel.TZ :: nil) (Skel.TTup Skel.TZ Skel.TZ) min_idx p}.
Proof.
  unfold min_idx; simpl.
  reifyFunc.
  apply compileOk.
  repeat econstructor; simpl.
  - unfold bind, ret; simpl.
    intros.
    do 4 rewrite <-if_app; reflexivity.
  - introv; simpl; repeat lazymatch goal with
            | [|- context [(?X <? ?Y)%Z]] => destruct (Z.ltb_spec0 X Y)
            end; eauto; try omega.
    destruct x, y; simpl in *; f_equal; try omega.
  - introv; simpl; repeat lazymatch goal with
            | [|- context [(?X <? ?Y)%Z]] =>
              let H := fresh in
              destruct (Z.ltb_spec0 X Y) as [H | H];
              revert H
            end; eauto; intros; omega.
Defined.

Lemma min_idx_None : forall (arr : list Z) n,
  reduceM
    (fun x y => if (fst x) <? (fst y) then ret x
                else if (fst y) <? (fst x) then ret y
                else if (snd x) <? (snd y) then ret x
                else if (snd y) <? (snd x) then ret y
                else ret x)
    (zip arr (seq n (len arr))) = None
  -> arr = [].
Proof.
  unfold min_idx, reduceM, seq, lift_op; destruct arr as [|x xs]; simpl; introv He; [congruence|].
  match type of He with
  | context [match ?x with Some _ => _ | None => _ end ] => remember x as e
  end.
  destruct e as [e|]; inverts He.
  rewrite SuccNat2Pos.id_succ in *; simpl in Heqe.
  match type of Heqe with
  | context [match ?x with Some _ => _ | None => _ end ] => remember x as e0
  end.
  destruct e0 as [[idx' mx']|]; simpl in *.
  repeat match type of Heqe with
  | context [if ?b then _ else _] => destruct b
  end; inverts Heqe. 
  inverts Heqe.
Qed.

Lemma nth_error_Z_succ A x y (xs : list A) n :
  nth_error xs n = Some y ->
  nth_error (x :: xs) (Z.succ n) = Some y.
Proof.
  unfold nth_error, Z_to_nat_error, bind, ret; simpl; unfold bind_opt.
  repeat destruct Z_le_dec; intros; try first [omega | congruence].
  rewrites* Z2Nat.inj_succ; omega.
Qed.

Lemma min_idx_correct_aux : forall (arr : list Z) idx mx n,
  reduceM
    (fun x y => if (fst x) <? (fst y) then ret x
                else if (fst y) <? (fst x) then ret y
                else if (snd x) <? (snd y) then ret x
                else if (snd y) <? (snd x) then ret y
                else ret x)
    (zip arr (seq n (len arr))) = Some [(mx, idx)]
  -> List.Forall (fun x => mx <= x) arr /\
     nth_error arr (idx - n) = Some mx.
Proof.
  unfold min_idx, reduceM, seq, lift_op; induction arr as [|x xs]; simpl; introv He; [congruence|].
  match type of He with
  | context [match ?x with Some _ => _ | None => _ end ] => remember x as e
  end.
  destruct e as [e|]; inverts He.
  rewrite SuccNat2Pos.id_succ in *; simpl in Heqe.
  match type of Heqe with
  | context [match ?x with Some _ => _ | None => _ end ] => remember x as e0
  end.
  destruct e0 as [[mx' idx']|]; simpl in *.
  - forwards*: (>>IHxs idx' mx' (Z.succ n)).
    unfold len; rewrite Nat2Z.id; rewrite <-Heqe0; eauto.
    destruct H as [Hle Heq].
    destruct (Z.ltb_spec0 x mx') as [Hlt|].
    { inverts Heqe; rewrite Z.sub_diag.
      splits; [|reflexivity].
      constructor; [omega|].
      rewrite List.Forall_forall in *; intros; forwards*: Hle; omega. }
    destruct (Z.ltb_spec0 mx' x) as [Hlt|].
    { inverts Heqe.
      rewrite List.Forall_forall in *.
      split.
      - introv [Hin|Hin]; substs; [omega|jauto].
      - asserts_rewrite (idx' - n = Z.succ (idx' - Z.succ n)); [omega|].
        rewrites* (>>nth_error_Z_succ Heq).  }
    assert (x = mx') by omega; substs.
    destruct (Z.ltb_spec0 n idx'); [inverts Heqe|].
    { split; [constructor; [omega|now eauto] |].
      rewrite Z.sub_diag; eauto. }
    destruct (Z.ltb_spec0 idx' n); [inverts Heqe|].
    { split; [constructor; [omega|now eauto]|].
      asserts_rewrite (idx' - n = Z.succ (idx' - Z.succ n)); [omega|].
      rewrites* (>>nth_error_Z_succ Heq). }
    assert (n = idx') by omega; substs.
    inverts Heqe.
    split; [constructor; [omega|now eauto]|].
    rewrite Z.sub_diag; eauto.
  - forwards*: (>>min_idx_None xs (Z.succ n)).
    { unfold reduceM, seq, lift_op, len; rewrite Nat2Z.id; eauto.
      rewrite <-Heqe0; eauto. }
    subst; inverts Heqe.
    simpl in *.
    split; [repeat constructor; try omega|rewrite Z.sub_diag; reflexivity].
Qed.    

Lemma min_idx_correct arr :
  arr <> [] ->
  exists mx idx,
    min_idx arr = Some [(mx, idx)] /\
    List.Forall (fun x => mx <= x) arr /\
    nth_error arr idx = Some mx.
Proof.
  destruct (min_idx arr) as [res|] eqn:Heq.
  - destruct res as [| [mx idx] [| y]];
      try now (unfold min_idx, reduceM in *; destruct List.fold_right; inverts Heq).
    forwards*: min_idx_correct_aux.
    asserts_rewrite (idx - 0 = idx) in H; [omega|jauto].
  - forwards*: min_idx_None.
Qed.  
  
Definition res := save_to_file (`min_idx_GPGPU) "./min_idx.cu".

Cd "extracted".

Separate Extraction res.