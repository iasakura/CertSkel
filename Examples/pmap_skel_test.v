Require Import GPUCSL.
Require Import pmap_skel.
Require Import Skel_lemma.
Require Import scan_lib.
Require Import LibTactics.
Require Import Psatz.

(*
 Code generating example:
 let idxs := generate (length arr0) (\i -> i) in
 let t := map (\i -> (i, arr0[i])) idxs in
 map (\(i, t) -> arr1[i] + t)

 fused version:
 map (\(i, t) -> arr1[i] + t) (DArr (\i -> (i, arr0[i])))
*)

Section verification_example.
  Variable ntrd : nat.
  Variable nblk : nat.
  
  Hypothesis ntrd_neq_0 : ntrd <> 0.
  Hypothesis nblk_neq_0 : nblk <> 0.

  Open Scope list.
  Open Scope string.
  Close Scope exp.
  Eval compute in names_of_arg (grpOfInt 0) 1.
  (* length of the array: shInO, the top address of the array: arrInOO *)
  Definition env := (0, 1) :: (1, 1) :: nil.
  Notation t0 := (Var "lv10").
  Notation t1 := (Var "lv11").

  Notation arr0 := (Var "arrInOO").
  Notation arr1 := (Var "arrInSOO").

  Variable len : nat.
  Hypothesis len_neq_0 : len <> 0.
  Variable arr0_ptr : Z.
  Variable arr1_ptr : Z.
  Variable arr0_elms : nat -> Z.
  Variable arr1_elms : nat -> Z.
  Variable out_ptr : Z.
  Variable out_elms : nat -> Z.
  Import ListNotations.
  Open Scope list_scope.
  Definition arr0_elms' i := arr0_elms i :: nil.
  Definition arr1_elms' i := arr1_elms i :: nil.
  Definition out_elms' i := out_elms i :: nil.
  
  Definition env_den := (arr0_ptr :: nil, len, arr0_elms') ::
                        (arr1_ptr :: nil, len, arr1_elms') :: nil.
  Definition out_ptr' := out_ptr :: nil.
  
  Definition default_var := Var "l".

  Definition inDim := 2.
  Definition get (x : var) :=
    ( t0 ::= x ;; t1 ::= [Gl arr0 +o x], Evar t0 :: Evar t1 :: nil).

  Definition get_den val v :=
    match v with
    | v0 :: v1 :: nil => 
      v0 = val /\
      if Z_le_dec 0 val then 
        if Z_lt_dec v0 (Zn len) then v1 = arr0_elms (Z.to_nat val) else False
      else False
    | _ => False
    end.

  Definition func (xs : list var) :=
    let in0 := nth 0 xs default_var in
    let in1 := nth 1 xs default_var in
    ( t1 ::= [Gl arr1 +o in0 ], (in1 +C t1) :: nil).

  Definition default_val := 0%Z.

  Definition func_den (vin vout : list val) :=
    match vin with
    | i0 :: i1 :: nil =>
      match vout with
      | o :: nil =>
        if Z_le_dec 0 i0 then 
          if  Z_lt_dec i0 (Zn len) then o = (arr1_elms (Z.to_nat i0) + i1)%Z else False
        else False
      | _ => False
      end
    | _ => False
    end.

  Definition outDim := 1.

  Lemma pure_emp stk : stk ||= !(emp) <=> emp.
  Proof.
    split.
    - intros; destruct H; eauto.
    - intros; split; eauto.
  Qed.

  (* Lemma g_dec i v1 v2 : get_den i v1 -> get_den i v2 -> v1 = v2. *)
  (* Proof. *)
  (*   unfold get_den; destruct v1 as [|? [|? [|? ?]]]; simpl; try tauto. *)
  (*   unfold get_den; destruct v2 as [|? [|? [|? ?]]]; simpl; try tauto. *)
  (*   repeat destruct lt_dec; try tauto. *)
  (*   intros [? ?] [? ?]; congruence. *)
  (* Qed. *)

  Theorem gen_code_correct :
    exists fgi, 
      (forall i : nat, i < len -> exists t, get_den (Zn i) t /\ func_den t (fgi i)) /\
    CSLg ntrd nblk ntrd_neq_0 nblk_neq_0 
    (!(Outs outDim ==t out_ptr :: nil) **
     !(Len outDim === Zn len) **
     input_spec env env_den 1 **
     is_tuple_array_p (es2gls (vs2es out_ptr')) len out_elms' 0 1)
    {| get_sh_decl := nil;
       get_cmd := map' ntrd nblk inDim outDim get func |}
    (input_spec' env_den 1 **
     is_tuple_array_p (es2gls (vs2es out_ptr')) len (fun v : nat => fgi v) 0 1).
  Proof.
    apply map_correct_g; eauto.
    - (* safety *)
      intros i Hl; unfold get_den, func_den; split.
      + exists (Zn i :: arr0_elms i :: nil); repeat split; try congruence.
        destruct Z_lt_dec; try omega.
        destruct Z_le_dec; try omega.
        rewrite Nat2Z.id; eauto.
      + intros gv Hgv.
        destruct gv as [| gv0 [|gv1 [|? ?]]]; try tauto.
        destruct Hgv as [Hi Hgv].
        destruct (Z_le_dec _ (Zn i)), (Z_lt_dec gv0 _); try tauto.
        exists ((arr1_elms i + gv1)%Z :: nil).
        destruct Z_le_dec; try omega.
        subst; rewrite Nat2Z.id; eauto.
    - unfold get; simpl; intros.
      destruct H as [? | [? | []]]; subst; eauto.
    - simpl; intros.
      destruct H as [? | [? | []]]; subst; simpl in *.
      destruct H0 as [? | []]; subst; right; eauto.
      destruct H0 as [? | []]; subst; right; eauto.
    - intros x nt tid ix gv Hgv Hneq. simpl in *.
      destruct gv as [| gv0 [|gv1 [|? ?]]]; try tauto; simpl in *.
      destruct (Z_le_dec _ _), (Z_lt_dec gv0 (Zn len)); try tauto.
      destruct Hgv as [Hgv1 Hgv2].
      assert (Ht0x : t0 <> x) by eauto.
      assert (Ht1x : t1 <> x) by eauto.
      eapply rule_seq.
      { apply rule_frame.
        hoare_forward.
        - intros s h [v0 H].
          remember t0.
          subA_normalize_in H with (fun H =>  H).
          assert ((!(t0 === ix) ** !(x === ix)) s h).
          { sep_rewrite_in_r emp_unit_l H; sep_split_in H; sep_split; eauto.
            unfold_conn_all; simpl in *.
            destruct var_eq_dec; try congruence; eauto.
            unfold_conn_all; simpl in *.
            destruct var_eq_dec; simpl in *; try congruence. }
          exact H0.
        - repeat prove_inde. }
      eapply Hbackward.
      Focus 2. { 
        intros s h H.
        sep_split_in H.
        sep_normal_in HP0.
        sep_normal_in HP2.
        change_in H.
        { unfold_pures.
          sep_rewrite_in (@is_array_unfold (Gl arr0_ptr) (Z.to_nat ix)) H.
          rewrite <-plus_n_O in H.
          2: zify; rewrite Z2Nat.id; nia.
          rewrite Z2Nat.id in H; [|nia].
          assert ((Gl arr0_ptr +o ix ===l Gl arr0 +o ix) s h).
          { destruct HP0; unfold_conn; simpl in *; f_equal; omega. }
          sep_rewrite_in mps_eq1 H; [|exact H0].
          sep_normal_in H; exact H. }
        sep_combine_in H.
        exact H. } Unfocus.
      eapply Hforward.
      { hoare_forward; try (destruct var_eq_dec; congruence).
        eauto. }
      intros s h H.
      repeat (try sep_rewrite_r sep_assoc; try sep_rewrite pure_star; try sep_rewrite pure_pure).
      sep_rewrite pure_emp; sep_normal.
      repeat (try sep_rewrite_in_r sep_assoc H; try sep_rewrite_in pure_star H;
              try sep_rewrite_in pure_pure H).
      try sep_rewrite_in pure_emp H; sep_normal_in H.
      unfold arr0_elms', fst_of_vals in *; simpl in H.
      sep_normal_in H.
      sep_split; sep_split_in H; subst; eauto.
      unfold_pures.
      sep_rewrite (@is_array_unfold (Gl arr0_ptr) (Z.to_nat ix)); simpl.
      2: zify; rewrite Z2Nat.id; nia.
      sep_normal; sep_cancel.
      rewrite <-plus_n_O, Z2Nat.id; [|nia].
      assert ((Gl arr0_ptr +o ix ===l Gl arr0 +o ix) s h).
      { unfold_conn_all; simpl in *; f_equal; omega. }
      sep_rewrite mps_eq1; [|exact H1].
      repeat sep_cancel.
    - unfold get_den; destruct gv as [|? [|? [|? ?]]]; simpl; tauto.
    - unfold func; simpl; intros.
      destruct H as [? | []]; subst; eauto.
    - simpl; intros.
      destruct H as [? | []]; subst; simpl in *.
      destruct H0 as [? | [? | []]]; subst; eauto.
      destruct v as [| ? [| ? ?]]; simpl; eauto.
    - simpl; introv Hfv Hlen Hdis.
      apply disjoint_comm in Hdis; simpl in Hdis; destruct Hdis as [Hdis _].
      unfold inDim in *.
      destruct x as [|x0 [|x1 [|? ?]]]; simpl in Hlen; try congruence.
      unfold func_den in *; destruct vs as [| v0 [| v1 [| ? ?]]]; simpl in Hfv; try tauto.
      destruct fv as [| fv0 [| fv1 [| ? ?]]]; try tauto.
      destruct (Z_le_dec 0 v0), (Z_lt_dec v0 (Zn len)); try tauto.
      simpl in Hdis.
      assert (Hv0t1 : x0 <> t1) by eauto.
      assert (Hv1t1 : x1 <> t1) by eauto.
      simpl.
      eapply Hbackward.
      Focus 2. {
        intros s h H.
        repeat (try sep_rewrite_in_r sep_assoc H; try sep_rewrite_in pure_star H;
                try sep_rewrite_in pure_pure H);
        repeat sep_rewrite_in pure_emp H; sep_normal_in H.
        exact H. } Unfocus.
      eapply Hforward.
      Focus 2. {
        intros s h H.
        repeat (try sep_rewrite_r sep_assoc; try sep_rewrite pure_star; try sep_rewrite pure_pure);
          sep_rewrite pure_emp; sep_normal.
        exact H. } Unfocus.
      eapply Hbackward.
      Focus 2. { 
        intros s h H.
        sep_split_in H.
        change_in H. {
          unfold_pures.
          sep_rewrite_in (@is_array_unfold (Gl arr1_ptr) (Z.to_nat v0)) H; simpl. 
          2: zify; rewrite Z2Nat.id; nia.
          rewrite <-plus_n_O, Z2Nat.id in H; [|nia].
          assert ((Gl arr1_ptr +o v0 ===l Gl arr1 +o v0) s (emp_ph loc)).
          { unfold_conn; simpl; f_equal; congruence. }
          sep_rewrite_in mps_eq1 H; [|exact H0].
          sep_normal_in H; exact H. }
        sep_combine_in H; exact H. } Unfocus.
      eapply Hforward.
      { hoare_forward; simpl in Hdis; [destruct var_eq_dec; try congruence..|].
        intros s h H; sep_normal_in H; eauto. }
      intros s h H; sep_split_in H; sep_split; eauto.
      + unfold_pures; unfold_conn; simpl; eauto.
        unfold fst_of_vals, arr1_elms' in *; simpl in *; subst; omega.
      + sep_cancel.
        unfold_pures.
        sep_rewrite (@is_array_unfold (Gl arr1_ptr) (Z.to_nat v0)); simpl. 
        2: zify; rewrite Z2Nat.id; nia.
        rewrite <-plus_n_O, Z2Nat.id; [|nia].
        assert ((Gl arr1_ptr +o v0 ===l Gl arr1 +o v0) s (emp_ph loc)).
        { unfold_conn; simpl; f_equal; congruence. }
        sep_rewrite mps_eq1; [|exact H1].
        sep_normal; repeat sep_cancel.
    - unfold func_den; intros [|? [|? [|? ?]]] [|? [|? ?]]; try tauto.
  Qed.
End verification_example.

Goal False.
Proof.
  let t := type of gen_code_correct in pose t.
  simpl in P.
  unfold map', map_ker, WhileI, get, func in P; simpl in P.
Abort.

