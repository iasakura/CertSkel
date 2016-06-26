Require Import GPUCSL.
Require Import scan_lib.
Section fold.

(* 
  0  1  2  3  4  5  6  7  8 
----------------------------  st = (9+1) / 2 = 5
  05 16 27 38 4               
----------------------------  st = (5+1) / 2 = 3
  05 16 27                    
  39 37 
----------------------------  st = (3+1) / 2 = 2
  05 16
  39 37
  27
---------------------------   st = (2+1) / 2 = 1
  ..
*)
Variable val : Set.
Variable sum : val -> val -> val.
Local Infix "+v" := sum (at level 40).

Definition split_merge (a : nat -> val) (d : nat) (i : nat) :=
  a i +v a (i + d).

Fixpoint red_sum' (s len : nat) (f : nat -> val) (c : nat) :=
  match c with
    | O => (len, f)
    | S c => let d := (len + 1) / 2 in
             let f' i := if lt_dec (i-s + d) len then f i +v f (i + d) else f i in
             red_sum' s d f' c
  end.
End fold.
Definition init i : list nat := i::nil.

Eval cbv in let (l, f) := red_sum' _ (@app _) 0 9 init 0 in (l, ls_init 0 9 f).
Eval cbv in let (l, f) := red_sum' _ (@app _) 0 9 init 1 in (l, ls_init 0 9 f).
Eval cbv in let (l, f) := red_sum' _ (@app _) 0 9 init 2 in (l, ls_init 0 9 f).
Eval cbv in let (l, f) := red_sum' _ (@app _) 0 9 init 3 in (l, ls_init 0 9 f).
Eval cbv in let (l, f) := red_sum' _ (@app _) 0 9 init 4 in (l, ls_init 0 9 f).

Notation red_sum := (red_sum' _ (Z.add)).

Arguments div _ _ : simpl never.

Lemma red_sum_ok s len f c:
  let df := red_sum s len f c in
  fst df = 1 -> snd df s = sum_of s len f.
Proof.
  simpl; revert s len f; induction c; simpl; intros.
  - subst; simpl; omega.
  - apply IHc in H; rewrite H.
    Lemma sum_of_shift f s len :
      sum_of s ((len+1) / 2)
             (fun i => if lt_dec (i - s + (len+1)/2) len
                       then (f i + f (i + (len+1)/2)%nat)%Z else f i) =
      sum_of s len f.
    Proof.
      assert (len mod 2 = 0 \/ len mod 2 = 1).
      { pose proof (Nat.mod_upper_bound len 2); omega. }
      destruct H.
      - assert ((len+1)/2 = len / 2).
        { rewrite (Nat.div_mod len 2), H at 1; auto.
          cutrewrite (2 * (len / 2) + 0 + 1 = 1 + (len / 2) * 2); [|ring].
          rewrite Nat.div_add; auto. }
        rewrite H0.
        assert (len = len / 2 * 2).
        { rewrite (Nat.div_mod len 2) at 1; omega. }
        rewrite H1 at 2.
        rewrite shift_arr; auto.
        apply sum_of_eq.
        intros i Hi.
        repeat destruct lt_dec; try omega.
      - assert ((len+1)/2 = len/2+1).
        { rewrite (Nat.div_mod len 2), H at 1; auto.
          cutrewrite (2 * (len / 2) + 1 + 1 = (1 + (len / 2)) * 2); [|ring].
          rewrite Nat.div_mul; omega. }
        rewrite H0.
        rewrite sum_of_concat; simpl.
        destruct lt_dec.
        rewrite (Nat.div_mod len 2) in l at 3; auto; omega.
        erewrite sum_of_eq.
        Focus 2.
        { intros.
          destruct lt_dec; try omega.
          reflexivity.
          rewrite (Nat.div_mod len 2) in n0 at 2; omega. } Unfocus.
        rewrite <-shift_values.
        assert (len = len / 2 + 1 + len / 2).
        { rewrite (Nat.div_mod len 2) at 1; omega. }
        rewrite H1 at 5.
        repeat rewrite sum_of_concat; simpl.
        cutrewrite (s + (len / 2 + 1) = len / 2 + 1 + s); [|ring].
        omega.
    Qed.
    rewrite sum_of_shift; auto.
Qed.

Lemma red_sum_next_d s len f c: 
  fst (red_sum s len f (S c)) = (fst (red_sum s len f c) + 1) / 2.
Proof.
  revert s len f; induction c; [simpl; auto|].
  intros.
  remember (S c); simpl.
  rewrite Heqn at 2; simpl; auto.
Qed.

Lemma red_sum_next_f1 s len f c i:
  let df  := red_sum s len f c in
  let df' := red_sum s len f (S c) in
  snd df' i =
  if lt_dec (i - s + fst df') (fst df) then
    (snd df i + snd df (i + fst df')%nat)%Z
  else snd df i.
Proof.
  intros df df'; subst df df'.
  revert s len f; induction c; [simpl; auto|].
  intros.
  remember (S c); simpl.
  rewrite IHc. subst. auto.
Qed.

Section reduce.
Notation TID := (Var "tid").
Notation BID := (Var "bid").
Notation D := (Var "d").
Notation L := (Var "l").
Notation ARR := (Var "arr").
Notation T1 := (Var "t1").
Notation T2 := (Var "t2").
Notation C := (Var "c").

Variable ntrd : nat.
Variable f_ini : nat -> Z.
Variable arr : Z.
Variable len : nat.
Hypothesis len_neq_0 : len <> 0.
Notation Next x := ((x +C 1%Z)>>1).

Notation sum := (red_sum 0 len f_ini).

Definition INV (i : Fin.t ntrd) :=
  Ex c l f,
    !(TID === Z_of_fin i) **
    !(ARR === arr) **
    !(L === Enum' l) **
    !(C === Enum' c) **
    !(pure (l = fst (sum c))) **
    !(pure (0 < l)) **
    (if lt_dec (nf i) ((l+1)/2) then
       Sh arr +o (Z_of_fin i) -->p (1,  (snd (sum c) (nf i)))
     else emp) **
    (if lt_dec (nf i + (l+1)/2) l then
      (Sh arr +o Zn (nf i + (l+1)/2) -->p (1, (snd (sum c) (nf i + (l+1)/2))))
     else emp) **
    if Nat.eq_dec (nf i) 0 then is_array (Sh arr) (len - l) f l else emp.

Definition binv0 :=
  (MyVector.init (fun i : Fin.t ntrd =>
    (Ex c l f,
      !(ARR === arr) **
      !(L === Enum' ((l+1)/2)) **
      !(C === Enum' (c+1)) **
      !(pure (l = fst (sum c))) **
      !(pure (0 < l)) **
      (if lt_dec (nf i) ((l+1)/2) then
         Sh arr +o (Z_of_fin i) -->p (1,  (snd (sum (c+1)) (nf i)))
       else emp) **
      (if lt_dec (nf i + (l+1)/2) l then
         (Sh arr +o Zn (nf i + (l+1)/2) -->p (1, (snd (sum (c+1)) (nf i + (l+1)/2))))
       else emp) ** 
    if Nat.eq_dec (nf i) 0 then is_array (Sh arr) (len - l) f l else emp)),
   MyVector.init (fun i : Fin.t ntrd =>
    (Ex c l f,
      !(ARR === arr) **
      !(L === Enum' l) **
      !(C === Enum' c) **
      !(pure (l = fst (sum c))) **
      !(pure (0 < l)) **
      (if lt_dec (nf i) ((l+1)/2) then
         Sh arr +o (Z_of_fin i) -->p (1,  (snd (sum c) (nf i)))
       else emp) **
      (if lt_dec (nf i + (l+1)/2) l then
         (Sh arr +o Zn (nf i + (l+1)/2) -->p (1, (snd (sum c) (nf i + (l+1)/2))))
       else emp) ** 
      if Nat.eq_dec (nf i) 0 then is_array (Sh arr) (len - l) f l else emp))).

Definition reduce_ker (i : Fin.t ntrd) :=
  L ::= Enum' len ;;
  C ::= 0%Z ;;
  WhileI (INV i) (1%Z <C L) (
    D ::= (L +C 1%Z)>>1 ;;
    Cif (TID +C D <C L) (
      T1 ::= [ Sh ARR +o TID ] ;;
      T2 ::= [ Sh ARR +o (TID +C D) ] ;;
      [ Sh ARR +o TID ] ::= T1 +C T2
    ) Cskip ;;
    L ::= D ;;
    C ::= C +C 1%Z ;;
    Cbarrier 0
  ).

Lemma subA_TrueP v E : subA v E TrueP |= TrueP.
Proof.
  cbv; auto.
Qed.

Lemma subA_leeq (X : var) (E : exp) (E1 E2 : loc_exp) s h :
  subA X E (E1 ===l E2) s h -> (sublE X E E1 ===l sublE X E E2) s h.
Proof.
  intros; unfold subA' in *; unfold_conn_all; simpl in *;
  repeat rewrite <-sublE_assign in *; auto.
Qed.

Ltac subA_normalize_in H :=
  let Hf := fresh in
  match goal with
  | _ => idtac
  end;
   match type of H with
   | (_ ** _) _ _ =>
       eapply scRw in H;
        [ idtac | intros ? ? Hf; subA_normalize_in Hf; exact Hf.. ]
   | (subA _ _ (_ ** _)) _ _ =>
       apply subA_sconj in H; eapply scRw in H;
        [ idtac | intros ? ? Hf; subA_normalize_in Hf; exact Hf.. ]
   | (subA _ _ (_ //\\ _)) _ _ =>
       apply subA_conj in H; eapply conj_mono in H;
        [ idtac | intros Hf; subA_normalize_in Hf; exact Hf.. ]
   | (subA _ _ (_ \\// _)) _ _ =>
       apply subA_disj in H; eapply disj_mono in H;
        [ idtac | intros Hf; subA_normalize_in Hf; exact Hf.. ]
   | (subA _ _ (_ -->p (_, _))) _ _ =>
       apply subA_pointto in H
   | (subA _ _ !( _)) _ _ =>
       eapply subA_pure in H; eapply pure_mono in H;
        [  | intros Hf; subA_normalize_in Hf; exact Hf ]
   | (subA _ _ (pure _)) _ _ =>
       apply subA_pure' in H
   | (subA _ _ (_ === _)) _ _ => apply subA_eeq in H
   | subA _ _ (_ ===l _) _ _ => apply subA_leeq in H
   | (subA _ _ emp) _ _ => apply subA_emp in H
   | (subA _ _ ?b) _ _ =>
       apply subA_bexp_to_assn in H
   | (subA _ _ (nth _ (distribute _ _ _ _ _ _) _)) _ _ =>
       apply distribute_subA in H; auto
   | (subA _ _ (is_array _ _ _ _)) _ _ =>
       apply subA_is_array in H; auto
   | (subA _ _ (if _ then _ else _)) _ _ =>
       apply subA_if_dec in H; eapply if_mono in H;
        [ idtac | intros ? ? Hf; subA_normalize_in Hf; exact Hf.. ]
   | (subA _ _ TrueP) _ _ => apply subA_TrueP in H
   | _ => simpl in H
 end.

Require Import Psatz.
Require Import LibTactics.

Lemma succ_div2_mul2 (n : nat) :
  n <= (n + 1) / 2 * 2.
Proof.
  rewrite (Nat.div_mod n 2); auto.
  assert (n mod 2 = 0 \/ n mod 2 = 1) by (lets: (Nat.mod_upper_bound n 2); omega).
  destruct H as [H|H]; rewrite H.
  - cutrewrite (2 * (n / 2) + 0 + 1 = 1 + (n / 2) * 2); [|ring].
    rewrite Nat.div_add; auto.
    lia.
  - cutrewrite (2 * (n / 2) + 1 + 1 = 2 + (n / 2) * 2); [|ring].
    rewrite Nat.div_add, Nat.div_same; auto.
    lia.
Qed.

Lemma i_sdiv2_lt (i l : nat) :
  i + (l + 1) / 2 < l -> i < (l + 1) / 2.
Proof.
  lets: (succ_div2_mul2 l).
  intros; omega.
Qed.

Ltac subst_term E :=
  repeat match goal with
         | [H : (E === _) _ _ |- _] => unfold_conn_in H; simpl in H;
                                       rewrite_all H in *; clear H
         | [H : E = _ |- _] => rewrite_all H in *; clear H
         | [H : (_ === E) _ _ |- _] => unfold_conn_in H; simpl in H;
                                       rewrite_all H in *; clear H
         | [H : E = _ |- _] => rewrite_all H in *; clear H
         end.

Hint Rewrite div_Zdiv Nat2Z.inj_add : sep.

Lemma reduce_cerrct_t (i : Fin.t ntrd) :
  CSL (fun b => if Nat.eq_dec b 0 then binv0 else default ntrd) i
  (!(TID === Zn (nf i)) **
   !(ARR === arr) **
   ((if lt_dec (nf i) ((len + 1) / 2)
     then Sh arr +o Zn (nf i) -->p (1, snd (sum 0) (nf i))
     else emp) **
    (if lt_dec (nf i + (len + 1) / 2) len
     then
      Sh arr +o Zn (nf i + (len + 1) / 2) -->p (1,
      snd (sum 0) (nf i + (len + 1) / 2))
     else emp)))
  (reduce_ker i)
  (Ex f,
   (if Nat.eq_dec (nf i) 0 then
      is_array (Sh arr) len f 0 **
      !(pure (f 0 = sum_of 0 len f_ini))
   else emp)).
Proof.
  unfold reduce_ker.
  eapply rule_seq.
  { hoare_forward.
    intros ? ? [v H]. subA_normalize_in H. simpl in H. exact H. }
  eapply rule_seq.
  { hoare_forward.
    intros ? ? [v H]; subA_normalize_in H. simpl in H; exact H. }
  hoare_forward; unfold INV.
  - eapply Hbackward; [|
      intros ? ? H; apply ex_lift_l_in in H as [v H]; apply ex_lift_l_in in H as [v' H];
      apply ex_lift_l_in in H as [v'' H]; sep_normal_in H; ex_intro v'' H; ex_intro v' H;
      ex_intro v H; simpl in H; exact H].
    apply rule_ex; intros c; apply rule_ex; intros l; apply rule_ex; intro f.
    eapply rule_seq; [hoare_forward|].
    { intros ? ? [v H]; subA_normalize_in H. simpl in H; sep_normal_in H; exact H. }
    eapply rule_seq; [eapply rule_if_disj|].
    2: apply rule_skip.
    { eapply Hbackward.
      Focus 2. {
        intros ? ? H.
        sep_split_in H.
        change_in H.
        { unfold_pures.
          subst_term (s TID).
          subst_term (s D).
          subst_term (s L).
          autorewrite with sep in *; auto.
          lets: (i_sdiv2_lt (nf i) l); auto.
          zify.
          destruct lt_dec. 
          2: zify; autorewrite with sep in *; auto; simpl in *; omega.
          destruct lt_dec.
          eauto.
          zify; autorewrite with sep in *; auto; simpl in *; omega. }
        assert ((Sh arr +o (Zn (nf i) + (Zn l + 1) / 2)%Z ===l
                 Sh arr +o (Zn (nf i) + Z.div2 (Zn l + 1)%Z)) s (emp_ph loc))%Z.
        { unfold_conn; simpl; f_equal; repeat autorewrite with sep; auto. }
        sep_normal_in H.
        sep_lift_in H 1.
        sep_rewrite_in mps_eq1 H; [|exact H0]. 
        sep_combine_in H; exact H. } Unfocus.
      eapply rule_seq; [hoare_forward|].
      intros ? ? H; exact H.
      eapply rule_seq; [hoare_forward|].
      intros ? ? H; exact H.
      hoare_forward.
      intros; eauto. }
    eapply Hforward.

    apply rule_disj.
  
    + eapply rule_seq; [hoare_forward|].
      intros ? ? [v H]. subA_normalize_in H. simpl in H.
      sep_split_in H.
      subst_term (Enum v). sep_combine_in H. exact H.
      
      eapply rule_seq; [hoare_forward|].
      intros ? ? [v H]. subA_normalize_in H. simpl in H.
      sep_split_in H.
      subst_term (Enum v). sep_combine_in H. exact H.
      
      forward_barr; [intros ? ? H; exact H|].
      simpl; rewrite MyVector.init_spec; intros s h H.
      apply ex_lift_l; exists c.
      apply ex_lift_l; exists l.
      apply ex_lift_l; exists f.
      sep_split_in H.
      sep_normal; sep_split; eauto.
      * unfold_pures; unfold_conn; simpl.
        autorewrite with sep in *; simpl; auto.
        congruence.
      * unfold_pures; unfold_conn; simpl; autorewrite with sep; auto.
      * unfold_pures.
        lets: (i_sdiv2_lt (nf i) l).
        assert (nf i < (l + 1) / 2).
        { zify; autorewrite with sep in *; auto; simpl in *; omega. }
        assert (nf i + (l + 1) / 2 < l).
        { zify; autorewrite with sep in *; auto; simpl in *; omega. }
        repeat destruct lt_dec; try omega.
        assert ((T1 +C T2 === snd (sum (c + 1)) (nf i)) s (emp_ph loc)).
        { unfold_conn; simpl; subst_term (s T1); subst_term (s T2).
          cutrewrite ((c + 1) = S c); [|omega].
          rewrite red_sum_next_f1, red_sum_next_d.
          destruct lt_dec; subst l; lia. }
        sep_rewrite_in mps_eq2 H; [|apply H3].
        asserts_rewrite (snd (sum (c + 1)) (nf i + (l + 1) / 2) =
                         snd (sum c) (nf i + (l + 1) / 2)).
        { cutrewrite (c+1 = S c); [|omega].
          rewrite red_sum_next_f1, red_sum_next_d.
          destruct lt_dec; eauto.
          pose proof (@succ_div2_mul2 l). subst. omega. }
        assert (Hl : (Sh ARR +o (TID +C D) ===l Sh arr +o (Zn (nf i) + (Zn l + 1) / 2))%Z s (emp_ph loc)).
        { unfold_conn; simpl; f_equal; autorewrite with sep in *; congruence. }
        sep_lift_in H 1.
        sep_rewrite_in mps_eq1 H; [|exact Hl].
        repeat sep_cancel.
        unfold_pures.
        assert ((TID === Zn (nf i)) s (emp_ph loc)); [unfold_conn; simpl; eauto|].
        sep_combine_in H4.
        autorewrite with sep; auto.
        exact H4.

    + (* else case *) 
      eapply rule_seq; [hoare_forward|].
      intros ? ? [v H]. subA_normalize_in H. simpl in H.
      sep_split_in H.
      subst_term (Enum v). sep_combine_in H. exact H.

      eapply rule_seq; [hoare_forward|].
      intros ? ? [v H]. subA_normalize_in H. simpl in H.
      sep_split_in H.
      subst_term (Enum v). sep_combine_in H. exact H.

      forward_barr; [intros ? ? H; exact H|].
      simpl; rewrite MyVector.init_spec; intros s h H.
      apply ex_lift_l; exists c.
      apply ex_lift_l; exists l.
      apply ex_lift_l; exists f.
      sep_split_in H.
      sep_normal; sep_split; eauto.
      * unfold_pures; unfold_conn; simpl.
        autorewrite with sep in *; simpl; auto.
        congruence.
      * unfold_pures; unfold_conn; simpl; autorewrite with sep; auto.
      * unfold_pures.
        cutrewrite (c+1=S c); [|ring].
        repeat rewrite red_sum_next_f1, red_sum_next_d.
        assert(l <= nf i + (l + 1) / 2 ).
        { zify; autorewrite with sep in *; auto; simpl; omega. }
        destruct (lt_dec (nf i - 0 + (fst (sum c) + 1) / 2) (fst (sum c)));
          [subst l; omega|].
        destruct (lt_dec (nf i + (l + 1) / 2 - 0 + (fst (sum c) + 1) / 2)
         (fst (sum c))); [subst l; omega|].
        repeat sep_cancel.
        assert ((TID === Zn (nf i)) s (emp_ph loc)).
        { unfold_conn; eauto. }
        sep_combine_in H2; eauto.
    + intros s h [H|H];
      apply ex_lift_l_in in H; destruct H as [? H];
      apply ex_lift_l_in in H; destruct H as [? H];
      apply ex_lift_l_in in H; destruct H as [? H];
      do 3 eexists; sep_normal_in H; sep_split_in H; sep_split; eauto.
  - intros s h H.
    apply ex_lift_l_in in H as [c H].
    apply ex_lift_l_in in H as [l H].
    apply ex_lift_l_in in H as [f H].
    sep_normal_in H; sep_split_in H; unfold_pures.
    assert (l = 1) by omega; subst.
    rewrite H0 in *.
    rewrite Nat.div_same in H; auto.
    repeat destruct lt_dec; destruct Nat.eq_dec; try omega.
    assert ((Sh (s ARR) +o Zn (nf i) ===l Sh (s ARR)) s (emp_ph loc)).
    { unfold_conn; simpl; f_equal; omega. }
    sep_rewrite_in mps_eq1 H; [|exact H1].
    sep_normal_in H.
    exists (fun x => if Nat.eq_dec x 0 then snd (sum c) (nf i) else f x).
    sep_split.
    simpl.
    apply red_sum_ok in H0; rewrite <-H0.
    sep_normal_in H.
    rewrite e; reflexivity.
    destruct len; try omega; simpl in *; sep_cancel.
    rewrite <-minus_n_O in H.
    sep_rewrite is_array_change; eauto.
    intros; destruct Nat.eq_dec; omega.
    exists (fun _ : nat => 0%Z); sep_normal; sep_normal_in H; eauto.
  - exists 0 len f_ini.
    sep_normal_in H; sep_split_in H; sep_split; eauto.
    + cbv; auto.
    + unfold_conn; simpl; omega.
    + rewrite minus_diag.
      simpl.
      destruct Nat.eq_dec; sep_normal; sep_normal_in H; eauto.
Qed.

Require Import Bdiv.

Ltac default T :=
  lazymatch T with
    | nat => constr:(0)
    | Z => constr:(0%Z)
    | ?T1 -> ?T2 => let t := default T2 in constr:(fun _ : T1 => t)
  end.

Ltac ex_elim H :=
  lazymatch type of H with
    | conj_xs (ls_init _ _ (fun _ : nat => Ex _ : ?T, _)) _ _ =>
      let t := default T in
      sep_rewrite_in (@ls_exists0 _ t) H
  end.

Ltac istar_simplify_in H :=
  apply sc_v2l in H; rewrite (vec_to_list_init0 _ emp) in H; erewrite ls_init_eq0 in H;
  [|let i := fresh "i" in
    let Hi := fresh in
    let Hex := fresh in
    let Heq := fresh in
    intros i Hi;
    lazymatch goal with
      [|- match ?X with inleft _ => _ | inright _ => _ end = _] =>
      destruct X as [|Hex] eqn:Heq; [|destruct Hex; omega]
    end;
    rewrite (Fin_nat_inv Heq); reflexivity];
  match goal with _ => idtac end;
  (repeat (let vs := fresh "vs" in
          ex_elim H; destruct H as [vs H]; sep_split_in H));
  (repeat sep_rewrite_in (@ls_star) H);
  (repeat sep_rewrite_in (@ls_pure) H; sep_split_in H).


Ltac istar_simplify :=
  apply sc_v2l; rewrite (vec_to_list_init0 _ emp); erewrite ls_init_eq0;
  [|let i := fresh "i" in
    let Hi := fresh in
    let Hex := fresh in
    let Heq := fresh in
    intros i Hi;
    lazymatch goal with
      [|- match ?X with inleft _ => _ | inright _ => _ end = _] =>
      destruct X as [|Hex] eqn:Heq; [|destruct Hex; omega]
    end;
    rewrite (Fin_nat_inv Heq); reflexivity];
  match goal with _ => idtac end.

Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis len_nt : len <= 2 * ntrd.

Lemma binv_preserved : Aistar_v (fst binv0) |= Aistar_v (snd binv0).
Proof.
  unfold binv0; simpl; intros s h H.
  istar_simplify.
  istar_simplify_in H.
  
  Ltac rewrite_body lem tac :=
    erewrite ls_init_eq0; [|intros ? ?; rewrite lem; try tac; reflexivity ].
  Ltac rewrite_body_in lem tac H :=
    erewrite ls_init_eq0 in H; [|intros ? ?; rewrite lem; try tac; reflexivity ].
  
  Lemma conj_xs_var (va : var) n (vs : nat -> nat) stk : forall st,
    conj_xs (ls_init st n (fun i => va === Zn (vs i))) stk (emp_ph loc) ->
    forall i, i < n -> vs (st + i) = Z.to_nat (stk va).
  Proof.
    induction n; simpl; intros st Hsat i Hi; try omega.
    destruct Hsat as (? & ? & Hsat1 & Hsat2 & ? & ?); unfold_conn_in Hsat1; simpl in Hsat1.
    destruct i.
    - rewrite <-plus_n_O; eauto.
      rewrite Hsat1, Nat2Z.id; eauto.
    - apply phplus_emp in H0; destruct H0; subst.
      rewrite <-Nat.add_succ_comm; apply IHn; eauto; omega.
  Qed.

  lets HL: (>>conj_xs_var HP3); simpl in HL.
  lets HC: (>>conj_xs_var HP4); simpl in HC.

  assert (HC' : forall i, i < ntrd -> nth i vs 0 = Z.to_nat (s C) - 1).
  { intros; rewrite <-(HC i); omega. }

  rewrite_body_in HC' omega HP5.
  assert (HL' : forall i, i < ntrd -> nth i vs0 0 = fst (sum (Z.to_nat (s C) - 1))).
  { intros i Hi.
    lets Hi': (>>ls_emp i); apply Hi' in HP5; rewrite ls_init_spec in HP5.
    destruct lt_dec; unfold_conn_in HP5; simpl in HP5; try omega. }
  
  repeat rewrite_body_in HL' omega H.
  repeat rewrite_body_in HC' omega H.
  sep_lift_in H 1.
  repeat rewrite_body_in HL' omega H.
  repeat rewrite_body_in HC' omega H.
  sep_lift_in H 2.
  repeat rewrite_body_in HL' omega H.
  repeat rewrite_body_in HC' omega H.
  set (L' := (fst (sum (Z.to_nat (s C) - 1)))) in *.

  Lemma conj_xs_if_lt_is_arr stk e (f : nat -> Z) n m s:
    m - s <= n ->
    stk ||= conj_xs
      (ls_init s n
         (fun i => if lt_dec i m then e +o Zn i -->p (1, f i) else emp)) <=>
      is_array e (m - s) f s.
  Proof.
    intros Hmn.
    rewrite <-(firstn_skipn (m-s) (ls_init _ _ _)), conj_xs_app, firstn_init, skipn_init.
    rewrite Nat.min_l; eauto.
    let H := fresh in let H' := fresh in
    lazymatch goal with
      | [|- _ ||= (?P ** ?Q) <=> _] =>
        assert (H : stk ||= P <=> is_array e (m - s) f s); [|
          assert (H' : stk ||= Q <=> emp); [|
            rewrite H, H', emp_unit_r; reflexivity
          ]] end.
    - erewrite ls_init_eq'; [|intros; destruct lt_dec; try omega; generalize (s + i); reflexivity].
      Lemma is_array_distr e n (f' : nat -> Z) :
        forall s stk,
          stk ||= conj_xs (ls_init s n (fun i => e +o Zn i -->p (1, f' i))) <=>
              is_array e n f' s.
      Proof.
        induction n; intros s stk; simpl.
        - reflexivity.
        - rewrite IHn; reflexivity.
      Qed.
      apply is_array_distr.
    - erewrite ls_init_eq'; [|intros; destruct lt_dec; try omega].
      2: cutrewrite (emp = id (fun i => emp) (m - s + s + i)); reflexivity.
      unfold id; apply init_emp_emp.
  Qed.
  Lemma red_sum_fst_le s l f c :
    fst (red_sum s l f c) <= l.
  Proof.
    induction c; [simpl; eauto|].
    rewrite red_sum_next_d.
    Require Import NPeano.
    Lemma succ_div2_le n : (n + 1) / 2 <= n.
    Proof.
      destruct n; [cbv; omega|].
      apply Nat.div_le_upper_bound; omega.
    Qed.
    pose proof (succ_div2_le (fst (red_sum s l f c))).
    omega.
  Qed.

  assert ((L' + 1) / 2 <= ntrd).
  { assert (L' <= len).
    apply red_sum_fst_le.
    assert ((len + 1) / 2 <= ntrd).
    2: pose proof (Nat.div_le_mono (L' + 1) (len + 1) 2); omega.
    rewrite (Nat.div_mod len 2); auto.
    assert (Hm2 : len mod 2 = 0 \/ len mod 2 = 1) by (lets: (Nat.mod_upper_bound len 2); omega).
    destruct Hm2 as [Hm2|Hm2]; rewrite Hm2.
    cutrewrite (2 * (len / 2) + 0 + 1 = 1 + (len / 2) * 2); [|ring].
    rewrite Nat.div_add; eauto; simpl.
    apply Nat.div_le_upper_bound; eauto.
    cutrewrite (2 * (len / 2) + 1 + 1 = 2 + (len / 2) * 2); [|ring].
    rewrite Nat.div_add; eauto; simpl.
    rewrite (Nat.div_mod len 2), Hm2 in len_nt; eauto.
    assert (2 * (len / 2) <= 2 * ntrd - 2) by omega.
    cut (len / 2 <= ntrd - 1); intros; omega. }
  Lemma conj_xs_if_eq stk (f : nat -> assn) n m:
    m < n ->
    stk ||= conj_xs
      (ls_init 0 n
         (fun i => if Nat.eq_dec i m then f i else emp)) <=> f m.
  Proof.
    intros.
    rewrite <-(firstn_skipn m (ls_init _ _ _)), firstn_init, skipn_init.
    rewrite Nat.min_l; [|omega]; rewrite <-plus_n_O.
    rewrite <-(firstn_skipn 1 (ls_init m _ _)), firstn_init, skipn_init.
    rewrite Nat.min_l; [|omega].
    repeat rewrite conj_xs_app.
    let H := fresh in let H' := fresh in let H'' := fresh in
    lazymatch goal with
      | [|- _ ||= (?P ** ?Q ** ?R) <=> _] =>
        assert (H : stk ||= P <=> emp); [|
          assert (H' : stk ||= Q <=> f m); [|
            assert (H'' : stk ||= R <=> emp); [|
            rewrite H, H', H'', emp_unit_l, emp_unit_r; reflexivity
          ]]] end.
    erewrite (ls_init_eq _ _ _ 0) ; [|intros; destruct Nat.eq_dec; try omega].
    2: cutrewrite (emp = id (fun i => emp) i); reflexivity.
    unfold id; apply init_emp_emp.
    erewrite (ls_init_eq _ _ _ 0); [|intros; destruct Nat.eq_dec; try omega; reflexivity].
    simpl; rewrite emp_unit_r; reflexivity.
    erewrite (ls_init_eq _ _ _ 0) ; [|intros; destruct Nat.eq_dec; try omega].
    2: cutrewrite (emp = id (fun i => emp) (1+m+i)); reflexivity.
    unfold id; apply init_emp_emp.
  Qed.    
  sep_rewrite_in conj_xs_if_eq H; [|omega].
  
  sep_rewrite_in conj_xs_if_lt_is_arr H; try omega.
  rewrite <-minus_n_O in H.
  
  erewrite (ls_init_eq _ _ _ ((L' + 1) / 2)) in H.
  2: simpl; intros i Hi;
  cutrewrite ((L' + 1) / 2 + 0 + i = i + (L' + 1) / 2);
  [generalize (i + (L' + 1) / 2); reflexivity|omega].
  rewrite <-plus_n_O in H.
  
  assert (L' - (L' + 1) / 2 <= ntrd).
  { unfold L'. 
    rewrite (Nat.mul_le_mono_pos_r _ _ 2); eauto.
    rewrite Nat.mul_sub_distr_r.
    lets: (succ_div2_mul2 L'); unfold L' in *.
    lets: (red_sum_fst_le 0 len f_ini (Z.to_nat (s C) - 1)).
    eapply le_trans.
    apply Nat.sub_le_mono_l; eauto.
    omega. }
  sep_rewrite_in conj_xs_if_lt_is_arr H; eauto.

  Lemma is_array_change (e : loc_exp) (f1 f2 : nat -> Z) n :
    forall s, (forall x, x < n -> f1 (x + s) = f2(x + s)) ->
              forall stc,
                stc ||= is_array e n f1 s <=> is_array e n f2 s.
  Proof.
    induction n; simpl; intros s Hf; try reflexivity.
    intros stc; rewrite IHn.
    cutrewrite (f1 s = f2 s); [reflexivity|].
    pose proof (Hf 0); rewrite plus_O_n in H; rewrite H; omega.
    intros x Hx; rewrite <-Nat.add_succ_comm; apply Hf; omega.
  Qed.

  Lemma is_array_concat e f f1 f2 len1 len2 : forall s stc,
      (forall off, off < len1 + len2 ->
         f (s + off) = if lt_dec off len1 then f1 (s + off) else f2 (s + off)) ->
      stc||=
         is_array e (len1 + len2) f s <=>
         is_array e len1 f1 s ** is_array e len2 f2 (s + len1).
  Proof.
    induction len1; simpl; intros s stc H.
    - rewrite emp_unit_l, <-plus_n_O.
      rewrite is_array_change; [reflexivity|].
      intros; rewrite plus_comm; eauto.
    - intros. rewrite <-Nat.add_succ_comm, <-sep_assoc, IHlen1.
      cutrewrite (f s = f1 s); [reflexivity|].
      cutrewrite (s = s + 0); [apply H; omega|omega].
      intros off ?; cutrewrite (S s + off = s + S off); [rewrite H; repeat destruct lt_dec|]; omega.
  Qed.
  cutrewrite (Z.to_nat (s C) - 1 + 1 = Z.to_nat (s C)) in H; [|rewrite <-(HC 0); omega].
  set (f' := fun i =>
               if lt_dec i L' then snd (sum (Z.to_nat (s C))) i
               else (nth 0 vs1 (fun _ : nat => 0%Z)) i).
  assert ((is_array (Sh arr) len f' 0) s h).
  { assert (L' <= len) by apply red_sum_fst_le.
    cutrewrite (len = L' + (len - L')); [|omega].
    sep_rewrite is_array_concat; simpl.
    assert ((L' + 1) / 2 <= L') by apply succ_div2_le.
    assert (Heq : L' = (L' + 1) / 2 + (L' - (L' + 1) / 2)) by omega.
    rewrite Heq at 1; clear Heq.
    sep_rewrite is_array_concat; simpl.
    sep_normal.
    sep_lift 1; sep_lift 2.
    apply H.
    intros; reflexivity.
    unfold f'; intros; repeat destruct lt_dec; eauto. }
  
  Lemma TrueP_always s h : TrueP s h. cbv; auto. Qed.
  Hint Resolve TrueP_always.
  
  sep_rewrite (@ls_exists0 _ 0); exists (map (fun x => x+1) vs); sep_split.
  { rewrite map_length; eauto. }
  sep_rewrite (@ls_exists0 _ 0); exists (map (fun x => (x+1) / 2) vs0); sep_split.
  { rewrite map_length; eauto. }
  sep_rewrite (@ls_exists0 _ (fun _ : nat => 0%Z)); exists (nseq ntrd f'); sep_split; eauto.
  { rewrite length_nseq; reflexivity. }
  repeat sep_rewrite (@ls_star ntrd); repeat sep_rewrite (@ls_pure ntrd).
  Ltac unfold_pures :=
    repeat
      match goal with
      | H:_ ?s (emp_ph loc) |- _ => bexp H
      | H:_ ?s (emp_ph loc) |- _ => unfold_conn_in H; simpl in H
   end.
  unfold_conn_in (HP, HP0).
  sep_split; eauto.
  - apply ls_emp'; rewrite init_length; intros.
    rewrite_body (nth_map 0 0) ltac:(first [omega | eauto]).
    rewrite ls_init_spec; destruct lt_dec; try omega.
    apply (ls_emp _ _ i) in HP3; rewrite ls_init_spec in HP3; destruct lt_dec; eauto; omega.
  - apply ls_emp'; rewrite init_length; intros.
    rewrite_body (nth_map 0 0) ltac:(first [omega | eauto]).
    rewrite ls_init_spec; destruct lt_dec; try omega.
    apply (ls_emp _ _ i) in HP4; rewrite ls_init_spec in HP4; destruct lt_dec; eauto; omega.
  - repeat rewrite_body (nth_map 0 0) ltac:(first [omega | eauto]).
    repeat rewrite_body Nat.add_1_r omega.
    rewrite_body red_sum_next_d idtac.
    apply ls_emp'; intros ? _; rewrite ls_init_spec; destruct lt_dec; eauto.
    rewrite HL', HC', Nat.add_1_r; try omega; reflexivity.
  - apply ls_emp'; rewrite init_length; intros i _; rewrite ls_init_spec; destruct lt_dec; auto.
    unfold_conn.
    lets H': (>>ls_emp i); apply H' in HP6; rewrite ls_init_spec in HP6; destruct lt_dec; try omega; clear H'.
    unfold_conn_in HP6.
    rewrite (nth_map 0 0); try omega.
    destruct (nth (0 + i) vs0 0); try omega.
    cutrewrite (S n + 1 = n + 1 * 2); [|ring].
    rewrite Nat.div_add; omega.
  - repeat rewrite_body (nth_map 0 0) ltac:(first [omega | eauto]).
    rewrite_body HL' omega.
    rewrite_body HC omega.
    sep_rewrite conj_xs_if_lt_is_arr.
    rewrite <-minus_n_O.
    2: pose proof (succ_div2_le ((L' + 1) / 2)); omega.
    repeat rewrite_body (nth_map 0 0) ltac:(first [omega | eauto]).
    rewrite_body HL' omega.
    rewrite_body HC omega.
    erewrite (@ls_init_eq assn _ _ ntrd 0 (((L' + 1) / 2 + 1) / 2)).
    2: intros; simpl; repeat rewrite <-plus_n_O.
    2: cutrewrite (i + ((L' + 1) / 2 + 1) / 2 = ((L' + 1) / 2 + 1) / 2 + i); [|ring].
    2: generalize (((L' + 1) / 2 + 1) / 2 + i); reflexivity.
    repeat rewrite <-plus_n_O.
    sep_rewrite conj_xs_if_lt_is_arr.
    2: omega.
    repeat rewrite_body (nth_map 0 0) ltac:(first [omega | eauto]).
    rewrite_body HL' omega.
    rewrite_body nth_nseq omega.
    sep_rewrite conj_xs_if_eq; try omega.
    destruct (Compare_dec.leb _ _) eqn:Heq; try (rewrite leb_iff in Heq; omega).
    sep_rewrite sep_assoc.
    Ltac sep_rewrite_r lem :=
      match goal with
      | |- ?X _ _ => pattern X
      end; erewrite <-lem; cbv beta.
    sep_rewrite_r (is_array_concat (Sh arr) f').
    cutrewrite (((L' + 1) / 2 + 1) / 2 + ((L' + 1) / 2 - ((L' + 1) / 2 + 1) / 2) =
                (L' + 1) / 2).
    2: lets: (succ_div2_le ((L' + 1) / 2)).
    2: omega.
    sep_rewrite_r (is_array_concat (Sh arr) f').
    assert (Heq' : (L' + 1) / 2 + (len - (L' + 1) / 2) = len).
    { assert ((L' + 1) / 2 <= len).
      unfold L'; rewrite <-red_sum_next_d.
      apply red_sum_fst_le.
      omega. }
    rewrite Heq'; eauto; try omega.
    intros; destruct lt_dec; eauto; omega.
    intros; unfold f'.
    lazymatch type of H3 with
      | (_ < ?x) => asserts_rewrite (x = (L' + 1) / 2) in H3
    end.
    lets: succ_div2_le ((L' + 1) / 2); omega.
    lets: succ_div2_le L'.
    repeat destruct lt_dec; eauto; omega.
Qed.

Lemma precise_sat (P Q : assn) :
  (Q |= P) -> precise P -> precise Q.
Proof.
  unfold precise; simpl; intros Hsat HprecP; introv.
  intros HsatQ HsatQ' ? ? ?.
  eapply HprecP; eauto.
Qed.

Lemma precise_ex_var (P : val -> assn) E :
  (forall v, precise (P v)) ->
  precise (Ex v, !(E === Enum v) ** P v).
Proof.
  unfold precise; simpl; intros Hprec; introv Hsat1 Hsat2 ? ?.
  eapply Hprec; eauto;
  destruct Hsat1 as [v1 Hsat1], Hsat2 as [v2 Hsat2];
  sep_split_in Hsat1; sep_split_in Hsat2.
  cutrewrite (v1 = edenot E s) in Hsat1; [|unfold_pures; auto]; eauto.
  cutrewrite (v2 = edenot E s) in Hsat2; [|unfold_pures; auto]; eauto.
Qed.

Lemma precise_pts e1 e2 q :
  precise (e1 -->p (q, e2)).
Proof.
  unfold precise; intros; simpl in *.
  unfold_conn_all; simpl.
  destruct h1 as [h1 ?], h1' as [h1' ?]; apply pheap_eq.
  extensionality l; simpl in *; rewrite H, H0.
  auto.
Qed.

Import Vector.VectorNotations.
Hint Resolve precise_pts precise_emp.

Lemma binv_precise_fst tid : precise ((fst binv0)[@tid]).
Proof.
  unfold binv0; simpl; rewrite MyVector.init_spec.
  eapply precise_sat.
  { intros s h (c & l & f & H).
    sep_split_in H.
    unfold_pures; rewrite HP2 in H.
    assert ((C === Zn (c + 1)) s (emp_ph loc)) by (unfold_pures; eauto).
    cutrewrite (c = Z.to_nat (Zn (c + 1)) - 1) in H; [|rewrite Nat2Z.id; omega].
    revert H0 H; generalize (Zn (c + 1)); intros.
    ex_intro f H; sep_combine_in H.
    apply scC in H.
    ex_intro z H.
    exact H. }
  simpl.
  apply precise_ex_var.
  intros v.
  apply precise_ex_star, precise_star.
  destruct lt_dec; [eapply precise_sat; [intros ? ? [? H]; exact H|]..]; eauto.
  apply precise_ex_star, precise_star.
  destruct lt_dec; [eapply precise_sat; [intros ? ? [? H]; exact H|]..]; eauto.
  destruct Nat.eq_dec; eauto.
  2: eapply precise_sat; [intros ? ? [? H]|]; eauto.
  apply precise_is_array.
Qed.

Lemma binv_precise_snd tid : precise ((snd binv0)[@tid]).
Proof.
    unfold binv0; simpl; rewrite MyVector.init_spec.
  eapply precise_sat.
  { intros s h (c & l & f & H).
    sep_split_in H.
    unfold_pures; rewrite HP2 in H.
    assert ((C === Zn c) s (emp_ph loc)) by (unfold_pures; eauto).
    cutrewrite (c = Z.to_nat (Zn c)) in H; [|rewrite Nat2Z.id; omega].
    revert H0 H; generalize (Zn c); intros.
    ex_intro f H; sep_combine_in H.
    apply scC in H.
    ex_intro z H.
    exact H. }
  simpl.
  apply precise_ex_var.
  intros v.
  apply precise_ex_star, precise_star.
  destruct lt_dec; [eapply precise_sat; [intros ? ? [? H]; exact H|]..]; eauto.
  apply precise_ex_star, precise_star.
  destruct lt_dec; [eapply precise_sat; [intros ? ? [? H]; exact H|]..]; eauto.
  destruct Nat.eq_dec; eauto.
  2: eapply precise_sat; [intros ? ? [? H]|]; eauto.
  apply precise_is_array.
Qed.
End reduce.

