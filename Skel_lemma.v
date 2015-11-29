Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics.

Fixpoint fv_E (e : exp) :=
  match e with
    | Evar v => v :: nil
    | Enum n => nil
    | e1 +C e2 
    | e1 *C e2
    | e1 -C e2 => fv_E e1 ++ fv_E e2
    | e1>>1 => fv_E e1
  end%exp.

Fixpoint fv_lE (e : loc_exp) :=
  match e with
  | Sh e
  | Gl e => fv_E e
  | e1 +o e2 => fv_lE e1 ++ fv_E e2
  end%exp.

Fixpoint fv_B (e : bexp) :=
  match e with
   | e1 == e2
   | e1 <C e2 => fv_E e1 ++ fv_E e2
   | Band e1 e2 => fv_B e1 ++ fv_B e2
   | Bnot e1 => fv_B e1
  end.

Lemma fv_subE var v e :
  ~List.In var (fv_E e) -> subE var v e = e.
Proof.
  simpl in *; intros; induction e; simpl in *; jauto;
  try rewrite IHe1; try rewrite IHe2; try rewrite IHe; try rewrite in_app_iff in *; eauto.
  destruct var_eq_dec; jauto.
  contradict H; eauto.
Qed.

Fixpoint disjoint {T : Type} (l1 l2 : list T) :=
  match l1 with
  | nil => True
  | x :: l1 => ~(List.In x l2) /\ disjoint l1 l2
  end. 

Lemma disjoint_nil_r (T : Type) (l : list T) : disjoint l nil.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma disjoint_cons_r (T : Type) (x : T) (l1 l2 : list T) :
  disjoint l1 l2 -> ~(List.In x l1) -> disjoint l1 (x :: l2).
Proof.
  induction l1; simpl; eauto.
  intros; intuition.
Qed.

Hint Resolve disjoint_nil_r disjoint_cons_r.

Lemma disjoint_comm (T : Type) (l1 l2 : list T) : disjoint l1 l2 -> disjoint l2 l1.
Proof.
  revert l2; induction l1; simpl; eauto.
  intros.
  apply disjoint_cons_r; jauto.
Qed.  

Lemma indeE_fv (e : exp) (v : var) :
  ~List.In v (fv_E e) -> indeE e v.
Proof.
  unfold indeE; induction e; simpl; intros; intuition; try now (try erewrite H0; try erewrite H1; try reflexivity).
  unfold var_upd; destruct var_eq_dec; congruence.
Qed.

Lemma indelE_fv (e : loc_exp) (v : var) :
  ~List.In v (fv_lE e) -> indelE e v.
Proof.
  unfold indelE; induction e; simpl; intros; intuition; try (f_equal).
  lets Heq: (indeE_fv e v); unfold indeE in Heq; eauto.
  lets Heq: (indeE_fv e v); unfold indeE in Heq; eauto.
  assert (H' : ~In v (fv_E e0)).
  { intros Hc; apply H, in_app_iff; eauto. }
  rewrite <-H0; destruct ledenot; do 2 f_equal;
  lets Hinde : (>>indeE_fv H'); unfold indeE in Hinde; erewrite Hinde; eauto.
Qed.

Lemma indeB_fv (e : bexp) (v : var) :
  ~List.In v (fv_B e) -> indeB e v.
Proof.
  unfold indeB; induction e; simpl; intros; intuition; try (rewrite in_app_iff in H;
  lets Heq1: (indeE_fv e1 v); unfold indeE in Heq1; rewrite <-Heq1; eauto;
  lets Heq2: (indeE_fv e2 v); unfold indeE in Heq2; rewrite <-Heq2; eauto).
  rewrite <-H0, <-H1; auto.
  rewrite <-H0; auto.
Qed.
  
Hint Resolve indeE_fv indelE_fv indeB_fv.

Lemma disjoint_indeE (e : exp) (vs : list var) :
  disjoint (fv_E e) vs -> List.Forall (indeE e) vs.
Proof.
  induction vs; simpl; intros.
  - constructor.
  - apply disjoint_comm in H; simpl in H; constructor; intuition.
    apply IHvs, disjoint_comm; auto.
Qed.

Lemma disjoint_indelE (e : loc_exp) (vs : list var) :
  disjoint (fv_lE e) vs -> List.Forall (indelE e) vs.
Proof.
  induction vs; simpl; intros.
  - constructor.
  - apply disjoint_comm in H; simpl in H; constructor; intuition.
    apply IHvs, disjoint_comm; auto.
Qed.

Lemma disjoint_indeB (e : bexp) (vs : list var) :
  disjoint (fv_B e) vs -> List.Forall (indeB e) vs.
Proof.
  induction vs; simpl; intros.
  - constructor.
  - apply disjoint_comm in H; simpl in H; constructor; intuition.
    apply IHvs, disjoint_comm; auto.
Qed.

Hint Constructors typing_exp typing_lexp typing_bexp typing_cmd.

Lemma typing_exp_Hi E (e : exp) : typing_exp E e Hi.
Proof.
  induction e; eauto; equates 1; eauto.
  apply ty_var; destruct (E x); eauto.
Qed.

Hint Resolve typing_exp_Hi.

Lemma typing_bexp_Hi E (e : bexp) : typing_bexp E e Hi.
Proof.
  induction e; eauto; equates 1; eauto.
Qed.  

Lemma typing_lexp_Hi E (e : loc_exp) : typing_lexp E e Hi.
Proof.
  induction e; eauto; equates 1; eauto.
Qed.  

Hint Resolve typing_bexp_Hi typing_lexp_Hi.

Lemma typing_cmd_Hi E (c : cmd) :
  barriers c = nil ->
  (forall v, List.In v (writes_var c) -> E v = Hi) ->
  typing_cmd E c Hi.
Proof.
  induction c; intros; eauto; equates 1; eauto.
  - equates 1; [econstructor; eauto|].
    rewrite H0; simpl; eauto.
    reflexivity.
  - equates 1; [econstructor; eauto|].
    rewrite H0; simpl; eauto.
    reflexivity.
  - simpl in H.
    assert (barriers c1 = nil).
    { destruct (barriers c1); simpl in *;  congruence. }
    assert (barriers c2 = nil).
    { rewrite H1 in H; eauto. }
    assert (forall v, In v (writes_var c1) -> E v = Hi).
    { intros; apply H0; simpl; rewrite in_app_iff; eauto. }
    assert (forall v, In v (writes_var c2) -> E v = Hi).
    { intros; apply H0; simpl; rewrite in_app_iff; eauto. }
    equates 1; [econstructor; eauto|eauto].
  - simpl in *; econstructor; eauto.
    apply IHc1.
    destruct barriers; simpl in *; congruence.
    intros; apply H0; rewrite in_app_iff; eauto.
    apply IHc2.
    destruct barriers; simpl in *; congruence.
    intros; apply H0; rewrite in_app_iff; eauto.
  - simpl in H; congruence.
Qed.

Lemma le_type_refl ty : le_type ty ty = true.
Proof.
  destruct ty; eauto.
Qed.

Lemma disjoint_not_in_r (T : Type) (l1 l2 : list T) (x : T) :
  disjoint l1 l2 -> In x l2 -> ~In x l1.
Proof.
  intros. apply disjoint_comm in H; induction l2; eauto.
  simpl in *.
  destruct H0; subst; intuition.
Qed.

Definition dim := nat.

Fixpoint nat_to_string (n : nat) : string :=
  match n with
  | O => "O"
  | S n => "S" ++ nat_to_string n
  end%string.

Eval compute in nat_to_string 10.

(* In real accelerate compiler, names_of_array generates length variables for
   multi-dimention arrays. Currently, I only supports one-dimention arrays for
   simplicity.
 *)
Definition names_of_array grp d := ls_init 0 d (fun i => "arr" ++ grp ++ nat_to_string i)%string.
Definition name_of_len grp := ("sh" ++ grp)%string.
Definition names_of_arg grp d := (name_of_len grp, names_of_array grp d).

Open Scope list_scope.
Require Import List.

(* A generating function pl arr + ix := es. pl denotes array is on shared / global memory *)
Fixpoint gen_write pl (arrs : list exp) ix es :=
  match arrs, es with
  | a :: arrs, e :: es => ([pl a +o ix] ::= e) :: gen_write pl arrs ix es 
  | _, _ => nil
  end.

(* An assertion that denotes tups is a tuple whose values is vals and whose permission is p *)
Fixpoint is_tuple_p (tups : list loc_exp) (vals : list exp) p : assn :=
  match tups, vals with
    | nil, nil => emp
    | e :: tups, v :: vals => (e -->p (p, v)) ** is_tuple_p tups vals p
    | _, _ => emp
  end.

Definition fst_of_vals (fs : nat -> list val) : nat -> val :=
  fun x => hd 0%Z (fs x).

Definition tl_of_vals (fs : nat -> list val) : nat -> list val :=
  fun x => tl (fs x). 

(* An assertion that denotes es is a tuple of arrays with top ptrs es and vals fs  *)
Fixpoint is_tuple_array_p (es : list loc_exp) len (fs : nat -> list val) s p : assn :=
  match es with
  | nil => emp
  | e :: es => is_array_p e len (fst_of_vals fs) s p ** is_tuple_array_p es len (tl_of_vals fs) s p
  end.

(* accessor for a tuple of arrays es at index ix *)
Definition tarr_idx es ix := List.map (fun e => e +o ix) es.
Definition vs2es vs := List.map Enum vs.

Fixpoint distribute_tup d (es : list loc_exp) (n : nat) (fs : nat -> list Z) (dist : nat -> nat) (s : nat) p :=
  match n with
  | 0 => nseq d emp
  | S n =>
    add_nth (dist s) (is_tuple_p (tarr_idx es (Zn s)) (vs2es (fs s)) p)
      (distribute_tup d es n fs dist (S s) p)
  end.

Lemma distribute_tup_length d es n fs dist s p :
  length (distribute_tup d es n fs dist s p) = d.
Proof.
  revert s; induction n; intros; simpl.
  - rewrite length_nseq; auto.
  - rewrite add_nth_length; auto.
Qed.    

Lemma nth_dist_next_tup i es fs nt (Hnt0 : nt <> 0) dist p : forall next s n,
  i < nt ->
  (forall i, dist i < nt) ->
  dist (s + next) = i -> next < n ->
  (forall j, j < next -> dist (s + j) <> i) ->
  forall st, st ||= nth i (distribute_tup nt es n fs dist s p) emp <=>
              (is_tuple_p (tarr_idx es (Zn (s + next)))) (vs2es (fs (s + next))) p **
              nth i (distribute_tup nt es (n - S next) fs dist (S (s + next)) p) emp.
Proof.
  induction next; intros s n Hint Hdistnt Hdnx Hnxn Hltnx stc.
  - destruct n; [omega|].
    rewrite <-plus_n_O in Hdnx.
    simpl; rewrite nth_add_nth; [|rewrite distribute_tup_length; omega..].
    subst. rewrite <-beq_nat_refl.
    rewrite <-plus_n_O, <-minus_n_O; reflexivity.
  - destruct n; [omega|]; simpl.
    rewrite nth_add_nth; [|rewrite distribute_tup_length; auto..].
    assert (Heq : beq_nat i (dist s) = false); [| rewrite Heq; clear Heq].
    { specialize (Hltnx 0); rewrite <-plus_n_O in Hltnx.
      apply Nat.eqb_neq; intros Hc; rewrite Hc in Hltnx; apply Hltnx; auto; omega. }
    assert (Heq : s + S next = S s + next) by omega; rewrite Heq in *; clear Heq.
    rewrite IHnext; auto; [reflexivity|..].
    + omega.
    + intros j Hj.
      assert (S j < S next) by omega.
      cutrewrite (S s + j = s + S j); [|omega].
      apply Hltnx; auto.
Qed.

Lemma nth_dist_nil_tup i es fs nt (Hnt0 : nt <> 0) dist p : forall next s n,
  i < nt ->
  (forall i, dist i < nt) ->
  (forall j, j < next -> dist (s + j) <> i) ->
  forall stc, stc ||= nth i (distribute_tup nt es n fs dist s p) emp <=> 
  nth i (distribute_tup nt es (n - next) fs dist (s + next) p) emp.
Proof.
  induction next; intros s n Hint Hdist Hndist stc.
  - rewrite <-minus_n_O, <-plus_n_O; reflexivity.
  - destruct n; simpl; [reflexivity|].
    rewrite nth_add_nth; [|rewrite distribute_tup_length; auto..].
    assert (Heq : beq_nat i (dist s) = false); [|rewrite Heq; clear Heq].
    { apply Nat.eqb_neq; intros Hc; rewrite Hc in Hndist.
      apply (Hndist 0); [omega|f_equal; omega]. }
    rewrite IHnext; [rewrite <-plus_n_Sm; reflexivity|auto..].
    intros j Hj.
    cutrewrite (S s + j = s + S j); [|omega]; apply Hndist; omega.
Qed.

Lemma skip_arr_tup_unfold i es fs n nt (Hnt0 : nt <> 0) p : forall s, 
  i < nt -> 0 < n ->
  forall stc, stc ||= nth i (distribute_tup nt es n fs (nt_step nt) (s * nt + i) p) emp <=>
                  (is_tuple_p (tarr_idx es (Zn (s * nt + i))) (vs2es (fs (s * nt + i))) p  **
                   nth i (distribute_tup nt es (n - nt) fs (nt_step nt) (S s * nt + i) p) emp).
Proof.
  intros s Hint Hn0 stc.
  etransitivity.
  { apply nth_dist_next_tup with (next := 0); auto.
    - unfold nt_step.
      rewrite <-plus_n_O, plus_comm, Nat.mod_add; [rewrite Nat.mod_small; auto| auto].
    - intros; omega. }
  rewrite <-plus_n_O.
  match goal with [|- ?stc ||= _ ** ?X <=> _ ** ?Y] => assert (H : stc ||= X <=> Y); [|rewrite H; reflexivity] end.
  etransitivity; [apply nth_dist_nil_tup with (next := nt - 1); auto|].
  { intros j Hjnt; unfold nt_step.
    rewrite plus_Snm_nSm, <-plus_assoc, plus_comm, Nat.mod_add; auto.
    intros Hc.
    pose proof (Nat.div_mod (i + S j) nt Hnt0) as Heq; rewrite Hc in Heq.
    assert (S j = nt * ((i + S j) / nt)) by omega.
    destruct ((i + S j ) / nt) as [|n']; rewrite mult_comm in H; simpl in H; try omega.
    destruct (n' * nt) as [|n'']; omega. }
  cutrewrite (n - 1 - (nt - 1) = n - nt); [|omega].
  simpl; generalize (s * nt); intros n0.
  cutrewrite (S (n0 + i + (nt - 1)) = nt + n0 + i); [|omega].
  reflexivity.
Qed.

Lemma skip_arr_tup_unfold' i es fs n nt (Hnt0 : nt <> 0) p : forall s, 
  i < nt -> i < n ->
  forall stc, stc ||= nth i (distribute_tup nt es n fs (nt_step nt) (s * nt) p) emp <=>
   (is_tuple_p (tarr_idx es (Zn (s * nt + i))) (vs2es (fs (s * nt + i))) p **
    nth i (distribute_tup nt es (n - nt) fs (nt_step nt) (S s * nt) p) emp).
Proof.
  intros s Hint Hn0.
  etransitivity.
  { apply nth_dist_next_tup with (next := i); auto.
    - unfold nt_step.
      rewrite <-plus_comm, Nat.mod_add; [rewrite Nat.mod_small; auto| auto]. 
    - intros j Hji; unfold nt_step.
      rewrite <-plus_comm, Nat.mod_add; [rewrite Nat.mod_small; omega| auto]. }
  match goal with [|- ?stc ||= _ ** ?X <=> _ ** ?Y] => assert (H : stc ||= X <=> Y); [|rewrite H; reflexivity] end.
  etransitivity; [apply nth_dist_nil_tup with (next := nt - S i); auto|].
  { intros j Hjnt; unfold nt_step.
    rewrite plus_Snm_nSm, <-plus_assoc, plus_comm, Nat.mod_add; auto.
    intros Hc.
    pose proof (Nat.div_mod (i + S j) nt Hnt0) as Heq; rewrite Hc in Heq.
    assert (S j = nt * ((i + S j) / nt)) by omega.
    destruct ((i + S j ) / nt) as [|n']; rewrite mult_comm in H; simpl in H; try omega.
    destruct (n' * nt) as [|n'']; omega. }
  cutrewrite (n - S i - (nt - S i) = n - nt); [|omega].
  simpl; generalize (s * nt); intros n0.
  cutrewrite (S (n0 + i + (nt - S i)) = nt + n0); [|omega].
  reflexivity.
Qed.

Lemma gen_write_no_bars arrs ix es pl :
  barriers (fold_right Cseq Cskip (gen_write pl arrs ix es)) = nil.
Proof.
  revert es; induction arrs; intros [|e es]; simpl; eauto.
Qed.

Lemma writes_var_gen_write arrs ix es pl :
  writes_var (fold_right Cseq Cskip (gen_write pl arrs ix es)) = nil.
Proof.
  revert es; induction arrs; intros [|e es]; simpl; eauto.
Qed.

Lemma gen_write_correct pl arrs ix es0 es ntrd i:
  length es0 = length arrs -> length es = length arrs ->
  CSL (fun i => default ntrd) i
    (is_tuple_p (tarr_idx (List.map pl arrs) ix) es0 1%Qc)
    (fold_right Cseq Cskip (gen_write pl arrs ix es))
    (is_tuple_p (tarr_idx (List.map pl arrs) ix) es 1%Qc).
Proof.
  revert es0 es; induction arrs; intros es0 es HL0 HL; destruct es0 as [|e0 es0], es as [|e es]; 
  simpl in *; try congruence.
  - apply rule_skip.
  - eapply rule_seq.
    { hoare_forward; intros ? ? H; exact H. }
    eapply Hforward.
    { eapply Hbackward.
      2: intros ? ? H; apply scC in H; exact H.
      apply rule_frame.
      apply IHarrs; try omega.
      rewrite writes_var_gen_write; try omega; hnf; simpl; destruct 1. }
    intros; sep_cancel.
Qed.

Definition ss2es := List.map (fun x => Evar (Var x)).

Definition writeArray grp d pl : (list exp * exp * (exp -> list exp -> list cmd))  :=
  let (l, grp) := names_of_arg grp d in
  (ss2es grp, Evar (Var l), gen_write pl (map (fun x => Evar (Var x)) grp)).

Fixpoint locals base n :=
  match n with
  | S n => (Var (base ++ nat_to_string n)) :: locals base n
  | 0 => nil
  end%list.

Definition sublEs x e es := List.map (fun e' => sublE x e e') es.
Definition subEs x e es := List.map (fun e' => subE x e e') es.

Lemma subA_is_tuple_p x e es1 es2 p :
  subA x e (is_tuple_p es1 es2 p) |=
  is_tuple_p (sublEs x e es1) (subEs x e es2) p.
Proof.
  revert es2; induction es1; intros es2; simpl.
  - destruct es2; simpl; apply subA_emp.
  - destruct es2; simpl; [apply subA_emp|].
    intros s h H.
    subA_normalize_in H with (fun H => apply IHes1 in H).
    apply H.
Qed.

Lemma sublEs_tarr_idx x e es ix :
  sublEs x e (tarr_idx es ix) = tarr_idx (sublEs x e es) (subE x e ix).
Proof.
  induction es; simpl; congruence.
Qed.  

Lemma subEs_vs2es x e vs : subEs x e (vs2es vs) = (vs2es vs).
Proof.
  induction vs; simpl; auto; congruence.
Qed.
  
Lemma subA_distribute_tup nt arrs l f dist (i : nat) x e p : forall s,
    subA x e (List.nth i (distribute_tup nt arrs l f dist s p) emp) |=
      List.nth i (distribute_tup nt (sublEs x e arrs) l f dist s p) emp.
Proof.
  induction l; [unfold subA'|]; intros s st hp H; simpl in *.
  - simpl_nth; destruct (Compare_dec.leb _ _); auto;
    split; intros; simpl; auto.
  - assert (dist s < nt \/ nt <= dist s)%nat as [|] by omega.
    + assert (i < nt \/ nt <= i)%nat as [|] by omega.
      * rewrite nth_add_nth in *; [|rewrite distribute_tup_length; auto..].
        destruct (EqNat.beq_nat _ _); intuition.
        apply subA_sconj in H.
        revert st hp H; apply scRw; intros st hp H.
        apply subA_is_tuple_p in H; simpl in H. 
        rewrite sublEs_tarr_idx, subEs_vs2es in H; simpl in H; eauto.
        applys* IHl.
      * rewrite List.nth_overflow in *; [|rewrite add_nth_length, distribute_tup_length..]; auto.
    + rewrite add_nth_overflow in *; (try rewrite distribute_tup_length); auto.
Qed.

Fixpoint eq_tup (es : list exp) (vs : list val) : assn :=
  match es, vs with
  | nil, nil => emp
  | e :: es, v :: vs => !(e === v) ** eq_tup es vs
  | _, _ => FalseP
  end.

Notation "e1 ==t e2" := (eq_tup e1 e2) (at level 70, right associativity).

Lemma subA_eq_tup x e es1 es2 :
  subA x e (es1 ==t es2) |= (subEs x e es1 ==t es2).
Proof.
  revert es2; induction es1; simpl; destruct es2; simpl; intros s h H; subA_normalize_in H; eauto.
  sep_cancel; eauto.
Qed.

Ltac subA_norm_in H :=
  subA_normalize_in H with (fun H => first
    [apply subA_distribute_tup in H | apply subA_eq_tup in H | apply subA_is_tuple_p in H]).

Definition es2gls es := List.map (fun es => Gl es) es.
Definition es2shs es := List.map (fun es => Sh es) es.

Lemma sublEs_es2gls es x e :
  sublEs x e (es2gls es) = es2gls (subEs x e es).
Proof.
  induction es; simpl; try congruence.
Qed.
  
Lemma sublEs_es2shs es x e :
  sublEs x e (es2shs es) = es2shs (subEs x e es).
Proof.
  induction es; simpl; try congruence.
Qed.

Create HintDb subE_simpl.
Hint Rewrite sublEs_es2gls sublEs_es2shs subEs_vs2es : subE_simpl.

Tactic Notation "subE_simpl" "in" "*" := repeat (autorewrite with subE_simpl in *).

Definition var_of_str v : string :=
  match v with
    | Var v => v
  end.

Notation string_eq s1 s2 := (if string_dec s1 s2 then true else false).

Lemma subE_vars2es x e vs :
  List.Forall (fun v => string_eq v (var_of_str x) = false) vs -> subEs x e (ss2es vs) = ss2es vs.
Proof.  
  induction vs; simpl; eauto; intros.
  inversion H; subst.
  rewrite IHvs; eauto.
  destruct var_eq_dec; subst; eauto.
  simpl in H2; destruct string_dec; congruence.
Qed.


Lemma names_of_array_compare x grp n :
  prefix "arr" (var_of_str x) = false ->
  List.Forall (fun v => string_eq v (var_of_str x) = false) (names_of_array grp n).
Proof.
  unfold names_of_array; generalize 0; induction n.
  - simpl; intros _; constructor.
  - intros s H; constructor.
    destruct string_dec; auto.
    rewrite <-e in H. simpl in H.
    destruct (grp ++ _)%string; simpl in H; congruence.
    apply IHn; auto.
Qed.

Hint Resolve names_of_array_compare.

Lemma distribute_tup_snoc i e f nt (Hnt : nt <> 0) dist p : forall n s,
  i < nt ->
  (forall i, dist i < nt) ->
  forall stc, stc ||= nth i (distribute_tup nt e (S n) f dist s p) emp <=>
  nth i (add_nth (dist (s + n)) ((is_tuple_p (tarr_idx e (Zn (s + n))) (vs2es (f (s + n)))) p)
           (distribute_tup nt e n f dist s p)) emp.
Proof.
  induction n; intros s Hit Hdist; [simpl|].
  - rewrite !nth_add_nth; [| rewrite length_nseq || rewrite distribute_length..]; auto.
    simpl_nth; destruct (leb _ _); rewrite <-!plus_n_O; destruct (beq_nat _ _); reflexivity.
  - remember (S n) as Sn.
    simpl; rewrite nth_add_nth; [|rewrite distribute_tup_length; auto..].
    destruct (beq_nat i (dist s)) eqn:His.
    + intros; rewrite IHn; auto.
      cutrewrite (S s + n = s + Sn); [|omega]; rewrite !nth_add_nth; [|rewrite distribute_tup_length; auto..].
      destruct (beq_nat i (dist (s + Sn))); rewrite HeqSn; simpl.
      * rewrite nth_add_nth; [|rewrite distribute_tup_length; auto..]; rewrite His.
        split; intros H; repeat sep_cancel.
      * rewrite nth_add_nth; [|rewrite distribute_tup_length; auto..]; rewrite His.
        split; intros H; repeat sep_cancel.
    + intros; rewrite IHn; auto.
      cutrewrite (S s + n = s + Sn); [|omega]; rewrite !nth_add_nth; [|rewrite distribute_tup_length; auto..].
      destruct (beq_nat i (dist (s +Sn))) eqn:Hisn.
      * rewrite HeqSn; simpl; rewrite nth_add_nth; [|rewrite distribute_tup_length; auto..].
        rewrite His; split; intros; sep_cancel.
      * rewrite HeqSn; simpl; rewrite nth_add_nth; [|rewrite distribute_tup_length; auto..].
        rewrite His; split; intros; sep_cancel.
Qed.

Lemma nth_dist_snoc_tup i e f nt (Hnt0 : nt <> 0) dist p : forall next n s,
  i < nt ->
  (forall i, dist i < nt) ->
  dist (s + n + next) = i -> 
  (forall j, j < next -> dist (s + n + j) <> i) ->
  forall stc, stc ||= 
  nth i (distribute_tup nt e n f dist s p) emp ** 
  is_tuple_p (tarr_idx e (Zn (s + n + next))) (vs2es (f (s + n + next))) p
  <=> nth i (distribute_tup nt e (S (n + next)) f dist s p) emp.
Proof.
  induction next; intros n s Hint Hdist Hdisti Hj stc.
  - rewrite <-!plus_n_O in *.
    rewrite distribute_tup_snoc; auto; rewrite nth_add_nth; auto.
    2: rewrite distribute_tup_length; auto.
    2: rewrite distribute_tup_length; auto.
    symmetry in Hdisti; rewrite (proj2 (beq_nat_true_iff _ _) Hdisti).
    split; intros; repeat sep_cancel.
  - cutrewrite (S (n + S next) = S (S n + next)); [|omega].
    rewrite <-IHnext; auto.
    + cutrewrite (s + S n + next = s + n + S next); [|omega].
      rewrite distribute_tup_snoc; auto; rewrite nth_add_nth; auto.
      2: rewrite distribute_tup_length; auto.
      2: rewrite distribute_tup_length; auto.
      assert (H : beq_nat i (dist (s + n)) = false); [|rewrite H; clear H].
      { apply Nat.eqb_neq; intros Hc.
        apply (Hj 0); [omega| rewrite <-plus_n_O; auto]. }
      split; intros; repeat sep_cancel.
    + cutrewrite (s + S n + next = s + n + S next); [|omega]; auto.
    + intros j Hjnext.
      cutrewrite (s + S n + j = s + n + S j); [|omega]; apply Hj; omega.
Qed.

Hint Extern 1 (_ <  length (distribute_tup _ _ _ _ _ _ _) ) =>
  rewrite distribute_tup_length; auto.

Lemma nth_dist_tup_ext' i e f nt (Hnt0 : nt <> 0) dist p : forall n s,
  i < nt ->
  (forall i, dist i < nt) ->
  dist (s + n) <> i ->
  forall stc, 
  stc ||= nth i (distribute_tup nt e n f dist s p) emp <=> 
      nth i (distribute_tup nt e (S n) f dist s p) emp.
Proof.
  induction n; intros s Hint Hdisi Hdisneq stc.
  - simpl; rewrite nth_add_nth; simpl_nth.
    rewrite <-plus_n_O in Hdisneq.
    rewrite (proj2 (Nat.eqb_neq i (dist s))); auto; reflexivity.
  - remember (S (S n)) as n'; simpl; rewrite nth_add_nth; auto.
    assert (dist (S s + n) <> i) by (rewrite <-plus_n_Sm in Hdisneq; simpl; auto).
    destruct (beq_nat i (dist s)) eqn:His; rewrite IHn; auto;
    subst; remember (S n); simpl; rewrite nth_add_nth; auto; rewrite His; reflexivity.
Qed.    

Lemma nth_dist_tup_ext i e f nt (Hnt0 : nt <> 0) dist p : forall next s n,
  i < nt ->
  (forall i, dist i < nt) ->
  (forall j, j < next -> dist (s + n + j) <> i) ->
  forall stc, stc ||=
  nth i (distribute_tup nt e n f dist s p) emp <=> 
  nth i (distribute_tup nt e (n + next) f dist s p) emp.
Proof.
  induction next; intros s n Hint Hdist Hdisti stc.
  - rewrite <-plus_n_O; reflexivity.
  - rewrite <-plus_n_Sm; simpl.
    rewrite nth_add_nth; auto.
    destruct (beq_nat _ _) eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      rewrite <-IHnext; auto.
      destruct n.
      { contradict Heq; intros Hc; apply (Hdisti 0); [omega| rewrite <-!plus_n_O; auto]. }
      remember (S n) eqn:Heq'; rewrite Heq' at 1; simpl; rewrite nth_add_nth; auto.
      rewrite Heq, <-beq_nat_refl; subst.
      rewrite <-nth_dist_tup_ext' with (s := (S s)); [reflexivity|auto..].
      cutrewrite (S s + n = s + S n + 0); [|omega]; apply Hdisti; omega.
      intros j Hj; cutrewrite (S s + n + j = s + n + S j); [|omega]; apply Hdisti; omega.
    + rewrite <-IHnext; auto.
      destruct n; [simpl; reflexivity|].
      remember (S n) eqn:Heq'; rewrite Heq' at 1; simpl; rewrite nth_add_nth; auto; rewrite Heq.
      subst; rewrite <-nth_dist_tup_ext'; [reflexivity|auto..].
      cutrewrite (S s + n = s + S n + 0); [|omega]; apply Hdisti; omega.
      intros j Hj; cutrewrite (S s + n + j = s + n + S j); [|omega]; apply Hdisti; omega.
Qed.

Lemma skip_arr_tup_fold' i es f nt (Hnt0 : nt <> 0) p : forall s, 
  i < nt -> 
  forall stc, stc ||=
  nth i (distribute_tup nt es (s * nt) f (nt_step nt) 0 p) emp **
    (is_tuple_p (tarr_idx es (Zn (s * nt + i)))) (vs2es (f (s * nt + i))) p <=>
    nth i (distribute_tup nt es (S s * nt) f (nt_step nt) 0 p) emp.
Proof.
  intros s Hint stc.
  cutrewrite (s * nt + i = 0 + s * nt + i); [|omega].
  rewrite nth_dist_snoc_tup; try omega; eauto.
  rewrite nth_dist_tup_ext with (next := (nt - S i)); try omega; eauto.
  cutrewrite (S (s * nt + i) + (nt - S i) = S s * nt); [|simpl; omega]; reflexivity.
  intros; simpl; unfold nt_step.
  cutrewrite (S (s * nt + i + j) = (S (i + j) + s * nt));
    [rewrite Nat.mod_add, Nat.mod_small; omega|omega].
  unfold nt_step.
  cutrewrite (0 + s * nt + i = i + s * nt); [rewrite Nat.mod_add, Nat.mod_small; omega|omega].
  intros j Hji; simpl; unfold nt_step; rewrite plus_comm, Nat.mod_add, Nat.mod_small; omega.
Qed.  

Lemma is_array_tup_unfold es len' f p : forall s len,
  (forall i, i < len -> length (f (s + i) ) = length es) ->
  len' < len ->
  forall stc, 
    stc ||= is_tuple_array_p es len f s p <=>
        is_tuple_array_p es len' f s p **
        is_tuple_p (tarr_idx es (Zn (s + len') )) (vs2es (f (s + len'))) p **
        is_tuple_array_p es (len - len' - 1) f (S (len' + s)) p.
Proof.
  revert f; induction es; simpl; introv Hf.
  - intros; destruct vs2es; rewrite !emp_unit_l; reflexivity.
  - intros Hlen stc.
    lets Hslen: (>>Hf len' __); eauto.
    rewrite <-!sep_assoc.
    rewrite IHes; auto.
    lets unf: (>>is_array_unfold a len' (fst_of_vals f) s len stc); auto.
    unfold fst_of_vals, tl_of_vals in *; simpl.
    cutrewrite (len' + s = s + len') in unf; [|ring].
    destruct (f (s + len')); simpl in *; try omega.
    rewrite unf, <-!sep_assoc. split; intros; repeat sep_cancel.
    cutrewrite (s + len' = len' + s) in H3; [|ring]; auto.
    cutrewrite (s + len' = len' + s); [|ring]; auto.
    intros ? Htmp; specialize (Hf i Htmp); unfold tl_of_vals.
    destruct (f (s + i)); simpl in *; omega.
Qed.

Lemma is_array_tup_0 es f p : forall s,
  forall stc,
    stc ||= is_tuple_array_p es 0 f s p <=> emp.
Proof.
  revert f; induction es; simpl; eauto; intros.
  - reflexivity.
  - rewrite IHes; rewrite emp_unit_l; reflexivity.
Qed.

Lemma distribute_correct (d : nat) (e : list loc_exp) (n : nat) (f : nat -> list val) (dist : nat -> nat) p:
  forall s, (forall x, dist x < d) ->
            (forall i, i < n -> length (f (s + i)) = length e) ->
  forall st, st ||= is_tuple_array_p e n f s p <=> conj_xs (distribute_tup d e n f dist s p).
Proof.
  induction n; intros s Hdist; simpl; intros.
  - rewrite nseq_emp_emp, is_array_tup_0; reflexivity.
  - rewrite conj_xs_add_nth; [|rewrite distribute_tup_length; auto].
    lets unf: (>>is_array_tup_unfold e 0 f s (S n) ___); auto; try omega.
    rewrite unf.
    rewrite is_array_tup_0, emp_unit_l.
    simpl; rewrite <-plus_n_O, <-minus_n_O.
    rewrite IHn; [reflexivity|..].
    auto.
    intros; cutrewrite (S s + i = s + S i); [|ring]; rewrite H; omega.
Qed.
