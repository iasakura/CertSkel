Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics.
Require Import Psatz.

Notation perm_n n := (1 / injZ (Zn n))%Qc.

Fixpoint fv_E (e : exp) :=
  match e with
    | Evar v => v :: nil
    | Enum n => nil
    | Emin e1 e2
    | Eeq e1 e2
    | Elt e1 e2
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
  unfold indelE; induction e; try destruct p; simpl; intros; intuition; try (f_equal).
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
  induction e; try destruct p; eauto; equates 1; eauto.
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

Eval compute in nat_to_string 10.

(* In real accelerate compiler, names_of_array generates length variables for
   multi-dimention arrays. Currently, I only supports one-dimention arrays for
   simplicity.
 *)
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

Lemma gen_write_correct pl arrs ix es0 es ntrd (i : Fin.t ntrd) BS:
  length es0 = length arrs -> length es = length arrs ->
  CSL BS i
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

(* A generating function xs := pl arr + ix. pl denotes array is on shared / global memory *)
Fixpoint gen_read pl (xs : list var) (ctys : list CTyp) (arrs : list exp) ix :=
  match xs, ctys, arrs with
  | x :: xs, cty :: ctys, a :: arrs => (x :T cty ::= [pl a +o ix]) ;; gen_read pl xs ctys arrs ix 
  | x :: xs, nil, a :: arrs => (x ::= [pl a +o ix]) ;; gen_read pl xs ctys arrs ix 
  | _, _, _ => Cskip
  end.

Lemma gen_read_writes pl xs ctys arrs ix:
  length xs = length arrs ->
  writes_var (gen_read pl xs ctys arrs ix) = xs.
Proof.
  revert ctys arrs; induction xs; intros ctys [|v vs]; simpl in *; try congruence.
  intros; destruct ctys; simpl; f_equal; eauto.
Qed.

Lemma gen_read_no_bars pl xs ctys arrs ix :
  barriers (gen_read pl xs ctys arrs ix) = nil.
Proof.
  revert ctys arrs; induction xs; intros [|? ?] [|? ?]; simpl; eauto.
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
  simpl in *.
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

Definition str_of_var v : string :=
  match v with
    | Var v => v
  end.

Notation string_eq s1 s2 := (if string_dec s1 s2 then true else false).

Definition vars2es := List.map Evar.

Lemma subE_vars2es x e vs :
  List.Forall (fun v => string_eq v (str_of_var x) = false) vs -> subEs x e (ss2es vs) = ss2es vs.
Proof.  
  induction vs; simpl; eauto; intros.
  inversion H; subst.
  rewrite IHvs; eauto.
  destruct var_eq_dec; subst; eauto.
  simpl in H2; destruct string_dec; congruence.
Qed.

Lemma inde_is_tup es1 es2 vs p :
  List.Forall (fun e => forall v, List.In v vs -> indelE e v) es1 ->
  List.Forall (fun e => forall v, List.In v vs -> indeE e v) es2 ->
  inde (is_tuple_p es1 es2 p) vs.
Proof.
  revert es2; induction es1; simpl; intros [| e es2 ]; simpl; intros; prove_inde.
  inversion H; subst; rewrite Forall_forall; auto.
  inversion H0; subst; rewrite Forall_forall; auto.
  apply IHes1; inverts H; inverts H0; auto.
Qed.

Ltac simplify' := repeat (simpl in *; lazymatch goal with
  | [|- In _ (map _ _) -> _] =>
    rewrite in_map_iff; intros [? [? ?]]; subst
  | [H:In _ (map _ _) |-_] =>
    rewrite in_map_iff in H; destruct H as [? [? H]]; subst
  | [|- indeE _ _] => apply indeE_fv
  | [|- indelE _ _] => apply indelE_fv
  | [H : _ \/ False|-_] =>destruct H as [H|[]];subst
  | [|- ~(_ \/ _)] => intros [?|?]
  | [|- context [In _ (_ ++ _)]] => rewrite in_app_iff
  | [|- forall _, _] => intros ?
  end).

Lemma gen_read_correct nt (i : Fin.t nt) BS pl xs ctys arrs ix vs q:
  (pl = Sh \/ pl = Gl) ->
  (forall x i, In x xs -> In i (fv_E ix) -> ~In x (fv_E i)) ->
  (forall x a, In x xs -> In a arrs -> ~In x (fv_E a)) ->
  disjoint_list xs ->
  length xs = length arrs -> length xs = length vs ->
  CSL BS i
    ( is_tuple_p (tarr_idx (List.map pl arrs) ix) (vs2es vs) q )
    (gen_read pl xs ctys arrs ix)
    ( !(vars2es xs ==t vs) ** is_tuple_p (tarr_idx (List.map pl arrs) ix) (vs2es vs) q ).
Proof.
  revert ctys vs arrs; induction xs as [|x xs]; intros ctys vs arrs Hpl Hixxs Hv0 Hv1 HL0 HL1;
    destruct vs as [| v vs], arrs as [|a arrs]; simpl in *; try congruence.
  - eapply Hforward; [apply rule_skip|intros; sep_normal; sep_cancel].
    unfold_conn; split; eauto.
  - assert (forall cty, CSL BS i
     ((pl a +o ix -->p (q,  v)) **
      is_tuple_p (tarr_idx (map pl arrs) ix) (vs2es vs) q)
     (x ::T cty ::=  [pl a +o ix];; gen_read pl xs (tl ctys) arrs ix)
     (!(!(x === v) ** vars2es xs ==t vs) **
      (pl a +o ix -->p (q,  v)) **
      is_tuple_p (tarr_idx (map pl arrs) ix) (vs2es vs) q)); [|destruct ctys; eauto].
    intros cty; eapply rule_seq.
    { apply rule_frame; [apply rule_read|].
      - destruct Hpl; subst; apply indelE_fv; simpl; rewrite in_app_iff; intros [Hc | Hc]; eauto;
          try lets: (>>Hv0 Hc); try lets: (>>Hixxs Hc); eauto; tauto.
      - apply indeE_fv; simpl; eauto.
      - apply inde_is_tup; rewrite Forall_forall; unfold tarr_idx, vs2es.
        destruct Hpl; subst pl; simplify'; first [now (forwards :Hv0; eauto) | 
                                                 now (forwards :Hixxs; eauto)].
        destruct Hpl; subst pl; simplify'; first [now (forwards :Hv0; eauto) | 
                                                 now (forwards :Hixxs; eauto)]. }
    eapply Hbackward.
    2: intros; apply scC in H; apply H.
    eapply Hforward; [eapply rule_frame; [apply IHxs|]|]; eauto; try tauto; try omega.
    { rewrite gen_read_writes; prove_inde; try omega; rewrite Forall_forall; intros;
      first [apply indeE_fv | apply indelE_fv]; simpl in *; eauto.
      destruct Hpl; subst; simplify'; first [now (forwards :Hv0; eauto) | 
                                            now (forwards :Hixxs; eauto)].
      simplify'; eauto; subst; tauto. }
    intros; sep_normal_in H; sep_normal; repeat sep_cancel.
    apply scC; sep_cancel.
    sep_rewrite pure_star; apply scC; sep_cancel.
    repeat split; destruct H2; eauto.
Qed.
      
Lemma names_of_array_compare x grp n :
  prefix "arr" (str_of_var x) = false ->
  List.Forall (fun v => string_eq v (str_of_var x) = false) (names_of_array grp n).
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

Lemma skip_arr_tup_fold i es f nt (Hnt0 : nt <> 0) p : forall s, 
  i < nt -> 
  forall stc, stc ||=
  nth i (distribute_tup nt es (s * nt + i) f (nt_step nt) 0 p) emp **
    (is_tuple_p (tarr_idx es (Zn (s * nt + i)))) (vs2es (f (s * nt + i))) p <=>
    nth i (distribute_tup nt es (S s * nt + i) f (nt_step nt) 0 p) emp.
Proof.
  intros s Hint stc.
  assert (Heq : s * nt + i = 0 + (s * nt + i) + 0) by omega.
  rewrite Heq at 2; rewrite Heq at 3.
  rewrite nth_dist_snoc_tup; auto.
  rewrite nth_dist_tup_ext with (next := nt - 1); auto.
  cutrewrite (S (s * nt + i + 0) + (nt - 1) = S s * nt + i); [|simpl; omega]; reflexivity.
  intros j Hj; unfold nt_step.
  - cutrewrite (0 + S (s * nt + i + 0) + j = (S (i + j)) + s * nt); [|omega].
    rewrite Nat.mod_add; auto.
    intros Heqij. pose proof (Nat.div_mod (S (i + j)) nt Hnt0) as H'; rewrite Heqij in H'.
    assert (S j = nt * (S (i + j) / nt)) by omega.
    destruct (S (i + j) / nt); simpl in *; [omega|].
    rewrite mult_comm in H; simpl in *; destruct (n * nt); omega.
  - simpl; rewrite <-!plus_n_O; unfold nt_step.
    rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto.
  - inversion 1.
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

Lemma skip_arr_tup_forward ix i e f n nt (Hnt0 : nt <> 0) q : forall s, 
  ix < n -> (s + ix) mod nt = i ->
  forall stc, stc ||= nth i (distribute_tup nt e n f (nt_step nt) s q) emp <=>
                  nth i (distribute_tup nt e ix f (nt_step nt) s q) emp **
                  is_tuple_p (tarr_idx e (Zn (s + ix))) (vs2es (f (s + ix))) q **
                  nth i (distribute_tup nt e (n - ix - 1) f (nt_step nt) (s + ix + 1) q) emp.
Proof.
  intros s Hix0 Hix1 stc.
  revert ix Hix0 s Hix1; induction n; [intros; simpl; try omega|]; intros ix Hix0 s Hix1.
  cutrewrite (S n - ix - 1 = n - ix); [|omega].
  assert (i < nt) by (subst; apply mod_bound_pos; omega).
  simpl; rewrite nth_add_nth; [|rewrite distribute_tup_length; eauto..].
  destruct (beq_nat _ _) eqn:Heq;
    [rewrite beq_nat_true_iff in Heq | rewrite beq_nat_false_iff in Heq].
  - destruct ix; simpl.
    + rewrite <-plus_n_O, <-minus_n_O.
      cutrewrite (s + 1 = S s); [|omega].
      rewrite nth_nseq; destruct (Compare_dec.leb _ _); rewrite emp_unit_l;
      split; intros; repeat sep_cancel.
    + rewrite nth_add_nth; [|rewrite distribute_tup_length; try omega..].
      rewrite Heq at 2; rewrite <-beq_nat_refl.
      rewrite <-plus_n_Sm in Hix1.
      lets H':(>>IHn ix (S s)); try omega; rewrite H'; clear H'; eauto.
      cutrewrite (S s + ix = s + S ix); [|omega].
      cutrewrite (n - ix - 1 = n - S ix); [|omega].
      rewrite !sep_assoc; reflexivity.
  - destruct ix; simpl.
    + unfold nt_step in *; rewrite <-plus_n_O in *; congruence.
    + rewrite nth_add_nth; [|rewrite distribute_tup_length; try omega; eauto..].
      lets H': (>>beq_nat_false_iff ___); apply H' in Heq; rewrite Heq; clear H'.
      rewrite <-plus_n_Sm in Hix1.
      lets H':(>>IHn ix (S s)); try omega; rewrite H'; clear H'; eauto.
      cutrewrite (S s + ix = s + S ix); [|omega].
      cutrewrite (n - ix - 1 = n - S ix); [|omega].
      rewrite !sep_assoc; reflexivity.
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

Definition catcmd := fold_right Cseq Cskip. 

Fixpoint read_tup (vs : list var) (ctys : list CTyp) (es : list exp) :=
  match vs, ctys, es with
  | v :: vs, cty :: ctys, e :: es => (v :T cty ::= e) ;; read_tup vs ctys es
  | v :: vs, nil, e :: es => (v ::= e) ;; read_tup vs ctys es
  | _, _, _  => Cskip
  end.

Lemma pure_pure P stk : stk ||= !(!(P)) <=> !(P).
Proof.
  split; intros.
  apply H. unfold_conn_all; simpl.
  repeat split; destructs H; eauto.
Qed.  
    
Lemma fv_subE' var v es :
  (forall e, In e es -> ~In var (fv_E e)) ->
  subEs var v es = es.
Proof.
  induction es; intros; simpl in *; eauto.
  rewrite fv_subE; eauto; rewrite IHes; eauto.
Qed.  

Lemma read_tup_writes vs ctys es :
  length vs = length es ->
  writes_var (read_tup vs ctys es) = vs.
Proof.
  revert vs ctys; induction es; intros [|v vs] [|cty ctys]; simpl in *; try congruence;
  intros; f_equal; eauto.
Qed.

Lemma read_tup_correct nt (i : Fin.t nt) BS es vs ctys vars :
  (forall v e, In v vars -> In e es -> ~In v (fv_E e)) ->
  disjoint_list vars ->
  length vs = length es -> length vars = length es ->
  CSL BS i
    ( !(es ==t vs) )
    (read_tup vars ctys es)
    ( !(vars2es vars ==t vs) ).
Proof.
  revert vs vars ctys; induction es; simpl in *; intros [|v vs] [|var vars] ctys; simpl in *; try congruence;
  intros Hfv Hdisvars Hlen1 Hlen2.
  apply rule_skip.
  assert (forall cty, CSL BS i !(!(a === v) ** es ==t vs)
                          (var ::T cty ::= a;; read_tup vars (tl ctys) es)
                          !(!(var === v) ** vars2es vars ==t vs)); [intros cty|destruct ctys; eauto].
  lets: (>> IHes vs vars ___); try omega; jauto.
  eapply rule_seq; eauto.
  - hoare_forward.
    intros s h [v' H'].
    subA_norm_in H'. simpl in H'.
    sep_rewrite_in pure_star H'; sep_rewrite_in pure_pure H'; sep_normal_in H'.
    rewrite fv_subE in H'; eauto.
    rewrite fv_subE' in H'; [|eauto].
    assert ((!(es ==t vs) ** !(var === v)) s h).
    { sep_split_in H'.
      sep_split; eauto.
      unfold_conn_all; simpl in *; congruence. }
    exact H0.
  - eapply Hforward.
    Focus 2. { intros. sep_rewrite pure_star; sep_rewrite pure_pure. apply scC; exact H0. } Unfocus.
    apply rule_frame; eauto.
    prove_inde; rewrite Forall_forall, read_tup_writes; auto.
    intros; apply indeE_fv; simpl; intros [|]; intros; subst; jauto.
Qed.    

Lemma subEs_ss2es (ss : list string) (x : var) (e : exp) :
  (forall s, In s ss -> str_of_var x <> s) ->
  subEs x e (ss2es ss) = ss2es ss.
Proof.
  induction ss; simpl; eauto.
  intros H; destruct var_eq_dec; rewrite IHss; eauto.
  subst x; simpl in H.
  forwards: (>>H a ___); try congruence; eauto.
Qed.  



Fixpoint input_spec env env_den p :=
  match env, env_den with
  | (idx, d) :: env, (addrs, len, f) :: env_den =>
    let (Len, Arrs) := names_of_arg (grpOfInt idx) d in
    let Arrs' := (ss2es Arrs) in
    !(Evar (Var Len) === Zn len) **
    !(Arrs' ==t addrs) **
     (is_tuple_array_p (es2gls (vs2es addrs)) len f 0 p) **
     input_spec env env_den p
  | _, _ => emp
  end.

Fixpoint input_spec' env_den p :=
  match env_den with
  | (addrs, len, f) :: env_den =>
     (is_tuple_array_p (es2gls (vs2es addrs)) len f 0 p) **
     input_spec' env_den p
  | _ => emp
  end.

Lemma input_spec_forget E E_den p :
  length E = length E_den ->
  input_spec E E_den p |= input_spec' E_den p.
Proof.
  revert E_den; induction E as [|[? ?] ?]; destruct E_den as [|((? & ?) & ?) ?]; simpl; intros; try omega; eauto.
  sep_split_in H0; sep_cancel; eauto.
Qed.  

Lemma subA_is_tup_arr var e Es l f s p :
  subA var e (is_tuple_array_p Es l f s p) |=
  is_tuple_array_p (sublEs var e Es) l f s p.
Proof.
  revert f; induction Es; simpl; intros; eauto.
  subA_norm_in H.
  sep_cancel; eauto.
Qed.  

Lemma In_ls_init (T : Type) s l f (x : T) : 
  In x (ls_init s l f) <-> exists y, x = f y /\ s <= y < s + l.
Proof.
  revert s; induction l; intros s; simpl; eauto.
  - split; [destruct 1| destruct 1; omega].
  - split; intros H.
    + destruct H as [|H]; [exists s; split; eauto; omega| ].
      rewrite IHl in H; destruct H as [y [? ?]]; exists y; split; eauto; omega.
    + destruct H as [y [Hh  Ht]].
      assert (y = s \/ S s <= y < (S s) + l) as [|] by omega; [subst; left; eauto|].
      right; rewrite IHl; exists y; split; eauto; omega.
Qed.

Lemma names_of_array_in grp n x :
  In x (names_of_array grp n) -> prefix "arr" x = true.
Proof.
  unfold names_of_array.
  rewrite In_ls_init; intros [? [? ?]]; subst; simpl.
  destruct (_ ++ _)%string; eauto.
Qed.

Lemma subA_input_spec var e E Ed p :
  prefix "arr" (str_of_var var) = false ->
  prefix "sh" (str_of_var var) = false ->
  subA var e (input_spec E Ed p) |=
  input_spec E Ed p.
Proof.
  revert Ed; induction E as [|[? ?] ?]; intros Ed; simpl.
  - intros ? ? ? H; eauto.
  - intros H H' s h Hsat.
    destruct Ed as [| [[? ?] ?] ?]; [apply Hsat|].
    subA_norm_in Hsat. simpl in Hsat.
    assert (var <> Var (name_of_len (grpOfInt n))).
    { intros Hc; unfold name_of_len in Hc; subst; simpl in H'; congruence. }
    destruct var_eq_dec; try congruence.
    sep_cancel.
    revert H1; apply scRw; intros ? ? Hsat'.
    rewrite subEs_ss2es in Hsat'; eauto.
    intros s1 Hs1 Hc; apply names_of_array_in in Hs1; subst; congruence.
    revert Hsat'; apply scRw; intros ? ? Hsat'.
    apply subA_is_tup_arr in Hsat'.
    rewrite sublEs_es2gls, subEs_vs2es in Hsat'; eauto.
    apply IHE; eauto.
Qed.

Lemma inde_eq_tup E1 E2 vs:
  List.Forall (fun e => forall v, List.In v vs -> indeE e v) E1 -> inde (E1 ==t E2) vs.
Proof.
  revert E2; induction E1; intros [|e e2]; simpl; intros; prove_inde.
  inversion H; subst.
  rewrite Forall_forall; auto.
  inversion H; subst.
  rewrite Forall_forall; auto.
  apply IHE1; inversion H; subst; auto.
Qed.

Lemma outs_prefix x v grp d pl :
  In x (fst (fst (writeArray grp d pl))) -> In v (fv_E x) -> prefix "arr" (str_of_var v) = true.
Proof.
  unfold writeArray, names_of_arg, ss2es, names_of_array; simpl.
  intros H; apply in_map_iff in H as [? [? H]]; subst;
  apply In_ls_init in H as [? [? H]]; subst; simpl.
  intros [?|[]]; subst; simpl; auto.
  destruct (_ ++ _)%string; auto.
Qed.

Lemma outs_length grp d pl : length (fst (fst (writeArray grp d pl))) = d.
Proof.
  unfold writeArray, names_of_arg, names_of_arg, ss2es, names_of_array; simpl.
  rewrite map_length, init_length; auto.
Qed.

(* Lemma outs_inde vs : *)
(*   List.Forall (fun e => prefix "arr" (str_of_var e) = false) vs -> *)
(*   List.Forall (fun e => forall v, List.In v vs -> indeE e v) . *)
(* Proof. *)
(*   rewrite !Forall_forall. *)
(*   unfold Outs, writeArray, names_of_arg, names_of_array; simpl. *)
(*   unfold ss2es; intros H x Hx. *)
(*   apply in_map_iff in Hx as [? [? Hx]]; subst. *)
(*   apply In_ls_init in Hx as [? [? ?]]; subst. *)
(*   intros. *)
(*   unfold indeE; intros; simpl; unfold var_upd. *)
(*   destruct var_eq_dec; auto. *)
(*   subst; apply H in H0; cbv in H0; congruence. *)
(* Qed. *)

Lemma inde_distribute_tup nt es l f dist (i : nat) p vs : forall s,
    List.Forall (fun e => forall v, List.In v vs -> indelE e v) es ->
      inde (List.nth i (distribute_tup nt es l f dist s p) emp) vs.
Proof.
  induction l; [unfold subA'|]; intros s Hinde; simpl in *.
  - simpl_nth; destruct (Compare_dec.leb _ _); prove_inde.
  - assert (dist s < nt \/ nt <= dist s)%nat as [|] by omega.
    + assert (i < nt \/ nt <= i)%nat as [|] by omega.
      * rewrite nth_add_nth in *; [|rewrite distribute_tup_length; auto..].
        destruct (EqNat.beq_nat _ _); intuition.
        prove_inde.
        apply inde_is_tup; auto.
        rewrite Forall_forall; unfold tarr_idx; intros ? Htmp; rewrite in_map_iff in Htmp;
        destruct Htmp as [? [? ?]]; subst.
        rewrite Forall_forall in Hinde. specialize (Hinde x0 H2); intros;
        unfold indelE in *; simpl; intros; rewrite <-Hinde; auto.
        rewrite Forall_forall; intros ? Ht; unfold vs2es in Ht; rewrite in_map_iff in Ht.
        destruct Ht as [? [? ?]]; intros; subst.
        prove_inde.
        apply IHl; eauto.
      * rewrite List.nth_overflow in *; [|rewrite add_nth_length, distribute_tup_length..]; 
        prove_inde.
    + rewrite add_nth_overflow in *; (try rewrite distribute_tup_length); auto.
Qed.

Lemma inde_vals_l vs vals :
  List.Forall (fun e => forall v, List.In v vs -> indelE e v) (es2gls (vs2es vals)).
Proof.
  unfold es2gls, vs2es; rewrite map_map, Forall_forall.
  intros x Hx; rewrite in_map_iff in Hx; destruct Hx as [? [? Hx]]; subst.
  intros; auto.
Qed.

Lemma inde_vals vs vals :
  List.Forall (fun e => forall v, List.In v vs -> indeE e v) (vs2es vals).
Proof.
  unfold vs2es; rewrite Forall_forall.
  intros x Hx; rewrite in_map_iff in Hx; destruct Hx as [? [? Hx]]; subst.
  intros; auto.
Qed.

Lemma prefix_cat s1 s2 : prefix s1 (s1 ++ s2) = true.
Proof.
  induction s1; destruct s2; simpl; auto;
  rewrite IHs1; destruct Ascii.ascii_dec; congruence.
Qed.  

Lemma locals_pref grp d x : List.In x (locals grp d) -> prefix grp (str_of_var x) = true.
Proof.
  induction d; simpl; [destruct 1|].
  intros [H|H]; subst; simpl; eauto.
  rewrite prefix_cat; auto.
Qed.

Lemma mps_eq1_tup' (Es : list loc_exp) (E1 E1' : exp) (E2 : list exp) (p : Qc) (s : stack) :
  (E1 === E1') s (emp_ph loc) ->
  s ||= is_tuple_p (tarr_idx Es E1) E2 p <=>
        is_tuple_p (tarr_idx Es E1') E2 p.
Proof.
  revert E2; induction Es; intros [|e E2] Heq; simpl; try reflexivity.
  lets H: (>> mps_eq1' Heq); rewrite H.
  rewrite IHEs; eauto; reflexivity.
Qed.

Section String_lemma.
Open Scope string.
Lemma string_inj2 s1 s2 s1' s2' : s1 = s1' -> s1 ++ s2 = s1' ++ s2' -> s2 = s2'.
Proof.
  revert s1'; induction s1; intros [|? s1']; simpl in *; try congruence; intros.
  inverts H; inverts H0; subst; eauto.
Qed.

Lemma prefix_ex s1 s2 : prefix s1 s2 = true <-> exists s, s2 = s1 ++ s.
Proof.
  revert s1; induction s2; simpl; split; intros.
  - destruct s1; try congruence.
    exists ""; reflexivity.
  - destruct H as [? ?].
    destruct s1; inversion H; eauto.
  - destruct s1.
    + exists (String a s2); reflexivity.
    + destruct Ascii.ascii_dec; try congruence.
      apply IHs2 in H as [? ?]; subst.
      exists x; reflexivity.
  - destruct s1; auto.
    destruct Ascii.ascii_dec.
    + apply IHs2; destruct H as [s ?]; exists s.
      inversion H; eauto.
    + destruct H as [s ?].
      cutrewrite (String a0 s1 ++ s = String a0 (s1 ++ s)) in H; [|auto].
      inversion H; congruence.
Qed.
End String_lemma.

Lemma locals_not_in grp n m:
  n <= m ->
  ~In (Var (grp ++ nat_to_string m)) (locals grp n).
Proof.
  remember nat_to_string as to_s.
  revert m; induction n; simpl; intros [|m]; eauto; try omega.
  intros Hnm [Hc | Hc].
  + inverts Hc as Hc'.
    apply string_inj2 in Hc'; auto.
    subst; apply nat_to_string_inj in Hc'; omega.
  + apply IHn in Hc; eauto; omega.
Qed.        
  
Lemma locals_disjoint_ls grp n : disjoint_list (locals grp n).
Proof.
  induction n; simpl; auto; split; eauto; intros Hc.
  apply locals_not_in in Hc; eauto.
Qed.

Lemma locals_length grp n : length (locals grp n) = n.
Proof. induction n; simpl; auto; rewrite IHn; auto. Qed.

Lemma inde_is_tup_arr Es l f s p vs :
  (forall e v, In e Es -> In v vs -> indelE e v) ->
  inde (is_tuple_array_p Es l f s p) vs.
Proof.
  revert f; induction Es; simpl; intros; eauto.
  prove_inde.
  prove_inde.
  rewrite Forall_forall; intros; apply H; eauto.
  eauto.
Qed.  

Lemma inde_input_spec E Ed p vs :
  (forall v, In v vs -> prefix "arr" (str_of_var v) = false) ->
  (forall v, In v vs -> prefix "sh" (str_of_var v) = false) ->
  inde (input_spec E Ed p) vs.
Proof.
  revert Ed; induction E as [|[? ?] ?]; intros Ed; simpl.
  - intros; prove_inde.
  - intros.
    destruct Ed as [| [[? ?] ?] ?]; [prove_inde|].
    prove_inde; try (rewrite Forall_forall; intros; apply indeE_fv; simpl; eauto).
    intros Hc; destruct Hc as [|[]]; subst.
    apply H0 in H1; simpl in H1; congruence.
    apply inde_eq_tup; rewrite Forall_forall.
    intros.
    unfold es2gls, ss2es in H1; repeat (apply in_map_iff in H1 as [? [? H1]]; subst).
    apply indeE_fv; intros Hc; apply names_of_array_in in H1; destruct Hc as [|[]].
    subst.
    apply H in H2; simpl in H2; congruence.
    apply inde_is_tup_arr; intros.
    apply indelE_fv; intros Hc; simpl in Hc.
    unfold es2gls, vs2es in H1; repeat (apply in_map_iff in H1 as [? [? H1]]; subst).
    eauto.
    apply IHE; eauto.
Qed.

Lemma mps_eq1_tup (E1 : list exp) (E1' : list val) (E : exp) (E2 : list exp) (p : Qc) (s : stack) :
  (E1 ==t E1') s (emp_ph loc) ->
  s ||= is_tuple_p (tarr_idx (es2gls E1) E) E2 p <=>
    is_tuple_p (tarr_idx (es2gls (vs2es E1')) E) E2 p.
Proof.
  revert E1' E2; induction E1; intros [|e1' E1'] [|e2 E2] Heq; simpl in *; try reflexivity;
  try now destruct Heq.
  sep_split_in Heq.
  assert ((Gl a +o E ===l Gl e1' +o E) s (emp_ph loc)) by (unfold_conn_all; simpl in *; congruence).
  rewrite (mps_eq1); [|apply H].
  rewrite IHE1; eauto; reflexivity.
Qed.

Lemma mps_eq2_tup (Es : list loc_exp) E2 E2' (p : Qc) (s : stack) :
  (E2 ==t E2') s (emp_ph loc) ->
  s ||= is_tuple_p Es E2 p <=> is_tuple_p Es (vs2es E2') p.
Proof.
  revert E2 E2'; induction Es; intros [|e E2] [|e' E2'] Heq; simpl in *;
    try first [now destruct Heq | reflexivity | congruence].
  sep_split_in Heq.
  lets H: (>> mps_eq2 HP); rewrite H.
  rewrite IHEs; eauto; reflexivity.
Qed.

Lemma low_assn_eqt E1 E2 G :
  List.Forall (fun e => typing_exp G e Lo) E1 -> low_assn G (E1 ==t E2).
Proof.
  unfold low_assn.
  revert E2; induction E1; simpl; intros [|e2 E2] ?; repeat prove_low_assn; eauto;
  intros; inversion H; subst.
  repeat prove_low_assn; eauto.
  eauto.
Qed.

Lemma low_assn_is_tuple G E1 E2 q :
  List.Forall (fun e => typing_lexp G e Lo) E1 ->
  List.Forall (fun e => typing_exp G e Lo) E2 ->
  low_assn G (is_tuple_p E1 E2 q).
Proof.
  unfold low_assn.
  revert E2; induction E1; intros [|e2 E2]; simpl; rewrite !Forall_forall; intros;
  repeat prove_low_assn.
  apply H; simpl; eauto.
  apply H0; simpl; eauto.
  apply IHE1; rewrite !Forall_forall; intros; [apply H | apply H0]; simpl; eauto.
Qed.

Lemma low_assn_skip_arr_tup G Es n skip f dist i p : forall st,
    Forall (fun e => typing_lexp G e Lo) Es ->
    low_assn G (nth i(distribute_tup skip Es n f dist st p) emp).
Proof.
  unfold low_assn.
  assert (skip = 0 \/ skip <> 0) as [|] by omega.
  - subst; induction n; simpl in *; intros s He.
    destruct i; apply low_assn_emp.
    unfold nt_step; simpl.
    rewrite nth_overflow; [apply low_assn_emp|].
    rewrite add_nth_length, distribute_tup_length; omega.
  - unfold skip_arr; induction n; simpl in *; intros s He.
    + rewrite nth_nseq; destruct leb; apply low_assn_emp.
    + assert (i < skip \/ skip <= i) as [|] by omega.
      assert(dist s < skip \/ skip <= dist s) as [|] by omega.
      rewrite nth_add_nth; [|try rewrite distribute_tup_length; unfold nt_step; eauto..].
      destruct (beq_nat i (dist s)) eqn:Heq.
      apply low_assn_star; eauto.
      apply low_assn_is_tuple.
      rewrite Forall_forall in *; intros x H'.
      unfold tarr_idx in H'; rewrite in_map_iff in H'; destruct H' as [y [? ?]]; subst.
      cutrewrite (Lo = join Lo Lo); [|eauto].
      repeat constructor; eauto.
      unfold vs2es; rewrite Forall_forall; intros ? H'; apply in_map_iff in H' as [? [? ?]]; subst; constructor.
      eauto.
      rewrite add_nth_overflow; [|rewrite distribute_tup_length; eauto].
      apply IHn; auto.
      rewrite nth_overflow.
      apply low_assn_emp.
      rewrite add_nth_length, distribute_tup_length; eauto.
Qed.

Lemma low_assn_is_tup_arr E Es l f s p:
  (forall e, In e Es -> typing_lexp E e Lo) ->
  low_assn E (is_tuple_array_p Es l f s p).
Proof.
  unfold low_assn.
  revert f; induction Es; simpl; intros; eauto.
  prove_low_assn.
  repeat prove_low_assn.
  apply H; eauto.
  eauto.
Qed.  

Lemma low_assn_input_spec E Es Ed p  :
  (forall v, prefix "arr" (str_of_var v) = true -> E v = Lo) ->
  (forall v, prefix "sh" (str_of_var v) = true -> E v = Lo) ->
   low_assn E (input_spec Es Ed p).
Proof.
  unfold low_assn.
  revert Ed; induction Es as [|[? ?] ?]; intros Ed; simpl.
  - intros; prove_low_assn.
  - intros.
    destruct Ed as [| [[? ?] ?] ?]; [prove_low_assn|].
    prove_low_assn; try (rewrite Forall_forall; intros; apply indeE_fv; simpl; eauto).
    repeat prove_low_assn; constructor.
    rewrite H0; auto; simpl; auto.
    repeat prove_low_assn.
    apply low_assn_eqt.
    rewrite Forall_forall; intros; unfold ss2es, names_of_array in H1.
    repeat (apply in_map_iff in H1 as [? [? H1]]; subst).
    apply In_ls_init in H1 as [? [? H1]]; subst.
    repeat constructor.
    rewrite H; eauto.
    apply low_assn_is_tup_arr; intros.
    unfold es2gls, vs2es, names_of_array in H1.
    repeat (apply in_map_iff in H1 as [? [? H1]]; subst).
    repeat constructor.
    eauto.
Qed.

Lemma low_assn_input_spec' E Ed p  :
  low_assn E (input_spec' Ed p).
Proof.
  unfold low_assn.
  induction Ed as [|[[? ?] ?] ?]; simpl.
  - intros; prove_low_assn.
  - intros.
    repeat prove_low_assn; eauto.
    apply low_assn_is_tup_arr; intros.
    unfold es2gls, vs2es in H; simpl in H.
    repeat (rewrite in_map_iff in H; destruct H as [? [? H]]; subst).
    repeat constructor.
Qed.

Lemma read_tup_hi E xs ctys es :
  (forall x, In x xs -> E x = Hi) ->
  typing_cmd E (read_tup xs ctys es) Hi.
Proof.
  revert ctys es; induction xs; intros ctys [|? ?]; simpl; repeat econstructor.
  destruct ctys; intros; eauto.
  destruct ctys; intros; repeat econstructor; eauto; simpl; eauto;
  cbv; rewrite H; eauto.
Qed.

Lemma conj_xs_init_flatten (l1 l2 : nat) (a : assn) :
  forall (s : nat) (stk : stack),
    stk
      ||= conj_xs
      (ls_init s l1
         (fun i : nat =>
            conj_xs (ls_init 0 l2 (fun j : nat => a)))) <=>
      conj_xs (ls_init (s * l2) (l1 * l2) (fun i : nat => a)).
Proof.          
  induction l1; simpl.
  - intros; reflexivity.
  - intros; rewrite IHl1.
    rewrite ls_init_app, conj_xs_app; simpl.
    erewrite ls_init_eq.
    cutrewrite (l2 + s * l2 = s * l2 + l2); [|ring].
    rewrite <-plus_n_O.
    reflexivity.
    intros; simpl; auto.
Qed.
Lemma is_array_skip_arr Es n m len' f p :
  n <> 0 -> m <> 0 ->
  (forall i : nat, i < len' -> length (f i) = length Es) ->
  forall stk, stk ||= 
    is_tuple_array_p Es len' f 0 p <=>
    conj_xs (ls_init 0 n (fun i =>
    conj_xs (ls_init 0 m (fun j =>
    nth (j + i * m) (distribute_tup (n * m) Es len' f (nt_step (n * m)) 0 p) emp)))).
Proof.
  intros.
  lets flat: (>>conj_xs_init_flatten0 n m 
     (fun x => nth x (distribute_tup (n * m) Es len' f (nt_step (n * m)) 0 p) emp)).
  simpl in flat. rewrite flat.
  lets Heq: (>>distribute_correct (n * m) (nt_step (n * m))); rewrite Heq; clear Heq.
  2: unfold nt_step; intros; apply Nat.mod_upper_bound; nia.
  eapply (@equiv_from_nth emp).
  rewrite init_length, distribute_tup_length; ring. 
  rewrite distribute_tup_length; intros i Hi stk'.
  rewrite ls_init_spec; destruct lt_dec; try omega.
  reflexivity.
  auto.
Qed.

Lemma is_tup_array_p1 Es n f s nt stk :
  nt <> 0 ->
  stk ||=
      conj_xs (ls_init 0 nt (fun _ => is_tuple_array_p Es n f s (perm_n nt))) <=>
      is_tuple_array_p Es n f s 1.
Proof.
  revert f; induction Es; simpl; intros f.
  - rewrite init_emp_emp; reflexivity.
  - intros; rewrite ls_star, IHEs.
    rewrite <-is_array_is_array_p_1; eauto.
    rewrite is_array_p1; reflexivity.
    eauto.
Qed.

Lemma input_spec_p1 E Eden n stk :
  length E = length Eden ->
  n <> 0 ->
  stk ||=
      conj_xs (ls_init 0 n (fun _ => input_spec E Eden (perm_n n))) <=>
      input_spec E Eden 1.
Proof.
  revert Eden; induction E as [|[? ?] ?]; intros [|[[? ?] ?] Eden]; simpl in *; try omega.
  - rewrite init_emp_emp; reflexivity.
  - intros.
    repeat rewrite ls_star.
    rewrite IHE; try omega.
    rewrite !ls_pure.
    rewrite is_tup_array_p1; eauto.
    split; intros; repeat sep_cancel; eauto.
    sep_split_in H2; sep_split; eauto.
    eapply (ls_emp _ _ 0) in HP.
    rewrite ls_init_spec in HP; destruct lt_dec; try omega; eauto.
    eapply (ls_emp _ _ 0) in HP0.
    rewrite ls_init_spec in HP0; destruct lt_dec; try omega; eauto.
    sep_split_in H2; sep_split; eauto.
    eapply ls_emp'; rewrite init_length; intros.
    rewrite ls_init_spec; destruct lt_dec; try omega; eauto.
    eapply ls_emp'; rewrite init_length; intros.
    rewrite ls_init_spec; destruct lt_dec; try omega; eauto.
Qed.
Lemma input_spec'_p1 Eden n stk :
  n <> 0 ->
  stk ||=
      conj_xs (ls_init 0 n (fun _ => input_spec' Eden (perm_n n))) <=>
      input_spec' Eden 1.
Proof.
  induction Eden as  [|[[? ?] ?] Eden]; simpl in *; try omega.
  - rewrite init_emp_emp; reflexivity.
  - intros.
    repeat rewrite ls_star.
    rewrite IHEden; try omega.
    rewrite is_tup_array_p1; eauto.
    reflexivity.
Qed.

Lemma writeArray_vars grp dim pl x: 
  pl = Gl \/ pl = Sh ->
  In x (fst (fst (writeArray grp dim pl))) ->
  exists st, (Evar (Var st)) = x /\ prefix "arr" st = true.
Proof.
  unfold writeArray, names_of_arg, names_of_array, ss2es; simpl.
  intros H; rewrite in_map_iff; intros [? [? H']]; rewrite In_ls_init in H';
  destruct H' as [? [? H']]; subst; simpl.
  eexists; split; [reflexivity|].
  simpl; destruct (_ ++ _)%string; eauto.
Qed.

Lemma has_no_vars_is_tup_arr Es l f s p  :
  (forall e, In e Es -> has_no_vars_lE e) ->
  has_no_vars (is_tuple_array_p Es l f s p).
Proof.
  revert f; induction Es; simpl; intros; eauto.
  has_no_vars_assn.
  has_no_vars_assn.
  apply has_no_vars_is_array_p; auto.
  apply IHEs; eauto.
Qed.  

Lemma has_no_vars_input_spec Ed p :
  has_no_vars (input_spec' Ed p).
Proof.
  induction Ed as [|[[? ?] ?] ?]; simpl.
  - has_no_vars_assn.
  - intros.
    has_no_vars_assn.
    apply has_no_vars_is_tup_arr.
    intros.
    unfold es2gls, vs2es in H.
    repeat (apply in_map_iff in H as [? [? H]]; subst); simpl; eauto.
    eauto.
Qed.

Lemma has_no_vars_is_tup es1 es2 p :
  List.Forall (fun e => has_no_vars_lE e) es1 ->
  List.Forall (fun e => has_no_vars_E e) es2 ->
  has_no_vars (is_tuple_p es1 es2 p).
Proof.
  revert es2; induction es1; simpl; intros [| e es2 ]; simpl; intros; try apply has_no_vars_emp.
  inverts H; inverts H0.
  has_no_vars_assn.
  apply has_no_vars_mp; eauto.
  apply IHes1; eauto.
Qed.

Lemma has_no_vars_skip_arr_tup (Es : list loc_exp) (n skip : nat) (f : nat -> list Z) (i st : nat) dist p :
  forall s, 
    Forall (fun e => has_no_vars_lE e) Es ->
    has_no_vars (nth i (distribute_tup skip Es n f dist s p) emp).
Proof.
  induction n; intros s Hinde; simpl in *.
  - simpl_nth; destruct (Compare_dec.leb _ _); prove_inde.
  - assert ( dist s < skip \/ skip <= dist s)%nat as [|] by omega.
    + assert (i < skip \/ skip <= i)%nat as [|] by omega.
      * rewrite nth_add_nth in *; [|rewrite distribute_tup_length; auto..].
        destruct (EqNat.beq_nat _ _); intuition.
        has_no_vars_assn.
        apply has_no_vars_is_tup; auto.
        rewrite Forall_forall; unfold tarr_idx; intros ? Htmp; rewrite in_map_iff in Htmp;
        destruct Htmp as [? [? ?]]; subst.
        rewrite Forall_forall in Hinde; specialize (Hinde x0 H2); intros;
        unfold has_no_vars in *; simpl; intros; split; eauto.
        unfold vs2es; rewrite Forall_forall; unfold tarr_idx; intros ? Htmp; rewrite in_map_iff in Htmp.
        destruct Htmp as [? [? ?]]; subst.
        unfold has_no_vars_E; auto.
        eauto.
      * rewrite List.nth_overflow in *; [|rewrite add_nth_length, distribute_tup_length..]; 
        prove_inde.
    + rewrite add_nth_overflow in *; (try rewrite distribute_tup_length); auto.
Qed.

Lemma not_in_disjoint (T : Type) (l1 l2 : list T)  :
  (forall x, In x l1 -> ~In x l2) -> disjoint l1 l2.
Proof.
  revert l2; induction l1; simpl; eauto.
  intros l2 Hx.
  split.
  - apply Hx; eauto.
  - apply IHl1; intros; eauto.
Qed.

Lemma nth_dist_tup_change i e f1 f2 nt (Hnt0 : nt <> 0) dist q : forall n s,
  i < nt ->
  (forall i, dist i < nt) ->
  (forall j, j < n -> dist (j + s) = i -> f1 (j + s) = f2 (j + s)) ->
  forall stc, stc ||=
  nth i (distribute_tup nt e n f1 dist s q) emp <=> 
  nth i (distribute_tup nt e n f2 dist s q) emp.
Proof.
  induction n; intros s Hint Hdist Hf stc; simpl; [reflexivity|].
  rewrite !nth_add_nth; auto.
  destruct (beq_nat i (dist s)) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    pose (Hf 0) as Hf0; simpl in Hf0; rewrite Hf0; [|omega|auto].
    rewrite IHn; auto; [reflexivity|].
    intros j ?; rewrite <-plus_n_Sm; simpl; apply (Hf (S j)); omega.
  - apply IHn; auto.
    intros j ?; rewrite <-plus_n_Sm; simpl; apply (Hf (S j)); omega.
Qed.

Notation "l '+ol' i" := (tarr_idx l i) (at level 40).
Notation "l '-->l' ( p , e )" := (is_tuple_p l e p) (at level 75, right associativity).

Lemma nseq_in (A : Type) (x : A) y n : In x (nseq n y) -> x = y.
Proof.
  induction n; simpl; try tauto.
  intros [|]; intros; eauto; try congruence.
Qed.

Ltac simplify :=
  unfold vars2es, tarr_idx, vs2es in *;
  repeat (simpl in *; substs; lazymatch goal with
          | [|- In _ (map _ _) -> _] =>
            rewrite in_map_iff; intros [? [? ?]]; substs
          | [H:In _ (map _ _) |-_] =>
            rewrite in_map_iff in H; destruct H as [? [? H]]; substs
          | [|- indeE _ _] => apply indeE_fv
          | [|- indelE _ _] => apply indelE_fv
          | [H : _ \/ False|-_] =>destruct H as [H|[]];substs
          | [H : _ \/ _ |-_] =>destruct H as [?|H]
          | [|- ~(_ \/ _)] => intros [?|?]
          | [|- context [In _ (_ ++ _)]] => rewrite in_app_iff
          | [H : context [In _ (_ ++ _)] |- _] => rewrite in_app_iff in H
          | [|- forall _, _] => intros ?
          | [H : In _ (locals _ _) |- _] => apply locals_pref in H
          | [H : In _ (nseq _ _) |- _] => apply nseq_in in H
          | [H : prefix _ _ = true |- _] => apply prefix_ex in H as [? ?]; substs
          | [|- disjoint_list (locals _ _)] => apply locals_disjoint_ls
          | [|- context [length (locals _ _)]] => rewrite locals_length
          | [H :context [length (locals _ _)]|- _] => rewrite locals_length in H
          | [H :context [length (vars2es _)]|- _] => unfold vars2es in *; rewrite map_length
          | [|- context [length (vars2es _)]] => unfold vars2es; rewrite map_length
          | [H :context [In _ (vars2es _)]|- _] =>
            unfold vars2es in *; rewrite in_map_iff in H;
            destruct H as [? [? H]]; substs
          | [|- context [In _ (vars2es _)]] => unfold vars2es; rewrite in_map_iff
          | [|- Forall _ _] => rewrite Forall_forall; intros
          | [|- indeE _ _] => apply indeE_fv
          | [|- indelE _ _] => apply indelE_fv
          | [|- indeB _ _] => apply indeB_fv
          | [H : context [str_of_var ?x] |- _] => destruct x
          | [|- inde (_ ==t _) _] => apply inde_eq_tup
          | [|- inde (_ -->l (_, _)) _] => apply inde_is_tup
          | [|- inde (is_tuple_array_p _ _ _ _ _) _] => apply inde_is_tup_arr
          | [|- context [length (map _ _)]] => rewrite map_length
          | [H : context [length (map _ _)] |- _] => rewrite map_length in H
          | [H : In _ (names_of_array _ _) |- _] => apply names_of_array_in in H
          | [|- ~_] => intros ?
          end; simpl in *; try substs).

Lemma prefix_nil s : prefix "" s = true. destruct s; eauto. Qed.
