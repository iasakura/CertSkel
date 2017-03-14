Require Import Psatz Classical SetoidClass Qcanon.
Require Import LibTactics.
Require Import PHeap Lang.
Require Import List.

Notation val := Z.
Arguments Z.add _ _ : simpl never.

Coercion Var : string >-> var.
Open Scope string_scope.
Open Scope list_scope.

Close Scope Q_scope.
Close Scope Qc_scope.

Inductive entry := Ent {ent_e : var; ent_v : val}.
Definition ent_assn_denote va (s : stack) : Prop :=
  match va with
  | Ent x v => s x = v
  end.

Definition env_assns_denote env : stack -> Prop :=
  List.fold_right (fun x y => fun s => ent_assn_denote x s /\ y s) (fun s => True) env.

Coercion Evar : var >-> exp.
Coercion Enum : Z >-> exp.

Inductive res :=
| Emp : res
| Mps : loc -> Qc -> val -> res
| Star : res -> res -> res
| TT : res.

Definition loc2lexp (v : loc) :=
  match v with
  | Loc p v => Addr p v
  end.

Coercion loc2lexp : loc >-> loc_exp.

Fixpoint res_denote R (h : pheap) :=
  match R with
  | Emp => forall l, this h l = None
  | Mps cod p dom => forall l, this h l = if eq_dec l cod then Some (p, dom) else None
  | Star r1 r2 => exists h1 h2, res_denote r1 h1 /\ res_denote r2 h2 /\ pdisj h1 h2 /\ phplus h1 h2 = h
  | T => True
  end.

Definition sat_res h R := (res_denote R) h.

Definition equiv_res (P Q : res) := (forall h, sat_res h P <-> sat_res h Q).
Instance equiv_res_equiv : Equivalence (equiv_res).
unfold equiv_res; constructor.
- intros P h; reflexivity.
- intros P Q H h; rewrite H; reflexivity.
- intros P Q R H1 H2 h; forwards*: (H1 h); forwards*: (H2 h); auto.
Qed.

Program Instance res_setoid : Setoid res :=
  {| equiv := equiv_res;
     setoid_equiv := equiv_res_equiv |}.
Instance res_star_proper : Proper (equiv_res ==> equiv_res ==> equiv_res) Star.
Proof.
  intros p1 p2 H p3 p4 H' h; simpl.
  split; intros (h1 & h2 & ? & ? & ? & ?); exists h1 h2; splits; try apply H; try apply H'; eauto.
Qed.

Instance sat_res_proper h : Proper (equiv_res ==> iff) (sat_res h).
Proof.
  intros p q; unfold equiv_res, sat_res; auto.
Qed.

Notation "x |-> v" := (Ent x v) (at level 58).
Notation "l '|->p'  ( p , v )" := (Mps l p v) (at level 58).
Notation "r1 *** r2" := (Star r1 r2) (at level 70, right associativity).
Notation "P '|=R' Q" := (forall (h : pheap), sat_res h P -> sat_res h Q) (at level 87).

Arguments sat_res h R : simpl never.

Eval simpl in sat_res _ ((SLoc 1) |->p (1, 3%Z)).

(*
Res : an assertion for resource
P : an assertion for pure constraint
Env : an assertion for variables/expression bindings
 *)

(* Definition of equivalence between two assertion for rewrite *)

Inductive assn := 
| Assn (Res : res) (P : Prop) (Env : list entry) : assn
| Ex_assn (T : Type) (P : T -> assn) : assn
| Star_assn (P Q : assn) : assn
| Disj_assn (P Q : assn) : assn
| Emp_assn : assn.

Fixpoint assn_denote (P : assn) s h : Prop :=
  match P with
  | Assn R P Env => res_denote R h /\ P /\ env_assns_denote Env s
  | Star_assn P Q => exists h1 h2, assn_denote P s h1 /\ assn_denote Q s h2 /\ pdisj h1 h2 /\ phplus h1 h2 = h
  | Ex_assn T P => exists x, assn_denote (P x) s h
  | Disj_assn P Q => assn_denote P s h \/ assn_denote Q s h
  | Emp_assn => forall l, this h l = None
  end.

Definition sat s h (P : assn) := assn_denote P s h.
Notation "P |= Q" := (forall (s : stack) (h : pheap), sat s h P -> sat s h Q) (at level 87).
Hint Unfold sat.
Arguments sat s h P : simpl never.

Definition equiv_sep (P Q : assn) := (forall s h, sat s h P <-> sat s h Q).
Instance equiv_sep_equiv : Equivalence (equiv_sep).
unfold equiv_sep; constructor.
- intros P s h; reflexivity.
- intros P Q H s h; rewrite H; reflexivity.
- intros P Q R H1 H2 s h; forwards*: (H1 s h); forwards*: (H2 s h); auto.
Qed.

Instance sat_proper s h : Proper (equiv_sep ==> iff) (sat s h).
Proof.
  intros p q; eauto.
Qed.

Notation "P1 ** P2" := (Star_assn P1 P2) (at level 70, right associativity).
Notation "'Ex' x .. y , p" := (Ex_assn (fun x => .. (Ex_assn (fun y => p)) ..))
  (at level 200, x binder, right associativity).                               
Notation "P '\\//' Q" := (Disj_assn P Q) (at level 85, right associativity).

Program Instance assn_setoid : Setoid assn :=
  {| equiv := equiv_sep;
     setoid_equiv := equiv_sep_equiv |}.
Instance star_proper : Proper (equiv_sep ==> equiv_sep ==> equiv_sep) Star_assn.
Proof.
  intros p1 p2 H p3 p4 H' s h.
  unfold sat; simpl.
  split; intros (h1 & h2 & ? & ? & ? & ?); exists h1 h2; splits; try apply H; try apply H'; eauto.
Qed.

Inductive evalExp : list entry -> exp -> val -> Prop :=
| SEval_num env n : evalExp env (Enum n) n
| SEval_Ebinop env op e1 v1 e2 v2 :
    evalExp env e1 v1 -> evalExp env e2 v2 ->
    evalExp env (Ebinop op e1 e2) (binop_exp_denot op v1 v2)%Z
| SEval_var env e v : In (Ent e v) env -> evalExp env e v.

Lemma env_denote_in Env x v :
  In (Ent x v) Env -> forall s, env_assns_denote Env s -> s x = v.
Proof.
  induction Env; simpl; try tauto;
  destruct 1; destruct 1; substs; eauto.
Qed.  

Lemma evalExp_ok (Env : list entry) (e : exp) (v : val) :
  evalExp Env e v -> 
  forall s, env_assns_denote Env s -> edenot e s = v.
Proof.
  induction 1; simpl;
  intros; unfold sat in *;
  try forwards*: IHevalExp1;
  try forwards*: IHevalExp2;
  try forwards*: IHevalExp;
  simpl in *; try congruence;
  substs; auto.
  applys* env_denote_in.
Qed.

Definition loc_off l i := 
  match l with
  | Loc p e => Loc p (e + i)
  end%Z.

Notation "le +o e" := (loc_offset le e) (at level 50, left associativity).

Inductive evalLExp : list entry -> loc_exp -> loc -> Prop :=
| SEval_addr env e p v : 
    evalExp env e v ->
    evalLExp env (Addr p e) (Loc p v)
| SEval_off env e1 e2 v1 v2 :
    evalLExp env e1 v1 ->
    evalExp env e2 v2 ->
    evalLExp env (e1 +o e2) (loc_off v1 v2).

Lemma ledenot_id (l : loc) s : ledenot l s = l.
Proof.
  destruct l; auto.
Qed.

Lemma evalLExp_ok (Env : list entry) (e : loc_exp) (v : loc) :
  evalLExp Env e v ->
  forall s, env_assns_denote Env s -> ledenot e s = v.
Proof.
  induction 1; simpl.
  - intros; forwards*: evalExp_ok; simpl in *; congruence.
  - unfold sat in *; intros; unfold loc_off.
    rewrites* IHevalLExp.
    rewrites* (>>evalExp_ok e2 s).
Qed.

Definition binop_comp_denot_prop (op : binop_comp) :=
  match op with
  | OP_beq => fun x y => x = y
  | OP_blt => fun x y => x < y
  end%Z.

Definition binop_bool_denot_prop (op : binop_bool) :=
  match op with
  | OP_and => fun x y => x /\ y
  | OP_or => fun x y => x \/ y
  end%Z.

Definition unop_bool_denot_prop (op : unop_bool) :=
  match op with
  | OP_not => fun x => ~ x
  end%Z.

Inductive evalBExp : list entry -> bexp -> Prop -> Prop :=
| SEval_comp env op e1 e2 v1 v2 : 
    evalExp env e1 v1 ->
    evalExp env e2 v2 ->
    evalBExp env (Bcomp op e1 e2) (binop_comp_denot_prop op v1 v2)
| Seval_bool env op b1 b2 p1 p2 :
    evalBExp env b1 p1 ->
    evalBExp env b2 p2 ->
    evalBExp env (Bbool op b1 b2) (binop_bool_denot_prop op p1 p2)
| Seval_unop env op b1 p1 :
    evalBExp env b1 p1 ->
    evalBExp env (Bunary op b1) (unop_bool_denot_prop op p1).

Lemma evalBExp_ok (Env : list entry) (e : bexp) (p : Prop) :
  forall s, 
    evalBExp Env e p ->
    (env_assns_denote Env s) ->
    ((bdenot e s = true) <-> p).
Proof.
  intros s.
  induction 1; intros; simpl.
  - forwards*: (>>evalExp_ok e1); simpl in *; substs.
    forwards*: (>>evalExp_ok e2); simpl in *; substs.
    destruct op; split; simpl; lazymatch goal with [|- context [if ?b then _ else _]] => destruct b end; try congruence.
  - destruct op; simpl;
    rewrites* <-(>>IHevalBExp1); rewrites*<-(>>IHevalBExp2);
    destruct (bdenot b1 s), (bdenot b2 s); split; intros;
    try lazymatch goal with
      | [H : _ /\ _ |- _] => destruct H
      | [H : _ \/ _ |- _] => destruct H
      end;
    simpl in *; try congruence; eauto.
  - destruct op; simpl.
    rewrites* <-(>>IHevalBExp).
    destruct (bdenot b1 s); simpl; split; intros; try congruence.
Qed.

Definition remove_var (Env : list entry) (x : var) :=
  filter (fun e => if var_eq_dec x (ent_e e) then false else true) Env.

Lemma remove_var_imp (Env : list entry) x :
  forall s, env_assns_denote Env s -> env_assns_denote (remove_var Env x) s.
Proof.
  induction Env; simpl; eauto.
  intros s [? ?].
  destruct var_eq_dec; simpl;  eauto.
Qed.

Fixpoint fv_E (e : exp) :=
  match e with
    | Evar v => v :: nil
    | Enum n => nil
    | Ebinop op e1 e2 => fv_E e1 ++ fv_E e2
  end.

Fixpoint fv_lE (e : loc_exp) :=
  match e with
  | Sh e
  | Gl e => fv_E e
  | e1 +o e2 => fv_lE e1 ++ fv_E e2
  end.

Fixpoint fv_B (e : bexp) :=
  match e with
  | Bcomp op e1 e2 => fv_E e1 ++ fv_E e2
  | Bbool op b1 b2 => fv_B b1 ++ fv_B b2
  | Bunary op b => fv_B b
  end.

Fixpoint disjoint {T : Type} (l1 l2 : list T) :=
  match l1 with
  | nil => True
  | x :: l1 => ~(List.In x l2) /\ disjoint l1 l2
  end. 

Lemma disjoint_app_r1 (A : Type) (xs ys zs : list A) : disjoint xs (ys ++ zs) -> disjoint xs ys.
Proof.
  induction xs; simpl; eauto.
  intros [H1 H2].
  rewrite in_app_iff in *.
  split; try tauto.
Qed.

Lemma disjoint_app_r2 (A : Type) (xs ys zs : list A) : disjoint xs (ys ++ zs) -> disjoint xs zs.
Proof.
  induction xs; simpl; eauto.
  intros [H1 H2].
  rewrite in_app_iff in *.
  split; try tauto.
Qed.

Definition inde_env (Env : list entry) (xs : list var) := disjoint (map ent_e Env) xs.

Lemma remove_var_inde (Env : list entry) x :
  inde_env (remove_var Env x) (x :: nil).
Proof.
  unfold inde_env; induction Env as [|[x' e] Env]; simpl; eauto.
  destruct var_eq_dec; simpl; eauto.
  split; eauto.
  intros [? | []]; eauto.
Qed.

Lemma disjoint_inde_env (Env : list entry) xs :
  inde_env Env xs ->
  forall s x v,
    In x xs ->
    env_assns_denote Env s ->
    env_assns_denote Env (var_upd s x v).
Proof.
  induction Env as [|[x v] Env]; introv Hinde ?; simpl; eauto.
  unfold inde_env in *; simpl in Hinde.
  unfold var_upd in *; destruct var_eq_dec; intros [? ?]; split; jauto.
  substs; tauto.
Qed.

(* Lemma res_inde (Res : res) s s' h: *)
(*   res_denote Res s h -> res_denote Res s' h. *)
(* Proof. *)
(*   revert h; induction Res; intros; simpl in *; eauto. *)
(*   - unfold sat_res in *; simpl in *; unfold_conn_all; intros; rewrite H; destruct l; eauto. *)
(*   - unfold sat_res in *; simpl in *. *)
(*     destruct H as (? & ? & ? & ? & ? & ?); do 2 eexists; repeat split; eauto; *)
(*     try eapply mps_inde; eauto; try apply IHRes; eauto. *)
(* Qed.     *)

(* Hint Resolve res_inde. *)

(* Coercion assn_denote : assn_deep >-> assn. *)
(* Arguments assn_denote _ _ _ : simpl never. *)

(* Lemma rule_assign ntrd BS (tid : Fin.t ntrd) e x cty (v : val) Env P Res : *)
(*   evalExp Env e v -> *)
(*   CSL BS tid *)
(*       (Assn Res P Env) *)
(*       (x ::T cty ::= e) *)
(*       (Assn Res P (Ent x v :: remove_var Env x)). *)
(* Proof. *)
(*   intros HevalLe. *)
(*   unfold CSL, safe_nt, assn_denote; intros s h Hsat; destruct n; [now (simpl; eauto)|]. *)
(*   unfold Apure in *. *)
(*   sep_split_in Hsat. *)
(*   simpl; repeat split; try congruence. *)
(*   - introv ? ? HC; inverts HC. *)
(*   - introv Hdis Htoh Hred. *)
(*     inverts Hred; inverts EQ1. *)
(*     repeat eexists; repeat split; eauto. *)
(*     apply safe_skip; simpl. *)
(*     unfold has_no_vars, Bdiv.indeP in *; simpl in *. *)
(*     sep_split; try rewrite HnvR; try rewrite HnvP; eauto. *)
(*     cutrewrite (edenot e s0 = v); [|applys (>> evalExp_ok HevalLe); eauto]. *)
(*     unfold_conn; simpl. *)
(*     split. *)
(*     + unfold var_upd in *; destruct var_eq_dec; try congruence. *)
(*     + apply remove_var_inde; simpl in *; auto. *)
(*       applys* remove_var_imp. *)
(* Qed.     *)

(* Lemma rule_read ntrd BS (tid : Fin.t ntrd) le l x cty p (v : val) Env (P : Prop) (Res Res' : res) : *)
(*   evalLExp Env le l -> *)
(*   (P -> (Res |=R l |->p (p, v) *** Res')) -> *)
(*   CSL BS tid *)
(*       (Assn Res P Env) *)
(*       (x ::T cty ::= [le]) *)
(*       (Assn Res P (Ent x v :: remove_var Env x)). *)
(* Proof. *)
(*   intros HevalLe Hres. *)
(*   unfold CSL, safe_nt, assn_denote; intros s h Hsat; destruct n; [now (simpl; eauto)|]. *)
(*   (* destruct Hsat as [HnvR Hsat]; simpl in *. *) *)
(*   unfold Apure in *. *)
(*   sep_split_in Hsat. *)
(*   assert (exists p, PHeap.this h l = Some (p, v)) as [p' Heq]. *)
(*   { forwards* (? & ? & ? & ? & ? & ?): (>> Hres Hsat). *)
(*     simpl in *; unfold_conn_all; simpl in *. *)
(*     rewrite <-H2; unfold phplus. *)
(*     rewrite H; simpl. *)
(*     destruct l; try destruct pl; simpl in *; destruct (eq_dec _ _); try congruence; *)
(*     destruct (PHeap.this x1 _) as [[? ?]|]; eexists; eauto. } *)
(*   assert (Hle : ledenot le s = l). *)
(*   { forwards*: (>>evalLExp_ok HevalLe).  *)
(*     unfold_conn_all; destruct l; simpl in *; auto. } *)
(*   simpl; repeat split; try congruence. *)
(*   - intros hF h' Hdis Htoh HC. *)
(*     inverts HC; simpl in *. *)
(*     apply ptoheap_eq in Htoh. *)
(*     rewrites* (>>htop_eq Htoh) in NIN. *)
(*     unfold phplus in NIN. *)
(*     rewrite Hle, Heq in NIN. *)
(*     destruct (PHeap.this hF l) as [[? ?]|]; congruence. *)
(*   - hnf. *)
(*     eexists; rewrite Hle, Heq; eauto. *)
(*   - introv Hdis Htoh Hred. *)
(*     destruct ss' as [s' h']. *)
(*     inverts Hred; simpl in *. *)
(*     inverts EQ1; inverts EQ2. *)
(*     repeat eexists; eauto. *)
(*     apply safe_skip; simpl. *)
(*     (* (split; eauto). *) *)
(*     unfold has_no_vars, Bdiv.indeP in *; simpl in *. *)
(*     sep_split; try first [rewrite HnvR|rewrite HnvP]; eauto. *)
(*     split. *)
(*     + unfold_conn; auto; simpl. *)
(*       unfold var_upd; destruct (var_eq_dec _ _); try congruence. *)
(*       rewrite Hle in RD. *)
(*       apply ptoheap_eq in Htoh. *)
(*       apply (f_equal (fun x => x l)) in Htoh. *)
(*       unfold phplus, htop in Htoh. *)
(*       simpl in Htoh; unfold htop' in Htoh; rewrite Heq in Htoh. *)
(*       rewrite RD in Htoh. *)
(*       destruct (PHeap.this hF _) as [[? ?] |], (h1 _) as [|]; simpl in *; *)
(*       inverts* Htoh. *)
(*     + apply remove_var_inde; simpl; auto. *)
(*       applys* remove_var_imp. *)
(* Qed. *)

Require Import QArith.
Lemma QcleQ p q : (p <= q)%Qc <-> (p <= q)%Q.
Proof.
  destruct p, q; simpl.
  unfold "<="%Qc; simpl.
  reflexivity.
Qed.
Lemma QcltQ p q : (p < q)%Qc <-> (p < q)%Q.
Proof.
  destruct p, q; simpl.
  unfold "<"%Qc; simpl.
  reflexivity.
Qed.

Lemma this_id (p : Q) H : (Qcanon.this (Qcmake p H) == p)%Q.
Proof.
  destruct p; simpl; reflexivity.
Qed.
Lemma QcplusQ p q : (Qcanon.this (p + q)%Qc == Qcanon.this p + Qcanon.this q)%Q.
Proof.
  unfold "+"%Qc.
  unfold Q2Qc.
  rewrite this_id.
  apply Qred_correct.
Qed.

Ltac lra_Qc :=
  repeat rewrite QcleQ in *; repeat rewrite QcltQ in *;
  repeat rewrite QcplusQ in *; repeat rewrite this_id in *;
  simpl in *; lra.

(* Lemma rule_write ntrd BS (tid : Fin.t ntrd) le l e (v : val) v' Env (P : Prop) (Res Res' : res) :  *)
(*   evalLExp Env le l -> *)
(*   evalExp Env e v' -> *)
(*   (P -> Res |=R ((l |->p (1, v)) *** Res')) -> *)
(*   CSL BS tid  *)
(*       (Assn Res P Env)  *)
(*       ([le] ::= e) *)
(*       (Assn (l |->p (1, v') *** Res') P Env). *)
(* Proof. *)
(*   intros HevalLe Henv Hres. *)
(*   unfold CSL, safe_nt, assn_denote; intros s h Hsat; destruct n; [now (simpl; eauto)|]. *)
(*   (* destruct Hsat as [HnvR Hsat]; simpl in *. *) *)
(*   unfold Apure in *. *)
(*   sep_split_in Hsat. *)
(*   assert (Heq : PHeap.this h l = Some (1%Qc, v)). *)
(*   { forwards* (? & ? & ? & ? & ? & ?): (>> Hres Hsat). *)
(*     simpl in *; unfold_conn_all. *)
(*     rewrite <-H2; unfold phplus. *)
(*     forwards* Heq: (H l). *)
(*     rewrite ledenot_id in Heq; destruct (eq_dec _ _); try congruence. *)
(*     rewrite H; simpl. *)
(*     assert (PHeap.this x0 l = None). *)
(*     { forwards*Hdis: (H1 l); rewrite Heq in Hdis. *)
(*       destruct x0; simpl. *)
(*       forwards*: (is_p  l); simpl in *. *)
(*       destruct (this l) as [[? ?]|]; auto. *)
(*       lra_Qc. } *)
(*     rewrite H3. *)
(*     destruct l; simpl in *; destruct (eq_dec _ _); try congruence; auto. } *)
(*   assert (Hle : ledenot le s = l). *)
(*   { forwards*: (>>evalLExp_ok HevalLe). *)
(*     unfold_conn_all; destruct l; simpl in *; auto. } *)
(*   assert (Hv : edenot e s = v'). *)
(*   { forwards*: (>>evalExp_ok Henv). } *)
(*   simpl; repeat split; try congruence. *)
(*   - intros hF h' Hdis Htoh HC. *)
(*     inverts HC; simpl in *. *)
(*     apply ptoheap_eq in Htoh. *)
(*     rewrites* (>>htop_eq Htoh) in NIN. *)
(*     unfold phplus in NIN. *)
(*     rewrite Hle, Heq in NIN. *)
(*     destruct (PHeap.this hF l) as [[? ?]|]; congruence. *)
(*   - hnf. *)
(*     eexists; rewrite Hle, Heq; eauto. *)
(*   - hnf; eexists; rewrite Hle; eauto. *)
(*   - introv Hdis Htoh Hred. *)
(*     destruct ss' as [s' h']. *)
(*     inverts Hred; simpl in *. *)
(*     inverts EQ1; inverts EQ2. *)
(*     eexists; exists (ph_upd2 h l v'); repeat split. *)
(*     + unfold ph_upd2; simpl; apply (pdisj_upd _ _ Heq); eauto. *)
(*     + unfold ph_upd2; simpl. *)
(*       erewrite ph_upd_phplus; eauto. *)
(*       cutrewrite (phplus h hF = phplus_pheap Hdis); [|simpl; eauto]. *)
(*       rewrite Hle, Hv. *)
(*       apply (@ph_upd_ptoheap ntrd BS); eauto. *)
(*     + apply safe_skip; simpl. *)
(*       (* split; eauto. *) *)
(*       sep_split; eauto. *)
(*       apply Hres in Hsat; eauto. *)
(*       destruct Hsat as (? & ? & ? & ? & ? & ?). *)
(*       exists (ph_upd2 x l v') x0; repeat split; eauto. *)
(*       { simpl in *; unfold_conn_all; intros; rewrite ledenot_id in *. *)
(*         unfold ph_upd2, ph_upd; simpl. *)
(*         specialize (H x1). *)
(*         destruct (eq_dec l x1), (eq_dec x1 l); try congruence; simpl; eauto. } *)
(*       { unfold pdisj, ph_upd2, ph_upd in *; intros x'; specialize (H1 x'); simpl in *. *)
(*         specialize (H x'); rewrite ledenot_id in *; rewrite H in *. *)
(*         destruct x0 as [? ispx0]; simpl in *; clear H0. *)
(*         specialize (ispx0 x'). *)
(*         destruct (eq_dec x' l), (eq_dec l x'), (this x') as [[? ?]|]; simpl in *; *)
(*         repeat split; try congruence; try lra_Qc. } *)
(*       unfold phplus, ph_upd2, ph_upd in *; simpl; extensionality t. *)
(*       rewrite <- H2. *)
(*       destruct (eq_dec _ _); eauto. *)
(*       cutrewrite (PHeap.this x0 t = None); auto. *)
(*       specialize (H t); specialize (H1 t). *)
(*       rewrite H in H1. *)
(*       destruct x0 as [x0 ispx0]; simpl in *; clear H0; specialize (ispx0 t). *)
(*       destruct (x0 t) as [[? ?]|]; subst; repeat rewrite ledenot_id, e0 in *; auto. *)
(*       destruct (eq_dec _ _); try congruence. *)
(*       lra_Qc. *)
(* Qed. *)

(* Lemma rule_if_disj ntrd BS (tid : Fin.t ntrd) b c1 c2 P P1 P2 cond Res Res1 Res2 Env Env1 Env2: *)
(*   evalBExp Env b cond -> *)
(*   CSL BS tid (Assn Res (P /\ cond) Env) c1 (Assn Res1 P1 Env1) -> *)
(*   CSL BS tid (Assn Res (P /\ ~cond) Env) c2 (Assn Res2 P2 Env2) -> *)
(*   CSL BS tid (Assn Res P Env) (Cif b c1 c2) (AssnDisj P1 Res1 Env1 P2 Res2 Env2). *)
(* Proof. *)
(*   intros Heval Hc1 Hc2. *)
(*   apply rule_if_disj; eapply Hbackward; try first [apply Hc1 | apply Hc2]; *)
(*   intros s h Hsat; unfold assn_denote in *; sep_split_in Hsat; *)
(*   sep_split_in Hsat; *)
(*   forwards*: (>>evalBExp_ok Heval); *)
(*   eauto; sep_split; eauto; unfold_conn; try tauto. *)
(*   unfold bexp_to_assn in *; simpl in *. *)
(*   destruct (bdenot b s); simpl in *; try congruence. *)
(*   split; eauto. *)
(*   rewrite <-H; congruence. *)
(* Qed. *)

(* Lemma forward ntrd BS (tid : Fin.t ntrd) P Q Q' C : *)
(*   (Q |= Q') -> *)
(*   CSL BS tid P C Q ->  *)
(*   CSL BS tid P C Q'. *)
(* Proof. *)
(*   intros; eapply Hforward; eauto. *)
(* Qed. *)

(* Lemma backward ntrd BS (tid : Fin.t ntrd) P P' Q C : *)
(*   (P' |= P) -> *)
(*   CSL BS tid P C Q ->  *)
(*   CSL BS tid P' C Q. *)
(* Proof. *)
(*   intros; eapply Hbackward; eauto. *)
(* Qed. *)

(* Lemma rule_disj ntrd BS (tid : Fin.t ntrd) c P P1 P2 Res1 Res2 Env1 Env2: *)
(*   CSL BS tid (Assn Res1 P1 Env1) c P -> *)
(*   CSL BS tid (Assn Res2 P2 Env2) c P -> *)
(*   CSL BS tid (AssnDisj P1 Res1 Env1 P2 Res2 Env2) c P. *)
(* Proof. *)
(*   intros; eapply forward; [|apply rule_disj; eauto]. *)
(*   unfold_conn; unfold sat; simpl; tauto. *)
(* Qed.   *)

Lemma loc_off0 ptr : loc_off ptr 0 = ptr.
Proof.
  destruct ptr; simpl.
  f_equal; omega.
Qed.

Lemma loc_offS ptr n : loc_off ptr (Z.succ n) = loc_off (loc_off ptr 1%Z) n.
Proof.
  destruct ptr; simpl; f_equal; omega.
Qed.

Fixpoint array (ptr : loc) (arr : list val) p :=
  match arr with
  | nil => Emp
  | v :: arr =>
    ptr |->p (p, v) *** array (loc_off ptr 1) arr p
  end.
Close Scope Q_scope.

(* Lemma has_no_vars_mp (l : loc) (v : val) p : has_no_vars (l -->p (p, v)). *)
(* Proof. *)
(*   apply has_no_vars_mp; *)
(*   destruct l; simpl; eauto. *)
(* Qed. *)

(* Lemma has_no_vars_array l vs p : has_no_vars (array l vs p). *)
(* Proof. *)
(*   revert l; induction vs; intros l; simpl; eauto with novars_lemma. *)
(*   apply has_no_vars_star; eauto. *)
(*   apply has_no_vars_mp; simpl; eauto. *)
(* Qed. *)

(* Hint Resolve has_no_vars_array has_no_vars_mp : novars_lemma. *)

Notation Zn := Z.of_nat.

Lemma sep_assoc (P Q R : assn) : (P ** Q ** R) == ((P ** Q) ** R).
Proof.
  intros s h; split; unfold sat; simpl.
  - intros (h1 & h2 & ? & (h3 & h4 & ? & ? & ? & ?) & ? & ?); substs.
    rewrite <-H3 in *.
    assert (pdisj h1 h3) by (eauto using pdisjE1).
    exists (phplus_pheap H6) h4; splits; simpl; jauto.
    apply pdisj_padd_expand; eauto.
    rewrite padd_assoc; eauto.
  - intros (h1 & h2 & (h3 & h4 & ? & ? & ? & ?) & ? & ? & ?); substs.
    rewrite <-H2 in *.
    assert (pdisj h4 h2) by (eauto using pdisjE2).
    exists h3 (phplus_pheap H6); splits; simpl; jauto.
    apply pdisj_padd_expand; eauto.
    rewrite <-padd_assoc; eauto.
Qed.

Lemma res_assoc (P Q R : res) : (P *** Q *** R) == ((P *** Q) *** R).
Proof.
  intros h; split; unfold sat; simpl.
  - intros (h1 & h2 & ? & (h3 & h4 & ? & ? & ? & ?) & ? & ?); substs.
    rewrite <-H3 in *.
    assert (pdisj h1 h3) by (eauto using pdisjE1).
    exists (phplus_pheap H6) h4; splits; simpl; jauto.
    apply pdisj_padd_expand; eauto.
    rewrite padd_assoc; eauto.
  - intros (h1 & h2 & (h3 & h4 & ? & ? & ? & ?) & ? & ? & ?); substs.
    rewrite <-H2 in *.
    assert (pdisj h4 h2) by (eauto using pdisjE2).
    exists h3 (phplus_pheap H6); splits; simpl; jauto.
    apply pdisj_padd_expand; eauto.
    rewrite <-padd_assoc; eauto.
Qed.

Lemma sep_comm (P Q : assn) : (P ** Q) == (Q ** P).
Proof.
  intros s h; split; simpl;
  intros (h1 & h2 & ? & ? & ? & ?); exists h2 h1; splits; jauto;
  rewrites* phplus_comm.
Qed.

Lemma res_comm (P Q : res) : (P *** Q) == (Q *** P).
Proof.
  intros h; split; simpl;
  intros (h1 & h2 & ? & ? & ? & ?); exists h2 h1; splits; jauto;
  rewrites* phplus_comm.
Qed.

Lemma sep_CA (P Q R : assn) : (P ** Q ** R) == (Q ** P ** R).
Proof.
  intros s h; split; unfold sat; simpl.
  - intros (h1 & h2 & ? & (h3 & h4 & ? & ? & ? & ?) & ? & ?); substs.
    rewrite <-H3 in *.
    assert (pdisj h1 h4) by (eauto using pdisjE2).
    exists h3 (phplus_pheap H6); splits; simpl; jauto.
    rewrite padd_left_comm; eauto.
  - intros (h1 & h2 & ? & (h3 & h4 & ? & ? & ? & ?) & ? & ?); substs.
    rewrite <-H3 in *.
    assert (pdisj h1 h4) by (eauto using pdisjE2).
    exists h3 (phplus_pheap H6); splits; simpl; jauto.
    rewrite padd_left_comm; eauto.
Qed.

Lemma res_CA (P Q R : res) : (P *** Q *** R) == (Q *** P *** R).
Proof.
  intros h; split; unfold sat; simpl.
  - intros (h1 & h2 & ? & (h3 & h4 & ? & ? & ? & ?) & ? & ?); substs.
    rewrite <-H3 in *.
    assert (pdisj h1 h4) by (eauto using pdisjE2).
    exists h3 (phplus_pheap H6); splits; simpl; jauto.
    rewrite padd_left_comm; eauto.
  - intros (h1 & h2 & ? & (h3 & h4 & ? & ? & ? & ?) & ? & ?); substs.
    rewrite <-H3 in *.
    assert (pdisj h1 h4) by (eauto using pdisjE2).
    exists h3 (phplus_pheap H6); splits; simpl; jauto.
    rewrite padd_left_comm; eauto.
Qed.

Lemma res_emp_l_unit (P : res) : (Emp *** P) == P.
Proof.
  intros h; split; unfold sat_res; simpl.
  - intros (ph1 & ph2 & Hsat1 & Hsat2 & Hdis & Heq).
    assert (h = ph2).
    { destruct h, ph2; apply pheap_eq; simpl in *; rewrite <-Heq.
      unfold phplus; extensionality x.
      rewrite Hsat1; auto. }
    rewrite H; auto.
  - intros H.
    exists (emp_ph loc) h; repeat split; simpl; auto.
Qed.

Lemma res_emp_r_unit (P : res) : (P *** Emp) == P.
Proof.
  intros h; split; unfold sat_res; simpl.
  - intros (ph1 & ph2 & Hsat1 & Hsat2 & Hdis & Heq).
    assert (h = ph1).
    { destruct h, ph1; apply pheap_eq; simpl in *; rewrite <-Heq.
      unfold phplus; extensionality x.
      rewrite Hsat2; auto.
      destruct (this0 x) as [[? ?]|]; eauto. }
    rewrite H; auto.
  - intros H.
    exists h (emp_ph loc); repeat split; simpl; auto using phplus_emp2.
    apply disj_emp1.
    apply phplus_emp2.
Qed.

Lemma array_unfold i (arr : list val) ptr p:
  i < length arr -> 
  (array ptr arr p) ==
  ((array ptr (firstn i arr) p) ***
   (loc_off ptr (Zn i) |->p (p, nth i arr 0%Z)) ***
   (array (loc_off ptr (Z.succ (Zn i))) (skipn (S i) arr) p)).
Proof.
  simpl; unfold equiv_sep, sat_res, sat;
  revert arr ptr; induction i; intros arr ptr.
  - destruct arr; simpl; try (intros; omega); intros _ h.
    rewrite res_emp_l_unit, loc_off0; reflexivity.
  - destruct arr as [|v arr]; try (simpl; intros; omega).
    intros Hlen' h; simpl in Hlen'; assert (Hlen : i < length arr) by omega.
    rewrite Nat2Z.inj_succ.
    do 2 rewrite loc_offS; simpl.
    rewrite <-!res_assoc, IHi; try omega; reflexivity.
Qed.

(* Ltac fold_sat := *)
(*   match goal with *)
(*   | [|- ?P ?s ?h] => *)
(*     lazymatch type of s with *)
(*     | stack => cutrewrite (P s h = sat s h P); [|reflexivity] *)
(*     end *)
(*   | _ => idtac *)
(*   end. *)

(* Ltac fold_sat_in H := *)
(*   lazymatch type of H with *)
(*   | ?P ?s ?h =>  *)
(*     lazymatch type of s with *)
(*     | stack => cutrewrite (P s h = sat s h P) in H; [|reflexivity] *)
(*     end *)
(*   | _ => idtac *)
(*   end. *)

(* Lemma rule_read_array ntrd BS *)
(*       (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var) *)
(*       (cty : option CTyp) (p : Qc) (Env : list entry)  *)
(*       (P : Prop) (Res Res' : res) (arr : list val) ix i iz: *)
(*   evalLExp Env le l -> *)
(*   evalExp Env ix iz -> *)
(*   Res |=R array l arr p *** Res' -> *)
(*   iz = Zn i -> *)
(*   (P -> i < length arr) -> *)
(*   CSL BS tid *)
(*       (Assn Res P Env) *)
(*       (x ::T cty ::= [le +o ix]) *)
(*       (Assn Res P (Ent x (nth i arr 0%Z) :: (remove_var Env x))). *)
(* Proof. *)
(*   intros. *)
(*   eapply forward; [|applys (>>rule_read (loc_off l iz) p (nth i arr 0%Z) ) ]. *)
(*   2: constructor; eauto. *)
(*   Focus 2. *)
(*   { intros Hp s h Hres. *)
(*     apply H1 in Hres. *)
(*     rewrites* (array_unfold i arr) in Hres; simpl in Hres. *)
(*     repeat rewrite <-res_assoc in *. *)
(*     subst; unfold sat in *; sep_cancel; eauto. *)
(*     rewrite res_CA in Hres. *)
(*     eauto. } Unfocus. *)
(*   auto. *)
(* Qed.  *)

Fixpoint ith_vals {T : Type} (dist : nat -> nat) (vs : list T) i s :=
  match vs with
  | nil => nil
  | v :: vs => (if Nat.eq_dec (dist s) i then Some v else None) ::
               ith_vals dist vs i (S s)
  end.

Fixpoint array' (ptr : loc) (arr : list (option val)) p :=
  match arr with
  | nil => Emp
  | v :: arr =>
    match v with
    | Some v => (ptr |->p (p,  v)) 
    | None => Emp 
    end *** array' (loc_off ptr 1) arr p
  end.

Definition conj_xs : list res -> res := fold_right Star Emp.
Fixpoint ls_init {T : Type} s (n : nat) (f : nat -> T) := 
  match n with
    | O => nil
    | S n => f s :: ls_init (S s) n f
  end%list.

Lemma init_emp_emp (n : nat) : forall b,
  conj_xs (ls_init b n (fun _ => Emp)) == Emp.
Proof.
  induction n; simpl; intros ? h; [reflexivity|].
  rewrite res_emp_l_unit, IHn; reflexivity.
Qed.

Lemma ls_star {n : nat} (P Q : nat -> res) : 
  forall b,
    (conj_xs (ls_init b n (fun i => P i *** Q i))) == 
    (conj_xs (ls_init b n (fun i => P i)) ***
     conj_xs (ls_init b n (fun i => Q i))).
Proof.
  induction n; [simpl; intros |].
  - rewrite res_emp_l_unit; reflexivity.
  - intros s; simpl; rewrite <-!res_assoc, IHn.
    apply res_star_proper; [reflexivity|].
    rewrite res_CA; reflexivity.
Qed.

Lemma conj_xs_app (l1 l2 : list res) :
  conj_xs (l1 ++ l2) == (conj_xs l1 *** conj_xs l2).
Proof.
  induction l1; simpl.
  - rewrite res_emp_l_unit; reflexivity.
  - rewrite IHl1, <-res_assoc; reflexivity.
Qed.

Fixpoint nseq {T : Type} (n : nat) (d : T) : list T :=
  match n with
    | 0 => nil
    | S n => d :: nseq n d
  end.

Lemma nseq_emp_emp (n : nat) :
  conj_xs (nseq n Emp) == Emp.
Proof.
  induction n; simpl.
  - reflexivity.
  - intros; rewrite res_emp_l_unit; auto.
Qed.

(* Lemma array'_ok n ptr dist arr s p : *)
(*   (forall i, dist i < n) -> *)
(*   conj_xs (ls_init 0 n (fun i => res_denote (array' ptr (ith_vals dist arr i s) p))) == *)
(*   res_denote (array ptr arr p). *)
(* Proof. *)
(*   intros H; revert s ptr; induction arr; intros; simpl. *)
(*   - apply init_emp_emp. *)
(*   - rewrite ls_star. *)
(*     rewrite IHarr. *)
(*     unfold array in *; simpl. *)
(*     apply star_proper; try reflexivity. *)
(*     lazymatch goal with *)
(*     | [|- context [ls_init 0 n ?f]] => *)
(*       cutrewrite (ls_init 0 n f = *)
(*                   (ls_init 0 (dist s) (fun _ => emp) ++ *)
(*                   (ptr -->p (p, a)) :: *)
(*                   ls_init ((dist s) + 1) (n - dist s - 1) (fun _ => emp))) *)
(*     end. *)
(*     rewrite conj_xs_app, init_emp_emp; simpl; rewrite init_emp_emp. *)
(*     rewrite emp_unit_l, emp_unit_r; reflexivity. *)
(*     specialize (H s). *)
(*     cutrewrite (n = (dist s) + 1 + (n - dist s - 1)); [| omega]. *)
(*     repeat rewrite ls_init_app; simpl. *)
(*     rewrite <-app_assoc; simpl. *)
(*     f_equal; [apply ls_init_eq'|f_equal]; eauto. *)
(*     intros; simpl; destruct Nat.eq_dec; try omega; eauto. *)
(*     intros; simpl; destruct Nat.eq_dec; try omega; eauto. *)
(*     lazymatch goal with *)
(*     | [|- _ _ ?p _ = _ _ ?q _] => *)
(*       cutrewrite (q = p); [|lia]; *)
(*       apply ls_init_eq'; *)
(*       intros; simpl; destruct Nat.eq_dec; try omega; eauto *)
(*     end. *)
(* Qed.     *)

Notation skip arr n i := (ith_vals (fun x => x mod n) arr i 0).
Notation get v i := (nth i v 0%Z).
Definition option_get {T : Type} (x : option T) d := match x with Some x => x | None => d end.
Notation get' v i := (option_get (nth i v 0%Z) 0%Z).

Lemma ith_vals_length (T : Type) dist (arr : list T) i s :
  length (ith_vals dist arr i s) = length arr.
Proof.
  revert s; induction arr; simpl; eauto.
Qed.

Lemma array'_unfold i arr ptr p:
  i < length arr -> 
  (array' ptr arr p) ==
  ((array' ptr (firstn i arr) p) ***
   (match nth i arr None with
    | Some v => loc_off ptr (Zn i) |->p (p, v)
    | None => Emp
    end) ***
   (array' (loc_off ptr (Z.succ (Zn i))) (skipn (S i) arr) p)).
Proof.
  unfold array.
  revert arr ptr; induction i; intros arr ptr.
  - destruct arr; simpl; try (intros; omega); intros _ h.
    rewrite res_emp_l_unit, loc_off0; reflexivity.
  - destruct arr as [|v arr]; try (simpl; intros; omega).
    intros Hlen'; simpl in Hlen'; assert (Hlen : i < length arr) by omega.
    rewrite Nat2Z.inj_succ.
    do 2 rewrite loc_offS; simpl.
    rewrite IHi; try omega.
    rewrite <-res_assoc; reflexivity.
Qed.

(* Fixpoint distribute (d : nat) (assns : list assn) *)
(*          (dist : nat -> nat) (s : nat) : list assn := *)
(*   match assns with *)
(*   | nil => nseq d emp *)
(*   | a :: assns => *)
(*       add_nth (dist s) a (distribute d assns dist (S s)) *)
(*   end. *)

(* Definition sarray i d ptr arr p s : assn := *)
(*   nth i (distribute d (arrays ptr arr p) (fun x => x mod d) s) emp. *)
  
(* Lemma distribute_length d a dist s: *)
(*   length (distribute d a dist s) = d. *)
(* Proof. *)
(*   revert s; induction a; intros; simpl; *)
(*   [rewrite length_nseq|rewrite add_nth_length]; eauto. *)
(* Qed.   *)

(* Lemma distribute_unfold d assns dist s i j : *)
(*   j < length assns -> *)
(*   dist (s + j) = i ->  *)
(*   (forall i, dist i < d) -> *)
(*   nth i (distribute d assns dist s) emp == *)
(*   (nth i (distribute d (firstn j assns) dist s) emp ** *)
(*    nth j assns emp ** *)
(*    nth i (distribute d (skipn (S j) assns) dist (s + j + 1)) emp). *)
(* Proof. *)
(*   revert s i j; induction assns; intros s i j. *)
(*   - simpl; try omega. *)
(*   - intros Hj Hdist Hi. *)
(*     destruct j. *)
(*     + repeat rewrite <-plus_n_Sm; repeat rewrite <-plus_n_O in *; simpl. *)
(*       rewrite nth_add_nth; [|rewrite distribute_length; substs; eauto..]. *)
(*       subst; rewrite <-beq_nat_refl. *)
(*       rewrite nth_nseq; destruct Compare_dec.leb; *)
(*       rewrite emp_unit_l; reflexivity. *)
(*     + simpl in *. *)
(*       rewrite nth_add_nth; [|rewrite distribute_length; substs; eauto..]. *)
(*       destruct (beq_nat i _) eqn:Heq; [forwards*: beq_nat_true|forwards*: beq_nat_false]. *)
(*       * rewrites* (IHassns (S s) i j); *)
(*         repeat rewrites* <-plus_n_Sm in *; repeat rewrites* <-plus_n_O in *; try omega. *)
(*         rewrite nth_add_nth; [|rewrite distribute_length; substs; eauto..]. *)
(*         destruct (beq_nat i _) eqn:Heq'; [forwards*: beq_nat_true|forwards*: beq_nat_false]; try omega. *)
(*         repeat rewrite <-sep_assoc. *)
(*         reflexivity. *)
(*       * rewrites* (IHassns (S s) i j); *)
(*         repeat rewrites* <-plus_n_Sm in *; repeat rewrites* <-plus_n_O in *; try omega. *)
(*         rewrite nth_add_nth; [|rewrite distribute_length; substs; eauto..]. *)
(*         destruct (beq_nat i _) eqn:Heq'; [forwards*: beq_nat_true|forwards*: beq_nat_false]; try omega. *)
(*         repeat rewrite <-sep_assoc. *)
(*         reflexivity. *)
(* Qed. *)

(* Lemma length_arrays ptr arr p : length (arrays ptr arr p) = length arr. *)
(* Proof. revert ptr; induction arr; intros; simpl; congruence. Qed. *)

(* Lemma firstn_arrays n ptr arr p : firstn n (arrays ptr arr p) = arrays ptr (firstn n arr) p. *)
(* Proof. *)
(*   revert ptr arr; induction n; intros; simpl; eauto. *)
(*   destruct arr; simpl; congruence. *)
(* Qed. *)

(* Lemma skipn_arrays n ptr arr p : skipn n (arrays ptr arr p) = arrays (loc_off ptr (Zn n)) (skipn n arr) p. *)
(* Proof. *)
(*   revert ptr arr; induction n; intros; simpl; eauto. *)
(*   - rewrite loc_off0; eauto. *)
(*   - destruct arr; eauto; simpl. *)
(*     rewrite IHn. *)
(*     unsimpl (Z.of_nat (S n)). *)
(*     rewrite Nat2Z.inj_succ, loc_offS; eauto. *)
(* Qed. *)

(* Lemma nth_arrays n ptr arr p : *)
(*   nth n (arrays ptr arr p) emp = if lt_dec n (length arr) then (loc_off ptr (Zn n) -->p  (p,  (nth n arr 0%Z))) else emp. *)
(* Proof. *)
(*   revert ptr arr; induction n; intros ptr [|? arr]; simpl; eauto. *)
(*   - rewrite loc_off0; eauto. *)
(*   - rewrite IHn; repeat destruct lt_dec; try omega; eauto. *)
(*     unsimpl (Z.of_nat (S n)). *)
(*     rewrite Nat2Z.inj_succ, loc_offS; eauto. *)
(* Qed. *)

Lemma loc_off_nest p i j : 
  loc_off (loc_off p i) j = loc_off p (i + j).
Proof.
  destruct p; simpl; f_equal; omega.
Qed.

(* Lemma sarray_unfold d arr ptr p i j : *)
(*   d <> 0 -> *)
(*   j < length arr -> *)
(*   j mod d = i -> *)
(*   sarray i d ptr arr p 0 == *)
(*   (sarray i d ptr (firstn j arr) p 0 ** *)
(*    (loc_off ptr (Zn j) -->p (p, nth j arr 0%Z)) ** *)
(*    sarray i d (loc_off ptr (Z.succ (Zn j))) (skipn (S j) arr) p (S j)). *)
(* Proof. *)
(*   intros. *)
(*   unfold sarray. *)
(*   rewrites* (>>distribute_unfold d 0 i j); simpl. *)
(*   rewrites* length_arrays. *)
(*   rewrite firstn_arrays. *)
(*   rewrite nth_arrays; destruct lt_dec; try omega. *)
(*   lazymatch goal with *)
(*   | [|- equiv_sep (_ ** _ ** ?P) (_ ** _ ** ?Q)] => *)
(*     assert (Heq: P == Q); [|rewrite Heq; repeat rewrite sep_assoc; reflexivity] *)
(*   end. *)
(*   destruct arr; simpl. *)
(*   - destruct j; simpl; reflexivity. *)
(*   - rewrite <-plus_n_Sm, <-plus_n_O, skipn_arrays, loc_off_nest, Z.add_1_l; reflexivity. *)
(* Qed. *)

Lemma nth_skip T d i (arr : list T) dist j s :
  nth i (ith_vals dist arr j s) None =
  if Nat.eq_dec (dist (s + i)) j then 
    if lt_dec i (length arr) then Some (nth i arr d) 
    else None
  else None.
Proof.
  intros; revert i j s; induction arr; intros ? ?; intros; simpl.
  - destruct i; eauto; destruct Nat.eq_dec; eauto.
  - destruct i; eauto.
    + rewrite <-plus_n_O; destruct lt_dec; try omega; eauto.
    + rewrite <-plus_Snm_nSm; rewrite IHarr.
    repeat match goal with
           | [|- context [if ?b then _ else _]] => destruct b
           end; eauto; try now (destruct i; eauto); omega.
Qed.

(* Lemma rule_read_array' ntrd BS *)
(*       (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var) *)
(*       (cty : option CTyp) (p : Qc) (Env : list entry)  *)
(*       (P : Prop) (Res Res' : res) (arr : list val) dist ix i iz j st: *)
(*   evalLExp Env le l -> *)
(*   evalExp Env ix iz -> *)
(*   Res |=R array' l (ith_vals dist arr j st) p *** Res' -> *)
(*   iz = Zn i -> *)
(*   (P -> i < length arr /\ dist (st + i) = j) -> *)
(*   CSL BS tid *)
(*       (Assn Res P Env) *)
(*       (x ::T cty ::= [le +o ix]) *)
(*       (Assn Res P (Ent x (nth i arr 0%Z) :: (remove_var Env x))). *)
(* Proof. *)
(*   intros. *)
(*   eapply forward; [|applys (>>rule_read (loc_off l iz) p (nth i arr 0%Z) ) ]. *)
(*   2: constructor; eauto. *)
(*   Focus 2. *)
(*   { intros Hp s h Hres. *)
(*     apply H1 in Hres. *)
(*     rewrites* (array'_unfold i) in Hres. *)
(*     2: rewrite ith_vals_length; tauto. *)
(*     cutrewrite (nth i (ith_vals dist arr j st) None = Some (get arr i)) in Hres. *)
(*     repeat rewrite <-res_assoc in *. *)
(*     rewrite res_CA in Hres. *)
(*     subst; eauto. *)
(*     rewrite (nth_skip _ 0%Z); simpl. *)
(*     destruct Nat.eq_dec; try tauto. *)
(*     destruct lt_dec; try tauto. *)
(*   } Unfocus. *)
(*   auto. *)
(* Qed. *)

(* Lemma rule_read_sarray ntrd BS *)
(*       (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var) *)
(*       (cty : option CTyp) (p : Qc) (Env : list entry)  *)
(*       (P : Prop) (Res Res' : res) (arr : list val) ix i iz d j: *)
(*   evalLExp Env le l -> *)
(*   evalExp Env ix iz -> *)
(*   Res |=R array' l (skip arr d j) p *** Res' -> *)
(*   iz = Zn i -> *)
(*   (P -> i < length arr /\ i mod d = j) -> *)
(*   CSL BS tid *)
(*       (Assn Res P Env) *)
(*       (x ::T cty ::= [le +o ix]) *)
(*       (Assn Res P (Ent x (nth i arr 0%Z) :: (remove_var Env x))). *)
(* Proof. *)
(*   intros; eapply rule_read_array'; eauto. *)
(* Qed. *)

Fixpoint set_nth {A : Type} n (ls : list A) (x : A) :=
  match n with
  | 0 => match ls with
         | nil => nil
         | y :: ls' => x :: ls'
         end
  | S n => match ls with
           | nil => nil
           | y :: ls' => y :: set_nth n ls' x
           end
  end.

Lemma nth_set_nth (T : Type) i j (arr : list T) x d:
  nth i (set_nth j arr x) d = if Nat.eq_dec i j then
                                if lt_dec i (length arr) then x
                                else d
                              else nth i arr d.
Proof.
  revert j arr; induction i; destruct arr; intros.
  - destruct Nat.eq_dec; substs; simpl; eauto.
    destruct j; simpl; eauto.
  - destruct Nat.eq_dec; substs; simpl; eauto.
    destruct j; simpl; eauto; omega.
  - destruct j; try now simpl; eauto.
    destruct Nat.eq_dec; simpl; eauto.
  - destruct j; try now simpl; eauto.
    destruct Nat.eq_dec; simpl; eauto.
    destruct lt_dec; eauto.
    inverts e.
    rewrite IHi; destruct Nat.eq_dec.
    destruct lt_dec; eauto; omega.
    omega.
    inverts e.
    rewrite IHi.
    destruct Nat.eq_dec; try omega.
    destruct lt_dec; try omega; eauto.
    rewrite IHi; destruct Nat.eq_dec; try omega.
    auto.
Qed.

Lemma skipn_set_nth_ignore (T : Type) i (ls : list T) x:
  skipn (S i) (set_nth i ls x) = skipn (S i) ls.
Proof.
  revert ls; induction i; simpl; eauto; destruct ls; eauto.
Qed.

Lemma firstn_set_nth_ignore (T : Type) i (ls : list T) x:
  firstn i (set_nth i ls x) = firstn i ls.
Proof.
  revert ls; induction i; simpl; eauto.
  intros ls; destruct ls; simpl; eauto.
  rewrite IHi; eauto.
Qed.    

Lemma length_set_nth (T : Type) i x (xs : list T) : length (set_nth i xs x) = length xs.
Proof.
  revert i; induction xs; destruct i; simpl; eauto.
Qed.

(* Lemma rule_write_array : *)
(*   forall (ntrd : nat) BS *)
(*          (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (e : exp) *)
(*          (v : val) (Env : list entry) (P : Prop) (Res Res' : res) arr ix iz i, *)
(*     evalLExp Env le l -> *)
(*     evalExp Env ix iz -> *)
(*     iz = Zn i -> *)
(*     (P -> i < length arr) -> *)
(*     evalExp Env e v -> *)
(*     Res |=R array l arr 1 *** Res' -> *)
(*     CSL BS tid *)
(*         (Assn Res P Env) *)
(*         ([le +o ix]::=e) *)
(*         (Assn (array l (set_nth i arr v) 1 *** Res') P Env). *)
(* Proof. *)
(*   intros. *)
(*   eapply forward; [|applys (>>rule_write (loc_off l iz) (nth i arr 0%Z))]. *)
(*   2: do 1 constructor; eauto. *)
(*   2: eauto. *)
(*   Focus 2. *)
(*   { intros s h Hp Hsat; apply H4 in Hsat. *)
(*     rewrite (array_unfold i) in Hsat; [|forwards*: H2; lia]. *)
(*     repeat rewrite <-res_assoc in Hsat. *)
(*     rewrite res_CA in Hsat. *)
(*     substs; eauto. } Unfocus. *)
(*   unfold Assn; intros s h Hsat; sep_split_in Hsat. *)
(*   unfold sat in *; sep_split; sep_split_in Hsat; auto. *)
(*   Ltac fold_res_sat := repeat match goal with *)
(*   | [|- res_denote ?P ?s ?h] => cutrewrite (res_denote P s h = sat_res s h P); [|auto] *)
(*   | [H : res_denote ?P ?s ?h |- _] => cutrewrite (res_denote P s h = sat_res s h P) in H; [|auto] *)
(*   end. *)
(*   fold_res_sat. *)
(*   rewrite (array_unfold i); eauto. *)
(*   rewrite firstn_set_nth_ignore. *)
(*   rewrite skipn_set_nth_ignore; substs; repeat sep_cancel. *)
(*   rewrite nth_set_nth; destruct Nat.eq_dec; try omega. *)
(*   destruct lt_dec; try omega. *)
(*   repeat rewrite <-res_assoc; rewrite res_CA; auto. *)
(*   false; apply n; eauto. *)
(*   rewrite length_set_nth in *; unfold_conn; eauto. *)
(* Qed. *)

(* (* Lemma has_no_vars_array' ptr arr p : has_no_vars (array' ptr arr p). *) *)
(* (* Proof. *) *)
(* (*   revert ptr; induction arr; simpl; eauto with novars_lemma. *) *)
(* (*   destruct a; eauto with novars_lemma. *) *)
(* (* Qed. *) *)

(* (* Hint Resolve has_no_vars_array' : novars_lemma. *) *)

Notation set_nth' i arr v := (set_nth i arr (Some v)).

Lemma ith_vals_set_nth T dist ls (x : T) s i:
  ith_vals dist (set_nth i ls x) (dist (s + i)) s =
  set_nth i (ith_vals dist ls (dist (s + i)) s) (Some x).
Proof.
  revert s i; induction ls; simpl; intros s i; simpl; eauto.
  - destruct i; simpl; eauto.
  - destruct i; simpl.
    + rewrite <-plus_n_O; destruct Nat.eq_dec; try omega; eauto.
    + rewrite <-plus_Snm_nSm; rewrite IHls; eauto.
Qed.

Lemma ith_vals_set_nth0 T dist ls (x : T) i j:
  j = dist i ->
  ith_vals dist (set_nth i ls x) j 0 =
  set_nth i (ith_vals dist ls j 0) (Some x).
Proof. intros; substs; forwards*: (>>ith_vals_set_nth x 0). Qed.

(* Lemma rule_write_array'  ntrd BS *)
(*       (tid : Fin.t ntrd) (le : loc_exp) (l : loc)  *)
(*       (Env : list entry) (P : Prop) (Res Res' : res) (arr : list val) dist ix i iz j e v st: *)
(*   evalLExp Env le l -> *)
(*   evalExp Env ix iz -> *)
(*   Res |=R array' l (ith_vals dist arr j st) 1 *** Res' -> *)
(*   evalExp Env e v -> *)
(*   iz = Zn i -> *)
(*   (P -> i < length arr /\ dist (st + i) = j) -> *)
(*   CSL BS tid *)
(*       (Assn Res P Env) *)
(*       ([le +o ix] ::= e) *)
(*       (Assn (array' l (ith_vals dist (set_nth i arr v) j st) 1 *** Res') P Env). *)
(* Proof. *)
(*   intros. *)
(*   eapply forward; [|applys (>>rule_write (loc_off l iz) (nth i arr 0%Z) )]. *)
(*   2: constructor; eauto. *)
(*   2: eauto. *)
(*   Focus 2. *)
(*   { intros s h Hp Hres. *)
(*     apply H1 in Hres. *)
(*     rewrites* (array'_unfold i (ith_vals dist arr j st) l 1) in Hres; [|rewrites* ith_vals_length]. *)
(*     repeat rewrite <-res_assoc in *; substs. *)
(*     rewrite res_CA in Hres. *)
(*     rewrite (nth_skip _ 0%Z) in Hres. *)
(*     forwards*: H4. *)
(*     destruct Nat.eq_dec, (lt_dec i (length arr)); try now (simpl in *; omega). *)
(*     subst; unfold sat in *; sep_cancel; eauto. } Unfocus. *)
(*   unfold Assn; intros s h ?; unfold sat in *. *)
(*   sep_split_in H5; sep_split; eauto. *)
(*   fold_res_sat. *)
(*   rewrites* (>>array'_unfold i l 1%Qc); [rewrite ith_vals_length, length_set_nth; tauto|]. *)
(*   unfold_conn_in HP; forwards*[? ?]: H4; substs. *)
(*   repeat rewrite <-res_assoc in *; substs. *)
(*   rewrite (nth_skip _ 0%Z); destruct Nat.eq_dec; try (simpl in *; omega). *)
(*   destruct lt_dec; try (unfold_conn_all; tauto). *)
(*   2:rewrite length_set_nth in *; tauto. *)
(*   rewrite nth_set_nth; destruct (Nat.eq_dec i i), (lt_dec i (length arr)); try omega. *)
(*   subst; unfold sat in *; repeat sep_cancel; eauto. *)
(*   rewrites* ith_vals_set_nth. *)
(*   rewrite firstn_set_nth_ignore. *)
(*   rewrite skipn_set_nth_ignore. *)
(*   rewrite res_CA in H5. *)
(*   eauto. *)
(* Qed. *)

(* Lemma rule_write_sarray'  ntrd BS *)
(*       (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (Env : list entry)  *)
(*       (P : Prop) (Res Res' : res) (arr : list val) ix i iz d j e v: *)
(*   evalLExp Env le l -> *)
(*   evalExp Env ix iz -> *)
(*   Res |=R array' l (skip arr d j) 1 *** Res' -> *)
(*   evalExp Env e v -> *)
(*   iz = Zn i -> *)
(*   (P -> i < length arr /\ i mod d = j) -> *)
(*   CSL BS tid *)
(*       (Assn Res P Env) *)
(*       ([le +o ix] ::= e) *)
(*       (Assn ((array' l (skip (set_nth i arr v) d j) 1) *** Res') P Env). *)
(* Proof. *)
(*   intros; applys* rule_write_array'. *)
(* Qed. *)

Lemma Ent_eq_dec (e1 e2 : entry) : {e1 = e2} + {e1 <> e2}.
Proof. repeat decide equality. Qed.

(* Lemma env_assns_emp Env s h: *)
(*   env_assns_denote Env s h -> emp s h. *)
(* Proof. *)
(*   induction Env; simpl; eauto. *)
(*   intros [? ?]; eauto. *)
(* Qed. *)

Lemma remove_var_cons x Env :
  forall s, ent_assn_denote x s /\ env_assns_denote (remove Ent_eq_dec x Env) s ->
  env_assns_denote Env s.
Proof.
  induction Env; simpl.
  - intros s [? ?]; eauto.
  - destruct Ent_eq_dec; simpl; substs.
    + intros; split; eauto.
      destruct H; eauto.
    + intros s (? & ? & ?); split; eauto.
Qed.

Lemma in_remove T dec (a : T) x l :
  In a (remove dec x l) -> a <> x /\ In a l.
Proof.
  induction l; simpl; eauto.
  destruct (dec _ _); substs; simpl; intros; split; eauto; try tauto.
  destruct H; substs; eauto; try tauto.
Qed.

Lemma env_incl_imp (Env1 Env2 : list entry ) :
  incl Env2 Env1 ->
  (forall s, env_assns_denote Env1 s -> env_assns_denote Env2 s).
Proof.
  revert Env2; induction Env1 as [|[x v] Env1]; unfold incl; intros Env2.
  - simpl; intros H.
    assert (Env2 = nil).
    { destruct Env2; eauto.
      false; eapply H; simpl; eauto. }
    subst; simpl; eauto.
  - simpl; intros H s Hsat; destruct Hsat as [? Hsat].
    applys (>>remove_var_cons (x |-> v)); simpl.
    split; eauto.
    apply IHEnv1; eauto.
    unfold incl; intros.
    forwards*(? & ?): in_remove.
    forwards*[? | ?]: H; substs.
    congruence.
Qed.

Lemma Assn_imply (Res1 Res2 : res) (P1 P2 : Prop) Env1 Env2 :
  (P1 -> incl Env2 Env1) ->
  (P1 -> (Res1 |=R Res2)) ->
  (P1 -> P2) ->
  Assn Res1 P1 Env1 |= Assn Res2 P2 Env2.
Proof.
  intros Henv HP Hres s h Hsat.
  unfold sat in *; simpl in *.
  destruct Hsat as (? & ? & ?).
  splits; eauto.
  - applys* HP.
  - applys* env_incl_imp.
Qed.

Lemma Assn_split R1 R2 P E :
  Assn (R1 *** R2) P E |=
  Assn R1 P E ** Assn R2 P E.
Proof.
  unfold sat; intros s h H; simpl in *.
  destruct H as ((h1 & h2 & ? & ? & ? & ?) & ? & ?).
  exists h1 h2; splits; jauto.
Qed.

Lemma env_assns_app E1 E2 s:
  (env_assns_denote (E1 ++ E2)) s <->
  (env_assns_denote E1 s /\ env_assns_denote E2 s).
Proof.
  induction E1; simpl; intros.
  - split; intros; try split; try destruct H; eauto.
  - destruct (IHE1); split; intros; tauto.
Qed.

Lemma Assn_combine R1 R2 P1 P2 E1 E2 :
  (Assn R1 P1 E1 ** Assn R2 P2 E2) ==
  Assn (R1 *** R2) (P1 /\ P2) (E1 ++ E2).
Proof.
  intros s h; split.
  - intros (h1 & h2 & Hsat1 & Hsat2 & ? & ?).
    destruct Hsat1 as (? & ? & ?).
    destruct Hsat2 as (? & ? & ?).
    unfold sat; simpl; splits; eauto.
    2: apply env_assns_app; eauto.
    exists h1 h2; tauto.
  - unfold sat; simpl.
    intros ((h1 & h2 & ? & ? & ? & ?) & ? & ?).
    rewrite env_assns_app in *.
    exists h1 h2; splits; jauto.
Qed.

(* Lemma backwardR ntrd BS (tid : Fin.t ntrd) P P' Q C : *)
(*   CSL BS tid P C Q -> P' |= P -> CSL BS tid P' C Q. *)
(* Proof. *)
(*   intros; forwards*: backward. *)
(* Qed. *)

(* Lemma forwardR ntrd BS (tid : Fin.t ntrd) P Q Q' C : *)
(*   CSL BS tid P C Q -> Q |= Q' -> CSL BS tid P C Q'. *)
(* Proof. *)
(*   intros; forwards*: forward. *)
(* Qed. *)

(* Lemma rule_barrier ntrd BS b (i : Fin.t ntrd) Res Res_pre Res_post Res_f P P_pre P_post Env Env_pre Env_post : *)
(*   Vector.nth (fst (BS b)) i = Assn Res_pre P_pre Env_pre -> *)
(*   Vector.nth (snd (BS b)) i = Assn Res_post P_post Env_post -> *)
(*   (Assn Res P Env ===> Assn (Res_pre *** Res_f) P_pre Env_pre) -> *)
(*   CSL BS i *)
(*       (Assn Res P Env) *)
(*       (Cbarrier b) *)
(*       (Assn (Res_f *** Res_post) (P_pre /\ P_post) (Env_pre ++ Env_post)). *)
(* Proof. *)
(*   intros Heq1 Heq2 ?. *)
(*   eapply backward. *)
(*   { intros s h H'. *)
(*     apply H, Assn_split in H'; auto; eauto. } *)
(*   rewrite <- Heq1. *)
(*   eapply forwardR. *)
(*   eapply rule_frame; [| unfold inde; simpl; tauto ]. *)
(*   eapply rule_barrier. *)
(*   rewrite Heq2. *)
(*   intros; apply Assn_combine; eauto. *)
(*   unfold sat in *; repeat sep_cancel. *)
(* Qed.   *)

Definition precise (p : assn) :=
  forall (h1 h2 h1' h2' : pheap) s,
    sat s h1 p -> sat s h1' p ->
    pdisj h1 h2 -> pdisj  h1' h2' ->
    phplus h1 h2 = phplus h1' h2' ->
    h1 = h1'.

Definition precise_res P :=
  forall (h1 h2 h1' h2' : pheap),
    sat_res h1 P ->
    sat_res h2 P ->
    pdisj h1 h1' ->
    pdisj h2 h2' ->
    phplus h1 h1' = phplus h2 h2' -> h1 = h2. 

Lemma precise_sat (P Q : assn) :
  (Q |= P) -> precise P -> precise Q.
Proof.
  unfold precise; simpl; intros Hsat HprecP; introv.
  intros HsatQ HsatQ' ? ? ?.
  eapply HprecP; eauto; apply Hsat; eauto.
Qed.

Lemma precise_assn Res P Env :
  precise_res Res
  -> precise (Assn Res P Env).
Proof.
  unfold precise_res, precise; unfold sat, sat_res; simpl; intros.
  applys* H.
Qed.

Lemma precise_star (P Q : res) : precise_res P -> precise_res Q -> precise_res (P *** Q).
Proof.
  intros pp pq h1 h2 h1' h2' hsat hsat' hdis hdis' heq; simpl in *.
  destruct hsat as [ph1 [ph1' [satp1 [satq1 [Hdis1 Heq1]]]]], 
                   hsat' as [ph2 [ph2' [satp2 [satq2 [Hdis2 Heq2]]]]].
  destruct h1 as [h1 ?], h2 as [h2 ?]; apply pheap_eq; simpl in *; rewrite <-Heq1, <-Heq2 in *.
  apply pdisj_padd_expand in hdis; apply pdisj_padd_expand in hdis'; eauto.
  rewrite !padd_assoc in heq; try tauto. 
  f_equal; destruct hdis as [hdis1 hdis2], hdis' as [hdis1' hdis2'].
  - rewrite (pp ph1 ph2 (phplus_pheap hdis2) (phplus_pheap hdis2')); eauto.
  - rewrite padd_left_comm in heq at 1; try tauto.
    rewrite (@padd_left_comm _ ph2 ph2' h2') in heq; try tauto.
    pose proof (pdisjE2 hdis1 hdis2) as dis12; pose proof (pdisjE2 hdis1' hdis2') as dis12'.
    rewrite (pq ph1' ph2' (phplus_pheap dis12) (phplus_pheap dis12')); simpl in *; eauto; 
    apply pdisj_padd_comm; eauto.
Qed.

Lemma precise_mps l v p :
  precise_res (l |->p (p, v)).
Proof.
  unfold precise_res, precise; intros; simpl in *.
  unfold sat_res in *; simpl in *; simpl in *.
  destruct h1 as [h1 ?], h2 as [h2 ?]; apply pheap_eq.
  extensionality x; simpl in *; rewrite H, H0; auto.
Qed.

Lemma precise_emp :
  precise_res Emp.
Proof.
  unfold precise_res, sat_res, sat; simpl.
  intros; destruct h1 as [h1 ?], h2 as [h2 ?]; apply pheap_eq; simpl in *; eauto.
  extensionality l; rewrite H, H0; eauto.
Qed.

Hint Resolve precise_star precise_mps precise_emp (* precise_false  *)precise_assn.

Lemma precise_array l vs p: 
  precise_res (array l vs p).
Proof.
  revert l; induction vs; simpl; eauto.
Qed.

Lemma precise_array' l vs q :
  precise_res (array' l vs q).
Proof.
  revert l; induction vs as [|[?|] ?]; simpl; eauto.
Qed.              

Hint Resolve precise_star precise_array precise_array'.

(* Lemma emp_unit_l_res P:  *)
(*   (Emp *** P) == P. *)
(* Proof. *)
(*   intros s h; unfold sat_res; simpl. *)
(*   apply emp_unit_l. *)
(* Qed. *)

(* Lemma emp_unit_r_res P:  *)
(*   (P *** Emp) == P. *)
(* Proof. *)
(*   intros s h; unfold sat_res; simpl. *)
(*   apply emp_unit_r. *)
(* Qed. *)

Definition istar ls := List.fold_right Star Emp ls.

Lemma init_emp_emp_res b n :
  istar (ls_init b n (fun _ => Emp)) == Emp.
Proof.
  revert b; induction n; simpl; [reflexivity|]; intros.
  rewrite IHn.
  rewrite res_emp_l_unit; reflexivity.
Qed.

Lemma ls_star_res b n P Q :
  istar (ls_init b n (fun i => P i *** Q i)) ==
  (istar (ls_init b n (fun i => P i)) *** istar (ls_init b n (fun i => Q i))).
Proof.
   revert b; induction n; simpl; eauto.
   - intros; rewrite res_emp_l_unit; reflexivity.
   - intros; rewrite IHn; rewrite <-!res_assoc.
     apply res_star_proper; [reflexivity|].
     rewrite res_CA; reflexivity.
Qed.

Lemma istar_app Ps Qs: 
  istar (Ps ++ Qs) == (istar Ps *** istar Qs).
Proof.
  induction Ps; simpl; eauto.
  rewrite res_emp_l_unit; reflexivity.
  rewrite IHPs, <-res_assoc; reflexivity.
Qed.  
                       
Lemma ls_init_app {T : Type} l1 l2 (f_ini : nat -> T) :
  forall s, 
    ls_init s (l1 + l2) f_ini = ls_init s l1 f_ini ++ ls_init (s + l1) l2 f_ini.
Proof.
  induction l1; simpl.
  - introv; rewrite <-plus_n_O; reflexivity.
  - introv; f_equal.
    rewrite IHl1; do 2 f_equal; omega.
Qed.

Lemma ls_init_eq {T : Type} (fc fc' : nat -> T) n: forall s s',
  (forall i, i < n -> fc (s + i) = fc' (s' + s + i)) -> 
  ls_init s n fc = ls_init (s' + s) n fc'.
Proof.
  induction n; simpl; intros s s' H; auto.
  cutrewrite (s' + s = s' + s + 0); [|omega].
  rewrite <-H; f_equal; (omega || auto).
  cutrewrite (S (s' + s + 0) = s' + S s); [apply IHn|omega].
  intros i Hi.
  cutrewrite (S s + i = s + S i); [|omega].
  cutrewrite (s' + S s + i = s' + s + S i); [|omega].
  apply H; omega.
Qed.

Lemma ls_init_eq' {T : Type} (fc fc' : nat -> T) n: forall s,
  (forall i, i < n -> fc (s + i) = fc' (s + i)) -> 
  ls_init s n fc = ls_init s n fc'.
Proof.
  intros; cutrewrite (s = 0 + s); auto; apply ls_init_eq; simpl.
  apply H.
Qed.

Lemma array'_ok n ptr dist vals s p :
  (forall i, s <= i < length vals + s -> dist i < n) ->
  istar (ls_init 0 n (fun i => array' ptr (ith_vals dist vals i s) p)) ==
  array ptr vals p.
Proof.
  revert s ptr; induction vals; intros; simpl.
  - intros h.
    rewrite init_emp_emp_res; reflexivity.
  - rewrite ls_star_res.
    rewrite IHvals.
    apply res_star_proper; try reflexivity.
    lazymatch goal with
    | [|- context [ls_init 0 n ?f]] =>
      cutrewrite (ls_init 0 n f =
                  (ls_init 0 (dist s) (fun _ => Emp) ++
                  (ptr |->p (p, a)) ::
                  ls_init ((dist s) + 1) (n - dist s - 1) (fun _ => Emp)))
    end.
    rewrite istar_app, init_emp_emp_res; simpl; rewrite init_emp_emp_res.
    rewrite res_emp_l_unit, res_emp_r_unit; reflexivity.
    specialize (H s).
    simpl in *.
    cutrewrite (n = (dist s) + 1 + (n - dist s - 1)); [|omega].
    repeat rewrite ls_init_app; simpl.
    rewrite <-app_assoc; simpl.
    f_equal; [apply ls_init_eq'|f_equal]; eauto.
    intros; simpl; destruct Nat.eq_dec; try omega; eauto.
    intros; simpl; destruct Nat.eq_dec; try omega; eauto.
    lazymatch goal with
    | [|- _ _ ?p _ = _ _ ?q _] =>
      cutrewrite (q = p); [|lia];
      apply ls_init_eq';
      intros; simpl; destruct Nat.eq_dec; try omega; eauto
    end.
    intros; apply H; simpl; omega.
Qed.

Lemma mps_p_star loc v (p1 p2 : Qc) :
  (0 < p1 -> p1 <= 1 -> 0 < p2 -> p2 <= 1 -> p1 + p2 <= 1 ->
   (loc |->p (p1 + p2, v) == (loc |->p (p1, v) *** loc |->p (p2, v))))%Qc.
Proof.
  simpl; unfold equiv_res, sat_res; simpl.
  intros Hp1 Hp1' Hp2 Hp2' H12 ph; split; intros Hsat.
  - set (ph' := fun (p' : Qc) l => match PHeap.this ph l with
                               Some (p, x) => Some (p', x)
                             | None => None end).
    assert (forall (p : Qc) , 0 < p -> p <= 1 -> is_pheap (ph' p))%Qc.
    { intros p H0 H1 l; unfold ph'.
      rewrite Hsat; destruct (eq_dec _ _); eauto. }
    exists (Pheap (H _ Hp1 Hp1')) (Pheap (H _ Hp2 Hp2')); simpl.
    unfold ph'; simpl; repeat split; intros; repeat (rewrite Hsat; destruct (eq_dec _ _); eauto).
    + unfold pdisj; intros; rewrite Hsat; destruct (eq_dec _ _); eauto.
      repeat split; eauto.
      apply plus_gt_0; eauto.
    + destruct ph as [ph ?]; simpl in *; extensionality l; unfold phplus.
      rewrite Hsat; destruct (eq_dec _ _); eauto.
  - destruct Hsat as (ph1 & ph2 & Hph1 & Hph2 & Hdis & Heq).
    intros; rewrite <-Heq; unfold phplus; rewrite Hph1, Hph2.
    destruct (eq_dec _ _); eauto.
Qed.

Lemma array_p_star loc xs p q :
  (0 < p -> p <= 1 -> 0 < q -> q <= 1 -> p + q <= 1 ->
  array loc xs (p + q) == (array loc xs p *** array loc xs q))%Qc.
Proof.
  revert loc; induction xs; simpl; intros.
  - rewrite res_emp_l_unit; reflexivity.
  - rewrites* IHxs.
    rewrite* mps_p_star; eauto.
    rewrite <-!res_assoc, (res_CA (array (loc_off loc 1) xs p)); reflexivity.
Qed.   

Require Import QArith Qcanon.
Definition injZ (n : Z) : Qc := Q2Qc (inject_Z n).
Lemma inject_Z_1 : inject_Z 1 = 1%Q. auto. Qed.
Lemma this_inv q H : Qcanon.this {| Qcanon.this := q; canon := H |} = q. auto. Qed.
Ltac injZ_simplify :=
  unfold injZ in *;
  repeat rewrite Nat2Z.inj_succ in *;
  repeat rewrite <-Z.add_1_r in *;
  repeat rewrite inject_Z_plus in *;
  repeat rewrite inject_Z_1 in *.

Lemma QcmultQ p q : (this (p * q)%Qc == this p * this q)%Q.
Proof.
  unfold "*"%Qc.
  unfold Q2Qc.
  rewrite this_id.
  apply Qred_correct.
Qed.

Lemma inject_Z_n_ge0 n  : (0 <= inject_Z (Z.of_nat n))%Q.
Proof.
  assert (0 <= Z.of_nat n)%Z.
  { cutrewrite (0 = Z.of_nat 0)%Z; [|auto].
    apply inj_le; omega. }
  cutrewrite (0 = inject_Z 0)%Q; [|auto].
  rewrite <-Zle_Qle; auto.
Qed.

Lemma inject_Z_Sn_gt0 n : (1 <= inject_Z (Z.of_nat (S n)))%Q.
Proof.
  injZ_simplify.
  lets: (>>inject_Z_n_ge0 n).
  lra.
Qed.

Lemma is_array_is_array_p_n loc xs (p : Qc) (nt : nat) :
  (0 < p)%Qc -> (p <= 1)%Qc -> (injZ (Zn nt) * p <= 1)%Qc -> (nt <> 0)%nat -> 
  forall st,
    array loc xs (injZ (Z.of_nat nt) * p) == istar (ls_init st nt (fun i => array loc xs p)).
Proof.
  intros Hp0 Hp1 Hnp Hn0; induction nt as [|[|nt]]; intros; try omega.
  - simpl.
    asserts_rewrite (injZ 1 * p = p)%Qc.
    { apply Qc_is_canon.
      rewrite QcmultQ.
      lra_Qc. }
    rewrite res_emp_r_unit; reflexivity.
  - remember (S nt) as nt'.
    asserts_rewrite (Zn (S nt') = Zn nt' + 1)%Z.
     { rewrite Nat2Z.inj_succ; omega. }
     unfold injZ; rewrite inject_Z_plus; simpl.
     asserts_rewrite (Q2Qc (inject_Z (Zn nt') + inject_Z 1) = injZ (Zn nt') + 1).
     { apply Qc_is_canon.
       unfold injZ, "+", Q2Qc.
       rewrite !this_inv.
       rewrite !Qred_correct.
       reflexivity. }
     rewrite Qcmult_plus_distr_l, Qcmult_1_l; eauto; simpl.
Ltac Qc_to_Q :=
  match goal with
  | [q : Qc |- _] => destruct q; Qc_to_Q
  | [|- _] =>
    try applys Qc_is_canon;
    repeat ( unfold Q2Qc, Qcmult, Qcplus, Qcdiv, Qcinv, Qclt, Qcle in *);
    repeat (try rewrite this_inv in *; try rewrite Qred_correct in *)
  end.
     rewrite array_p_star, IHnt; [|clear IHnt; subst nt'; unfold injZ in *; injZ_simplify; Qc_to_Q; eauto; pose proof (inject_Z_n_ge0 nt); try lra..|].
     rewrite res_comm; reflexivity.
     assert (0 <= inject_Z (Zn nt) * this)%Q by (apply Qmult_le_0_compat; lra_Qc).
     lra.
     injZ_simplify.
     Qc_to_Q.
     lra.
Qed.

Lemma one_div_n n : (n <> 0)%nat -> 1 = injZ (Zn n) * (1 / (injZ (Zn n))).
Proof.
  intros; rewrite Qcmult_div_r; eauto.
  intros Hc.
  cutrewrite (0 = injZ (Zn 0%nat)) in Hc;[| auto].
  unfold injZ in Hc.
  unfold Q2Qc in *; apply (f_equal (fun x => Qcanon.this x)) in Hc.
  rewrite !this_inv in Hc.
  assert (Qred (inject_Z (Zn n)) == Qred (inject_Z (Zn 0)))%Q by (rewrite Hc; reflexivity).
  rewrite !Qred_correct in H0.
  rewrite inject_Z_injective in H0.
  rewrite Nat2Z.inj_iff in H0.
  auto.
Qed.

Lemma is_array_is_array_p_1 loc xs (nt : nat) st :
  (nt <> 0)%nat ->
  array loc xs 1 ==
  istar (ls_init st nt (fun i => array loc xs (1 / (injZ (Zn nt))))).
Proof.    
  intros; rewrite (@one_div_n nt) at 1; eauto.
  apply is_array_is_array_p_n; eauto;
  unfold injZ; Qc_to_Q; destruct nt; try omega; lets: (inject_Z_Sn_gt0 nt).
  apply Qlt_shift_div_l; lra.
  apply Qle_shift_div_r; try lra.
  lets Heq: Qmult_div_r; unfold Qdiv in Heq; rewrite Heq; lra.
Qed.