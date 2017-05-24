Require Import GPUCSL scan_lib LibTactics Skel_lemma Psatz Classical.

Notation val := Z.
Arguments Z.add _ _ : simpl never.

Coercion Var : string >-> var.
Open Scope string_scope.
Open Scope list_scope.

(* Definition of equivalence between two assertion for rewrite *)
Require Import SetoidClass.
Definition equiv_sep (P Q : assn) := (forall s h, P s h <-> Q s h).
Instance equiv_sep_equiv : Equivalence (equiv_sep).
unfold equiv_sep; constructor.
- intros P s h; reflexivity.
- intros P Q H s h; rewrite H; reflexivity.
- intros P Q R H1 H2 s h; forwards*: (H1 s h); forwards*: (H2 s h); auto.
Qed.

Program Instance assn_setoid : Setoid assn :=
  {| equiv := equiv_sep;
     setoid_equiv := equiv_sep_equiv |}.
Instance star_proper : Proper (equiv_sep ==> equiv_sep ==> equiv_sep) Astar.
Proof.
  intros p1 p2 H p3 p4 H' h.
  split; apply scRw_stack; intros  h'; firstorder.
Qed.

Definition sat s h (P : assn) := P s h.
Notation "P ===> Q" := (forall (s : stack) (h : pheap), P s h -> Q s h) (at level 87).
Notation "P |= Q" := (forall (s : stack) (h : pheap), sat s h P -> sat s h Q) (at level 87).
Hint Unfold sat.
Instance sat_proper s h : Proper (equiv_sep ==> iff) (sat s h).
Proof.
  intros p q; cbv; auto.
Qed.

Definition loc2lexp (v : loc) :=
  match v with
  | Loc p v => Addr p v
  end.

Coercion loc2lexp : loc >-> loc_exp.

Inductive entry := Ent {ent_e : var; ent_v : val}.
Definition ent_assn_denote va :=
  match va with
  | Ent x v => x === v
  end.

Inductive res :=
| Emp : res
| Mps : loc -> Qc -> val -> res
| Star : res -> res -> res
| T : res.

Fixpoint res_denote m :=
  match m with
  | Emp => emp
  | Mps cod p dom => cod -->p (p, dom)
  | Star r1 r2 => res_denote r1 ** res_denote r2
  | T => TrueP
  end.

Definition sat_res s h m := sat s h (res_denote m).

Definition equiv_res (P Q : res) := (forall s h, sat_res s h P <-> sat_res s h Q).
Instance equiv_res_equiv : Equivalence (equiv_res).
unfold equiv_res; constructor.
- intros P s h; reflexivity.
- intros P Q H s h; rewrite H; reflexivity.
- intros P Q R H1 H2 s h; forwards*: (H1 s h); forwards*: (H2 s h); auto.
Qed.

Program Instance res_setoid : Setoid res :=
  {| equiv := equiv_res;
     setoid_equiv := equiv_res_equiv |}.
Instance res_star_proper : Proper (equiv_res ==> equiv_res ==> equiv_res) Star.
Proof.
  intros p1 p2 H p3 p4 H' h h'; simpl.
  split; apply scRw_stack; intros  h'' ?; try apply H; eauto; try apply H'; eauto.
Qed.

Instance sat_res_proper s h : Proper (equiv_res ==> iff) (sat_res s h).
Proof.
  intros p q; unfold equiv_res, sat_res, sat; auto.
Qed.

Notation "x |-> v" := (Ent x v) (at level 58).
Notation "l '|->p'  ( p , v )" := (Mps l p v) (at level 58).
Notation "r1 *** r2" := (Star r1 r2) (at level 70, right associativity).
Notation "P '|=R' Q" := (forall (s : stack) (h : pheap), sat_res s h P -> sat_res s h Q) (at level 87).

Arguments sat_res s h m : simpl never.

Eval simpl in sat_res _ _ ((SLoc 1) |->p (1, 3%Z)).

Definition env_assns_denote env :=
  List.fold_right (fun x y => ent_assn_denote x //\\ y) emp env.

(*
Res : an assertion for resource
P : an assertion for pure constraint
Env : an assertion for variables/expression bindings
 *)
Definition Assn (Res : res) (P : Prop) (Env : list entry) :=
  res_denote Res ** !(pure P) ** !(env_assns_denote Env).

Inductive evalExp : list entry -> exp -> val -> Prop :=
| SEval_num env n : evalExp env (Enum n) n
| SEval_Ebinop env op e1 v1 e2 v2 :
    evalExp env e1 v1 -> evalExp env e2 v2 ->
    evalExp env (Ebinop op e1 e2) (binop_exp_denot op v1 v2)%Z
| SEval_var env e v : In (Ent e v) env -> evalExp env e v.

Lemma env_denote_in Env e v:
      In (Ent e v) Env -> (env_assns_denote Env ===> (e === v)).
Proof.
  induction Env; simpl; try tauto;
  destruct 1; destruct 1; substs; eauto.
Qed.  

Lemma evalExp_ok (Env : list entry) (e : exp) (v : val) :
  evalExp Env e v -> 
  env_assns_denote Env ===> (e === v).
Proof.
  induction 1; unfold_conn; simpl;
  intros; unfold sat in *;
  try forwards*: IHevalExp1;
  try forwards*: IHevalExp2;
  try forwards*: IHevalExp;
  unfold_conn_all; simpl in *; try congruence;
  substs; auto.
  applys* env_denote_in.
Qed.

Definition loc_off l i := 
  match l with
  | Loc p e => Loc p (e + i)
  end%Z.

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
  env_assns_denote Env ===> (e ===l v).
Proof.
  induction 1; unfold_conn; simpl.
  - intros; forwards*: evalExp_ok; unfold_conn_all; simpl in *; congruence.
  - unfold sat in *; intros; unfold loc_off;
    forwards*: IHevalLExp; unfold_conn_all; rewrite ledenot_id in *; substs.
    forwards*: evalExp_ok; unfold_conn_all; simpl in *; unfold sat in *; substs.
    eauto.
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
  forall s h, 
    evalBExp Env e p ->
    (env_assns_denote Env s h) ->
    ((bexp_to_assn e s h) <-> p).
Proof.
  intros s h.
  induction 1; unfold_conn; intros; simpl.
  - forwards*: (>>evalExp_ok e1); unfold_conn_all; simpl in *; substs.
    forwards*: (>>evalExp_ok e2); unfold_conn_all; simpl in *; substs.
    destruct op; split; simpl; lazymatch goal with [|- context [if ?b then _ else _]] => destruct b end; try congruence.
  - destruct op; simpl;
    rewrites* <-(>>IHevalBExp1); rewrites*<-(>>IHevalBExp2);
    unfold bexp_to_assn;
    destruct (bdenot b1 s), (bdenot b2 s); split; intros;
    try lazymatch goal with
      | [H : _ /\ _ |- _] => destruct H
      | [H : _ \/ _ |- _] => destruct H
      end;
    simpl in *; try congruence; eauto.
  - destruct op; simpl.
    rewrites* <-(>>IHevalBExp).
    unfold_conn.
    destruct (bdenot b1 s); simpl; split; intros; try congruence.
Qed.

Definition remove_var (Env : list entry) (x : var) :=
  filter (fun e => if var_eq_dec x (ent_e e) then false else true) Env.

Lemma remove_var_imp (Env : list entry) x :
  env_assns_denote Env ===> env_assns_denote (remove_var Env x).
Proof.
  induction Env; simpl; eauto.
  intros s h [? ?].
  destruct var_eq_dec; simpl;  eauto.
  split; eauto.
Qed.

Lemma remove_var_inde (Env : list entry) x :
  inde (env_assns_denote (remove_var Env x)) (x :: nil).
Proof.
  induction Env; simpl; prove_inde.
  destruct var_eq_dec; simpl; prove_inde.
  destruct a; simpl in *.
  apply inde_eeq; rewrite Forall_forall; intros;
  apply indeE_fv; simpl; eauto.
  simpl in *; destruct H as [? | []]; intros [? | []]; congruence.
Qed.

Definition fv_env (Env : list entry) := 
  List.fold_right (fun x e => fv_E (ent_e x) ++ e) nil Env.

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

Lemma disjoint_inde_env (Env : list entry) xs :
  disjoint xs (fv_env Env) ->
  inde (env_assns_denote Env) xs.
Proof.
  induction Env; intros Hdis; simpl; prove_inde.
  - destruct a; simpl in *.
    prove_inde; rewrite Forall_forall; eauto; intros.
    apply indeE_fv; intros Hc; simpl in *.
    destruct Hc as [|[]]; substs.
    apply disjoint_comm in Hdis; simpl in *; tauto.
  - simpl in Hdis.
    apply disjoint_comm in Hdis; simpl in *.
    apply IHEnv, disjoint_comm; tauto.
Qed.

Lemma res_inde (Res : res) s s' h:
  res_denote Res s h -> res_denote Res s' h.
Proof.
  revert h; induction Res; intros; simpl in *; eauto.
  - unfold sat_res in *; simpl in *; unfold_conn_all; intros; rewrite H; destruct l; eauto.
  - unfold sat_res in *; simpl in *.
    destruct H as (? & ? & ? & ? & ? & ?); do 2 eexists; repeat split; eauto;
    try eapply mps_inde; eauto; try apply IHRes; eauto.
Qed.    

Hint Resolve res_inde.

Lemma rule_assign ntrd BS (tid : Fin.t ntrd) e x cty (v : val) Env P Res :
  evalExp Env e v ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= e)
      (Assn Res P (Ent x v :: remove_var Env x)).
Proof.
  intros HevalLe.
  unfold CSL, safe_nt, Assn; intros s h Hsat; destruct n; [now (simpl; eauto)|].
  unfold Apure in *.
  sep_split_in Hsat.
  simpl; repeat split; try congruence.
  - introv ? ? HC; inverts HC.
  - introv Hdis Htoh Hred.
    inverts Hred; inverts EQ1.
    repeat eexists; repeat split; eauto.
    apply safe_skip; simpl.
    unfold has_no_vars, Bdiv.indeP in *; simpl in *.
    sep_split; try rewrite HnvR; try rewrite HnvP; eauto.
    cutrewrite (edenot e s0 = v); [|applys (>> evalExp_ok HevalLe); eauto].
    unfold_conn; simpl.
    split.
    + unfold var_upd in *; destruct var_eq_dec; try congruence.
    + apply remove_var_inde; simpl in *; auto.
      applys* remove_var_imp.
Qed.    

Lemma rule_read ntrd BS (tid : Fin.t ntrd) le l x cty p (v : val) Env (P : Prop) (Res Res' : res) :
  evalLExp Env le l ->
  (P -> (Res |=R l |->p (p, v) *** Res')) ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= [le])
      (Assn Res P (Ent x v :: remove_var Env x)).
Proof.
  intros HevalLe Hres.
  unfold CSL, safe_nt, Assn; intros s h Hsat; destruct n; [now (simpl; eauto)|].
  (* destruct Hsat as [HnvR Hsat]; simpl in *. *)
  unfold Apure in *.
  sep_split_in Hsat.
  assert (exists p, PHeap.this h l = Some (p, v)) as [p' Heq].
  { forwards* (? & ? & ? & ? & ? & ?): (>> Hres Hsat).
    simpl in *; unfold_conn_all; simpl in *.
    rewrite <-H2; unfold phplus.
    rewrite H; simpl.
    destruct l; try destruct pl; simpl in *; destruct (eq_dec _ _); try congruence;
    destruct (PHeap.this x1 _) as [[? ?]|]; eexists; eauto. }
  assert (Hle : ledenot le s = l).
  { forwards*: (>>evalLExp_ok HevalLe). 
    unfold_conn_all; destruct l; simpl in *; auto. }
  simpl; repeat split; try congruence.
  - intros hF h' Hdis Htoh HC.
    inverts HC; simpl in *.
    apply ptoheap_eq in Htoh.
    rewrites* (>>htop_eq Htoh) in NIN.
    unfold phplus in NIN.
    rewrite Hle, Heq in NIN.
    destruct (PHeap.this hF l) as [[? ?]|]; congruence.
  - hnf.
    eexists; rewrite Hle, Heq; eauto.
  - introv Hdis Htoh Hred.
    destruct ss' as [s' h'].
    inverts Hred; simpl in *.
    inverts EQ1; inverts EQ2.
    repeat eexists; eauto.
    apply safe_skip; simpl.
    (* (split; eauto). *)
    unfold has_no_vars, Bdiv.indeP in *; simpl in *.
    sep_split; try first [rewrite HnvR|rewrite HnvP]; eauto.
    split.
    + unfold_conn; auto; simpl.
      unfold var_upd; destruct (var_eq_dec _ _); try congruence.
      rewrite Hle in RD.
      apply ptoheap_eq in Htoh.
      apply (f_equal (fun x => x l)) in Htoh.
      unfold phplus, htop in Htoh.
      simpl in Htoh; unfold htop' in Htoh; rewrite Heq in Htoh.
      rewrite RD in Htoh.
      destruct (PHeap.this hF _) as [[? ?] |], (h1 _) as [|]; simpl in *;
      inverts* Htoh.
    + apply remove_var_inde; simpl; auto.
      applys* remove_var_imp.
Qed.

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

Lemma this_id (p : Q) H : (this (Qcmake p H) == p)%Q.
Proof.
  destruct p; simpl; reflexivity.
Qed.
Lemma QcplusQ p q : (this (p + q)%Qc == this p + this q)%Q.
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

Lemma rule_write ntrd BS (tid : Fin.t ntrd) le l e (v : val) v' Env (P : Prop) (Res Res' : res) : 
  evalLExp Env le l ->
  evalExp Env e v' ->
  (P -> Res |=R ((l |->p (1, v)) *** Res')) ->
  CSL BS tid 
      (Assn Res P Env) 
      ([le] ::= e)
      (Assn (l |->p (1, v') *** Res') P Env).
Proof.
  intros HevalLe Henv Hres.
  unfold CSL, safe_nt, Assn; intros s h Hsat; destruct n; [now (simpl; eauto)|].
  (* destruct Hsat as [HnvR Hsat]; simpl in *. *)
  unfold Apure in *.
  sep_split_in Hsat.
  assert (Heq : PHeap.this h l = Some (1%Qc, v)).
  { forwards* (? & ? & ? & ? & ? & ?): (>> Hres Hsat).
    simpl in *; unfold_conn_all.
    rewrite <-H2; unfold phplus.
    forwards* Heq: (H l).
    rewrite ledenot_id in Heq; destruct (eq_dec _ _); try congruence.
    rewrite H; simpl.
    assert (PHeap.this x0 l = None).
    { forwards*Hdis: (H1 l); rewrite Heq in Hdis.
      destruct x0; simpl.
      forwards*: (is_p  l); simpl in *.
      destruct (this l) as [[? ?]|]; auto.
      lra_Qc. }
    rewrite H3.
    destruct l; simpl in *; destruct (eq_dec _ _); try congruence; auto. }
  assert (Hle : ledenot le s = l).
  { forwards*: (>>evalLExp_ok HevalLe).
    unfold_conn_all; destruct l; simpl in *; auto. }
  assert (Hv : edenot e s = v').
  { forwards*: (>>evalExp_ok Henv). }
  simpl; repeat split; try congruence.
  - intros hF h' Hdis Htoh HC.
    inverts HC; simpl in *.
    apply ptoheap_eq in Htoh.
    rewrites* (>>htop_eq Htoh) in NIN.
    unfold phplus in NIN.
    rewrite Hle, Heq in NIN.
    destruct (PHeap.this hF l) as [[? ?]|]; congruence.
  - hnf.
    eexists; rewrite Hle, Heq; eauto.
  - hnf; eexists; rewrite Hle; eauto.
  - introv Hdis Htoh Hred.
    destruct ss' as [s' h'].
    inverts Hred; simpl in *.
    inverts EQ1; inverts EQ2.
    eexists; exists (ph_upd2 h l v'); repeat split.
    + unfold ph_upd2; simpl; apply (pdisj_upd _ _ Heq); eauto.
    + unfold ph_upd2; simpl.
      erewrite ph_upd_phplus; eauto.
      cutrewrite (phplus h hF = phplus_pheap Hdis); [|simpl; eauto].
      rewrite Hle, Hv.
      apply (@ph_upd_ptoheap ntrd BS); eauto.
    + apply safe_skip; simpl.
      (* split; eauto. *)
      sep_split; eauto.
      apply Hres in Hsat; eauto.
      destruct Hsat as (? & ? & ? & ? & ? & ?).
      exists (ph_upd2 x l v') x0; repeat split; eauto.
      { simpl in *; unfold_conn_all; intros; rewrite ledenot_id in *.
        unfold ph_upd2, ph_upd; simpl.
        specialize (H x1).
        destruct (eq_dec l x1), (eq_dec x1 l); try congruence; simpl; eauto. }
      { unfold pdisj, ph_upd2, ph_upd in *; intros x'; specialize (H1 x'); simpl in *.
        specialize (H x'); rewrite ledenot_id in *; rewrite H in *.
        destruct x0 as [? ispx0]; simpl in *; clear H0.
        specialize (ispx0 x').
        destruct (eq_dec x' l), (eq_dec l x'), (this x') as [[? ?]|]; simpl in *;
        repeat split; try congruence; try lra_Qc. }
      unfold phplus, ph_upd2, ph_upd in *; simpl; extensionality t.
      rewrite <- H2.
      destruct (eq_dec _ _); eauto.
      cutrewrite (PHeap.this x0 t = None); auto.
      specialize (H t); specialize (H1 t).
      rewrite H in H1.
      destruct x0 as [x0 ispx0]; simpl in *; clear H0; specialize (ispx0 t).
      destruct (x0 t) as [[? ?]|]; subst; repeat rewrite ledenot_id, e0 in *; auto.
      destruct (eq_dec _ _); try congruence.
      lra_Qc.
Qed.

Definition AssnDisj Res1 P1 Env1 Res2 P2 Env2 :=
  Assn P1 Res1 Env1 \\// Assn P2 Res2 Env2. 

Lemma rule_if_disj ntrd BS (tid : Fin.t ntrd) b c1 c2 P P1 P2 cond Res Res1 Res2 Env Env1 Env2:
  evalBExp Env b cond ->
  CSL BS tid (Assn Res (P /\ cond) Env) c1 (Assn Res1 P1 Env1) ->
  CSL BS tid (Assn Res (P /\ ~cond) Env) c2 (Assn Res2 P2 Env2) ->
  CSL BS tid (Assn Res P Env) (Cif b c1 c2) (AssnDisj P1 Res1 Env1 P2 Res2 Env2).
Proof.
  intros Heval Hc1 Hc2.
  apply rule_if_disj; eapply Hbackward; try first [apply Hc1 | apply Hc2];
  intros s h Hsat; unfold Assn in *; sep_split_in Hsat;
  sep_split_in Hsat;
  forwards*: (>>evalBExp_ok Heval);
  eauto; sep_split; eauto; unfold_conn; try tauto.
  unfold bexp_to_assn in *; simpl in *.
  destruct (bdenot b s); simpl in *; try congruence.
  split; eauto.
  rewrite <-H; congruence.
Qed.

Lemma forward ntrd BS (tid : Fin.t ntrd) P Q Q' C :
  (Q |= Q') ->
  CSL BS tid P C Q -> 
  CSL BS tid P C Q'.
Proof.
  intros; eapply Hforward; eauto.
Qed.

Lemma backward ntrd BS (tid : Fin.t ntrd) P P' Q C :
  (P' |= P) ->
  CSL BS tid P C Q -> 
  CSL BS tid P' C Q.
Proof.
  intros; eapply Hbackward; eauto.
Qed.

Lemma rule_disj ntrd BS (tid : Fin.t ntrd) c P P1 P2 Res1 Res2 Env1 Env2:
  CSL BS tid (Assn Res1 P1 Env1) c P ->
  CSL BS tid (Assn Res2 P2 Env2) c P ->
  CSL BS tid (AssnDisj P1 Res1 Env1 P2 Res2 Env2) c P.
Proof.
  intros; eapply forward; [|apply rule_disj; eauto].
  unfold_conn; unfold sat; simpl; tauto.
Qed.  

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

Lemma array_unfold i arr ptr p:
  i < length arr -> 
  (array ptr arr p) ==
  ((array ptr (firstn i arr) p) ***
   (loc_off ptr (Zn i) |->p (p, nth i arr 0%Z)) ***
   (array (loc_off ptr (Z.succ (Zn i))) (skipn (S i) arr) p)).
Proof.
  simpl; unfold equiv_sep, sat_res, sat;
  revert arr ptr; induction i; intros arr ptr.
  - destruct arr; simpl; try (intros; omega); intros _ s h; unfold sat_res, sat in *; simpl.
    split; intros; sep_normal; sep_normal_in H; rewrite loc_off0 in *; eauto. 
  - destruct arr as [|v arr]; try (simpl; intros; omega).
    intros Hlen'; simpl in Hlen'; assert (Hlen : i < length arr) by omega.
    rewrite Nat2Z.inj_succ.
    do 2 rewrite loc_offS; simpl.
    split; unfold sat_res, sat in *; unfold sat_res, sat in *;
    intros; simpl in *; sep_normal; sep_normal_in H; repeat sep_cancel.
    apply IHi in H0; sep_normal_in H0; eauto.
    apply IHi; sep_normal; eauto.
Qed.

Lemma sep_assoc (P Q R : assn) : (P ** Q ** R) == ((P ** Q) ** R).
Proof.
  split; intros; apply sep_assoc; auto.
Qed.

Lemma res_assoc (P Q R : res) : (P *** Q *** R) == ((P *** Q) *** R).
Proof.
  split; intros; apply sep_assoc; auto.
Qed.

Lemma sep_comm (P Q : assn) : (P ** Q) == (Q ** P).
Proof.
  split; apply scC; auto.
Qed.

Lemma res_comm (P Q : res) : (P *** Q) == (Q *** P).
Proof.
  split; apply scC; auto.
Qed.

Lemma res_CA (P Q R : res) : (P *** Q *** R) == (Q *** P *** R).
Proof.
  split; apply scCA; eauto.
Qed.

Ltac fold_sat :=
  match goal with
  | [|- ?P ?s ?h] =>
    lazymatch type of s with
    | stack => cutrewrite (P s h = sat s h P); [|reflexivity]
    end
  | _ => idtac
  end.

Ltac fold_sat_in H :=
  lazymatch type of H with
  | ?P ?s ?h => 
    lazymatch type of s with
    | stack => cutrewrite (P s h = sat s h P) in H; [|reflexivity]
    end
  | _ => idtac
  end.

Lemma rule_read_array ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var)
      (cty : option CTyp) (p : Qc) (Env : list entry) 
      (P : Prop) (Res Res' : res) (arr : list val) ix i iz:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array l arr p *** Res' ->
  iz = Zn i ->
  (P -> i < length arr) ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= [le +o ix])
      (Assn Res P (Ent x (nth i arr 0%Z) :: (remove_var Env x))).
Proof.
  intros.
  eapply forward; [|applys (>>rule_read (loc_off l iz) p (nth i arr 0%Z) ) ].
  2: constructor; eauto.
  Focus 2.
  { intros Hp s h Hres.
    apply H1 in Hres.
    rewrites* (array_unfold i arr) in Hres; simpl in Hres.
    repeat rewrite <-res_assoc in *.
    subst; unfold sat in *; sep_cancel; eauto.
    rewrite res_CA in Hres.
    eauto. } Unfocus.
  auto.
Qed. 

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

Lemma init_emp_emp (n : nat) : forall b,
  conj_xs (ls_init b n (fun _ => emp)) == emp.
Proof.
  induction n; simpl; intros; [reflexivity|].
  split; intros H.
  sep_rewrite_in IHn H. sep_rewrite_in emp_unit_l H; auto.
  sep_rewrite IHn; sep_rewrite emp_unit_l; auto.
Qed.

Lemma ls_star {n : nat} (P Q : nat -> assn) : 
  forall b,
    (conj_xs (ls_init b n (fun i => P i ** Q i))) == 
    (conj_xs (ls_init b n (fun i => P i)) **
     conj_xs (ls_init b n (fun i => Q i))).
Proof.
  induction n; [simpl; intros |].
  - split; intros; [sep_rewrite_in_r emp_unit_l H | sep_rewrite_in emp_unit_l H]; auto.
  - intros s; split; simpl; intros H.
    + sep_normal_in H; sep_normal; repeat sep_cancel.
      sep_rewrite_in IHn H1; auto.
    + sep_normal_in H; sep_normal; repeat sep_cancel.
      sep_rewrite_in_r IHn H1; auto.
Qed.

Lemma conj_xs_app (l1 l2 : list assn) :
  conj_xs (l1 ++ l2) == (conj_xs l1 ** conj_xs l2).
Proof.
  induction l1; simpl.
  split; intros H; sep_normal; sep_normal_in H; auto.
  intros; rewrite IHl1, sep_assoc; reflexivity.
Qed.

Lemma emp_unit_l P : (emp ** P) == P.
Proof.
  intros s h; split; intros; apply emp_unit_l; auto.
Qed.

Lemma emp_unit_r P : (P ** emp) == P.
Proof.
  intros s h; split; intros; apply emp_unit_r; auto.
Qed.    

Lemma nseq_emp_emp (n : nat) :
  conj_xs (nseq n emp) == emp.
Proof.
  induction n; simpl.
  - reflexivity.
  - intros; rewrite emp_unit_l; auto.
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
  simpl; unfold equiv_res, sat_res, sat;
  revert arr ptr; induction i; intros arr ptr.
  - destruct arr; simpl; try (intros; omega); intros _ s h.
    split; intros; sep_normal; sep_normal_in H; rewrite loc_off0 in *; eauto. 
  - destruct arr as [|v arr]; try (simpl; intros; omega).
    intros Hlen'; simpl in Hlen'; assert (Hlen : i < length arr) by omega.
    rewrite Nat2Z.inj_succ.
    do 2 rewrite loc_offS; simpl.
    split; intros; sep_normal; sep_normal_in H; repeat sep_cancel.
    rewrites* IHi in H0.
    rewrites* IHi.
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

Lemma rule_read_array' ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var)
      (cty : option CTyp) (p : Qc) (Env : list entry) 
      (P : Prop) (Res Res' : res) (arr : list val) dist ix i iz j st:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array' l (ith_vals dist arr j st) p *** Res' ->
  iz = Zn i ->
  (P -> i < length arr /\ dist (st + i) = j) ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= [le +o ix])
      (Assn Res P (Ent x (nth i arr 0%Z) :: (remove_var Env x))).
Proof.
  intros.
  eapply forward; [|applys (>>rule_read (loc_off l iz) p (nth i arr 0%Z) ) ].
  2: constructor; eauto.
  Focus 2.
  { intros Hp s h Hres.
    apply H1 in Hres.
    rewrites* (array'_unfold i) in Hres.
    2: rewrite ith_vals_length; tauto.
    cutrewrite (nth i (ith_vals dist arr j st) None = Some (get arr i)) in Hres.
    repeat rewrite <-res_assoc in *.
    rewrite res_CA in Hres.
    subst; eauto.
    rewrite (nth_skip _ 0%Z); simpl.
    destruct Nat.eq_dec; try tauto.
    destruct lt_dec; try tauto.
  } Unfocus.
  auto.
Qed.

Lemma rule_read_sarray ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var)
      (cty : option CTyp) (p : Qc) (Env : list entry) 
      (P : Prop) (Res Res' : res) (arr : list val) ix i iz d j:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array' l (skip arr d j) p *** Res' ->
  iz = Zn i ->
  (P -> i < length arr /\ i mod d = j) ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= [le +o ix])
      (Assn Res P (Ent x (nth i arr 0%Z) :: (remove_var Env x))).
Proof.
  intros; eapply rule_read_array'; eauto.
Qed.

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

Lemma rule_write_array :
  forall (ntrd : nat) BS
         (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (e : exp)
         (v : val) (Env : list entry) (P : Prop) (Res Res' : res) arr ix iz i,
    evalLExp Env le l ->
    evalExp Env ix iz ->
    iz = Zn i ->
    (P -> i < length arr) ->
    evalExp Env e v ->
    Res |=R array l arr 1 *** Res' ->
    CSL BS tid
        (Assn Res P Env)
        ([le +o ix]::=e)
        (Assn (array l (set_nth i arr v) 1 *** Res') P Env).
Proof.
  intros.
  eapply forward; [|applys (>>rule_write (loc_off l iz) (nth i arr 0%Z))].
  2: do 1 constructor; eauto.
  2: eauto.
  Focus 2.
  { intros s h Hp Hsat; apply H4 in Hsat.
    rewrite (array_unfold i) in Hsat; [|forwards*: H2; lia].
    repeat rewrite <-res_assoc in Hsat.
    rewrite res_CA in Hsat.
    substs; eauto. } Unfocus.
  unfold Assn; intros s h Hsat; sep_split_in Hsat.
  unfold sat in *; sep_split; sep_split_in Hsat; auto.
  Ltac fold_res_sat := repeat match goal with
  | [|- res_denote ?P ?s ?h] => cutrewrite (res_denote P s h = sat_res s h P); [|auto]
  | [H : res_denote ?P ?s ?h |- _] => cutrewrite (res_denote P s h = sat_res s h P) in H; [|auto]
  end.
  fold_res_sat.
  rewrite (array_unfold i); eauto.
  rewrite firstn_set_nth_ignore.
  rewrite skipn_set_nth_ignore; substs; repeat sep_cancel.
  rewrite nth_set_nth; destruct Nat.eq_dec; try omega.
  destruct lt_dec; try omega.
  repeat rewrite <-res_assoc; rewrite res_CA; auto.
  false; apply n; eauto.
  rewrite length_set_nth in *; unfold_conn; eauto.
Qed.

(* Lemma has_no_vars_array' ptr arr p : has_no_vars (array' ptr arr p). *)
(* Proof. *)
(*   revert ptr; induction arr; simpl; eauto with novars_lemma. *)
(*   destruct a; eauto with novars_lemma. *)
(* Qed. *)

(* Hint Resolve has_no_vars_array' : novars_lemma. *)

Notation set_nth' i arr v := (set_nth i arr (Some v)).

Lemma rule_write_array'  ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) 
      (Env : list entry) (P : Prop) (Res Res' : res) (arr : list val) dist ix i iz j e v st:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array' l (ith_vals dist arr j st) 1 *** Res' ->
  evalExp Env e v ->
  iz = Zn i ->
  (P -> i < length arr /\ dist (st + i) = j) ->
  CSL BS tid
      (Assn Res P Env)
      ([le +o ix] ::= e)
      (Assn (array' l (ith_vals dist (set_nth i arr v) j st) 1 *** Res') P Env).
Proof.
  intros.
  eapply forward; [|applys (>>rule_write (loc_off l iz) (nth i arr 0%Z) )].
  2: constructor; eauto.
  2: eauto.
  Focus 2.
  { intros s h Hp Hres.
    apply H1 in Hres.
    rewrites* (array'_unfold i (ith_vals dist arr j st) l 1) in Hres; [|rewrites* ith_vals_length].
    repeat rewrite <-res_assoc in *; substs.
    rewrite res_CA in Hres.
    rewrite (nth_skip _ 0%Z) in Hres.
    forwards*: H4.
    destruct Nat.eq_dec, (lt_dec i (length arr)); try now (simpl in *; omega).
    subst; unfold sat in *; sep_cancel; eauto. } Unfocus.
  unfold Assn; intros s h ?; unfold sat in *.
  sep_split_in H5; sep_split; eauto.
  fold_res_sat.
  rewrites* (>>array'_unfold i l 1%Qc); [rewrite ith_vals_length, length_set_nth; tauto|].
  unfold_conn_in HP; forwards*[? ?]: H4; substs.
  repeat rewrite <-res_assoc in *; substs.
  rewrite (nth_skip _ 0%Z); destruct Nat.eq_dec; try (simpl in *; omega).
  destruct lt_dec; try (unfold_conn_all; tauto).
  2:rewrite length_set_nth in *; tauto.
  rewrite nth_set_nth; destruct (Nat.eq_dec i i), (lt_dec i (length arr)); try omega.
  subst; unfold sat in *; repeat sep_cancel; eauto.
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
  rewrites* ith_vals_set_nth.
  rewrite firstn_set_nth_ignore.
  rewrite skipn_set_nth_ignore.
  rewrite res_CA in H5.
  eauto.
Qed.

Lemma rule_write_sarray'  ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (Env : list entry) 
      (P : Prop) (Res Res' : res) (arr : list val) ix i iz d j e v:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array' l (skip arr d j) 1 *** Res' ->
  evalExp Env e v ->
  iz = Zn i ->
  (P -> i < length arr /\ i mod d = j) ->
  CSL BS tid
      (Assn Res P Env)
      ([le +o ix] ::= e)
      (Assn ((array' l (skip (set_nth i arr v) d j) 1) *** Res') P Env).
Proof.
  intros; applys* rule_write_array'.
Qed.

Lemma Ent_eq_dec (e1 e2 : entry) : {e1 = e2} + {e1 <> e2}.
Proof. repeat decide equality. Qed.

Lemma env_assns_emp Env s h:
  env_assns_denote Env s h -> emp s h.
Proof.
  induction Env; simpl; eauto.
  intros [? ?]; eauto.
Qed.

Lemma remove_var_cons x Env :
  ent_assn_denote x //\\ env_assns_denote (remove Ent_eq_dec x Env)
  ===> env_assns_denote Env.
Proof.
  induction Env; simpl.
  - intros s h [? ?]; eauto using env_assns_emp.
  - destruct Ent_eq_dec; simpl; substs.
    + intros; split; eauto.
      destruct H; eauto.
    + intros s h (? & ? & ?); split; eauto.
      apply IHEnv; split; eauto.
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
  (env_assns_denote Env1 ===> env_assns_denote Env2).
Proof.
  revert Env2; induction Env1 as [|[x v] Env1]; unfold incl; intros Env2.
  - simpl; intros H.
    assert (Env2 = nil).
    { destruct Env2; eauto.
      false; eapply H; simpl; eauto. }
    subst; simpl; eauto.
  - simpl; intros H s h Hsat; destruct Hsat as [? Hsat].
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
  unfold Assn; intros Henv HP Hres s h Hsat.
  unfold sat in *; sep_split_in Hsat; 
  eauto; sep_split; eauto.
  - unfold_conn; eauto.
  - applys* env_incl_imp.
  - apply HP; eauto.
Qed.

Lemma Assn_split R1 R2 P E :
  Assn (R1 *** R2) P E |=
  Assn R1 P E ** Assn R2 P E.
Proof.
  unfold Assn, sat; intros s h H; sep_split_in H.
  destruct H as (h1 & h2 & ? & ? & ? & ?).
  exists h1 h2.
  split; [|split; [|split]]; eauto;
  unfold Assn; eauto; sep_split; eauto.
Qed.

Lemma Assn_combine R1 R2 P1 P2 E1 E2 :
  (Assn R1 P1 E1 ** Assn R2 P2 E2) ==
  Assn (R1 *** R2) (P1 /\ P2) (E1 ++ E2).
Proof.
  unfold Assn; intros s h; split.
  - intros (h1 & h2 & Hsat1 & Hsat2 & ? & ?).
    unfold Apure in Hsat1, Hsat2.
    sep_split_in Hsat1; sep_split_in Hsat2; sep_split; try now unfold_conn; tauto.
    Lemma env_assns_app E1 E2 s h :
      (env_assns_denote (E1 ++ E2)) s h <->
      (env_assns_denote E1 s h /\ env_assns_denote E2 s h).
    Proof.
      induction E1; simpl; intros.
      - split; intros; try split; try destruct H; eauto.
        eauto using env_assns_emp.
      - destruct (IHE1); split; intros;
        unfold_conn_all; tauto.
    Qed.
    rewrite env_assns_app; unfold sat; unfold_conn; tauto.
    exists h1 h2; tauto.
  - intros Hsat; sep_split_in Hsat.
    destruct HP; rewrite env_assns_app in HP0.
    destruct Hsat as (h1 & h2 & Hsat1 & Hsat2 & ? & ?).
    exists h1 h2; split; [|split]; eauto;
    sep_split; unfold_conn; tauto.
Qed.

Lemma backwardR ntrd BS (tid : Fin.t ntrd) P P' Q C :
  CSL BS tid P C Q -> P' |= P -> CSL BS tid P' C Q.
Proof.
  intros; forwards*: backward.
Qed.

Lemma forwardR ntrd BS (tid : Fin.t ntrd) P Q Q' C :
  CSL BS tid P C Q -> Q |= Q' -> CSL BS tid P C Q'.
Proof.
  intros; forwards*: forward.
Qed.

Lemma rule_barrier ntrd BS b (i : Fin.t ntrd) Res Res_pre Res_post Res_f P P_pre P_post Env Env_pre Env_post :
  Vector.nth (fst (BS b)) i = Assn Res_pre P_pre Env_pre ->
  Vector.nth (snd (BS b)) i = Assn Res_post P_post Env_post ->
  (Assn Res P Env ===> Assn (Res_pre *** Res_f) P_pre Env_pre) ->
  CSL BS i
      (Assn Res P Env)
      (Cbarrier b)
      (Assn (Res_f *** Res_post) (P_pre /\ P_post) (Env_pre ++ Env_post)).
Proof.
  intros Heq1 Heq2 ?.
  eapply backward.
  { intros s h H'.
    apply H, Assn_split in H'; auto; eauto. }
  rewrite <- Heq1.
  eapply forwardR.
  eapply rule_frame; [| unfold inde; simpl; tauto ].
  eapply rule_barrier.
  rewrite Heq2.
  intros; apply Assn_combine; eauto.
  unfold sat in *; repeat sep_cancel.
Qed.  

Lemma precise_false : precise (fun _ _ => False).
Proof.
  unfold precise; intros; tauto.
Qed.

Lemma precise_sat (P Q : assn) :
  (Q |= P) -> precise P -> precise Q.
Proof.
  unfold precise; simpl; intros Hsat HprecP; introv.
  intros HsatQ HsatQ' ? ? ?.
  eapply HprecP; eauto; apply Hsat; eauto.
Qed.

Definition precise_res P :=
  forall (h1 h2 h1' h2' : pheap) s,
    sat_res s h1 P ->
    sat_res s h2 P ->
    pdisj h1 h1' ->
    pdisj h2 h2' ->
    phplus h1 h1' = phplus h2 h2' -> h1 = h2. 

Lemma precise_assn Res P Env :
  precise_res Res
  -> precise (Assn Res P Env).
Proof.
  unfold Assn; intros.
  eapply precise_sat; unfold sat; intros s h Hsat; sep_split_in Hsat; eauto.
Qed.

Lemma precise_star (P Q : res) : precise_res P -> precise_res Q -> precise_res (P *** Q).
Proof.
  unfold_conn; intros pp pq h1 h2 h1' h2' s hsat hsat' hdis hdis' heq; simpl in *.
  destruct hsat as [ph1 [ph1' [satp1 [satq1 [Hdis1 Heq1]]]]], 
                   hsat' as [ph2 [ph2' [satp2 [satq2 [Hdis2 Heq2]]]]].
  destruct h1 as [h1 ?], h2 as [h2 ?]; apply pheap_eq; simpl in *; rewrite <-Heq1, <-Heq2 in *.
  apply pdisj_padd_expand in hdis; apply pdisj_padd_expand in hdis'; eauto.
  rewrite !padd_assoc in heq; try tauto. 
  f_equal; destruct hdis as [hdis1 hdis2], hdis' as [hdis1' hdis2'].
  - rewrite (pp ph1 ph2 (phplus_pheap hdis2) (phplus_pheap hdis2') s); eauto.
  - rewrite padd_left_comm in heq at 1; try tauto.
    rewrite (@padd_left_comm _ ph2 ph2' h2') in heq; try tauto.
    pose proof (pdisjE2 hdis1 hdis2) as dis12; pose proof (pdisjE2 hdis1' hdis2') as dis12'.
    rewrite (pq ph1' ph2' (phplus_pheap dis12) (phplus_pheap dis12') s); simpl in *; eauto; 
    apply pdisj_padd_comm; eauto.
Qed.

Lemma precise_mps l v p :
  precise_res (l |->p (p, v)).
Proof.
  unfold precise_res, precise; intros; simpl in *.
  unfold sat_res in *; simpl in *; unfold_conn_all; simpl in *.
  destruct h1 as [h1 ?], h2 as [h2 ?]; apply pheap_eq.
  extensionality x; simpl in *; rewrite H, H0; auto.
Qed.

Lemma precise_emp :
  precise_res Emp.
Proof.
  unfold precise_res, sat_res, sat; simpl.
  intros; applys precise_emp; simpl; eauto.
Qed.

Hint Resolve precise_star precise_mps precise_emp precise_false precise_assn.

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

Lemma emp_unit_l_res P: 
  (Emp *** P) == P.
Proof.
  intros s h; unfold sat_res; simpl.
  apply emp_unit_l.
Qed.

Lemma emp_unit_r_res P: 
  (P *** Emp) == P.
Proof.
  intros s h; unfold sat_res; simpl.
  apply emp_unit_r.
Qed.

Definition istar ls := List.fold_right Star Emp ls.

Lemma init_emp_emp_res b n :
  istar (ls_init b n (fun _ => Emp)) == Emp.
Proof.
  revert b; induction n; simpl; [reflexivity|]; intros.
  rewrite IHn.
  rewrite emp_unit_l_res; reflexivity.
Qed.

Lemma ls_star_res b n P Q :
  istar (ls_init b n (fun i => P i *** Q i)) ==
  (istar (ls_init b n (fun i => P i)) *** istar (ls_init b n (fun i => Q i))).
Proof.
   revert b; induction n; simpl; eauto.
   - intros; rewrite emp_unit_l_res; reflexivity.
   - intros; rewrite IHn; rewrite <-!res_assoc.
     apply res_star_proper; [reflexivity|].
     rewrite res_CA; reflexivity.
Qed.

Lemma istar_app Ps Qs: 
  istar (Ps ++ Qs) == (istar Ps *** istar Qs).
Proof.
  induction Ps; simpl; eauto.
  rewrite emp_unit_l_res; reflexivity.
  rewrite IHPs, <-res_assoc; reflexivity.
Qed.  
                       
Lemma array'_ok n ptr dist vals s p :
  (forall i, s <= i < length vals + s -> dist i < n) ->
  istar (ls_init 0 n (fun i => array' ptr (ith_vals dist vals i s) p)) ==
  array ptr vals p.
Proof.
  revert s ptr; induction vals; intros; simpl.
  - intros s' h.
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
    rewrite emp_unit_l_res, emp_unit_r_res; reflexivity.
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
  intros; apply pts_star_p; auto.
Qed.

Lemma array_p_star loc xs p q :
  (0 < p -> p <= 1 -> 0 < q -> q <= 1 -> p + q <= 1 ->
  array loc xs (p + q) == (array loc xs p *** array loc xs q))%Qc.
Proof.
  revert loc; induction xs; simpl; intros.
  - rewrite emp_unit_l_res; reflexivity.
  - rewrites* IHxs.
    rewrite* mps_p_star; eauto.
    rewrite <-!res_assoc, (res_CA (array (loc_off loc 1) xs p)); reflexivity.
Qed.   

Require Import QArith Qcanon.
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
    rewrite emp_unit_r_res; reflexivity.
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