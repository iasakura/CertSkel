Require Import GPUCSL scan_lib LibTactics Skel_lemma Psatz Classical.

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

Inductive entry := Ent {ent_e : exp; ent_v : val}.
Definition ent_assn_denote va :=
  match va with
  | Ent x v => x === v
  end.
Definition env_assns_denote env :=
  List.fold_right (fun x y => ent_assn_denote x //\\ y) emp env.

Create HintDb novars_lemma.

Hint Resolve
     has_no_vars_star
     has_no_vars_mp
     has_no_vars_emp : novars_lemma.

(*
Res : an assertion for resource
P : an assertion for pure constraint
Env : an assertion for variables/expression bindings
 *)
Definition Assn Res (P : Prop) (Env : list entry) :=
  pure (has_no_vars Res) //\\
  Res ** !(pure P) ** !(env_assns_denote Env).

Inductive evalExp : list entry -> exp -> val -> Prop :=
| SEval_num env n : evalExp env (Enum n) n
| SEval_plus env e1 v1 e2 v2 :
    evalExp env e1 v1 -> evalExp env e2 v2 ->
    evalExp env (e1 +C e2) (v1 + v2)%Z
| SEval_min env e1 v1 e2 v2 :
    evalExp env e1 v1 -> evalExp env e2 v2 ->
    evalExp env (Emin e1 e2) (Z.min v1 v2)%Z
| SEval_lt env e1 v1 e2 v2 :
    evalExp env e1 v1 -> evalExp env e2 v2 ->
    evalExp env (Elt e1 e2) (if Z_lt_dec v1 v2 then 1 else 0)%Z
| SEval_eq env e1 v1 e2 v2 :
    evalExp env e1 v1 -> evalExp env e2 v2 ->
    evalExp env (Eeq e1 e2) (if eq_dec v1 v2 then 1 else 0)%Z
| SEval_mul env e1 v1 e2 v2 :
    evalExp env e1 v1 -> evalExp env e2 v2 ->
    evalExp env (e1 *C e2) (v1 * v2)%Z
| SEval_sub env e1 v1 e2 v2 :
    evalExp env e1 v1 -> evalExp env e2 v2 ->
    evalExp env (e1 -C e2) (v1 - v2)%Z
| SEval_div2 env e1 v1 :
    evalExp env e1 v1 -> 
    evalExp env (e1 >>1) (Z.div2 v1)
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
  - applys* env_denote_in.
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

Definition loc2lexp (v : loc) :=
  match v with
  | Loc p v => Addr p v
  end.

Coercion loc2lexp : loc >-> loc_exp.

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

Inductive evalBExp : list entry -> bexp -> Prop -> Prop :=
| SEval_beq env e1 e2 v1 v2 : 
    evalExp env e1 v1 ->
    evalExp env e2 v2 ->
    evalBExp env (e1 == e2) (v1 = v2)
| SEval_blt env e1 e2 v1 v2 : 
    evalExp env e1 v1 ->
    evalExp env e2 v2 ->
    evalBExp env (e1 <C e2) (v1 < v2)%Z
| Seval_band env b1 b2 p1 p2 :
    evalBExp env b1 p1 ->
    evalBExp env b2 p2 ->
    evalBExp env (Band b1 b2) (p1 /\ p2)
| Seval_bnot env b1 p1 :
    evalBExp env b1 p1 ->
    evalBExp env (Bnot b1) (~p1).

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
    destruct eq_dec; split; intros; try congruence.
  - forwards*: (>>evalExp_ok e1); unfold_conn_all; simpl in *; substs.
    forwards*: (>>evalExp_ok e2); unfold_conn_all; simpl in *; substs.
    destruct Z_lt_dec; split; intros; try congruence.
  - rewrites* <-(>>IHevalBExp1); rewrites*<-(>>IHevalBExp2).
    unfold bexp_to_assn.
    destruct (bdenot b1 s), (bdenot b2 s); split; intros;
    try lazymatch goal with [H : _ /\ _ |- _] => destruct H end;
    simpl in *; try congruence; eauto.
  - rewrites* <-(>>IHevalBExp).
    unfold bexp_to_assn.
    destruct (bdenot b1 s); simpl; split; intros; try congruence.
Qed.

Definition remove_var (Env : list entry) (x : var) :=
  filter (fun e => if In_dec var_eq_dec x (fv_E (ent_e e)) then false else true) Env.

Lemma remove_var_imp (Env : list entry) x :
  env_assns_denote Env ===> env_assns_denote (remove_var Env x).
Proof.
  induction Env; simpl; eauto.
  intros s h [? ?].
  destruct in_dec; simpl;  eauto.
  split; eauto.
Qed.

Lemma remove_var_inde (Env : list entry) x :
  inde (env_assns_denote (remove_var Env x)) (x :: nil).
Proof.
  induction Env; simpl; prove_inde.
  destruct in_dec; simpl; prove_inde.
  destruct a; simpl in *.
  apply inde_eeq; rewrite Forall_forall; intros;
  apply indeE_fv; eauto.
  simpl in *; destruct H; try tauto; subst.
  eauto.
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
    apply indeE_fv; intros Hc.
    apply disjoint_app_r1 in Hdis.
    forwards*: (>>disjoint_not_in_r Hdis).
  - simpl in Hdis.
    apply disjoint_app_r2 in Hdis; eauto.
Qed.

Lemma rule_assign ntrd BS (tid : Fin.t ntrd) e x cty (v : val) Env P (Res : assn) :
  evalExp Env e v ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= e)
      (Assn Res P (Ent x v :: remove_var Env x)).
Proof.
  intros HevalLe.
  unfold CSL, safe_nt, Assn; intros s h Hsat; destruct n; [now (simpl; eauto)|].
  destruct Hsat as [HnvR Hsat]; simpl in *.
  unfold Apure in *.
  sep_split_in Hsat.
  simpl; repeat split; try congruence.
  - introv ? ? HC; inverts HC.
  - introv Hdis Htoh Hred.
    inverts Hred; inverts EQ1.
    repeat eexists; repeat split; eauto.
    apply safe_skip; simpl.
    (split; eauto).
    unfold has_no_vars, Bdiv.indeP in *; simpl in *.
    sep_split; try rewrite HnvR; try rewrite HnvP; eauto.
    cutrewrite (edenot e s0 = v); [|applys (>> evalExp_ok HevalLe); eauto].
    unfold_conn; simpl.
    split.
    + unfold var_upd in *; destruct var_eq_dec; try congruence.
    + apply remove_var_inde; simpl in *; auto.
      applys* remove_var_imp.
Qed.    

Lemma rule_read ntrd BS (tid : Fin.t ntrd) le l x cty p (v : val) Env (P : Prop) (Res Res' : assn) :
  evalLExp Env le l ->
  (P -> (Res |= l -->p (p, v) ** Res')) ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= [le])
      (Assn Res P (Ent x v :: remove_var Env x)).
Proof.
  intros HevalLe Hres.
  unfold CSL, safe_nt, Assn; intros s h Hsat; destruct n; [now (simpl; eauto)|].
  destruct Hsat as [HnvR Hsat]; simpl in *.
  unfold Apure in *.
  sep_split_in Hsat.
  assert (exists p, PHeap.this h l = Some (p, v)) as [p' Heq].
  { forwards* (? & ? & ? & ? & ? & ?): (>> Hres Hsat).
    unfold_conn_all.
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
    (split; eauto).
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
  unfold "!!"%Qc.
  rewrite this_id.
  apply Qred_correct.
Qed.

Ltac lra_Qc :=
  repeat rewrite QcleQ in *; repeat rewrite QcltQ in *;
  repeat rewrite QcplusQ in *; repeat rewrite this_id in *;
  simpl in *; lra.

Lemma rule_write ntrd BS (tid : Fin.t ntrd) le l e (v : val) v' Env (P : Prop) (Res Res' : assn) : 
  evalLExp Env le l ->
  evalExp Env e v' ->
  has_no_vars Res' ->
  (P -> Res |= ((l -->p (1, v)) ** Res')) ->
  CSL BS tid 
      (Assn Res P Env) 
      ([le] ::= e)
      (Assn (l -->p (1, v') ** Res') P Env).
Proof.
  intros HevalLe Henv HnvR' Hres.
  unfold CSL, safe_nt, Assn; intros s h Hsat; destruct n; [now (simpl; eauto)|].
  destruct Hsat as [HnvR Hsat]; simpl in *.
  unfold Apure in *.
  sep_split_in Hsat.
  assert (Heq : PHeap.this h l = Some (1%Qc, v)).
  { forwards* (? & ? & ? & ? & ? & ?): (>> Hres Hsat).
    unfold_conn_all.
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
      split; eauto.
      * apply has_no_vars_star; eauto.
        apply has_no_vars_mp; try now (cbv; destruct l; auto).
      * sep_split; eauto.
        apply Hres in Hsat; eauto.
        destruct Hsat as (? & ? & ? & ? & ? & ?).
        exists (ph_upd2 x l v') x0; repeat split; eauto.
        { unfold_conn_all; intros; rewrite ledenot_id in *.
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
  intros s h Hsat; sep_split_in Hsat;
  destruct Hsat as (? & Hsat); sep_split_in Hsat;
  forwards*: (>>evalBExp_ok Heval);
  split; eauto; sep_split; eauto; unfold_conn; try tauto.
  unfold bexp_to_assn in *; simpl in *.
  destruct (bdenot b s); simpl in *; try congruence.
  split; eauto.
  rewrite <-H0; congruence.
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

Fixpoint arrays (ptr : loc) (arr : list val) p :=
  match arr with
  | nil => nil
  | v :: arr =>
    ptr -->p (p, v) :: arrays (loc_off ptr 1) arr p
  end.
Close Scope Q_scope.

Definition array ptr arr p := conj_xs (arrays ptr arr p).

Lemma has_no_vars_mp (l : loc) (v : val) p : has_no_vars (l -->p (p, v)).
Proof.
  apply has_no_vars_mp;
  destruct l; simpl; eauto.
Qed.

Lemma has_no_vars_array l vs p : has_no_vars (array l vs p).
Proof.
  revert l; induction vs; intros l; simpl; eauto with novars_lemma.
  apply has_no_vars_star; eauto.
  apply has_no_vars_mp; simpl; eauto.
Qed.

Hint Resolve has_no_vars_array has_no_vars_mp : novars_lemma.

Lemma array_unfold i arr ptr p:
  i < length arr -> 
  (array ptr arr p) ==
  ((array ptr (firstn i arr) p) **
   (loc_off ptr (Zn i) -->p (p, nth i arr 0%Z)) **
   (array (loc_off ptr (Z.succ (Zn i))) (skipn (S i) arr) p)).
Proof.
  unfold array.
  simpl; unfold equiv_sep;
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

Lemma sep_assoc (P Q R : assn) : (P ** Q ** R) == ((P ** Q) ** R).
Proof.
  split; intros; apply sep_assoc; auto.
Qed.

Lemma sep_comm (P Q : assn) : (P ** Q) == (Q ** P).
Proof.
  split; apply scC; auto.
Qed.

Lemma rule_read_array ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var)
      (cty : option CTyp) (p : Qc) (Env : list entry) 
      (P : Prop) (Res Res' : assn) (arr : list val) ix i iz:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |= array l arr p ** Res' ->
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
  { intros s h Hp Hres.
    apply H1 in Hres.
    rewrites* (array_unfold i arr) in Hres.
    repeat rewrite <-sep_assoc in *.
    subst; unfold sat in *; sep_cancel; eauto. } Unfocus.
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
  | nil => emp
  | v :: arr =>
    match v with
    | Some v => (ptr -->p (p,  v)) 
    | None => emp 
    end ** array' (loc_off ptr 1) arr p
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

Lemma array'_ok n ptr dist arr s p :
  (forall i, dist i < n) ->
  conj_xs (ls_init 0 n (fun i => array' ptr (ith_vals dist arr i s) p)) ==
  array ptr arr p.
Proof.
  intros H; revert s ptr; induction arr; intros; simpl.
  - apply init_emp_emp.
  - rewrite ls_star.
    rewrite IHarr.
    unfold array in *; simpl.
    apply star_proper; try reflexivity.
    lazymatch goal with
    | [|- context [ls_init 0 n ?f]] =>
      cutrewrite (ls_init 0 n f =
                  (ls_init 0 (dist s) (fun _ => emp) ++
                  (ptr -->p (p, a)) ::
                  ls_init ((dist s) + 1) (n - dist s - 1) (fun _ => emp)))
    end.
    rewrite conj_xs_app, init_emp_emp; simpl; rewrite init_emp_emp.
    rewrite emp_unit_l, emp_unit_r; reflexivity.
    specialize (H s).
    cutrewrite (n = (dist s) + 1 + (n - dist s - 1)); [| omega].
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
Qed.    

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
  ((array' ptr (firstn i arr) p) **
   (match nth i arr None with
    | Some v => loc_off ptr (Zn i) -->p (p, v)
    | None => emp
    end) **
   (array' (loc_off ptr (Z.succ (Zn i))) (skipn (S i) arr) p)).
Proof.
  unfold array.
  simpl; unfold equiv_sep;
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

Lemma length_arrays ptr arr p : length (arrays ptr arr p) = length arr.
Proof. revert ptr; induction arr; intros; simpl; congruence. Qed.

Lemma firstn_arrays n ptr arr p : firstn n (arrays ptr arr p) = arrays ptr (firstn n arr) p.
Proof.
  revert ptr arr; induction n; intros; simpl; eauto.
  destruct arr; simpl; congruence.
Qed.

Lemma skipn_arrays n ptr arr p : skipn n (arrays ptr arr p) = arrays (loc_off ptr (Zn n)) (skipn n arr) p.
Proof.
  revert ptr arr; induction n; intros; simpl; eauto.
  - rewrite loc_off0; eauto.
  - destruct arr; eauto; simpl.
    rewrite IHn.
    unsimpl (Z.of_nat (S n)).
    rewrite Nat2Z.inj_succ, loc_offS; eauto.
Qed.

Lemma nth_arrays n ptr arr p :
  nth n (arrays ptr arr p) emp = if lt_dec n (length arr) then (loc_off ptr (Zn n) -->p  (p,  (nth n arr 0%Z))) else emp.
Proof.
  revert ptr arr; induction n; intros ptr [|? arr]; simpl; eauto.
  - rewrite loc_off0; eauto.
  - rewrite IHn; repeat destruct lt_dec; try omega; eauto.
    unsimpl (Z.of_nat (S n)).
    rewrite Nat2Z.inj_succ, loc_offS; eauto.
Qed.

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

Lemma nth_skip i (arr : list val) dist j s :
  nth i (ith_vals dist arr j s) None =
  if Nat.eq_dec (dist (s + i)) j then 
    if lt_dec i (length arr) then Some (get arr i) 
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

Lemma rule_read_sarray ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var)
      (cty : option CTyp) (p : Qc) (Env : list entry) 
      (P : Prop) (Res Res' : assn) (arr : list val) ix i iz d j:
  d <> 0 ->
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |= array' l (skip arr d j) p ** Res' ->
  iz = Zn i ->
  (P -> i < length arr /\ i mod d = j) ->
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
    apply H2 in Hres.
    rewrites* (array'_unfold i) in Hres.
    2: rewrite ith_vals_length; tauto.
    cutrewrite (nth i (skip arr d j) None = Some (get arr i)) in Hres.
    repeat rewrite <-sep_assoc in *.
    subst; unfold sat in *; sep_cancel; eauto.
    rewrite nth_skip; simpl.
    destruct Nat.eq_dec; try tauto.
    destruct lt_dec; try tauto.
  } Unfocus.
  auto.
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
         (v : val) (Env : list entry) (P : Prop) (Res Res' : assn) arr ix iz i,
    evalLExp Env le l ->
    evalExp Env ix iz ->
    iz = Zn i ->
    (P -> i < length arr) ->
    evalExp Env e v ->
    has_no_vars Res' ->
    Res |= array l arr 1 ** Res' ->
    CSL BS tid
        (Assn Res P Env)
        ([le +o ix]::=e)
        (Assn (array l (set_nth i arr v) 1 ** Res') P Env).
Proof.
  intros.
  eapply forward; [|applys (>>rule_write (loc_off l iz) (nth i arr 0%Z))].
  2: do 1 constructor; eauto.
  2: eauto.
  Focus 3.
  { intros s h Hp Hsat; apply H5 in Hsat.
    rewrite (array_unfold i) in Hsat.
    repeat rewrite <-sep_assoc in Hsat.
    unfold sat in *; subst.
    sep_cancel; eauto.
    unfold sat in *; sep_split_in Hsat; eauto. } Unfocus.
  2: eauto with novars_lemma.
  intros s h (? & Hsat); sep_split_in Hsat.
  split; [unfold_conn; eauto with novars_lemma|].
  match goal with
  | [|- ?P s h] => cutrewrite (P s h = sat s h P); [|eauto]
  end.
  rewrite (array_unfold i); eauto.
  unfold sat; sep_split; eauto.
  rewrite firstn_set_nth_ignore.
  rewrite skipn_set_nth_ignore; substs; repeat sep_cancel.
  rewrite nth_set_nth; destruct Nat.eq_dec; try omega.
  destruct lt_dec; try omega.
  sep_cancel.
  sep_normal; repeat sep_cancel.
  false; apply n; eauto.
  rewrite length_set_nth in *; unfold_conn; eauto.
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

Lemma has_no_vars_array' ptr arr p : has_no_vars (array' ptr arr p).
Proof.
  revert ptr; induction arr; simpl; eauto with novars_lemma.
  destruct a; eauto with novars_lemma.
Qed.

Hint Resolve has_no_vars_array' : novars_lemma.

Notation set_nth' i arr v := (set_nth i arr (Some v)).

Lemma rule_write_sarray  ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) 
      (Env : list entry) (P : Prop) (Res Res' : assn) (arr : list val) ix i iz d j e v:
  d <> 0 ->
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |= array' l (skip arr d j) 1 ** Res' ->
  evalExp Env e v ->
  iz = Zn i ->
  (P -> i < length arr /\ i mod d = j) ->
  has_no_vars Res' ->
  CSL BS tid
      (Assn Res P Env)
      ([le +o ix] ::= e)
      (Assn (array' l (skip (set_nth i arr v) d j) 1 ** Res') P Env).
Proof.
  intros.
  eapply forward; [|applys (>>rule_write (loc_off l iz) (nth i arr 0%Z) )].
  2: constructor; eauto.
  2: eauto.
  Focus 3.
  { intros s h Hp Hres.
    apply H2 in Hres.
    rewrites* (array'_unfold i (skip arr d j) l 1) in Hres; [|rewrites* ith_vals_length].
    repeat rewrite <-sep_assoc in *; substs.
    rewrite nth_skip in Hres.
    forwards*: H5.
    destruct Nat.eq_dec, (lt_dec i (length arr)); try now (simpl in *; omega).
    subst; unfold sat, val in *; sep_cancel; eauto. } Unfocus.
  unfold Assn; intros s h [? ?]; split.
  unfold Apure; simpl; eauto with novars_lemma.
  sep_split_in H8; sep_split; eauto.
  fold_sat.
  rewrites* (>>array'_unfold i l 1%Qc); [rewrite ith_vals_length, length_set_nth; tauto|].
  repeat rewrite plus_O_n in H8.
  unfold_conn_in HP; forwards*[? ?]: H5; substs.
  repeat rewrite <-sep_assoc in *; substs.
  rewrite nth_skip; destruct Nat.eq_dec; try (simpl in *; omega).
  destruct lt_dec; try (unfold_conn_all; tauto).
  2:rewrite length_set_nth in *; tauto.
  rewrite nth_set_nth; destruct (Nat.eq_dec i i), (lt_dec i (length arr)); try omega.
  subst; unfold sat, val in *; repeat sep_cancel; eauto.
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
  rewrites* ith_vals_set_nth0.
  rewrite firstn_set_nth_ignore.
  rewrite skipn_set_nth_ignore.
  eauto.
  eauto with novars_lemma.
Qed.

Lemma rule_write_sarray'  ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (Env : list entry) 
      (P : Prop) (Res Res' : assn) (arr : list val) ix i iz d j e v:
  d <> 0 ->
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |= array' l (skip arr d j) 1 ** Res' ->
  evalExp Env e v ->
  iz = Zn i ->
  (P -> i < length arr /\ i mod d = j) ->
  has_no_vars Res' ->
  CSL BS tid
      (Assn Res P Env)
      ([le +o ix] ::= e)
      (Assn ((array' l (set_nth' i (skip arr d j) v) 1) ** Res') P Env).
Proof.
  intros.
  eapply forward; [|applys (>>rule_write (loc_off l iz) (nth i arr 0%Z) )].
  2: constructor; eauto.
  2: eauto.
  Focus 3.
  { intros s h Hp Hres.
    apply H2 in Hres.
    rewrites* (array'_unfold i (skip arr d j) l 1) in Hres; [|rewrites* ith_vals_length].
    repeat rewrite <-sep_assoc in *; substs.
    rewrite nth_skip in Hres.
    forwards*: H5.
    destruct Nat.eq_dec, (lt_dec i (length arr)); try now (simpl in *; omega).
    subst; unfold sat, val in *; sep_cancel; eauto. } Unfocus.
  unfold Assn; intros s h [? ?]; split.
  unfold Apure; simpl; eauto with novars_lemma.
  sep_split_in H8; sep_split; eauto.
  fold_sat.
  rewrites* (>>array'_unfold i l 1%Qc); [rewrite length_set_nth, ith_vals_length; tauto|].
  repeat rewrite plus_O_n in H8.
  unfold_conn_in HP; forwards*[? ?]: H5; substs.
  repeat rewrite <-sep_assoc in *; substs.
  rewrite firstn_set_nth_ignore.
  rewrite skipn_set_nth_ignore.
  rewrite nth_set_nth, ith_vals_length.
  destruct (Nat.eq_dec i i), (lt_dec i (length arr)); try omega.
  subst; unfold sat, val in *; repeat sep_cancel; eauto.
  eauto with novars_lemma.
Qed.

Fixpoint assigns (vs : list var) (ctys : list CTyp) (es : list exp) :=
  match vs, es, ctys with
  | v :: vs, e :: es, cty :: ctys => (v :T cty ::= e) ;; assigns vs ctys es
  | v :: vs, e :: es, nil => (v ::= e) ;; assigns vs ctys es
  | _, _, _  => Cskip
  end.

(* A generating function xs := pl arr + ix. pl denotes array is on shared / global memory *)
Fixpoint reads (xs : list var) (ctys : list CTyp) (arrs : list loc_exp) :=
  match xs, arrs, ctys with
  | x :: xs, a :: arrs, cty :: ctys => (x :T cty ::= [a]) ;; reads xs ctys arrs  
  | x :: xs, a :: arrs, nil => (x ::= [a]) ;; reads xs ctys arrs 
  | _, _, _ => Cskip
  end.

(* A generating function pl arr + ix := es. pl denotes array is on shared / global memory *)
Fixpoint writes (arrs : list loc_exp) es :=
  match arrs, es with
  | a :: arrs, e :: es => ([a] ::= e) ;; writes arrs es 
  | _, _ => Cskip
  end.

Fixpoint eq_tup (es : list exp) (vs : list val) : assn :=
  match es, vs with
  | nil, nil => emp
  | e :: es, v :: vs => !(e === v) ** eq_tup es vs
  | _, _ => FalseP
  end.

Notation "e1 ==t e2" := (eq_tup e1 e2) (at level 70, right associativity).

Definition evalExps (Env : list entry) (e : list exp) (v : list val) :=
  List.Forall2 (fun e v => evalExp Env e v) e v.

Lemma env_assns_emp Env s h:
  env_assns_denote Env s h -> emp s h.
Proof.
  induction Env; simpl; eauto.
  intros [? ?]; eauto.
Qed.

Lemma evalExps_ok Env e v : 
  evalExps Env e v ->
  env_assns_denote Env ===> (e ==t v).
Proof.
  induction 1; simpl; eauto.
  - apply env_assns_emp.
  - intros; forwards*: IHForall2.
    sep_split; eauto.
    forwards*: evalExp_ok.
Qed.

Fixpoint eq_ltup (es : list loc_exp) (vs : list loc) : assn :=
  match es, vs with
  | nil, nil => emp
  | e :: es, v :: vs => !(e ===l v) ** eq_ltup es vs
  | _, _ => FalseP
  end.

Notation "e1 ==lt e2" := (eq_ltup e1 e2) (at level 70, right associativity).

Definition evalLExps (Env : list entry) (e : list loc_exp) (v : list loc) :=
  List.Forall2 (fun e v => evalLExp Env e v) e v.

Lemma evalLExps_ok Env e v :
  evalLExps Env e v ->
  env_assns_denote Env ===> (e ==lt v).
Proof.
  induction 1; simpl; eauto.
  - apply env_assns_emp.
  - intros; forwards*: IHForall2.
    sep_split; eauto.
    forwards*: evalLExp_ok.
Qed.

Definition removed_xs (Env : assn) (xs : list var) (Env' : assn) :=
  (Env |= Env') /\ (inde Env' (xs)).

Definition vars := List.map Evar.

Lemma evalExps_cons Env e es v vs:
  evalExps Env (e :: es) (v :: vs) -> evalExp Env e v /\ evalExps Env es vs.
Proof.
  intros H; inverts H; split; eauto.
Qed.

(* Lemma remove_xs_hd x xs Env Env' : removed_xs Env (x :: xs) Env' -> remove Env x Env'. *)
(* Proof. *)
(*   unfold removed_xs, removed, inde; simpl. *)
(*   intros; split; intros. *)
(*   - destruct H; eauto. *)
(*   - destruct H0; try tauto; subst. *)
(*     destruct H; eauto. *)
(* Qed. *)

(* Lemma remove_xs_tl x xs Env Env' : removed_xs Env (x :: xs) Env' -> removed_xs Env xs Env'. *)
(* Proof. *)
(*   unfold removed_xs, removed, inde; simpl. *)
(*   intros; split; intros. *)
(*   - destruct H; eauto. *)
(*   - destruct H; try tauto; subst. *)
(*     eauto. *)
(* Qed. *)

Definition remove_vars Env (xs : list var) :=
  List.fold_right (fun x e => remove_var e x) Env xs.

Lemma remove_vars_imp (Env : list entry) xs :
  env_assns_denote Env ===> env_assns_denote (remove_vars Env xs).
Proof.
  revert Env; induction xs; simpl; eauto.
  intros Env s h Hsat.
  applys* remove_var_imp.
Qed.

Lemma not_in_remove_var x Env:
  ~In x (fv_env (remove_var Env x)).
Proof.
  induction Env; simpl; eauto.
  destruct in_dec; simpl; eauto.
  rewrite in_app_iff; try tauto.
Qed.
Lemma disjoint_incl (A : Type) (xs ys zs : list A) :
  incl zs ys ->
  disjoint xs ys -> disjoint xs zs.
Proof.
  unfold incl; induction xs; eauto.
  intros; simpl in *; split; eauto.
  - intros Hc; apply H in Hc; tauto.
  - apply IHxs; tauto.
Qed.
Lemma remove_var_incl Env x:
  incl (fv_env (remove_var Env x)) (fv_env Env).
Proof.
  unfold incl; induction Env; simpl; eauto.
  intros; destruct in_dec; simpl in *; eauto;
  rewrite in_app_iff in *; eauto.
  destruct H; eauto.
Qed.

Lemma remove_vars_inde (Env : list entry) xs :
  inde (env_assns_denote (remove_vars Env xs)) xs.
Proof.
  apply disjoint_inde_env.
  revert Env; induction xs; simpl; eauto.
  split.
  - apply not_in_remove_var.
  - applys (>>disjoint_incl (IHxs Env)).
    applys* remove_var_incl.
Qed.

Fixpoint EEq_tup xs vs :=
  match xs, vs with
  | x :: xs, v :: vs => Ent x v :: EEq_tup xs vs
  | _, _ => nil
  end.

Definition fv_Es es := fold_right (fun e xs => fv_E e ++ xs) nil es.

Lemma evalExp_remove e v (x : var) Env:
  evalExp Env e v -> ~In x (fv_E e) ->
  evalExp (remove_var Env x) e v.
Proof.
  induction 1; intros; simpl in *; repeat rewrite in_app_iff in *;
  try forwards*: IHevalExp;
  try forwards*: IHevalExp1;
  try forwards*: IHevalExp2;
  econstructor; eauto; simpl; eauto.
  (* var case *)
  induction env; simpl in *; eauto.
  destruct H; substs; destruct in_dec; simpl in *; eauto; tauto.
Qed.
Lemma evalExps_remove e v (x : var) Env:
  evalExps Env e v -> ~In x (fv_Es e) ->
  evalExps (remove_var Env x) e v.
Proof.
  induction 1; intros; simpl in *; constructor; eauto;
  rewrite in_app_iff in *.
  apply evalExp_remove; eauto.
  forwards*: IHForall2.
Qed.

Lemma evalExp_cons Env a e v:
  evalExp Env e v ->
  evalExp (a :: Env) e v.
Proof.
  induction 1;
  try forwards*: IHevalExp;
  try forwards*: IHevalExp1;
  try forwards*: IHevalExp2;
  econstructor; eauto; simpl; eauto.
Qed.
Lemma evalExps_cons_inv Env a e v:
  evalExps Env e v ->
  evalExps (a :: Env) e v.
Proof.
  induction 1; intros; simpl in *; constructor; eauto.
  apply evalExp_cons; auto.
Qed.
      
Lemma env_assns_cons a env s h :
  env_assns_denote (a :: env) s h <-> 
  (ent_e a === ent_v a) s h /\ (env_assns_denote env) s h.
Proof.
  destruct a; simpl; split; intros [? ?]; split; eauto.
Qed.
Lemma env_assns_app env1 env2 s h :
  env_assns_denote (env1 ++ env2) s h <-> 
  env_assns_denote env1 s h /\ env_assns_denote env2 s h.
Proof.
  induction env1 as [| a env1]; simpl.
  - split; intros; try split; try destruct H; eauto using env_assns_emp.
  - unfold "//\\"; rewrite IHenv1.
    split; tauto.
Qed.
Lemma env_assns_remove_cons a env x :
  ~In x (fv_E (ent_e a)) ->
  remove_var (a :: env) x = a :: remove_var env x.
Proof.
  induction env; simpl; auto; destruct in_dec; intros; tauto.
Qed.
Lemma env_assns_removes_cons a env xs :
  disjoint xs (fv_E (ent_e a)) ->
  remove_vars (a :: env) xs = a :: remove_vars env xs.
Proof.
  revert a env; induction xs; intros a' env; simpl; try tauto.
  destruct 1.
  rewrites* IHxs; rewrites* env_assns_remove_cons.
Qed.
Lemma remove_comm env x y :
  remove_var (remove_var env x) y = remove_var (remove_var env y) x.
Proof.
  induction env; simpl; eauto.
  destruct in_dec; simpl; destruct in_dec; simpl; eauto.
  destruct in_dec; simpl; try tauto.
  destruct in_dec; simpl; try tauto.
  congruence.
Qed.
Lemma remove_removes env x xs :
  remove_vars (remove_var env x) xs =
  remove_var (remove_vars env xs) x.
Proof.
  induction xs; simpl; eauto.
  rewrite IHxs, remove_comm; eauto.
Qed.

Ltac no_side_cond tac := tac; [now auto_star..|idtac].
Ltac simplify_env := simpl in *;
  repeat (first [rewrite env_assns_cons in * |
                 rewrite env_assns_app in * |
                 rewrite remove_removes in * |
                 no_side_cond ltac:(rewrite env_assns_remove_cons in *) |
                 no_side_cond ltac:(rewrite env_assns_removes_cons in *)
                ]; unfold "//\\" in *) .

Lemma rule_assigns
  (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (es : list exp) (xs : list var) (ctys : list CTyp) 
  (vs : list val) Env P (Res : assn) :
  disjoint xs (fv_Es es) ->
  disjoint_list xs ->
  length xs = length es ->
  evalExps Env es vs ->
  CSL BS tid
      (Assn Res P Env)
      (assigns xs ctys es)
      (Assn Res P (EEq_tup (vars xs) vs ++ (remove_vars Env xs))).
Proof.
  revert es vs Env ctys; induction xs as [|x xs]; simpl in *;
  intros [|e es] vs Env; simpl in *; try (intros; congruence).
  - intros _ _ Hdisj Hlen Heval Hremove.
    eapply rule_conseq; eauto using rule_skip.
  - intros ctys [Hnin Hdisj] [Hxxs Hdisxs]  Hlen Heval.
    destruct vs.
    { applys (>>Hbackward FalseP).
      2: now (intros; unfold evalExps, Assn in *; simpl in *; destruct H as (? & ? & H'); sep_split_in H'; eauto).
      unfold CSL; destruct 1. }
    apply evalExps_cons in Heval as [Heval1 Heval2].
    let tac :=
        eapply rule_seq; eauto; try now forwards* Htri: (>>rule_assign)
    in
    destruct ctys; tac.
    eapply Hforward; [applys* IHxs|].
    + eapply disjoint_app_r2 in Hdisj; auto.
    + rewrite in_app_iff in Hnin.
      apply evalExps_cons_inv, evalExps_remove; try tauto.
      apply Heval2.
    + unfold Assn; intros ? ? (? & ?); split; eauto.
      sep_split_in H0; sep_split; eauto.
      repeat rewrite in_app_iff in *.
      rewrite env_assns_removes_cons in *.
      2: simpl; apply disjoint_comm; simpl; eauto.
      simplify_env; simpl in *.
      tauto.
    + eapply Hforward; [applys* IHxs|].
      * forwards*: disjoint_app_r2.
      * apply evalExps_cons_inv; applys* evalExps_remove.
        repeat rewrite in_app_iff in *; auto.
      * unfold Assn; intros ? ? (? & ?); split; eauto.
        sep_split_in H0; sep_split; eauto.
        rewrite env_assns_removes_cons in *.
        2: simpl; apply disjoint_comm; simpl; eauto.
        simplify_env; simpl in *.
        tauto.
Qed.

(* Lemma rule_read_tup_arr es len f s p P loc xs ts arrs ie iv : *)
(*   evalLExp Env le l -> *)
(*   (Res |= l -->p (p, v) ** Res') -> *)
(*   CSL BS tid *)
(*       (Assn Res P Env) *)
(*       (x ::T cty ::= [le]) *)
(*       (Assn Res P (Ent x v :: remove_var Env x)). *)