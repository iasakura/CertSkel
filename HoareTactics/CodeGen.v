Require Import GPUCSL scan_lib LibTactics Psatz CSLLemma Skel_lemma SetoidClass.
Require Import CSLLemma.

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
Definition fv_lEs es := fold_right (fun e xs => fv_lE e ++ xs) nil es.

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
  (env_assns_denote (a :: env)) s h <-> 
  (ent_e a === ent_v a) s h /\ (env_assns_denote env) s h.
Proof.
  destruct a; simpl; split; intros [? ?]; split; eauto.
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
  (vs : list val) Env P (Res : res) :
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
    { applys (>>Hbackward FalseP); [|now idtac].
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
    + unfold Assn; intros ? ? ?; eauto.
      sep_split_in H; sep_split; eauto.
      repeat rewrite in_app_iff in *.
      rewrite env_assns_removes_cons in *.
      2: simpl; apply disjoint_comm; simpl; eauto.
      simplify_env; simpl in *.
      tauto.
    + eapply Hforward; [applys* IHxs|].
      * forwards*: disjoint_app_r2.
      * apply evalExps_cons_inv; applys* evalExps_remove.
        repeat rewrite in_app_iff in *; auto.
      * unfold Assn; intros ? ? ?; eauto.
        sep_split_in H; sep_split; eauto.
        rewrite env_assns_removes_cons in *.
        2: simpl; apply disjoint_comm; simpl; eauto.
        simplify_env; simpl in *.
        tauto.
Qed.

Fixpoint Mpss (ls : list loc) p (vs : list val) :=
  match ls, vs with
  | l :: ls, v :: vs => l |->p (p, v) *** Mpss ls p vs
  | nil, nil => Emp
  | _, _ => Bot
  end.

Notation "ls '|=>p'  ( p , vs )" := (Mpss ls p vs) (at level 58).

Lemma evalLExps_cons Env e es v vs:
  evalLExps Env (e :: es) (v :: vs) -> evalLExp Env e v /\ evalLExps Env es vs.
Proof.
  intros H; inverts H; split; eauto.
Qed.

Lemma evalLExp_cons Env a e v:
  evalLExp Env e v ->
  evalLExp (a :: Env) e v.
Proof.
  induction 1;
  constructor; eauto using evalExp_cons.
Qed.

Lemma evalLExp_remove e v (x : var) Env:
  evalLExp Env e v -> ~In x (fv_lE e) ->
  evalLExp (remove_var Env x) e v.
Proof.
  induction 1; intros; simpl in *; repeat rewrite in_app_iff in *.
  econstructor; apply evalExp_remove; destruct p; eauto.
  econstructor; eauto; simpl; eauto.
  eapply evalExp_remove; eauto.
Qed.

Lemma evalLExps_remove e v (x : var) Env:
  evalLExps Env e v -> ~In x (fv_lEs e) ->
  evalLExps (remove_var Env x) e v.
Proof.
  induction 1; intros.
  - constructor.
  - constructor; eauto; simpl in *; rewrite in_app_iff in *.
    simpl in *; apply evalLExp_remove; eauto.
    apply IHForall2; eauto.
Qed.

Lemma evalLExps_cons_inv Env a e v:
  evalLExps Env e v ->
  evalLExps (a :: Env) e v.
Proof.
  induction 1; intros; simpl in *; constructor; eauto.
  apply evalLExp_cons; auto.
Qed.

Lemma rule_reads
  (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (es : list loc_exp) (xs : list var) (ctys : list CTyp) 
  (ls : list loc) (vs : list val) Env (Res Res' : res) p (P : Prop) :
  disjoint xs (fv_lEs es) ->
  disjoint_list xs ->
  length xs = length es ->
  evalLExps Env es ls ->
  (P -> Res |=R ls |=>p (p, vs) *** Res') ->
  CSL BS tid
      (Assn Res P Env)
      (reads xs ctys es)
      (Assn Res P (EEq_tup (vars xs) vs ++ (remove_vars Env xs))).
Proof.
  revert es ls vs Env ctys Res'; induction xs as [|x xs]; simpl in *;
  intros [|e es] ls vs Env ctys Res'; simpl in *; try (intros; congruence).
  - intros _ _ Hdisj Hlen Heval Hremove.
    eapply rule_conseq; eauto using rule_skip.
  - intros [Hnin Hdisj] [Hxxs Hdisxs]  Hlen Heval Hres.
    destruct ls.
    { applys (>>Hbackward FalseP); [|now idtac].
      unfold CSL; destruct 1. }
    apply evalLExps_cons in Heval as [Heval1 Heval2].
    destruct vs as [|v vs].
    { simpl in Hres.
      eapply Hbackward.
      Focus 2. {
        unfold Assn; intros s h H; sep_split_in H.
        apply (Hres HP) in H; unfold sat_res in H; simpl in H.
        apply H. } Unfocus.
      intros ? ? ?; unfold sat in *; simpl in *; destruct H as (? & ? & [] & ?). }
    simpl in Hres.
    assert (P -> Res |=R l |->p  (p, v) *** (ls |=>p  (p, vs)) *** Res') by (intros; rewrite res_assoc; eauto).
    let tac :=
        eapply rule_seq; eauto; try now forwards* Htri: (>>rule_read)
    in
    destruct ctys; tac.
    + eapply Hforward; [applys* IHxs|].
      * eapply disjoint_app_r2 in Hdisj; auto.
      * rewrite in_app_iff in Hnin.
        apply evalLExps_cons_inv, evalLExps_remove; try tauto.
        apply Heval2.
      * unfold Assn; intros ? ? ? ?; eauto.
        assert (P -> Res |=R ls |=>p (p, vs) *** l |->p (p, v) *** Res') by (intros; apply res_CA; eauto); eauto.
      * unfold Assn; intros ? ? Hsat; eauto;
        sep_split_in Hsat; sep_split; eauto.
        rewrite env_assns_removes_cons in *.
        2: simpl; apply disjoint_comm; simpl; eauto.
        simplify_env; simpl in *; tauto.
    + eapply Hforward; [applys* IHxs|].
      * eapply disjoint_app_r2 in Hdisj; auto.
      * rewrite in_app_iff in Hnin.
        apply evalLExps_cons_inv, evalLExps_remove; try tauto.
        apply Heval2.
      * unfold Assn; intros ? ? ? ?; eauto.
        assert (P -> Res |=R ls |=>p  (p, vs) *** l |->p  (p, v) *** Res') by (intros; apply res_CA; eauto); eauto.
      * unfold Assn; intros ? ? Hsat; eauto;
        sep_split_in Hsat; sep_split; eauto.
        rewrite env_assns_removes_cons in *.
        2: simpl; apply disjoint_comm; simpl; eauto.
        simplify_env; simpl in *; tauto.
Qed.

Notation gets v i := (nth i v nil).
Notation vals := (list val).

Definition locs_off ls i := List.map (fun l => loc_off l i) ls.

Fixpoint arrays ptr (arr : list vals) p :=
  match arr with
  | nil => Emp
  | vs :: arr => (ptr |=>p (p, vs)) *** arrays (locs_off ptr 1) arr p
  end.

Fixpoint arrays' ptr (arr : list (option vals)) p :=
  match arr with
  | nil => Emp
  | vs :: arr => match vs with 
                 | None => Emp
                 | Some vs => (ptr |=>p (p, vs))
                 end *** arrays' (locs_off ptr 1) arr p
  end.

Lemma locs_off0 l :
  locs_off l 0 = l.
Proof.
  induction l; simpl; eauto.
  rewrite loc_off0; congruence.
Qed.

Lemma locs_offS ptr n :
  locs_off ptr (Z.succ n) = locs_off (locs_off ptr 1) n.
Proof.
  induction ptr; simpl; eauto.
  rewrite loc_offS; congruence.
Qed.

Lemma arrays_unfold i arr ptr p:
  i < length arr -> 
  (arrays ptr arr p) ==
  ((arrays ptr (firstn i arr) p) ***
   (locs_off ptr (Zn i) |=>p (p, gets arr i)) ***
   (arrays (locs_off ptr (Z.succ (Zn i))) (skipn (S i) arr) p)).
Proof.
  simpl; unfold equiv_sep, sat_res, sat;
  revert arr ptr; induction i; intros arr ptr.
  - destruct arr; simpl; try (intros; omega); intros _ s h; unfold sat_res, sat in *; simpl.
    split; intros; sep_normal; sep_normal_in H; rewrite locs_off0 in *; eauto. 
  - destruct arr as [|v arr]; try (simpl; intros; omega).
    intros Hlen'; simpl in Hlen'; assert (Hlen : i < length arr) by omega.
    rewrite Nat2Z.inj_succ.
    do 2 rewrite locs_offS; simpl.
    split; unfold sat_res, sat in *; unfold sat_res, sat in *;
    intros; simpl in *; sep_normal; sep_normal_in H; repeat sep_cancel.
    apply IHi in H0; sep_normal_in H0; eauto.
    apply IHi; sep_normal; eauto.
Qed.

Lemma arrays_eq ls vs vs' p :
  vs = vs' -> arrays ls vs p == arrays ls vs' p.
Proof.
  intros ->; reflexivity.
Qed.

Lemma precise_bot :
  precise_res Bot.
Proof.
  unfold precise_res, sat_res; simpl; intros.
  destruct H.
Qed.

Hint Resolve precise_bot.

Lemma precise_mpss ls vs p :
  precise_res (ls |=>p (p, vs)).
Proof.
  revert vs; induction ls; intros [|v vs]; simpl; eauto.
Qed.

Lemma precise_arrays ls vs p:
  precise_res (arrays ls vs p).
Proof.
  revert ls; induction vs; simpl; intros; eauto using precise_mpss.
Qed.

Lemma precise_arrays' ls vs p:
  precise_res (arrays' ls vs p).
Proof.
  revert ls; induction vs as [|[?|] ?]; simpl; intros; eauto using precise_mpss.
Qed.

Lemma bot_bot :
  (Bot *** Bot) == Bot.
Proof.
  split; intros.
  destruct H as (? & ? & [] & ?).
  destruct H.
Qed.

Lemma mpss_p_star ls vs p1 p2 :
  (0 < p1)%Qc ->
  (p1 <= 1)%Qc ->
  (0 < p2)%Qc ->
  (p2 <= 1)%Qc ->
  (p1 + p2 <= 1)%Qc ->
  ls |=>p  (p1 + p2, vs) == (ls |=>p  (p1, vs) *** ls |=>p  (p2, vs)).
Proof.
  revert vs; induction ls; intros [|v vs]; simpl; intros; eauto;
  try rewrite emp_unit_l_res; try rewrite bot_bot; try reflexivity.
  rewrites* mps_p_star; rewrites* IHls.
  rewrite <-!res_assoc.
  rewrite (res_CA (a |->p (p2, v))); reflexivity.
Qed.

Lemma arrays_p_star loc xs p q :
  (0 < p)%Qc ->
  (p <= 1)%Qc ->
  (0 < q)%Qc ->
  (q <= 1)%Qc ->
  (p + q <= 1)%Qc ->
  arrays loc xs (p + q) == (arrays loc xs p *** arrays loc xs q).
Proof.
  revert loc; induction xs; simpl; intros; eauto.
  - rewrite emp_unit_l_res; reflexivity.
  - rewrite* mpss_p_star; rewrite* IHxs.
    rewrite <-!res_assoc.
    rewrite (res_CA (arrays (locs_off loc 1) xs p)); reflexivity.
Qed.
Section Q.
Require Import QArith Qcanon.

Ltac Qc_to_Q :=
  match goal with
  | [q : Qc |- _] => destruct q; Qc_to_Q
  | [|- _] =>
    try applys Qc_is_canon;
    repeat ( unfold Q2Qc, Qcmult, Qcplus, Qcdiv, Qcinv, Qclt, Qcle in *);
    repeat (try rewrite this_inv in *; try rewrite Qred_correct in *)
  end.

Lemma arrays_p_n loc xs (p : Qc) (nt : nat) :
  (0 < p)%Qc -> (p <= 1)%Qc -> (injZ (Zn nt) * p <= 1)%Qc -> (nt <> 0)%nat -> 
  forall st,
    arrays loc xs (injZ (Z.of_nat nt) * p) == istar (ls_init st nt (fun i => arrays loc xs p)).
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
     rewrite arrays_p_star, IHnt; [|subst nt'; unfold injZ in *; injZ_simplify; Qc_to_Q; eauto; pose proof (inject_Z_n_ge0 nt); try lra..|].
     rewrite res_comm; reflexivity.
     assert (0 <= inject_Z (Zn nt) * this)%Q by (apply Qmult_le_0_compat; lra_Qc).
     lra.
     injZ_simplify.
     Qc_to_Q.
     lra.
Qed.

Lemma is_array_is_array_p_1 loc xs (nt : nat) st :
  (nt <> 0)%nat ->
  arrays loc xs 1 ==
  istar (ls_init st nt (fun i => arrays loc xs (1 / (injZ (Zn nt))))).
Proof.    
  intros; rewrite (@one_div_n nt) at 1; eauto.
  apply arrays_p_n; eauto;
  unfold injZ; Qc_to_Q; destruct nt; try omega; lets: (inject_Z_Sn_gt0 nt).
  apply Qlt_shift_div_l; lra.
  apply Qle_shift_div_r; try lra.
  lets Heq: Qmult_div_r; unfold Qdiv in Heq; rewrite Heq; lra.
Qed.
End Q.
Close Scope Q_scope.
Close Scope Qc_scope.

Lemma arrays'_unfold i arr ptr p:
  i < length arr -> 
  (arrays' ptr arr p) ==
  ((arrays' ptr (firstn i arr) p) ***
   (match nth i arr None with
    | Some v => locs_off ptr (Zn i) |=>p (p, v)
    | None => Emp
    end) ***
   (arrays' (locs_off ptr (Z.succ (Zn i))) (skipn (S i) arr) p)).
Proof.
  unfold array.
  simpl; unfold equiv_res, sat_res, sat;
  revert arr ptr; induction i; intros arr ptr.
  - destruct arr; simpl; try (intros; omega); intros _ s h.
    split; intros; sep_normal; sep_normal_in H; rewrite locs_off0 in *; eauto. 
  - destruct arr as [|v arr]; try (simpl; intros; omega).
    intros Hlen'; simpl in Hlen'; assert (Hlen : i < length arr) by omega.
    rewrite Nat2Z.inj_succ.
    do 2 rewrite locs_offS; simpl.
    split; intros; sep_normal; sep_normal_in H; repeat sep_cancel.
    rewrites* IHi in H0.
    rewrites* IHi.
Qed.

Lemma arrays'_oq ls ls' ptr p :
  ls = ls' -> arrays' ptr ls p == arrays' ptr ls' p.
Proof.
  intros ->; reflexivity.
Qed.

Lemma array'_ok n ptr dist vals s p :
  (forall i, s <= i < length vals + s -> dist i < n) ->
  istar (ls_init 0 n (fun i => arrays' ptr (ith_vals dist vals i s) p)) ==
  arrays ptr vals p.
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
                  (ptr |=>p (p, a)) ::
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

Definition locs_offset le e :=
  List.map (fun l => loc_offset l e) le.

Infix "+os" := (locs_offset) (at level 50, left associativity).

Definition equiv_list_set (T : Type) (ls1 ls2 : list T) := (forall x, In x ls1 <-> In x ls2).
Instance equiv_list_set_equiv T : Equivalence (equiv_list_set T).
Proof.
  unfold equiv_list_set; constructor.
  - intros ? ?; tauto.
  - intros xs ys H ?; rewrite H; tauto.
  - intros xs ys zs H1 H2 ?; rewrite H1, H2; reflexivity.
Qed.

Program Instance list_set_setoid T : Setoid (list T) :=
  {| equiv := equiv_list_set T;
     setoid_equiv := equiv_list_set_equiv T |}.

Instance In_proper T x : Proper (equiv_list_set T ==> iff) (In x).
Proof.
  unfold equiv_list_set; intros ls1 ls2 H; rewrite H; tauto.
Qed.

Instance disjoint_proper T : Proper (equiv_list_set T ==> equiv_list_set T ==> iff) disjoint.
Proof.
  unfold equiv_list_set; intros l1 l1' Heq1 l2 l2' Heq2.
  split; intros;
  apply not_in_disjoint; intros x; lets*: (>>disjoint_not_in_r x H); intros;
  rewrite <-Heq2, <-Heq1 in *; tauto.
Qed.

Lemma eval_locs_off Env es ls ix i :
  evalLExps Env es ls ->
  evalExp Env ix i ->
  evalLExps Env (es +os ix) (locs_off ls i).
Proof.
  revert ls; induction es; intros [|l ls]; intros H Hix; inverts H; simpl; eauto.
  - constructor.
  - constructor.
    constructor; eauto.
    applys* IHes.
Qed.

Lemma fv_lEs_off es ix:
  incl (fv_lEs (es +os ix)) (fv_lEs es ++ fv_E ix).
Proof.
  unfold incl; intros x; induction es; simpl; eauto; try tauto.
  rewrite !in_app_iff in *.
  intros [[? | ?] | ?]; tauto.
Qed.

Lemma disjoint_app T (xs ys zs : list T) :
  disjoint xs (ys ++ zs) <-> disjoint xs ys /\ disjoint xs zs.
Proof.
  induction xs; simpl; try tauto.
  rewrite !in_app_iff; split; intros; tauto.
Qed.

Lemma locs_off_length es ix :
  length (es +os ix) = length es.
Proof.
  unfold "+os"; rewrite* map_length.
Qed.

Lemma rule_reads_arrays (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (es : list loc_exp) (xs : list var) (ctys : list CTyp) 
  (ls : list loc) (vs : list val) Env (Res Res' : res) p (P : Prop) arr ix iz i_n :
  disjoint xs (fv_lEs es) ->
  disjoint xs (fv_E ix) ->
  disjoint_list xs ->
  length xs = length es ->

  evalLExps Env es ls ->
  evalExp Env ix iz ->
  (P -> Res |=R arrays ls arr p *** Res') ->

  iz = Zn i_n ->
  (P -> i_n < length arr) ->

  CSL BS tid
      (Assn Res P Env)
      (reads xs ctys (es +os ix))
      (Assn Res P (EEq_tup (vars xs) (gets arr i_n) ++ (remove_vars Env xs))).
Proof.
  intros.
  applys* rule_reads.
  - eapply disjoint_incl; [apply fv_lEs_off|].
    rewrite disjoint_app; eauto.
  - rewrite locs_off_length; eauto.
  - apply eval_locs_off; eauto.
  - intros; forwards*Himp: H5.
    rewrite arrays_unfold in Himp; [|applys* H7].
    substs; rewrite <-!res_assoc in Himp; rewrites* res_CA in Himp.
Qed.

Lemma rule_reads_arrays' (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (es : list loc_exp) (xs : list var) (ctys : list CTyp) 
  (ls : list loc) (vs : list val) Env (Res Res' : res) p (P : Prop) arr ix iz i_n dist j st:
  disjoint xs (fv_lEs es) ->
  disjoint xs (fv_E ix) ->
  disjoint_list xs ->
  length xs = length es ->

  evalLExps Env es ls ->
  evalExp Env ix iz ->
  (P -> Res |=R arrays' ls (ith_vals dist arr j st) p *** Res') ->

  iz = Zn i_n ->
  (P -> i_n < length arr /\ dist (st + i_n) = j) ->

  CSL BS tid
      (Assn Res P Env)
      (reads xs ctys (es +os ix))
      (Assn Res P (EEq_tup (vars xs) (gets arr i_n) ++ (remove_vars Env xs))).
Proof.
  intros.
  applys* rule_reads.
  - eapply disjoint_incl; [apply fv_lEs_off|].
    rewrite disjoint_app; eauto.
  - rewrite locs_off_length; eauto.
  - apply eval_locs_off; eauto.
  - intros; forwards*Himp: H5.
    rewrites (>>arrays'_unfold i_n) in Himp; [|].
    rewrite ith_vals_length; tauto.
    rewrite (nth_skip _ nil) in Himp.
    destruct Nat.eq_dec; [|forwards*: H7; try lia].
    destruct lt_dec; [|forwards*: H7; try lia].
    substs; rewrite <-!res_assoc in Himp; rewrites* res_CA in Himp.
Qed.    

Lemma rule_writes  (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (les : list loc_exp) (es : list exp) 
  (ls : list loc) (vs vs' : list val) Env (Res Res' : res) (P : Prop) :
  length les = length es ->
  evalExps Env es vs ->
  evalLExps Env les ls ->
  (P -> Res |=R ls |=>p (1, vs') *** Res') ->
  CSL BS tid
      (Assn Res P Env)
      (writes les es)
      (Assn (ls |=>p (1, vs) *** Res') P Env).
Proof.
  revert es ls vs vs' Env Res Res'; induction les as [|le les]; simpl in *;
  intros [|e es] ls vs vs' Env Res Res'; simpl in *; try (intros; congruence).
  - intros _ Heval Hleval Hres.
    inverts Hleval; inverts Heval.
    eapply rule_conseq; eauto using rule_skip.
    apply Assn_imply; eauto using incl_refl.
    destruct vs'; simpl in *; eauto.
    intros; forwards*(? & ? & [] & ?): Hres.
  - intros Hlen Heval Hleval Hres.
    destruct ls; [inverts Hleval | ].
    apply evalLExps_cons in Hleval as [Hleval1 Hleval2].
    destruct vs as [|v vs]; [inverts Heval|].
    apply evalExps_cons in Heval as [Heval1 Heval2].
    destruct vs' as [|v' vs'].
    { simpl in Hres.
      eapply Hbackward.
      Focus 2. {
        unfold Assn; intros s h H; sep_split_in H.
        apply (Hres HP) in H; unfold sat_res in H; simpl in H.
        apply H. } Unfocus.
      intros ? ? ?; unfold sat in *; simpl in *; destruct H as (? & ? & [] & ?). }
    simpl in Hres.
    assert (P -> Res |=R l |->p (1, v') *** (ls |=>p (1, vs')) *** Res') by (intros; rewrite res_assoc; eauto).
    simpl.
    applys (>>forward (Assn (l |->p (1, v) *** (ls |=>p (1, vs) *** Res')) P Env)).
    { intros ? ?; eapply Assn_imply; eauto; eauto using incl_refl; intros; rewrite <-res_assoc; auto. }
    eapply rule_seq; eauto; try now forwards* Htri: (>>rule_write).
    let tac := 
        intros ? ?; eapply Assn_imply; eauto; eauto using incl_refl; intros; rewrite <-res_CA; auto in
    applys (>>forward (Assn (ls |=>p  (1, vs) *** l |->p  (1, v) *** Res') P Env)); [tac|];
    applys (>>backward (Assn (ls |=>p  (1, vs') *** l |->p  (1, v) *** Res') P Env)); [tac|]. 
    applys* IHles.
Qed.

Lemma rule_writes_arrays  (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (les : list loc_exp) (es : list exp) 
  (ls : list loc) (vs : list val) Env (Res Res' : res) (P : Prop) arr ix iz i_n:
  length les = length es ->
  evalExps Env es vs ->
  evalExp Env ix iz ->
  evalLExps Env les ls ->
  iz = Zn i_n ->
  (P -> i_n < length arr) ->
  (P -> Res |=R arrays ls arr 1 *** Res') ->
  CSL BS tid
      (Assn Res P Env)
      (writes (les +os ix) es)
      (Assn (arrays ls (set_nth i_n arr vs) 1 *** Res') P Env).
Proof.
  intros; eapply forward; [|applys* (>>rule_writes (locs_off ls iz) vs)].
  2: rewrite* locs_off_length.
  2: applys* eval_locs_off.
  intros ? ?.
  apply Assn_imply; eauto using incl_refl.
  intros Hp ? ? Hsat; rewrites (>>arrays_unfold i_n); [rewrite* length_set_nth|].
  rewrite nth_set_nth.
  forwards*: H4.
  destruct Nat.eq_dec; try lia.
  destruct lt_dec; try lia.
  rewrite <-!res_assoc, res_CA; substs; eauto.
  intros Hp ? ? Hsat.
  lets* Hsat': (>> H5 Hsat).
  rewrites (>>arrays_unfold i_n) in Hsat'; eauto.
  rewrite <-!res_assoc, res_CA in Hsat'; eauto.
  clear Hsat.
  substs.
  rewrite skipn_set_nth_ignore, firstn_set_nth_ignore; eauto.
Qed.

Lemma rule_writes_array'  ntrd BS
      (tid : Fin.t ntrd) (les : list loc_exp) (ls : list loc) 
      (Env : list entry) (P : Prop) (Res Res' : res) (arr : list vals) dist ix i iz j es vs st:
  length les = length es ->
  evalLExps Env les ls ->
  evalExp Env ix iz ->
  evalExps Env es vs ->
  iz = Zn i ->
  (P -> i < length arr /\ dist (st + i) = j) ->
  (P -> Res |=R arrays' ls (ith_vals dist arr j st) 1 *** Res') ->
  CSL BS tid
      (Assn Res P Env)
      (writes (les +os ix) es)
      (Assn (arrays' ls (ith_vals dist (set_nth i arr vs) j st) 1 *** Res') P Env).
Proof.
  intros.
  eapply forward; [|applys* (>>rule_writes (locs_off ls iz) vs)].
  2: rewrites* locs_off_length.
  2: applys* eval_locs_off.
  apply Assn_imply; eauto using incl_refl.
  intros Hp ? ? Hsat.
  forwards*: H4.
  rewrite (arrays'_unfold i).
  2: rewrite ith_vals_length, length_set_nth; lia.
  rewrite (nth_skip _ nil).
  destruct Nat.eq_dec; try lia.
  rewrite length_set_nth; destruct lt_dec; [|lia].
  rewrite nth_set_nth.
  destruct Nat.eq_dec; try lia.
  destruct lt_dec; try lia.
  rewrite <-!res_assoc, res_CA; substs; eauto.
  
  intros Hp s h Hsat.
  apply H5 in Hsat; auto.
  forwards*: H4.
  rewrite (arrays'_unfold i) in Hsat.
  2: rewrite ith_vals_length; lia.
  rewrite (nth_skip _ nil) in Hsat.
  destruct Nat.eq_dec; try (false; lia).
  destruct lt_dec; [|false; lia].
  rewrite <-!res_assoc, res_CA in Hsat; substs; eauto.
  rewrite ith_vals_set_nth, firstn_set_nth_ignore, skipn_set_nth_ignore.
  eauto.
Qed.