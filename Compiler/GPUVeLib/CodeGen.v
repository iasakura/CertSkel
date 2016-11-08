Require Import GPUCSL scan_lib LibTactics Psatz CSLLemma Skel_lemma SetoidClass.
Require Import CUDALib CSLLemma TypedTerm CUDALib.

Fixpoint evalExps {ty : Skel.Typ} (Env : list entry) :=
  match ty return exps ty -> vals ty -> Prop with
  | Skel.TBool | Skel.TZ => fun e v => evalExp Env e v
  | Skel.TTup _ _ => fun es vs => evalExps Env (fst es) (fst vs) /\ evalExps Env (snd es) (snd vs)
  end.

(* Lemma evalExps_ok Env e v :  *)
(*   evalExps Env e v -> *)
(*   env_assns_denote Env ===> (e ==t v). *)
(* Proof. *)
(*   induction 1; simpl; eauto. *)
(*   - apply env_assns_emp. *)
(*   - intros; forwards*: IHForall2. *)
(*     sep_split; eauto. *)
(*     forwards*: evalExp_ok. *)
(* Qed. *)

(* Fixpoint eq_ltup (es : list loc_exp) (vs : list loc) : assn := *)
(*   match es, vs with *)
(*   | nil, nil => emp *)
(*   | e :: es, v :: vs => !(e ===l v) ** eq_ltup es vs *)
(*   | _, _ => FalseP *)
(*   end. *)

(* Notation "e1 ==lt e2" := (eq_ltup e1 e2) (at level 70, right associativity). *)

Fixpoint evalLExps {ty : Skel.Typ} (Env : list entry) :=
  match ty return lexps ty -> locs ty -> Prop with
  | Skel.TBool | Skel.TZ => fun e v => evalLExp Env e v
  | Skel.TTup _ _ => fun es vs => evalLExps Env (fst es) (fst vs) /\ evalLExps Env (snd es) (snd vs)
  end.

(* Lemma evalLExps_ok Env e v : *)
(*   evalLExps Env e v -> *)
(*   env_assns_denote Env ===> (e ==lt v). *)
(* Proof. *)
(*   induction 1; simpl; eauto. *)
(*   - apply env_assns_emp. *)
(*   - intros; forwards*: IHForall2. *)
(*     sep_split; eauto. *)
(*     forwards*: evalLExp_ok. *)
(* Qed. *)

Definition removed_xs (Env : assn) (xs : list var) (Env' : assn) :=
  (Env |= Env') /\ (inde Env' (xs)).

(* Definition vars := List.map Evar. *)

Lemma evalExps_tup t1 t2 Env (es1 : exps t1) (es2 : exps t2) (vs1 : vals t1) (vs2 : vals t2) :
  @evalExps (Skel.TTup t1 t2) Env (es1, es2) (vs1, vs2) -> evalExps Env es1 vs1 /\ evalExps Env es2 vs2.
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

Lemma remove_var_app e1 e2 x :
  remove_var (e1 ++ e2) x = remove_var e1 x ++ remove_var e2 x.
Proof.
  induction e1; simpl; eauto; rewrite IHe1.
  destruct var_eq_dec; eauto.
Qed.

Lemma remove_vars_app e1 e2 xs :
  remove_vars (e1 ++ e2) xs = remove_vars e1 xs ++ remove_vars e2 xs.
Proof.
  induction xs; simpl; eauto.
  rewrite IHxs, remove_var_app; eauto.
Qed.

Lemma remove_vars_cons e env xs :
  remove_vars (e :: env) xs = remove_vars (e :: nil) xs ++ remove_vars env xs.
Proof.
  cutrewrite (e :: env = (e :: nil) ++ env); [|eauto].
  rewrite* remove_vars_app.
Qed.

Lemma remove_vars_nil xs : remove_vars nil xs = nil.
Proof.
  induction xs; simpl; eauto.
  rewrite IHxs; eauto.
Qed.          

Lemma remove_var_disjoint es x :
  ~In x (map ent_e es)  ->
  remove_var es x = es.
Proof.
  induction es; simpl; eauto.
  destruct var_eq_dec; simpl; intros; rewrite IHes; eauto.
  substs; false; eauto.
Qed.
  
Lemma remove_vars_disjoint es xs :
  disjoint (map ent_e es) xs ->
  remove_vars es xs = es.
Proof.
  induction xs; simpl; eauto.
  intros H; apply disjoint_comm in H as [? H]; simpl in *.
  forwards*Heq: IHxs; eauto using disjoint_comm.
  rewrite Heq, remove_var_disjoint; eauto.
Qed.

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
  destruct var_eq_dec; simpl; eauto.
  intros [? | ?]; try tauto; congruence.
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
  intros; destruct var_eq_dec; simpl in *; eauto.
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

Fixpoint EEq_tup {ty : Skel.Typ}  :=
  match ty return vars ty -> vals ty -> _ with
  | Skel.TBool | Skel.TZ => fun x v => Ent x v :: nil
  | Skel.TTup _ _ => fun xs vs =>
    EEq_tup (fst xs) (fst vs) ++ EEq_tup (snd xs) (snd vs)
  end.

Notation "x |=> v" := (EEq_tup x v) (at level 58).

Fixpoint fv_Es {ty : Skel.Typ} := 
  match ty return exps ty -> list var with
  | Skel.TBool | Skel.TZ => fun e => fv_E e
  | Skel.TTup _ _ => fun es => 
    fv_Es (fst es) ++ fv_Es (snd es)
  end.

Fixpoint fv_lEs {ty : Skel.Typ} := 
  match ty return lexps ty -> list var with
  | Skel.TBool | Skel.TZ => fun le => fv_lE le
  | Skel.TTup _ _ => fun les => 
    fv_lEs (fst les) ++ fv_lEs (snd les)
  end.

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
  destruct H; substs; destruct var_eq_dec; simpl in *; eauto; try tauto.
  substs; false; tauto.
Qed.

Lemma evalExps_remove {ty : Skel.Typ} (e : exps ty) v (x : var) Env:
  evalExps Env e v -> ~In x (fv_Es e) ->
  evalExps (remove_var Env x) e v.
Proof.
  induction ty; simpl in *; intros; eauto using evalExp_remove.
  constructor; [apply IHty1 | apply IHty2]; try tauto;
  rewrite in_app_iff in *; eauto.
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

Lemma evalExps_cons_inv ty Env a (e : exps ty) v:
  evalExps Env e v ->
  evalExps (a :: Env) e v.
Proof.
  induction ty; simpl in *; eauto using evalExp_cons.
  intuition.
Qed.
      
Lemma env_assns_cons a env s h :
  (env_assns_denote (a :: env)) s h <-> 
  (ent_e a === ent_v a) s h /\ (env_assns_denote env) s h.
Proof.
  destruct a; simpl; split; intros [? ?]; split; eauto.
Qed.

Lemma env_assns_remove_cons a env x :
  x <> (ent_e a) ->
  remove_var (a :: env) x = a :: remove_var env x.
Proof.
  induction env; simpl; auto; destruct var_eq_dec; intros; try tauto.
Qed.

Lemma env_assns_removes_cons a env xs :
  ~In (ent_e a) xs ->
  remove_vars (a :: env) xs = a :: remove_vars env xs.
Proof.
  revert a env; induction xs; intros a' env; simpl; try tauto.
  intros; rewrite IHxs, env_assns_remove_cons; eauto.
Qed.

Lemma remove_comm env x y :
  remove_var (remove_var env x) y = remove_var (remove_var env y) x.
Proof.
  induction env; simpl; eauto.
  destruct var_eq_dec; simpl; destruct var_eq_dec; simpl; eauto.
  destruct var_eq_dec; simpl; try tauto.
  destruct var_eq_dec; simpl; try tauto.
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

Lemma env_assns_remove_app ty (xs : vars ty) vs e x :
  disjoint x (flatTup xs) ->
  remove_vars (EEq_tup xs vs ++ e) x = EEq_tup xs vs ++ remove_vars e x.
Proof.
  revert e; induction ty; simpl in *; intros;
  try now (apply disjoint_comm in H; simpl in H; try now applys* env_assns_removes_cons).
  rewrite <-!app_assoc, IHty1, IHty2; eauto using disjoint_app_r1, disjoint_app_r2.
Qed.

Lemma remove_vars_nest (xs ys : list var) e :
  remove_vars e (xs ++ ys) =
  remove_vars (remove_vars e xs) ys.
Proof.
  induction xs; simpl; eauto.
  rewrite IHxs, remove_removes; eauto.
Qed.

Lemma evalExps_app_inv2 ty Env1 Env2 (e : exps ty) v:
  evalExps Env2 e v ->
  evalExps (Env1 ++ Env2) e v.
Proof.
  induction Env1; simpl; eauto using evalExps_cons_inv.
Qed.
Lemma evalExps_removes ty Env xs (es : exps ty) vs :
  disjoint xs (fv_Es es) ->
  evalExps Env es vs ->
  evalExps (remove_vars Env xs) es vs.
Proof.
  induction xs; simpl; [|intros [? ?]]; eauto using evalExps_remove.
Qed.

Lemma disjoint_list_proj1 T (xs ys : list T) :
  disjoint_list (xs ++ ys) -> disjoint_list xs.
Proof.
  induction xs; simpl; eauto.
  rewrite !in_app_iff; tauto.
Qed.
Lemma disjoint_list_proj2 T (xs ys : list T) :
  disjoint_list (xs ++ ys) -> disjoint_list ys.
Proof.
  induction xs; simpl; eauto.
  rewrite !in_app_iff; tauto.
Qed.
Lemma disjoint_list_app_disjoint T (xs ys : list T) :
  disjoint_list (xs ++ ys) -> disjoint xs ys.
Proof.
  induction xs; simpl; eauto.
  rewrite !in_app_iff; tauto.
Qed.

Lemma rule_assigns
  (ty : Skel.Typ)
  (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (es : exps ty) (xs : vars ty) (tys : ctys ty) 
  (vs : vals ty) Env P (Res : res) :
  disjoint (flatTup xs) (fv_Es es) ->
  disjoint_list (flatTup xs) ->
  evalExps Env es vs ->
  CSL BS tid
      (Assn Res P Env)
      (assigns xs tys es)
      (Assn Res P (EEq_tup xs vs ++ (remove_vars Env (flatTup xs)))).
Proof.
  Ltac tac := eauto using disjoint_app_r1, disjoint_comm, disjoint_app_r2,
              disjoint_list_proj1, disjoint_list_proj2, disjoint_list_app_disjoint.
  revert Env; induction ty; simpl in *; try now (intros ? [Hnin _] Heval; eauto using rule_assign).
  intros Env Hdisj Hdisjxs [Heval1 Heval2]; eapply rule_seq; [apply IHty1 | eapply forward; [|apply IHty2] ]; jauto; tac.
  apply Assn_imply; eauto.
  intros ? x; repeat rewrite in_app_iff in *; intros [[? | ?] | ?]; tac.
  

  rewrite env_assns_remove_app, in_app_iff; tac.
  rewrite env_assns_remove_app; tac.
  rewrite in_app_iff, <-remove_vars_nest; eauto.
  apply evalExps_app_inv2.

  apply evalExps_removes; tac.
Qed.

Fixpoint Mpss {ty : Skel.Typ} :=
  match ty return locs ty -> Qc -> vals ty -> res with
  | Skel.TBool | Skel.TZ => fun l p v => l |->p (p, v)
  | Skel.TTup _ _ => fun ls p vs => 
    Mpss (fst ls) p (fst vs) *** Mpss (snd ls) p (snd vs)
  end.

Notation "ls '|=>p'  ( p , vs )" := (Mpss ls p vs) (at level 58).

Lemma evalLExps_tup t1 t2 Env es1 es2 vs1 vs2:
  @evalLExps (Skel.TTup t1 t2) Env (es1, es2) (vs1, vs2) ->
  evalLExps Env es1 vs1 /\ evalLExps Env es2 vs2.
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

Lemma evalLExps_remove ty (e : lexps ty) v (x : var) Env:
  evalLExps Env e v -> ~In x (fv_lEs e) ->
  evalLExps (remove_var Env x) e v.
Proof.
  induction ty; intros; try applys* evalLExp_remove.
  simpl in *; rewrite in_app_iff in *; intuition.
Qed.

Lemma evalLExps_cons_inv ty Env a (e : lexps ty) v:
  evalLExps Env e v ->
  evalLExps (a :: Env) e v.
Proof.
  induction ty; intros; simpl in *; eauto using evalLExp_cons.
  intuition.
Qed.

Lemma evalLExps_app_inv2 ty Env1 Env2 (e : lexps ty) v:
  evalLExps Env2 e v ->
  evalLExps (Env1 ++ Env2) e v.
Proof.
  induction Env1; simpl; eauto using evalLExps_cons_inv.
Qed.
Lemma evalLExps_removes ty Env xs (es : lexps ty) vs :
  disjoint xs (fv_lEs es) ->
  evalLExps Env es vs ->
  evalLExps (remove_vars Env xs) es vs.
Proof.
  induction xs; simpl; [|intros [? ?]]; eauto using evalLExps_remove.
Qed.

Lemma rule_reads
  (ty : Skel.Typ) (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (es : lexps ty) (xs : vars ty) (ctys : ctys ty) 
  (ls : locs ty) (vs : vals ty) Env (Res Res' : res) p (P : Prop) :
  disjoint (flatTup xs) (fv_lEs es) ->
  disjoint_list (flatTup xs) ->
  evalLExps Env es ls ->
  (P -> Res |=R ls |=>p (p, vs) *** Res') ->
  CSL BS tid
      (Assn Res P Env)
      (reads xs ctys es)
      (Assn Res P (EEq_tup xs vs ++ (remove_vars Env (flatTup xs)))).
Proof.
  revert Env Res'; induction ty; simpl in *; try now (intros ? ? [Hnin _] Heval; eauto using rule_read).
  intros Env Res' Hdisj Hdisjxs [Heval1 Heval2] Hres; eapply rule_seq; [eapply IHty1 |]; tac.
  { intros; rewrite res_assoc; eauto. }
  eapply forward; [|eapply IHty2]; tac.

  apply Assn_imply; eauto.
  intros ? x; repeat rewrite in_app_iff in *; intros [[? | ?] | ?]; tac.

  rewrite env_assns_remove_app, in_app_iff; tac.
  rewrite env_assns_remove_app; tac.
  rewrite in_app_iff, <-remove_vars_nest; eauto.

  apply evalLExps_app_inv2.
  apply evalLExps_removes; tac.

  intros; rewrite res_CA, res_assoc; eauto.
Qed.

Fixpoint defval {ty} : vals ty:= 
  match ty return vals ty with
  | Skel.TBool | Skel.TZ => 0%Z
  | Skel.TTup t1 t2 => (@defval t1, @defval t2)
  end.

Notation gets v i := (nth i v defval).

Fixpoint locs_off {ty} : locs ty -> Z -> locs ty:= 
  match ty return locs ty -> Z -> locs ty with
  | Skel.TBool | Skel.TZ => loc_off 
  | Skel.TTup t1 t2 => fun l off => (locs_off (fst l) off, locs_off (snd l) off)
  end.

Fixpoint arrays {ty} (ptr : locs ty) (arr : list (vals ty)) p :=
  match arr with
  | nil => Emp
  | vs :: arr => (ptr |=>p (p, vs)) *** arrays (locs_off ptr 1) arr p
  end.

Fixpoint arrays' {ty} ptr (arr : list (option (vals ty))) p :=
  match arr with
  | nil => Emp
  | vs :: arr => match vs with 
                 | None => Emp
                 | Some vs => (ptr |=>p (p, vs))
                 end *** arrays' (locs_off ptr 1) arr p
  end.

Lemma locs_off0 ty (l : locs ty) :
  locs_off l 0 = l.
Proof.
  induction ty; simpl; try rewrite loc_off0; eauto. 
  rewrite IHty1, IHty2; destruct l; eauto.
Qed.

Lemma locs_offS ty (ptr : locs ty) n :
  locs_off ptr (Z.succ n) = locs_off (locs_off ptr 1) n.
Proof.
  induction ty; simpl; try rewrite loc_offS; eauto.
  congruence.
Qed.

Lemma arrays_unfold ty i (arr : list (vals ty)) ptr p:
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

Lemma arrays_eq ty (ls : locs ty) vs vs' p :
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

Lemma precise_mpss ty (ls : locs ty) vs p :
  precise_res (ls |=>p (p, vs)).
Proof.
  revert vs; induction ty; simpl in *; eauto using precise_mps.
Qed.

Lemma precise_arrays ty (ls : locs ty) vs p:
  precise_res (arrays ls vs p).
Proof.
  revert ls; induction vs; simpl; intros; eauto using precise_mpss.
Qed.

Lemma precise_arrays' ty (ls : locs ty) vs p:
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

Lemma mpss_p_star ty (ls : locs ty) vs p1 p2 :
  (0 < p1)%Qc ->
  (p1 <= 1)%Qc ->
  (0 < p2)%Qc ->
  (p2 <= 1)%Qc ->
  (p1 + p2 <= 1)%Qc ->
  ls |=>p  (p1 + p2, vs) == (ls |=>p  (p1, vs) *** ls |=>p  (p2, vs)).
Proof.
  revert vs; induction ty; simpl; intros; eauto; try rewrite* mps_p_star; try reflexivity.
  rewrite IHty1, IHty2; eauto.
  rewrite <-!res_assoc.
  rewrite (res_CA (fst ls |=>p (p2, fst vs))); reflexivity.
Qed.

Lemma arrays_p_star ty (loc : locs ty) xs p q :
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

Lemma arrays_p_n ty (loc : locs ty) xs (p : Qc) (nt : nat) :
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
     rewrite arrays_p_star, IHnt; [|clear IHnt; subst nt'; unfold injZ in *; injZ_simplify; Qc_to_Q; eauto; pose proof (inject_Z_n_ge0 nt); try lra..|].
     rewrite res_comm; reflexivity.
     assert (0 <= inject_Z (Zn nt) * this)%Q by (apply Qmult_le_0_compat; lra_Qc).
     lra.
     injZ_simplify.
     Qc_to_Q.
     lra.
Qed.

Lemma is_array_is_array_p_1 ty (loc : locs ty) xs (nt : nat) st :
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

Lemma arrays'_unfold ty i (arr : list (option (vals ty))) ptr p:
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

Lemma arrays'_oq ty ls ls' (ptr : locs ty) p :
  ls = ls' -> arrays' ptr ls p == arrays' ptr ls' p.
Proof.
  intros ->; reflexivity.
Qed.

Lemma array'_ok ty n (ptr : locs ty) dist vals s p :
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

Definition equiv_list_set (T : Type) (ls1 ls2 : list T) := (forall x, In x ls1 <-> In x ls2).
Instance equiv_list_set_equiv T : Equivalence (equiv_list_set T).
Proof.
  unfold equiv_list_set; constructor.
  - intros ? ?; tauto.
  - intros xs ys H ?; rewrite H; tauto.
  - intros xs ys zs H1 H2 ?; rewrite H1, H2; reflexivity.
Qed.

Program Instance list_set_setoid T : Setoid (list T) :=
  {| SetoidClass.equiv := equiv_list_set T;
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

Lemma eval_locs_off ty Env (es : lexps ty) ls ix i :
  evalLExps Env es ls ->
  evalExp Env ix i ->
  evalLExps Env (es +os ix) (locs_off ls i).
Proof.
  revert ls; induction ty; simpl; intros; try now constructor.
  intuition.
Qed.

Lemma fv_lEs_off ty (es : lexps ty)  ix:
  incl (fv_lEs (es +os ix)) (fv_lEs es ++ fv_E ix).
Proof.
  unfold incl; intros x; induction ty; simpl; eauto; try tauto.
  rewrite !in_app_iff in *.
  intros [? | ?]; [forwards*: (IHty1 (fst es)) | forwards*: (IHty2 (snd es))]; eauto;
  rewrite in_app_iff in *; intuition.
Qed.

Lemma disjoint_app T (xs ys zs : list T) :
  disjoint xs (ys ++ zs) <-> disjoint xs ys /\ disjoint xs zs.
Proof.
  induction xs; simpl; try tauto.
  rewrite !in_app_iff; split; intros; tauto.
Qed.

Lemma rule_reads_arrays (ty : Skel.Typ) (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (es : lexps ty) (xs : vars ty) (ctys : ctys ty) 
  (ls : locs ty) Env (Res Res' : res) p (P : Prop) arr ix iz i_n :
  disjoint (flatTup xs) (fv_lEs es) ->
  disjoint (flatTup xs) (fv_E ix) ->
  disjoint_list (flatTup xs) ->

  evalLExps Env es ls ->
  evalExp Env ix iz ->
  (P -> Res |=R arrays ls arr p *** Res') ->

  iz = Zn i_n ->
  (P -> i_n < length arr) ->

  CSL BS tid
      (Assn Res P Env)
      (reads xs ctys (es +os ix))
      (Assn Res P (EEq_tup xs (gets arr i_n) ++ (remove_vars Env (flatTup xs)))).
Proof.
  intros.
  applys* rule_reads.
  - eapply disjoint_incl; [apply fv_lEs_off|].
    rewrite disjoint_app; eauto.
  - apply eval_locs_off; eauto.
  - intros; forwards*Himp: H4.
    rewrite arrays_unfold in Himp; [|applys* H6].
    substs; rewrite <-!res_assoc in Himp; rewrites* res_CA in Himp.
Qed.

Lemma rule_reads_arrays' (ty : Skel.Typ) (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (es : lexps ty) (xs : vars ty) (ctys : ctys ty) 
  (ls : locs ty) Env (Res Res' : res) p (P : Prop) arr ix iz i_n dist j st:
  disjoint (flatTup xs) (fv_lEs es) ->
  disjoint (flatTup xs) (fv_E ix) ->
  disjoint_list (flatTup xs) ->

  evalLExps Env es ls ->
  evalExp Env ix iz ->
  (P -> Res |=R arrays' ls (ith_vals dist arr j st) p *** Res') ->

  iz = Zn i_n ->
  (P -> i_n < length arr /\ dist (st + i_n) = j) ->

  CSL BS tid
      (Assn Res P Env)
      (reads xs ctys (es +os ix))
      (Assn Res P (EEq_tup xs (gets arr i_n) ++ (remove_vars Env (flatTup xs)))).
Proof.
  intros.
  applys* rule_reads.
  - eapply disjoint_incl; [apply fv_lEs_off|].
    rewrite disjoint_app; eauto.
  - apply eval_locs_off; eauto.
  - intros; forwards*Himp: H4.
    rewrites (>>arrays'_unfold i_n) in Himp; [|].
    rewrite ith_vals_length; tauto.
    rewrite (nth_skip _ defval) in Himp.
    destruct Nat.eq_dec; [|forwards*: H7; try lia].
    destruct lt_dec; [|forwards*: H7; try lia].
    substs; rewrite <-!res_assoc in Himp; rewrites* res_CA in Himp.
Qed.    

Lemma rule_writes (ty : Skel.Typ)  (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (les : lexps ty) (es : exps ty) 
  (ls : locs ty) (vs vs' : vals ty) Env (Res Res' : res) (P : Prop) :
  evalExps Env es vs ->
  evalLExps Env les ls ->
  (P -> Res |=R ls |=>p (1, vs') *** Res') ->
  CSL BS tid
      (Assn Res P Env)
      (writes les es)
      (Assn (ls |=>p (1, vs) *** Res') P Env).
Proof.
  revert Env Res Res' vs'; induction ty; simpl in *; try now (eauto using rule_write).
  simpl in *; intros Env Res Res' vs' [Heval1 Heval2] [Hleval1 Hleval2] Hres.
  eapply rule_seq; [applys* IHty1|].
  { intros; rewrite* res_assoc. }
  eapply forward; [|applys* IHty2].
  apply Assn_imply; eauto using incl_refl.
  intros; rewrite <-res_assoc, res_CA; eauto.
  intros; rewrite res_CA; eauto.
Qed.

Lemma rule_writes_arrays (ty : Skel.Typ) (ntrd : nat) (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
  (tid : Fin.t ntrd) (les : lexps ty) (es : exps ty) 
  (ls : locs ty) (vs : vals ty) Env (Res Res' : res) (P : Prop) arr ix iz i_n:
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
  2: applys* eval_locs_off.
  intros ? ?.
  apply Assn_imply; eauto using incl_refl.
  intros Hp ? ? Hsat; rewrites (>>arrays_unfold i_n); [rewrite* length_set_nth|].
  rewrite nth_set_nth.
  forwards*: H3.
  destruct Nat.eq_dec; try (clear Hsat; false; lia).
  destruct lt_dec; try (clear Hsat; false; lia).
  rewrite <-!res_assoc, res_CA; substs; eauto.
  intros Hp ? ? Hsat.
  lets* Hsat': (>> H4 Hsat).
  rewrites (>>arrays_unfold i_n) in Hsat'; eauto.
  rewrite <-!res_assoc, res_CA in Hsat'; eauto.
  clear Hsat.
  substs.
  rewrite skipn_set_nth_ignore, firstn_set_nth_ignore; eauto.
Qed.

Lemma rule_writes_arrays' (ty : Skel.Typ) ntrd BS
      (tid : Fin.t ntrd) (les : lexps ty) (ls : locs ty) 
      (Env : list entry) (P : Prop) (Res Res' : res) (arr : list (vals ty)) dist ix i iz j es vs st:
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
  2: applys* eval_locs_off.
  apply Assn_imply; eauto using incl_refl.
  intros Hp ? ? Hsat.
  forwards*: H3.
  rewrite (arrays'_unfold _ i).
  2: rewrite ith_vals_length, length_set_nth; (clear Hsat; lia).
  rewrite (nth_skip _ defval).
  destruct Nat.eq_dec; try (clear Hsat; lia).
  rewrite length_set_nth; destruct lt_dec; [|clear Hsat; lia].
  rewrite nth_set_nth.
  destruct Nat.eq_dec; try (clear Hsat; lia).
  destruct lt_dec; try (clear Hsat; lia).
  rewrite <-!res_assoc, res_CA; substs; eauto.
  
  intros Hp s h Hsat.
  apply H4 in Hsat; auto.
  forwards*: H3.
  rewrite (arrays'_unfold _ i) in Hsat.
  2: rewrite ith_vals_length; lia.
  rewrite (nth_skip _ defval) in Hsat.
  destruct Nat.eq_dec; try (false; lia).
  destruct lt_dec; [|false; lia].
  rewrite <-!res_assoc, res_CA in Hsat; substs; eauto.
  rewrite ith_vals_set_nth, firstn_set_nth_ignore, skipn_set_nth_ignore.
  eauto.
Qed.

Definition val2sh {ty} := @maptys ty _ _ SLoc.
Definition val2gl {ty} := @maptys ty _ _ GLoc.

Lemma evalLExps_gl ty env (e : exps ty) v :
  evalExps env e v
  -> evalLExps env (e2gl e) (val2gl v).
Proof.
  induction ty; simpl; eauto; try now constructor; eauto.
  destruct 1; split; firstorder.
Qed.

Lemma evalLExps_sh ty env (e : exps ty) v :
  evalExps env e v
  -> evalLExps env (e2sh e) (val2sh v).
Proof.
  induction ty; simpl; eauto; try now constructor; eauto.
  destruct 1; split; firstorder.
Qed.

Lemma evalExps_vars ty env (xs : vars ty) vs :
  incl (xs |=> vs) env
  -> evalExps env (v2e xs) vs.
Proof.
  unfold v2e, incl; induction ty; simpl; eauto; intros; [constructor; firstorder..|].
  split; firstorder.
Qed.

Lemma incl_cons_ig T (a : T) xs ys :
  incl xs ys -> incl xs (a :: ys).
Proof.
  unfold incl; firstorder.
Qed.

Lemma incl_app_iff T (xs ys zs : list T) :
  (incl xs ys \/ incl xs zs) -> incl xs (ys ++ zs).
Proof.
  destruct 1; intros a; specialize (H a); firstorder.
Qed.

Hint Resolve incl_refl.

Lemma evalExp_cons_ig e env exp v :
  evalExp env exp v
  -> evalExp (e :: env) exp v.
Proof.
  induction 1; constructor; simpl; eauto.
Qed.

Lemma evalExp_app_ig env1 env2 exp v :
  evalExp env2 exp v
  -> evalExp (env1 ++ env2) exp v.
Proof.
  induction 1; constructor; simpl; eauto.
  rewrite in_app_iff; eauto.
Qed.

Lemma evalLExp_cons_ig e env le lv :
  evalLExp env le lv
  -> evalLExp (e :: env) le lv.
Proof.
  induction 1; constructor; eauto using evalExp_cons_ig.
Qed.          

Lemma evalLExp_app_ig env1 env2 le lv :
  evalLExp env2 le lv
  -> evalLExp (env1 ++ env2) le lv.
Proof.
  induction 1; constructor; eauto using evalExp_app_ig.
Qed.          

Lemma evalLExps_cons_ig ty e env (le : lexps ty) lv :
  evalLExps env le lv
  -> evalLExps (e :: env) le lv.
Proof.
  induction ty; simpl; eauto using evalLExp_cons_ig.
  firstorder.
Qed.

Lemma evalLExps_app_ig ty env1 env2 (le : lexps ty) lv :
  evalLExps env2 le lv
  -> evalLExps (env1 ++ env2) le lv.
Proof.
  induction ty; simpl; eauto using evalLExp_app_ig.
  firstorder.
Qed.

Lemma assigns_writes ty (vs : vars ty) (ts : ctys ty) (es : exps ty) :
  writes_var (assigns vs ts es) = (flatTup vs).
Proof.
  induction ty; simpl; congruence.
Qed.

Lemma reads_writes ty (xs : vars ty) (ts : ctys ty) (es : lexps ty):
  (writes_var (reads xs ts es)) = (flatTup xs).
Proof.
  induction ty; simpl;  congruence.
Qed.

Lemma writes_writes ty (les : lexps ty) (es : exps ty) :
  (writes_var (writes les es)) = nil.
Proof.
  induction ty; simpl; eauto.
  rewrite IHty1, IHty2; simpl; congruence.
Qed.