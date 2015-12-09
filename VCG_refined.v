Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics.
Definition penv := list (var * val).

Fixpoint var_in (x : var) (E : penv) :=
  match E with
  | nil => False
  | (y, _) :: E => x = y \/ var_in x E
  end.

Fixpoint esat (E : penv) :=
  match E with
  | nil => TrueP
  | (x, v) :: E => (x === v) //\\ esat E
  end.

Inductive SP := Spts : loc -> Qc -> val -> SP.
Definition SProp := list SP.

Definition loc_to_exp (l : loc) : loc_exp :=
  match l with
  | SLoc l => Sh l
  | GLoc l => Gl l
  end.

Fixpoint Ssat (ps : SProp) :=
  match ps with
  | nil => emp
  | Spts l p v :: ps => (loc_to_exp l -->p (p, v)) ** Ssat ps
  end.

Fixpoint env_wf (E : penv) :=
  match E with
  | nil => True
  | (x, _) :: E => ~var_in x E /\ env_wf E
  end.

Record Astate := {Aenv : penv; Aenv_wf : env_wf Aenv; Ap : Prop; sp : SProp}.

Definition Ast_denote (st : Astate) : assn :=
  !(esat (Aenv st) //\\ pure (Ap st)) ** Ssat (sp st).

Definition Asts_denote (sts : list Astate) : assn :=
  fold_right (fun st assn => Ast_denote st \\// assn) TrueP sts.

Fixpoint get (E : penv) (x : var) : option val :=
  match E with
  | nil => None
  | (y, v) :: E => if var_eq_dec x y then Some v else get E x
  end.

Notation "f <$> x" := (option_map f x) (at level 55, left associativity).
Definition option_ap {A B : Type} (f : option (A -> B)) (x : option A) :=
  match f with
  | None => None
  | Some f => match x with
              | Some x => Some (f x)
              | None => None
              end
  end.

Notation "f <*> x" := (option_ap f x) (at level 55, left associativity).

Definition div2 x := (x / 2)%Z.
Fixpoint eval (E : penv) (e : exp) :=
  match e with
  | Evar x => get E x
  | Enum v => Some v
  | e1 +C e2 => Z.add <$> eval E e1 <*> eval E e2
  | e1 *C e2 => Z.mul <$> eval E e1 <*> eval E e2
  | e1 -C e2 => Z.sub <$> eval E e1 <*> eval E e2
  | e1 >>1 => div2 <$> eval E e1
  end.

Definition loc_off (v : loc) (v' : val) :=
  match v with
  | SLoc v => SLoc (v + v')
  | GLoc v => GLoc (v + v')
  end%Z.

Fixpoint leval (E : penv) (e : loc_exp) :=
  match e with
  | Sh e => SLoc <$> (eval E e)
  | Gl e => GLoc <$> (eval E e)
  | e +o e' => loc_off <$> leval E e <*> eval E e'
  end.

Fixpoint flatten {A B : Type} (xs : list A) (f : A -> option B): option (list B) :=
  match xs with
  | nil => Some nil
  | x :: xs => cons <$> f x <*> flatten xs f
  end.

Fixpoint env_update (x : var) (v : val) (E : penv) :=
  match E with
  | nil => (x, v) :: nil
  | (y, v') :: E => if var_eq_dec x y then (x, v) :: E else (y, v') :: env_update x v E
  end.

Lemma env_update_var_in x y v E : var_in x (env_update y v E) <-> x = y \/ var_in x E.
Proof.
  induction E as [|[z v'] ?]; simpl; eauto.
  - split; eauto.
  - destruct var_eq_dec; subst; simpl; eauto.
    + split; intros; destruct H; eauto.
    + rewrite IHE.
      split; intros H; repeat destruct H; eauto.
Qed.
    
Lemma env_update_wf x v E : env_wf E -> env_wf (env_update x v E).
Proof.
  induction E as [|[y v'] ?]; simpl in *.
  - split; eauto.
  - intros [Hy HE].
    destruct var_eq_dec; simpl; subst; eauto.
    split; eauto.
    rewrite env_update_var_in; intros [? | ?]; eauto; congruence.
Qed.

Definition exec_assign (st : Astate) (x : var) (E : exp) :=
  match eval (Aenv st) E with
  | None => None
  | Some v =>
    Some {| Aenv := env_update x v (Aenv st); Aenv_wf := env_update_wf x v (Aenv st) (Aenv_wf st);
            Ap := Ap st; sp := sp st|}
  end.

Variable ntrd : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.

Notation bspec := (Bdiv.barrier_spec ntrd).

Hint Unfold Ast_denote exec_assign.

Lemma esat_irr env s x v h :
  esat env s h ->
  ~var_in x env ->
  esat env (var_upd s x v) h.
Proof.
  induction env as [|[y v'] ?]; simpl; eauto.
  - intros [Heq Hsat] Hnin.
    split; eauto.
    unfold_conn; simpl; unfold var_upd.
    destruct var_eq_dec; eauto.
    elimtype False; apply Hnin; eauto.
Qed.
  
Lemma esat_update env s x v h:
  env_wf env ->
  esat env s h ->
  esat (env_update x v env) (var_upd s x v) h.
Proof.
  induction env as [|[y v'] ?]; simpl; intros Hwf Hsat; eauto.
  - split; eauto.
    unfold_conn; unfold var_upd; simpl.
    destruct var_eq_dec; eauto; congruence.
  - destruct var_eq_dec; simpl; subst; eauto.
    + destruct Hsat; split; eauto.
      * unfold_conn; simpl; unfold var_upd; destruct var_eq_dec; congruence.
      * apply esat_irr; jauto.
    + split.
      * unfold_conn; simpl; unfold var_upd; destruct var_eq_dec; try congruence.
        destruct Hsat; eauto.
      * apply IHenv; jauto.
        destruct Hsat; eauto.
Qed.

Lemma eval_correct E s h e v:
  esat E s h ->
  eval E e = Some v ->
  edenot e s = v.
Proof.
  revert v; induction e; simpl; intros; try congruence;
  try 
    (destruct (eval E e1), (eval E e2); simpl in *; try congruence;
     erewrite (IHe1 _ H eq_refl) , (IHe2 _ H eq_refl); auto; congruence).
  induction E as [|[x' v'] E]; simpl in *; try congruence.
  - destruct var_eq_dec; subst.
    + destruct H; unfold_conn_in H; simpl in H; congruence.
    + apply IHE in H0; destruct H; eauto.
  - destruct (eval E e); simpl in *; try congruence.
    erewrite IHe; eauto.
    unfold div2 in *.
    rewrite Zdiv2_div; congruence.
Qed.

Lemma Ssat_novars ps x v s h:
  Ssat ps s h -> Ssat ps (var_upd s x v) h.
Proof.
  revert s h; induction ps; simpl; eauto.
  destruct a as ([? | ?] & ? & ?); simpl; intros.
  - destruct H as (? & ? & ? & ? & ? & ?); repeat eexists; repeat split; eauto.
  - destruct H as (? & ? & ? & ? & ? & ?); repeat eexists; repeat split; eauto.
Qed.

Lemma exec_assign_correct (i : Fin.t ntrd) (BS : bspec) (st st' : Astate) x E:
  exec_assign st x E = Some st' ->
  CSL BS i (Ast_denote st) (x ::= E) (Ast_denote st').
Proof.
  autounfold; intros H.
  destruct st as [env envwf P S], st'; simpl in *.
  eapply Hbackward; [apply rule_assign| intros s h Hsat].
  destruct (eval env E) eqn:Heq; simpl in H; try congruence.
  inversion H; subst.
  subA_normalize_in Hsat.
  sep_split_in Hsat; sep_split; eauto.
  - destruct HP.
    simpl; repeat split; eauto.
    erewrite eval_correct; eauto.
    apply esat_update; eauto.
  - apply Ssat_novars; eauto.
Qed.

Fixpoint get_addr (l : loc) (sp : SProp) :=
  match sp with
  | nil => None
  | (Spts l' p v) :: sp => if eq_dec l l' then Some (p, v) else get_addr l sp
  end.

Definition exec_read (st : Astate) (x : var) (E : loc_exp) :=
  match leval (Aenv st) E with
  | None => None
  | Some l =>
    match get_addr l (sp st) with
    | None => None
    | Some (_, v) =>
      Some {| Aenv := env_update x v (Aenv st);
              Aenv_wf := env_update_wf x v (Aenv st) (Aenv_wf st);
              Ap := Ap st; sp := sp st|}
    end
  end.

Hint Unfold exec_read.

Require Import Skel_lemma.

Lemma leval_correct E s h e v:
  esat E s h ->
  leval E e = Some v ->
  ledenot e s = v.
Proof.
  revert v; induction e; simpl; intros; try congruence;
  try (destruct (eval E e) eqn:Heq; simpl in *; try congruence;
       inversion H0; erewrite eval_correct; eauto).
  destruct (leval E e) eqn:?, (eval E e0) eqn:?; simpl in *; try congruence.
  erewrite IHe; eauto.
  erewrite eval_correct; eauto.
  destruct l; simpl in *; congruence.
Qed.

Lemma get_addr_correct (l : loc) (sp : SProp) p v :
  get_addr l sp = Some (p, v) ->
  exists sp0 sp1,
    sp = sp0 ++ (Spts l p v) :: sp1.
Proof.
  induction sp as [|[? ? ?] ?]; simpl; try congruence.
  intros H.
  destruct (eq_dec l l0); subst.
  - inverts H.
    exists (@nil SP) sp0; simpl; eauto.
  - lets (sp1 & sp2 & ?): (IHsp H); subst.
    exists (Spts l0 q v0 :: sp1) sp2; eauto.
Qed.    

Lemma SP_order stk sp0 sp1 s: 
  stk ||= Ssat (sp0 ++ s :: sp1) <=> Ssat (s :: sp0 ++ sp1).
Proof.
  induction sp0 as [|? ?]; simpl; eauto.
  - reflexivity.
  - destruct a as [[? | ?] ? ?]; rewrite IHsp0; simpl.
    destruct s as [[? | ?] ? ?]; split; intros; repeat sep_cancel.
    destruct s as [[? | ?] ? ?]; split; intros; repeat sep_cancel.
Qed.

Fixpoint env_remove (e : penv) (x : var) :=
  match e with
  | nil => nil
  | (y, v) :: e => if var_eq_dec y x then env_remove e x else (y, v) :: env_remove e x
  end.

Lemma env_remove_weak (e : penv) (x : var) s h :
  esat e s h ->
  esat (env_remove e x) s h.
Proof.
  induction e as [|[y v] ?]; simpl; eauto.
  intros [Heq Hsat]; destruct var_eq_dec; subst; simpl; eauto.
  split; eauto.
Qed.

Lemma env_remove_inde (e : penv) (x : var) :
  inde (esat (env_remove e x)) (x :: nil).
Proof.
  induction e as [|[y v] ?]; simpl; repeat prove_inde.
  destruct var_eq_dec; simpl; repeat prove_inde.
  destruct var_eq_dec; try congruence.
Qed.

Lemma inde_Ssat (sp : SProp) xs: inde (Ssat sp) xs.
Proof.
  induction sp as [|[[? | ?] ? ?] ?]; simpl; repeat prove_inde;
  rewrite Forall_forall; intros; try first [apply indelE_fv| apply indeE_fv]; simpl; eauto.
Qed.

Lemma env_remove_nin (e : penv) (x : var) :
  ~var_in x e -> env_remove e x = e.
Proof.
  induction e as [|[? ?] ?]; simpl; eauto.
  destruct var_eq_dec; simpl; subst; eauto.
  intros H.
  elimtype False; apply H; eauto.
  intros; f_equal; eauto.
Qed.

Lemma esat_remove_update (e : penv) (x : var) v s h:
  env_wf e ->
  (esat (env_remove e x)) s h ->
  (x === Enum v) s h ->
  (esat (env_update x v e) s h).
Proof.
  induction e as [|[y v'] ?]; simpl; eauto.
  - intros; split; eauto.
  - repeat destruct var_eq_dec; substs; try congruence; simpl; intros.
    split; eauto.
    rewrite env_remove_nin in H0; jauto.
    split; eauto; destruct H0; jauto.
Qed.
    
Lemma exec_read_correct (i : Fin.t ntrd) (BS : bspec) (st st' : Astate) x E:
  indelE E x ->
  exec_read st x E = Some st' ->
  CSL BS i (Ast_denote st) (x ::= [E]) (Ast_denote st').
Proof.
  autounfold; intros Hfv H.
  destruct st as [env envwf P S], st'; simpl in *.
  destruct (leval env E) eqn:Heval; try congruence.
  destruct (get_addr l S) as [[p v]| ] eqn:Hget; try congruence.
  inversion H; subst.
  lets (sp1 & sp2 & Heq): (>> get_addr_correct Hget); subst.
  eapply Hbackward.
  Focus 2. { 
    intros s h Hsat.
    sep_split_in Hsat.
    sep_rewrite_in SP_order Hsat; simpl in Hsat.
    assert ((loc_to_exp l ===l E) s (emp_ph loc)).
    { destruct HP.
      eapply leval_correct in Heval; eauto.
      unfold_conn; simpl; rewrite Heval.
      destruct l; simpl; eauto. }
    sep_rewrite_in mps_eq1 Hsat; [|exact H0].
    destruct HP.
    apply (env_remove_weak _ x) in H1.
    sep_combine_in Hsat; sep_normal_in Hsat; eauto. } Unfocus.
  hoare_forward.
  - simpl.
    apply env_remove_inde.
  - destruct l; simpl; auto.
  - apply inde_Ssat.
  - intros s h Hsat.
    sep_normal_in Hsat; sep_split_in Hsat.
    sep_split; try split; eauto.
    apply esat_remove_update; eauto.
    sep_rewrite SP_order; simpl; sep_cancel.
Qed.

Fixpoint SP_update (l : loc) (v : val) (SP : SProp) :=
  match SP with
  | nil => nil
  | Spts l' p v' :: SP =>
    if eq_dec l l' then Spts l' p v :: SP else Spts l' p v' :: SP_update l v SP
  end.

Definition exec_write (st : Astate) (E : loc_exp) (E' : exp) :=
  match leval (Aenv st) E with
  | None => None
  | Some l =>
    match get_addr l (sp st) with
    | None => None
    | Some (p, v) =>
      if Qc_eq_dec p 1 then 
        match eval (Aenv st) E' with
        | None => None
        | Some v =>
          Some {| Aenv := Aenv st; Aenv_wf := Aenv_wf st;
                  Ap := Ap st; sp := SP_update l v (sp st) |}
        end
      else None
    end
  end.

Hint Unfold exec_write.

Lemma exec_write_correct (i : Fin.t ntrd) (BS : bspec) (st st' : Astate) E E':
  exec_write st E E' = Some st' ->
  CSL BS i (Ast_denote st) ([E] ::= E') (Ast_denote st').
Proof.
  autounfold; intros H.
  destruct st as [env envwf P S], st'; simpl in *.
  destruct (leval env E) eqn:Hleval; try congruence.
  destruct (get_addr l S) as [[p v]| ] eqn:Hget; try congruence.
  destruct Qc_eq_dec; try congruence.
  destruct (eval env E') eqn:Heval; try congruence.
  inversion H; subst.
  lets (sp1 & sp2 & Heq): (>> get_addr_correct Hget); subst.
  eapply Hbackward.
  Focus 2. { 
    intros s h Hsat.
    sep_split_in Hsat.
    sep_rewrite_in SP_order Hsat; simpl in Hsat.
    assert ((loc_to_exp l ===l E) s (emp_ph loc)).
    { destruct HP.
      eapply leval_correct in Hleval; eauto.
      unfold_conn; simpl; rewrite Hleval.
      destruct l; simpl; eauto. }
    sep_rewrite_in mps_eq1 Hsat; [|exact H0].
    sep_combine_in Hsat; sep_normal_in Hsat; eauto. } Unfocus.
  hoare_forward.
  - intros s h Hsat.
    sep_normal_in Hsat; sep_split_in Hsat.
    destruct HP.
    sep_split; try split; eauto.
    assert ((E ===l loc_to_exp l) s (emp_ph loc)).
    { eapply leval_correct in Hleval; eauto.
      unfold_conn; simpl; rewrite Hleval.
      destruct l; simpl; eauto. }
    assert ((E' === v0) s (emp_ph loc)).
    { eapply eval_correct in Heval; eauto. }
    clear H.
    revert h Hsat; induction sp1; simpl in *; intros.
    + destruct (eq_dec l l); try congruence; simpl.
      sep_cancel.
    + destruct a.
      destruct (eq_dec l l0); simpl; subst.
      inversion Hget; subst.
      repeat sep_cancel.
      sep_rewrite SP_order; simpl; eauto.
      repeat sep_cancel.
      apply IHsp1; eauto.
Qed.

Fixpoint bexp_denote (env : penv) (b : bexp) :=
  match b with
  | e1 == e2 => (eq) <$> (eval env e1) <*> (eval env e2)
  | e1 <C e2 => (Z.lt) <$> (eval env e1) <*> (eval env e2)
  | Band b1 b2 => (and) <$> bexp_denote env b1 <*> bexp_denote env b2
  | Bnot b1 => not <$> bexp_denote env b1
  end.

Definition exec_if (st : Astate) (b : bexp) (C1 C2 : cmd) :=
  match bexp_denote (Aenv st) b with
  | None => None
  | Some p =>
    Some ({| Aenv := Aenv st; Aenv_wf := Aenv_wf st;
             Ap := p /\ Ap st; sp := sp st |},
          {| Aenv := Aenv st; Aenv_wf := Aenv_wf st;
             Ap := ~p /\ Ap st; sp := sp st |})
  end.

Hint Unfold exec_if.

Lemma bexp_denote_correct' (env : penv) (b : bexp) P s h :
  esat env s h ->
  bexp_denote env b = Some P ->
  ((bexp_to_assn b) s h -> P) /\ ((bexp_to_assn (Bnot b)) s h -> ~P).
Proof.
  revert P; induction b; simpl; eauto; intros P Henv Heq;
  try (destruct (eval env e1) eqn:Heq1, (eval env e2) eqn:Heq2; simpl in *; try congruence;
       inverts Heq;
       eapply eval_correct in Heq1; eapply eval_correct in Heq2; eauto).
  - unfold_conn_all; simpl in *; destruct eq_dec; split; intros; simpl in *; try congruence.
  - unfold_conn_all; simpl in *; destruct Z_lt_dec; split; intros; simpl in *; try congruence.
  - destruct (bexp_denote env b1), (bexp_denote env b2); simpl in *; try congruence.
    inverts Heq; split; intros Hsat; unfold bexp_to_assn in Hsat; simpl in *;
    lets (? & ?): (>>IHb1 Henv (@eq_refl));
    lets (? & ?): (>>IHb2 Henv (@eq_refl)).
    rewrite Bool.andb_true_iff in Hsat; split; jauto.
    intros [? ?].
    unfold bexp_to_assn in *; simpl in *.
    rewrite Bool.negb_true_iff, Bool.andb_false_iff in *.
    destruct Hsat; jauto.
  - destruct (bexp_denote env b); simpl in *; try congruence.
    inverts Heq.
    lets (? & ?): (>>IHb P0 Henv (@eq_refl)).
    unfold bexp_to_assn in *; simpl in *.
    rewrite !Bool.negb_true_iff in *.
    rewrite Bool.negb_false_iff in *.
    split; jauto.
Qed.

Lemma bexp_denote_correct (env : penv) (b : bexp) P s h :
  esat env s h ->
  bexp_denote env b = Some P -> ((bexp_to_assn b) s h -> P).
Proof.
  intros.
  lets ?: (>>bexp_denote_correct' ___); eauto; jauto.
Qed.  
  
Lemma exec_if_correct (i : Fin.t ntrd) (BS : bspec)
      (st st_th st_el st_th' st_el' : Astate) b C1 C2:
  exec_if st b C1 C2 = Some (st_th, st_el) ->
  CSL BS i (Ast_denote st_th) C1 (Ast_denote st_th') ->
  CSL BS i (Ast_denote st_el) C2 (Ast_denote st_el') ->
  CSL BS i (Ast_denote st) (Cif b C1 C2) (Asts_denote (st_th' :: st_el' :: nil)).
Proof.
  autounfold; intros H H1 H2.
  destruct (bexp_denote _ _) eqn:Heq; simpl in H; try congruence.
  inverts H; simpl in *.
  eapply Hforward.
  apply rule_if_disj; eauto; [eapply Hbackward; [eauto|]..];
  intros; sep_split_in H; sep_split; eauto; repeat split; destruct HP0; jauto;
  eapply bexp_denote_correct; eauto.
  simpl in *.
  destruct bexp_denote; simpl in *; congruence.

  unfold Ast_denote; simpl.
  intros s h [? | ?].
  - left; eauto.
  - right; left; eauto.
Qed.