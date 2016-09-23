Require Import Monad DepList GPUCSL TypedTerm Compiler.
Require Import Program.Equality LibTactics.
Require Import CodeGen CSLLemma CSLTactics.

Section CorrectnessProof.
  Import Skel_lemma.
  (* the set of free variables *)
  (* Variable GA : list Skel.Typ. *)
  (* (* the evaluation environment *) *)
  (* Variable aeval_env : hlist Skel.aTypDenote GA. *)
  (* (* the typing environment *) *)
  (* (* Variable aty_env : Env varA (option Sx.Typ) _. *) *)
  (* (* the variable mapping environment between source and dest. *) *)
  (* Variable avar_env : hlist (fun _ => var * list var)%type GA. *)

  Notation SVarEnv GS := (hlist (fun _ : Skel.Typ => list var) GS).
  Notation SEvalEnv GS := (hlist Skel.typDenote GS).
  Notation AVarEnv GA := (hlist (fun _ : Skel.Typ => (var * list var)%type) GA).
  Notation AEvalEnv GA := (hlist Skel.aTypDenote GA).

  (* source lang. values -> dest. lang. values *)
  Fixpoint vs_of_sval {ty : Skel.Typ} :=
    match ty return Skel.typDenote ty -> list Z with
    | Skel.TBool => fun b => (if b then 1%Z else 0%Z) :: nil
    | Skel.TZ => fun z => z :: nil
    | Skel.TTup t1 t2 => fun xy => vs_of_sval (fst xy) ++ vs_of_sval (snd xy)
    end%list.

  Variable sorry : forall A, A.
  Arguments sorry {A}.

  Fixpoint hzip {A B C} {ls : list A}
    (hl1 : hlist B ls) :=
    match hl1 in hlist _ ls' return hlist C ls' -> hlist (fun x => (B x * C x))%type ls' with
    | HNil => fun hl2 => 
      match hl2 in hlist _ ls'' return match ls'' with | nil => _ | _ :: _ => unit end with
      | HNil => HNil
      | HCons _ _ _ _ => tt
      end
    | HCons _ _ x xs => fun hl2 => 
      (match hl2 in hlist _ ls'' return match ls'' with | nil => unit | x :: ls''' => B x -> hlist B ls''' -> _ end with
      | HNil => tt
      | HCons _ _ y ys => fun x xs => (x, y) ::: hzip xs ys
       end) x xs
    end.

  Section TestHzip.
    Variable A : Type.
    Variable B C : A -> Type.
    Variable x y : A.
    Variable xs ys : list A.

    Variable bx : B x.
    Variable cx : C x. 

    Variable bxs : hlist B xs.
    Variable cxs : hlist C xs.
    
    Eval simpl in hzip (bx ::: bxs) (cx ::: cxs). 
  End TestHzip.

  Fixpoint undep_list {A B} {xs : list A} (ls : hlist (fun _ => B) xs) : list B :=
    match ls with
    | HNil => nil
    | HCons _ _ x xs => x :: (undep_list xs)
    end.

  Fixpoint nth_arr {ty : Skel.Typ} (i : nat) : Skel.aTypDenote ty -> Skel.typDenote ty :=
    match ty with
    | Skel.TZ => fun xs => nth i xs 0%Z
    | Skel.TBool => fun xs => nth i xs false
    | Skel.TTup t1 t2 => fun xs =>
                           (@nth_arr t1 i (List.map fst xs), 
                            @nth_arr t2 i (List.map snd xs))
    end.

  Notation APtrEnv GA := (hlist ptrType GA).

  (* precondition of free variable arrays *)
  Definition res_of_avs {GA : list Skel.Typ}
    (aeval_env : AEvalEnv GA) (aptr_env : APtrEnv GA) : res :=
    let f (_ : Skel.Typ) x :=
        let '(ptr, ls) := x in
        arrays (GLs ls) 
    istar (undep_list (hmap f (hzip aptr_env aeval_env))).
  
  (* (* the set of free variables of scalar exp *) *)
  (* Variable free_svs : list varE. *)
  (* (* the evaluation environment of scalar exp *) *)
  (* Variable seval_env : Env varE (option SVal) _. *)
  (* (* the typing environment *) *)
  (* Variable sty_env : Env varE Typ _. *)
  (* (* the variable mapping environment between source and dest. *) *)
  (* Variable svar_env : Env varE (list var) _ . *)

  (* preconditions of scalar variables *)
  Definition assn_of_svs {GS : list Skel.Typ}
             (seval_env : hlist Skel.typDenote GS)
             (svar_env : hlist (fun _ => list var) GS) : assn :=
    let f (_ : Skel.Typ) x :=
        let '(xs, vs) := x in
        !(vars2es xs ==t vs_of_sval vs) in
    conj_xs (undep_list (hmap f (hzip svar_env seval_env))).
  
  Import scan_lib.

  (* Arguments uniq {A} {eqt} x. *)

  (* Definition free_sv e := uniq (free_sv' e). *)
  (* Definition free_av e := uniq (free_av' e). *)

  Ltac unfoldM := unfold freshes, get, set, ret in *; simpl in *; unfold bind_opt in *.
  
  Lemma freshes_incr d m n xs :
    freshes d n = (inl xs, m) ->
    m = n + 1.
  Proof.
    revert n m xs; induction d; simpl; intros n m xs.
    - unfoldM; simpl; intros H; inverts H; eauto.
    - unfoldM.
      lazymatch goal with [|- context [(Var _ :: ?E) ]] => remember E eqn:Heq end.
      intros H; inverts H.
      forwards*: (>>IHd n).
  Qed.
  
  (* some lemma for generetated variables *)
  Lemma freshes_vars d n m xs:
    freshes d n = (inl xs, m) ->
    (forall x, In x xs -> exists l, x = Var (str_of_pnat n l) /\ l < d).
  Proof.
    revert n m xs; induction d; simpl; intros n m xs; unfoldM.
    - intros H; inverts H.
      destruct 1.
    - unfoldM.
      lazymatch goal with [|- context [(Var _ :: ?E) ]] => remember E eqn:Heq end.
      intros H; inverts H.
      intros ? H'; apply in_inv in H' as [? | ?]; eauto.
      forwards* (? & ?): IHd.
      substs; eauto.
  Qed.
  
  Lemma freshes_len d n m xs:
    freshes d n = (inl xs, m) -> length xs = d.
  Proof.
    revert n m xs; induction d; unfoldM;
      simpl; inversion 1; simpl in *; try omega.
    forwards * : IHd.
  Qed.

  Lemma var_pnat_inj n m n' m' : Var (str_of_pnat n m) = Var (str_of_pnat n' m') -> n = n' /\ m = m'.
  Proof.
    intros Heq.
    apply str_of_pnat_inj; inversion Heq.
    unfold str_of_pnat; f_equal; eauto.
  Qed.

  Variable ntrd : nat.
  Variable tid : Fin.t ntrd.
  Variable BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd.
  Arguments assn_of_svs _ _ _ _ _ : simpl never.
  Arguments assn_of_avs : simpl never.
  (* Tactic Notation "simpl_avs" "in" hyp(HP) := unfold assn_of_svs, SE.assn_of_vs, SE.fold in HP; simpl in HP. *)
  (* Tactic Notation "simpl_avs" := unfold assn_of_svs, SE.assn_of_vs, SE.fold; simpl. *)
  (* Tactic Notation "simpl_avs" "in" "*" := unfold assn_of_svs, SE.assn_of_vs, SE.fold in *; simpl in *. *)
  (* Arguments flip / _ _ _ _ _ _. *)
  Require Import SetoidClass.
  Instance ban_proper stk : Proper (equiv_sep stk ==> equiv_sep stk) ban.
  Proof.
    intros P1 P2 Heq h; lets:(Heq h).
    unfold ban, Aconj; rewrite H; split; eauto.
  Qed.

  Lemma compile_don't_decrease GA GS typ
    (se : Skel.SExp GA GS typ) c es
    (avar_env : AVarEnv GA) (svar_env : SVarEnv GS) n0 n1 :
    compile_sexp se avar_env svar_env n0 = (inl (c, es), n1) ->
    n0 <= n1.
  Proof.
    revert n0 n1 svar_env c es; induction se; simpl;
      intros n0 n1 svar_env c es' Hsuc; eauto; try inverts Hsuc as Hsuc;
    eauto; unfoldM;
          (repeat lazymatch type of Hsuc with
             | context [compile_sexp ?X ?Y ?Z ?n] => destruct (compile_sexp X Y Z n) as [[(? & ?) | ?] ?] eqn:?
             | context [freshes ?X ?Y] => destruct (freshes X Y) as ([? | ?] & ?) eqn:?
             end);
    (repeat lazymatch goal with [H : context [match ?E with | _ => _ end]|- _] => destruct E eqn:? end);
          try now (inverts Hsuc; first
            [now auto|
             forwards*: IHse1; forwards*: IHse2; omega |
             forwards*: IHse1; forwards*: IHse2; forwards*: IHse3; omega |
             forwards*: IHse; omega |
             forwards*: IHse1; forwards*: IHse2; forwards*: freshes_incr; omega |
             forwards*: IHse1; forwards*: IHse2; forwards*: IHse3; forwards*: freshes_incr; omega |
             forwards*: IHse; forwards*: freshes_incr; omega |
             forwards*: IHse; omega]).
  Qed.

  (* Lemma fold_assn_svs se sv : *)
  (*   SE.assn_of_vs SVal se (fun (x_e : VarE_eq.t) (v : SVal) => !(vars2es (sv x_e) ==t vs_of_sval v)) = *)
  (*   assn_of_svs se sv. auto. Qed. *)
  (* Lemma fold_assn_avs : *)
  (*   SA.assn_of_vs array aeval_env *)
  (*     (fun (x_a : VarA_eq.t) (a : array) => *)
  (*        !(fst (avar_env x_a) === Z.of_nat (length a)) ** *)
  (*        S.is_tuple_array_p (S.es2gls (S.vars2es (snd (avar_env x_a)))) *)
  (*                           (length a) (fun i : nat => vs_of_sval (nth i a (VZ 0))) 0 1) = *)
  (*   assn_of_avs. auto. Qed. *)

  Lemma inde_equiv P P' xs :
    (forall stk, stk ||= P <=> P') ->
    (inde P xs <-> inde P' xs).
  Proof.
    unfold inde, equiv_sep.
    intros; simpl.
    split; intros; split; intros; intuition;
      try (apply H, H0, H); eauto.
    apply H; apply <-H0; eauto; apply H; eauto.
    apply H; apply <-H0; eauto; apply H; eauto.
  Qed.

  Fixpoint hIn {A B : Type} {l : list A} (x : B) (ys : hlist (fun _ => B) l) :=
    match ys with
    | HNil => False
    | y ::: ys => x = y \/ hIn x ys
    end.

  Lemma inde_assn_of_svs GS (seval_env : SEvalEnv GS)
        (svar_env : SVarEnv GS) (xs : list var) :
    (forall x ty (m : member ty GS), In x xs -> ~In x (hget svar_env m)) ->
    inde (assn_of_svs seval_env svar_env) xs.
  Proof.
    unfold assn_of_svs.
    dependent induction seval_env; dependent destruction svar_env; intros H; simpl; repeat prove_inde.
    (* rewrites (>>inde_equiv). *)
    (* { intros; rewrite SE.fold_left_assns; reflexivity. } *)
    { apply inde_eq_tup.
      rewrite Forall_forall; intros.
      forwards*: (>>H (@HFirst _ x ls)); simpl in *.
      simplify; eauto. }
    { apply IHseval_env; intros.
      forwards*: (>>H (@HNext _ _ x _ m)). }
  Qed.
  
  Lemma inde_assn_of_avs GA (aeval_env : AEvalEnv GA) (avar_env : AVarEnv GA) (xs : list var) :
    (forall x ty (m : member ty GA), In x xs -> ~In x (snd (hget avar_env m))) ->
    (forall ty (m : member ty GA), ~In (fst (hget avar_env m)) xs) ->
    inde (assn_of_avs aeval_env avar_env) xs.
  Proof.
    unfold assn_of_avs.
    dependent induction aeval_env; dependent destruction avar_env; intros H1 H2; simpl; repeat prove_inde.
    - destruct p as [len arrs] eqn:Heq; repeat prove_inde;
      try now (rewrite Forall_forall; simplify; eauto).
      + forwards*: (>>H2 (@HFirst _ x ls)); simplify; eauto.
      + unfold S.es2gls in *; apply inde_is_tup_arr; intros; forwards*: (>>H1 (@HFirst _ x ls)); simplify; eauto.
    - apply IHaeval_env; intros.
      + forwards*: (>>H1 (@HNext _ _ x _ m)).
      + forwards*: (>>H2 (@HNext _ _ x _ m)).
  Qed.
  
  Ltac unfoldM' := unfold get, set, ret in *; simpl in *; unfold bind_opt in *.

  Lemma ctyps_of_typ__len_of_ty t : 
    length (ctyps_of_typ t) = len_of_ty t.
  Proof.
    induction t; simpl; eauto.
    rewrite app_length; auto.
  Qed.
  Hint Resolve ctyps_of_typ__len_of_ty app_length.

  Lemma compiler_preserve GA GS typ (se : Skel.SExp GA GS typ)
        (avar_env : AVarEnv GA)
        (svar_env : SVarEnv GS) (n0 n1 : nat)
        c es :
    (forall ty (m : member ty GS), length (hget svar_env m) = len_of_ty ty) ->
    (forall ty (m : member ty GA), length (snd (hget avar_env m)) = len_of_ty ty) ->
    compile_sexp se avar_env svar_env n0 = (inl (c, es), n1) ->
    length es = len_of_ty typ.
  Proof.
    revert svar_env n0 n1 c es.
    induction se; simpls*; introv Hsctx Hactx Hsucc.
    - inverts Hsucc; simplify; eauto.
    - inverts* Hsucc.
    - unfoldM'.
      destruct (compile_sexp se1 _ _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct (compile_sexp se2 _ _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hsucc].
      destruct b, es1 as [|? [| ? ?]], es2 as [|? [| ? ?]];
        inverts Hsucc; simpl in *; try congruence; eauto; simpl in *; try case_if; inverts* Hop.
    - unfoldM'.
      destruct (compile_sexp se _ _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct (hget avar_env m) as [? aname] eqn:Heq'.
      destruct (freshes _ _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hsucc].
      destruct es1 as [|i [|? ?]]; inverts Hsucc.
      simplify.
      rewrites* (>>freshes_len Hfeq1).
    - destruct (hget avar_env m) eqn:Heq; simpl in *.
      inverts* Hsucc.
    - unfoldM'.
      destruct (compile_sexp se1 _ _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct (compile_sexp se2 _ _ _) as [[(cs2 & es2) | ?] n''] eqn:Hceq2; [|inversion Hsucc].
      destruct (compile_sexp se3 _ _ _) as [[(cs3 & es3) | ?] n'''] eqn:Hceq3; [|inversion Hsucc].
      destruct (freshes _ _) as [[fvs1 | ?] n''''] eqn:Hfeq1; [|inversion Hsucc].
      destruct es1 as [|? [|? ?]]; simpl in *; inverts Hsucc.
      forwards*: freshes_len; simplify.
      rewrites* H.
    - unfoldM'.
      destruct (compile_sexp se1 _ _ _) as [[(ce1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct (compile_sexp se2 _ _ _) as [[(ce2 & es2) | ?] n''] eqn:Hceq2; [|inversion Hsucc].
      inversion Hsucc; rewrites* app_length.
    - unfoldM'.
      destruct (compile_sexp se _ _ _) as [[(ce1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      inverts* Hsucc; eauto.
      rewrites* firstn_length; rewrites* min_l.
      forwards*: IHse; omega.
    - unfoldM'.
      destruct (compile_sexp se _ _ _) as [[(ce1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      inverts* Hsucc; eauto.
      rewrites* firstn_length; rewrites* skipn_length; rewrites* min_l.
      forwards*: IHse; omega.
    - unfoldM'.
      destruct (compile_sexp se1 _ _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct (freshes _ _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hsucc].
      destruct (compile_sexp se2 _ _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hsucc].
      forwards*: IHse1; forwards*: IHse2.
      { intros ty m; dependent destruction m; simpl; eauto.
        forwards*: freshes_len.
        forwards*: (ctyps_of_typ__len_of_ty t1); congruence. }
      inverts* Hsucc.
  Qed.


  Lemma read_tup_writes' (vs : list var) (ts : list CTyp) (es : list exp) :
    forall x,  In x (writes_var (read_tup vs ts es)) -> In x vs.
  Proof.
    revert ts es; induction vs; simpl in *; introv; eauto.
    destruct es, ts; simpl; first [now destruct 1| destruct 1; jauto].
  Qed.

  Lemma gen_read_writes' loc (vs : list var) (ts : list CTyp) (es : list exp) e:
    forall x,  In x (writes_var (S.gen_read loc vs ts es e)) -> In x vs.
  Proof.
    revert ts es; induction vs; simpl in *; introv; eauto.
    destruct es, ts; simpl; first [now destruct 1| destruct 1; jauto].
  Qed.
  
  Lemma compile_wr_vars GA GS typ (se : Skel.SExp GA GS typ)
        (svar_env : SVarEnv GS) (avar_env : AVarEnv GA) (n0 n1 : nat) c es :
    compile_sexp se avar_env svar_env n0 =  (inl (c, es), n1) ->
    (forall x, In x (writes_var c) ->
               exists k l, (Var (str_of_pnat k l)) = x /\ n0 <= k < n1).
  Proof.
    Lemma id_mark A (x : A) :
      x = id x. eauto. Qed.
    Ltac t := do 2 eexists; splits*; omega.
    Ltac fwd H := first [forwards* (? & ? & ? & ?): H | forwards* (? & ? & ?): H ].
    revert n0 n1 svar_env c es; induction se; simpl;
      intros n0 n1 svar_env c es' Hsuc; eauto; try inverts Hsuc as Hsuc;
    eauto; unfoldM'; unfold compile_op in *;
          (repeat lazymatch type of Hsuc with
             | context [compile_sexp ?X ?Y ?Z ?n] => destruct (compile_sexp X Y Z n) as [[(? & ?) | ?] ?] eqn:?
             | context [freshes ?X ?Y] => destruct (freshes X Y) as ([? | ?] & ?) eqn:?
             end);
    (repeat lazymatch goal with [H : context [match ?E with | _ => _ end]|- _] => destruct E eqn:? end);
    (repeat lazymatch goal with [H : (_, _) = (_, _) |- _] => inverts* H end);
    (try inverts Hsuc); simpl; try tauto; intros; repeat rewrite in_app_iff in *;
    repeat lazymatch goal with
      | [H : False |- _] => destruct H
      | [H : _ \/ _ |- _] => destruct H
      end;
    try (forwards (? & ? & ? & ?): IHse; [now auto_star..|idtac]);
    try (forwards (? & ? & ? & ?): IHse1; [now auto_star..|idtac]);
    try (forwards (? & ? & ? & ?): IHse2; [now auto_star..|idtac]);
    try (forwards (? & ? & ? & ?): IHse3; [now auto_star..|idtac]);
    repeat lazymatch goal with
      | [H : compile_sexp ?A ?B ?C ?D = ?E |- _] =>
          forwards*: (>>compile_don't_decrease H);
            rewrite (id_mark _ (compile_sexp A B C D = E)) in H
      | [H : freshes ?A ?B = ?C |- _] =>
        forwards*: (>>freshes_incr H);
            rewrite (id_mark _ (freshes A B = C)) in H
      end; unfold id in *; 
    try (repeat eexists; eauto; omega);
    try (forwards ?: gen_read_writes'; [now auto_star..|idtac]);
    try (forwards ?: read_tup_writes'; [now auto_star..|idtac]);
    try (forwards (? & ? & ?): freshes_vars; [now auto_star..|idtac]);
    try (repeat eexists; eauto; omega).
    Grab Existential Variables.
    (* TODO: Fix me!*)
    apply (Var "").
    apply (Var "").
    apply (Var "").
    apply (Var "").
    apply (Var "").
  Qed.

  Lemma freshes_disjoint d n m xs :
    freshes d n = (inl xs, m) ->
    disjoint_list xs.
  Proof.
    revert n m xs; induction d; simpl; introv.
    - intros H; inverts H; simpl; eauto.
    - unfoldM.
      intros H; inverts H; simpl.
      split; eauto.
      intros Hin; clear IHd.
      assert (forall k, In (Var (str_of_pnat n k)) ((fix f (dim n : nat) :=
                                                       match dim with
                                                       | 0 => nil
                                                       | S d => Var (str_of_pnat n d) :: f d n
                                                       end) d n) ->
                        k < d).
      { clear Hin; induction d; simpl.
        - destruct 1.
        - intros k [H1 | H2].
          + lets* [? ?]: (>>var_pnat_inj H1); omega.
          + forwards*: IHd. }
      forwards*: H; omega.
  Qed.

  Lemma var_str_of_pnat_inj :
    forall n m n' m' : nat, Var (str_of_pnat n m) = Var (str_of_pnat n' m') -> n = n' /\ m = m'.
  Proof.
    Arguments str_of_pnat : simpl never.
    intros.
    assert (str_of_pnat n m = str_of_pnat n' m') by congruence.
    apply str_of_pnat_inj; auto.
  Qed.

  Lemma member_assn_svs GS ty (m : member GS ty) svar_env seval_env s:
    assn_of_svs seval_env svar_env s (emp_ph loc) -> 
    (S.vars2es (hget svar_env m) ==t vs_of_sval (hget seval_env m)) s (emp_ph loc).
  Proof.
    unfold assn_of_svs; dependent induction seval_env;
    dependent destruction svar_env; dependent destruction m; simpl; intros H;
    sep_split_in H; eauto.
  Qed.

  Fixpoint remove_by_mem {A t} (ls : list A) : member t ls -> list A :=
    match ls with
    | nil => fun m => nil
    | x :: ls => fun m =>
                   match m with
                   | HFirst _ => fun _ => ls
                   | HNext _ _ m => fun rec => rec m
                   end (remove_by_mem ls)
    end.

  (* Fixpoint remove_member {A B} {ls : list A} {t : A} *)
  (*          (hls : hlist B ls) : forall (m : member t ls), hlist B (remove_by_mem ls m) := *)
  (*   match hls with *)
  (*   | HNil => fun m => match m with *)
  (*                      | HFirst _ => _ *)
  (*                      | HNext _ _ m => _ *)
  (*                      end *)
  (*   | HCons x ls hx hls => fun m => match m with  *)
  (*                                 | HFirst _ => hls *)
  (*                                 | HNext _ _ m => remove_member hls m  *)
  (*                                 end *)
  (*   end. *)

  Lemma member_assn_avs GA ty (m : member ty GA) avar_env aeval_env:
    exists P, (forall stk,
    stk ||= assn_of_avs aeval_env avar_env <=>
            !(fst (hget avar_env m) === G.Zn (length (hget aeval_env m))) **
            (S.is_tuple_array_p (S.es2gls (S.vars2es (snd (hget avar_env m))))
               (length (hget aeval_env m)) (fun i : nat => vs_of_sval (nth_arr i (hget aeval_env m))) 0 1) ** P) /\
              (forall xs, (forall (x : var) (ty : Skel.Typ) (m : member ty GA), 
                  In x xs -> ~ In x (snd (hget avar_env m))) ->
               (forall (ty : Skel.Typ) (m : member ty GA), ~ In (fst (hget avar_env m)) xs) ->
               inde P xs).
  Proof.
    unfold assn_of_avs; dependent induction aeval_env;
    dependent destruction avar_env; dependent destruction m;
    destruct p.
    - eexists; split; intros; [simpl; rewrite <-!sep_assoc; reflexivity..|].
      forwards*: (>>inde_assn_of_avs aeval_env avar_env xs).
      intros; forwards*: (>>H (@HNext _ _ x _ m)).
      intros; forwards*: (>>H0 (@HNext _ _ x _ m)).
    - forwards*(P & Heq & ?): (>>IHaeval_env m avar_env).
      eexists; split. 
      + intros; simpl; rewrite Heq, <-!sep_assoc.
        split; intros; repeat sep_cancel; eauto.
      + intros.
        prove_inde.
        * rewrite Forall_forall; intros.
          forwards*: (>>H1 (@HFirst _ x ls)); simplify; eauto.
        * simplify; auto.
        * apply inde_is_tup_arr.
          intros; forwards*: (>>H0 (@HFirst _ x ls)).
          unfold S.es2gls, S.vars2es in *; simplify; auto.
        * apply H.
          intros; forwards*: (>>H0 (@HNext _ _ x _ m0)).
          intros; forwards*: (>>H1 (@HNext _ _ x _ m0)).
  Qed.  

  Lemma len_of_val typ (v : Skel.typDenote typ) : length (vs_of_sval v) = len_of_ty typ.
  Proof. induction typ; simpl; eauto; rewrite app_length; auto. Qed.

  Hint Rewrite prefix_nil ctyps_of_typ__len_of_ty gen_read_writes : core.
  Ltac sep_rewrites_in lem H :=
    match type of H with
    | ?X _ _ => pattern X in H
    end; rewrites lem in H; cbv beta in H.
  Ltac sep_rewrites_in_r lem H :=
    match type of H with
    | ?X _ _ => pattern X in H
    end; rewrites <- lem in H; cbv beta in H.
  Ltac sep_rewrites lem :=
    match goal with
    | |- ?X _ _ => pattern X
    end; rewrites lem; cbv beta.
  Ltac sep_rewrites_r lem :=
    match goal with
    | |- ?X _ _ => pattern X
    end; rewrites <- lem; cbv beta.
  Hint Rewrite len_of_val : core.
  Hint Unfold S.es2gls S.vars2es.

  Require Import SkelLib Psatz.
  Lemma nth_error_lt' A (arr : list A) i v : 
    List.nth_error arr i = Some v -> i < length arr.
  Proof.
    revert i v; induction arr; intros i v; destruct i; simpl; inversion 1; try omega.
    forwards*: IHarr; omega.
  Qed.
  Lemma nth_error_lt A (arr : list A) i v : 
    nth_error arr i = Some v -> (0 <= i /\ i < len arr)%Z.
  Proof.
    unfold nth_error, Z_to_nat_error.
    destruct Z_le_dec; try now inversion 1.
    unfold ret; simpl; unfold bind_opt.
    intros H; apply nth_error_lt' in H.
    rewrite Nat2Z.inj_lt in H.
    rewrite !Z2Nat.id in H; unfold len; omega.
  Qed.
  Hint Rewrite prefix_nil ctyps_of_typ__len_of_ty gen_read_writes : core.

  Ltac no_side_cond tac :=
    tac; [now auto_star..|idtac].

  Opaque freshes. 

  Lemma compile_gens GA GS typ (se : Skel.SExp GA GS typ) avar_env svar_env n0 n1 c es :
    compile_sexp se avar_env svar_env n0 = (inl (c, es), n1) ->
    (forall ty (m : member ty GS),
       forall k l, In (Var (str_of_pnat k l)) (hget svar_env m) -> k < n0) -> (* fvs are not in the future generated vars *)
    (forall ty (m : member ty GA),
        prefix "l" (S.str_of_var (fst (hget avar_env m))) = false) ->
    (forall e k l , In e es -> In (Var (str_of_pnat k l)) (fv_E e) -> k < n1).
  Proof.
    Definition used {A : Type} (x : A) := x.
    Lemma used_id (A : Type) (x : A) : x = used x. auto. Qed.

    revert avar_env svar_env n0 n1 c es; induction se; introv; simpl;
    intros H; unfold bind_opt, compile_op in *;
    repeat match type of H with
           | context [compile_sexp ?x ?y ?z ?w] =>
             destruct (compile_sexp x y z w) as [[(? & ?) | ?] ?] eqn:?; [|inversion H]; simpl in *
           | context [hget avar_env ?y] => 
             destruct (hget avar_env y) eqn:?; simpl in *
           | context [freshes ?x ?y ] => 
             destruct (freshes x y) as [[? | ?] ?] eqn:?; [|inversion H]; simpl in *
           | context [match ?t with _ => _ end] =>
             lazymatch type of t with list _ => idtac | Skel.BinOp _ _ _ => idtac end;
               destruct t; try now inversion H
           end; inverts H; intros; simplify; try tauto;
    (try now forwards*: H);
    repeat match goal with
    | [H : compile_sexp ?x ?y ?z ?w = ?u |- _] => 
      forwards*: (>>compile_don't_decrease H);
        rewrite (used_id _ (compile_sexp x y z w = u)) in H
    end; unfold used in *;
    try (forwards ?: IHse; [simpl; now auto_star..|idtac]);
    try (forwards ?: IHse1; [simpl; now auto_star..|idtac]);
    try (forwards ?: IHse2; [first [simpl; now auto_star | intros; forwards*: H; omega]..|idtac]);
    try (forwards ?: IHse3; [first [simpl; now auto_star | intros; forwards*: H; omega]..|idtac]); try omega;
    try now (forwards* (? & ? & ?): freshes_vars;
             forwards*: freshes_incr;
             lazymatch goal with
             | [H : Var (str_of_pnat _ _) = Var (str_of_pnat _ _) |- _ ] =>
               apply var_str_of_pnat_inj in H; omega
             end).
    forwards*: (>>H0 m); rewrite Heqp in *; simpl in *; autorewrite with core in *; congruence.
    Lemma in_firstn (A : Type) (x : A) l n : In x (firstn n l) -> In x l.
    Proof.
      revert l; induction n; intros l; simpl; try tauto.
      destruct l; simpl; try tauto.
      destruct 1; auto.
    Qed.
    apply in_firstn in H1.
    forwards*: IHse.
    Lemma in_skipn (A : Type) (x : A) l n : In x (skipn n l) -> In x l.
    Proof.
      revert l; induction n; intros l; simpl; try tauto.
      destruct l; simpl; try tauto.
      eauto.
    Qed.
    apply in_firstn, in_skipn in H1.
    forwards*: IHse.

    forwards*: IHse2.
    introv H'; dependent destruction m; simpl in *.
    forwards* (? & ? & ?): freshes_vars; substs.
    apply var_str_of_pnat_inj in H5.
    forwards*: freshes_incr. omega.
    
    forwards*: H.
    forwards*: freshes_incr. omega.
  Qed.

  Lemma compile_ok GA GS typ (se : Skel.SExp GA GS typ)
        (seval_env : SEvalEnv GS)
        (svar_env : SVarEnv GS)
        (aeval_env : AEvalEnv GA)
        (avar_env : AVarEnv GA)
        (n m : nat) 
        (v : Skel.typDenote typ) c es :
    Skel.sexpDenote GA GS typ se aeval_env seval_env = Some v ->
    compile_sexp se avar_env svar_env n = (inl (c, es), m) ->
    (forall ty (m : member ty GS), length (hget svar_env m) = len_of_ty ty) ->
    (forall ty (m : member ty GA), length (snd (hget avar_env m)) = len_of_ty ty) ->
    (forall ty (m : member ty GS),
       forall k l, In (Var (str_of_pnat k l)) (hget svar_env m) -> k < n) -> (* fvs are not in the future generated vars *)
    (forall ty (m : member ty GA) y,
        In y (snd (hget avar_env m)) -> prefix "l" (S.str_of_var y) = false) ->
    (forall ty (m : member ty GA),
        prefix "l" (S.str_of_var (fst (hget avar_env m))) = false) ->
    (* (iii) return exps. don't have future generated vars*)
    CSL BS tid  (* correctness of gen. code *)
        (!(assn_of_svs seval_env svar_env) **
          (assn_of_avs aeval_env avar_env))
        c
        (!(assn_of_svs seval_env svar_env) **
          (assn_of_avs aeval_env avar_env) ** !(es ==t vs_of_sval v)).
  Proof.
    revert typ se seval_env svar_env n m v c es.
    induction se; simpl;
    introv Heval Hcompile Hsvctx Havctx Hsvar Havar1 Havar2; unfold bind_opt in Hcompile.
    - (* case of var *)
      inverts Hcompile.
      inverts Heval.
      { eapply Hforward; eauto using rule_skip.
        intros; sep_split; sep_split_in H; repeat sep_cancel.
        eauto using member_assn_svs. }
    - (* the case of const *)
      inverts Hcompile; substs.
      { eapply Hforward; [apply rule_skip|].
        intros; sep_split; sep_split_in H; eauto.
        inversion Heval; substs.
        simpl; sep_split; eauto using emp_emp_ph; unfold_conn; simpl; auto. }
    - (* the case of binop *) 
      (* getting compilation/evaluation/typing results of sub-expressions *)
      destruct (compile_sexp se1 _ _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (compile_sexp se2 _ _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hcompile].
      destruct es1 as [|e1 [|]]; try now inverts Hcompile.
      destruct es2 as [|e2 [|]]; try now inverts Hcompile.

      destruct (compile_op _ _ _) as [c0 es0]; inverts Hcompile.
      admit.
    - destruct (compile_sexp se _ _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inverts Hcompile].
      destruct (hget avar_env m) as [arr anames] eqn:Haname.
      destruct (freshes _ _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inverts Hcompile].
      destruct es1 as [|i [|? ?]]; inverts Hcompile.
      
      unfold Monad.bind_opt in Heval.
      destruct (Skel.sexpDenote _ _ _ _ _ _) as [iv|] eqn:Heval1; inverts Heval.
      forwards* ?: IHse.
      eapply rule_seq; [eauto|].
      lets (P & Heq & HPinde): (member_assn_avs GA _ m avar_env aeval_env).
      eapply Hbackward.
      Focus 2.
      { intros s h Hpre.
        sep_rewrite_in Heq Hpre.
        repeat sep_rewrite_in_r sep_assoc Hpre.
        sep_split_in Hpre; simpl in *.
        sep_split_in HP1.
        sep_rewrites_in (>>S.is_array_tup_unfold (Z.to_nat iv)) Hpre.
        { simpl; intros.
          autorewrite with core; autounfold; simplify.
          forwards*: Havctx. }
        { forwards*: (>>nth_error_lt H0).
          unfold len in *. 
          rewrite Nat2Z.inj_lt; rewrite Z2Nat.id; omega. }
        simpl in Hpre.
        repeat sep_rewrite_in_r sep_assoc Hpre.
        rewrite Z2Nat.id in Hpre; [|forwards*: (>>nth_error_lt H0)].
        sep_rewrites_in (>>S.mps_eq1_tup' i) Hpre; [unfold_conn_all; eauto|].
        clear HP1; sep_combine_in Hpre.
        instantiate (1 :=
          (S.es2gls (S.vars2es (snd (hget avar_env m))) +ol i -->l (1,
            S.vs2es (vs_of_sval (nth_arr (Z.to_nat iv) (hget aeval_env m))))) **
          (S.is_tuple_array_p
            (S.es2gls (S.vars2es (snd (hget avar_env m)))) 
            (Z.to_nat iv)
            (fun i0 : nat => vs_of_sval (nth_arr i0 (hget aeval_env m))) 0
            1 **
          !(assn_of_svs seval_env svar_env) **
          !(fst (hget avar_env m) ===
            G.Zn (Datatypes.length (hget aeval_env m))) **
          !(i === iv) **
          S.is_tuple_array_p
            (S.es2gls (S.vars2es (snd (hget avar_env m))))
            (Datatypes.length (hget aeval_env m) - Z.to_nat iv - 1)
            (fun i0 : nat => vs_of_sval (nth_arr i0 (hget aeval_env m)))
            (S (Z.to_nat iv + 0)) 1 ** P)).
        sep_normal; repeat sep_cancel. } Unfocus.

      rewrite Haname; simpl.
      cutrewrite (anames = snd (hget avar_env m)); [|rewrite Haname; auto].
      assert (length (snd (hget avar_env m)) = length fvs1).
      { simplify.
        rewrites* (>>freshes_len fvs1).
        rewrites* (>>Havctx). }
      forwards*: compile_don't_decrease.
      forwards*: freshes_incr; substs.
      eapply Hforward; [apply rule_frame; [applys* S.gen_read_correct|]|]; eauto;
      prove_inde; try repeat first [apply HPinde | apply S.inde_is_tup_arr | apply inde_assn_of_svs];
      autounfold; introv; autorewrite with core; simplify; eauto;
      try lazymatch goal with
      | [Hfv : In _ fvs1 |- _] => 
        forwards* (? & ? & ?): (>>freshes_vars Hfv); substs
      end.
      match goal with
      | [Hin : In _ ?xs |- _] =>
        match xs with
        | fvs1 => fail 
        | S.fv_E ?e => 
          match goal with
          | [H : compile_sexp _ _ _ _ = (inl (_, ?f e), _) |- _] => forwards*: comp
        
      
      
      { simplify; simpl in *; eauto.
        forwards* (? & ? & ?): (freshes_vars); substs.
        forwards*: H; omega. }
      { simplify; eauto.
        forwards* (? & ? & ?): (freshes_vars); substs.
        forwards*: Havar1; simpl in *; autorewrite with core in *; congruence. }
      { forwards*: (freshes_disjoint). }
      { rewrites* (>>freshes_len fvs1).
        repeat autorewrite with core; auto. }
      { autorewrite with core; auto.
        Ltac contains expr n :=
          match expr with
          | n => idtac
          | S ?e => contains e n
          end.
        Ltac states_cond P n m :=
          let rel lhs rhs := first [contains lhs n; contains rhs m | contains lhs m; contains rhs n] in
          match P with
          | ?lhs < ?rhs => rel lhs rhs
          | ?lhs <= ?rhs => rel lhs rhs
          | ?lhs > ?rhs => rel lhs rhs
          | ?lhs >= ?rhs => rel lhs rhs
          | ?lhs = ?rhs => rel lhs rhs
          end.
        Ltac des :=
          first [ simpl in *; autorewrite with core in *; congruence |
                  match goal with
                  | [n : nat, m : nat |- _] =>
                    match goal with
                    | [H : ?P, Hcomp : compile_sexp _ _ _ n = (_, m) |- _] =>
                      states_cond P n m; 
                        no_side_cond ltac:(forwards*: (>>compile_don't_decrease Hcomp)); omega
                    end
                  end].
        prove_inde;
          try repeat first [apply HPinde | apply S.inde_is_tup_arr | apply inde_assn_of_svs];
        autounfold in *;
        simplify; forwards*(? & ? & ?): freshes_vars; substs;
        match goal with
        | [H : In _ (snd (hget avar_env ?m)) |- _] => forwards*: (>>Havar1 H); try des
        | [H : In _ (fst (hget avar_env ?m)) |- _] => forwards*: (>>Havar2 H); try des
        | [H : In _ (hget svar_env ?m) |- _] => forwards*: (>>Hsvar H); try des
        | _ => idtac
        end.
        



        try first [no_side_cond ltac:(forwards*: Havar1)]. 
          try (apply inde_is_tup_arr; autounfold; simplify; eauto;
           forwards* (? & ? & ?): (freshes_vars); substs; forwards*: (>>Havar1);
           simpl in *; autorewrite with core in *; congruence);
          try (prove_inde; simplify; forwards* (? & ? & ?): freshes_vars; substs; 
          forwards*: H; omega); auto.
        - apply inde_assn_of_svs; simplify.
          forwards* (? & ? & ?): freshes_vars; substs; 
          forwards*: (>>Hsvar m1).
          forwards*: (compile_don't_decrease); omega.
        - apply HPinde; auto; simplify; forwards* (? & ? & ?): freshes_vars; substs;
          [forwards*: Havar1 | forwards*: (>>Havar2 m1)]; simpl in *; autorewrite with core in *.
          congruence.
          rewrite H4 in H6; simpl in *; autorewrite with core in *; congruence. }
      introv Hpre; sep_rewrites Heq; sep_normal; sep_normal_in Hpre;
      sep_split_in Hpre;
      sep_rewrites (>>S.is_array_tup_unfold (Z.to_nat iv)).
      { simpl; intros.
        autorewrite with core; autounfold; simplify.
        forwards*: Havctx. }
      { forwards*: (>>nth_error_lt H0).
        unfold len in *. 
        rewrite Nat2Z.inj_lt; rewrite Z2Nat.id; omega. }
      sep_rewrites (>>S.mps_eq1_tup' i); [unfold_conn_all; simpl; rewrite Z2Nat.id; forwards*: (>>nth_error_lt H0); try omega|].
      sep_normal; sep_split; repeat sep_cancel.
      
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - (* the case of let *) 
      unfold bind_opt in Hcompile.
      (* getting compilation/evaluation/typing results of sub-expressions *)
      destruct (compile_sexp se1 _ _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (freshes _ _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hcompile].
      destruct (compile_sexp se2 _ _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hcompile].
      inverts Hcompile.
      
      destruct (Skel.sexpDenote _ _ t1 _ _ _) as [v1|] eqn:Heval1; simpl in Heval; [|inversion Heval].
      destruct (Skel.sexpDenote _ _ t2 _ _ _) as [v2|] eqn:Heval2; simpl in Heval; [|inversion Heval].
      inverts Heval.
      
      (* obtaining induction hypothesis1 *)
      forwards* (Hres1 & Htri1): IHse1; clear IHse1.

      (* freshness of generated variables *)
      forwards* : (>>freshes_incr Hfeq1); substs.

      (* obtaining induction hypothesis 2 *)
      forwards* (Hres2 & Htri2): IHse2; [..|clear IHse2].
      { introv; dependent destruction m0; simpl; jauto.
        forwards*: freshes_len.
        rewrite ctyps_of_typ__len_of_ty in *; eauto. }
      { introv; dependent destruction m0; simpl; jauto.
        - intros; forwards* (? & ? & ?): freshes_vars.
          forwards*: (>> var_str_of_pnat_inj H0); omega.
        - intros; forwards*: Hsvar.
          forwards*: (>>compile_don't_decrease t1); omega. }
      
      (* prove goals *)
      splits; eauto.

      eapply rule_seq; [apply Htri1|].

      (* assignment to generated variables *)
      eapply rule_seq.
      eapply Hbackward.
      Focus 2.
      { intros; sep_normal_in H.
        assert ((!(es1 ==t vs_of_sval v1) ** (!(assn_of_svs seval_env svar_env) **
                 assn_of_avs aeval_env avar_env)) s h).
        { repeat sep_cancel. }
        apply H0. } Unfocus.
      eapply rule_frame; [applys* read_tup_correct|].
      (* side-conditions of the assignment *)
      { intros.
        forwards* (? & ? & ?): freshes_vars; substs.
        intros Hc; forwards*: Hres1; try omega. }
      { forwards*: freshes_disjoint. }
      { rewrite len_of_val.
        forwards*: compiler_preserve. }
      { forwards*: freshes_len; forwards*: compiler_preserve.
        Hint Rewrite ctyps_of_typ__len_of_ty app_length prefix_nil : core.
        autorewrite with core in *; congruence. }
      { rewrite S.read_tup_writes; [|rewrites* (>>freshes_len)].
        prove_inde.
        - apply inde_assn_of_svs; simplify.
          forwards*(? & ? & ?): freshes_vars; substs; forwards*: Hsvar;
          forwards*: (>>compile_don't_decrease se1); omega.
        - apply inde_assn_of_avs; simplify.
          + forwards*(? & ? & ?): freshes_vars; substs; forwards*: Havar1.
            simpl in *; autorewrite with core in *; congruence.
          + forwards*(? & H' & ?): freshes_vars; substs.
            forwards*H'': (>>Havar2 m0); 
            rewrite H' in H''; simpl in *; autorewrite with core in *; congruence.
        - autorewrite with core; forwards*: (>>compiler_preserve es1). }
      unfold assn_of_svs in *; simpl in *.
      eapply rule_conseq; eauto; intros ? ? H; 
      sep_normal_in H; sep_normal; sep_split_in H; sep_split; eauto.
      sep_split; eauto.
      sep_split_in HP; eauto.
Qed.


      eapply Hbackward.
      Focus 2. {
        intros s h H; sep_normal_in H.
        assert ((!(vars2es fvs1 ==t vs_of_sval v1) **
                 !(assn_of_svs seval_env svar_env (free_sv (Sx.ELet x se1 se2 ty0))) **
                 assn_of_avs (free_av (Sx.ELet x se1 se2 ty0))) s h).
        { simpl.
          unfold assn_of_svs; sep_rewrite SE.union_assns; sep_rewrite pure_star.
          unfold assn_of_avs; sep_rewrite SA.union_assns.
          rewrite !fold_assn_svs, !fold_assn_avs.
          sep_normal; repeat sep_cancel. }
        simpl in H0.

        sep_rewrite_in SE.union_comm H0.
        sep_rewrite_in SA.union_comm H0.
        unfold assn_of_svs in H0; sep_rewrite_in SE.union_assns H0.
        unfold assn_of_avs in H0; sep_rewrite_in SA.union_assns H0.
        rewrite !fold_assn_svs, !fold_assn_avs in H0.
        assert (((!(assn_of_svs (upd_opt seval_env x v1) (upd svar_env x fvs1) (free_sv se2)) **
                  assn_of_avs (free_av se2)) **
                 (!(assn_of_svs seval_env svar_env (SE.SE.diff (free_sv se1) (SE.remove x (free_sv se2)))) **
                  assn_of_avs (SA.SE.diff (free_av se1) (free_av se2)))) s h).
        { sep_normal; repeat sep_cancel.
          sep_lift 2; sep_cancel.
          sep_rewrite_in pure_star H2.
          sep_lift 1; sep_cancel.
          destruct (SE.in_dec (free_sv se2) x).
          - sep_rewrite (SE.choose_remove _ _ i).
            unfold assn_of_svs.
            sep_rewrite SE.add_equiv; [|autorewrite with setop; intros [Hc Hc']; congruence].
            unfold upd, upd_opt; destruct eq_dec; [|congruence].
            sep_rewrite pure_star; sep_rewrite pure_pure.
            sep_cancel.
            sep_rewrite SE.assn_of_vs_eq;
              [unfold assn_of_svs in *; eauto | introv; autorewrite with setop;
                                                intros [? ?]; try destruct eq_dec; try congruence..].
          - sep_rewrite (SE.remove_id (free_sv se2) x); eauto.
            unfold assn_of_svs in *; sep_rewrite SE.assn_of_vs_eq;
              [ sep_split_in H3; sep_split; eauto |
                introv; autorewrite with setop;
                unfold upd, upd_opt; case_if; intros [? ?]; eauto; congruence..]. }
        exact H1. } Unfocus.
      eapply Hforward; [eapply rule_frame; [apply Htri2|]| ].
      + prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs];
          introv; repeat autorewrite with setop; intros ? ? ?; simplify;
            forwards* (? & ? & ? & ?): Hwr2; des; substs.
        * forwards*: Hsvar; autorewrite with setop; eauto.
          forwards*: (>>compile_don't_decrease se1); omega.
        * forwards*: Havar1; autorewrite with setop; eauto.
          simpl in *; rewrite prefix_nil in *; congruence.
        * forwards*: Havar2; autorewrite with setop; eauto.
          rewrite <-H2 in *; simpl in *; rewrite prefix_nil in *; congruence.
      + intros s h H; simpl.
        sep_rewrite SE.union_comm; sep_rewrite SA.union_comm.
        unfold assn_of_svs, assn_of_avs.
        sep_rewrite SE.union_assns; sep_rewrite pure_star;
          sep_rewrite SA.union_assns; sep_normal.
        rewrite !fold_assn_svs, !fold_assn_avs.
        repeat sep_cancel.
        apply scC; sep_cancel.
        destruct (SE.in_dec (free_sv se2) x).
        * sep_rewrite_in (SE.choose_remove _ _ i) H3.
          unfold assn_of_svs in H3.
          sep_rewrite_in SE.add_equiv H3; [|autorewrite with setop; intros [Hc Hc']; congruence].
          unfold upd, upd_opt in H3; destruct (eq_dec x x); [|congruence].
          sep_rewrite_in pure_star H3; sep_split_in H3.
          sep_split; unfold assn_of_svs; eauto.
          sep_rewrite SE.assn_of_vs_eq;
              [unfold assn_of_svs in *; eauto | introv; autorewrite with setop;
                                                intros [? ?]; try destruct eq_dec; try congruence..].
        * sep_rewrite_in (SE.remove_id _ _ n0) H3.
          unfold assn_of_svs in *;
          sep_rewrite SE.assn_of_vs_eq; eauto;
          introv; autorewrite with setop; intros [? ?]; unfold upd, upd_opt;
            destruct eq_dec; substs; eauto; congruence.
    - unfoldM'.
      destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hcompile].
      destruct es1 as [|e1 [|? ?]]; try now inverts Hcompile.
      destruct es2 as [|e2 [|? ?]]; inverts Hcompile.

      inverts Heval as Heval1 Heval2; substs.
      inverts Htyp as Htyp1 Htyp2; substs.
      forwards* (Hres1 & Htri1): IHse1.
      { intros; eapply Hsvar; eauto; autorewrite with setop; eauto. }
      { intros; applys* Havar1; rewrite SA.union_spec; eauto. }
      { intros; applys* Havar2; rewrite SA.union_spec; eauto. }
      forwards* ( Hres2 & Htri2): IHse2.
      { intros; forwards*: Hsvar; eauto; autorewrite with setop; eauto.
        forwards*: (>>compile_don't_decrease se1); omega. }
      { intros; applys* Havar1; rewrite SA.union_spec; eauto. }
      { intros; applys* Havar2; rewrite SA.union_spec; eauto. }

      splits; try omega.
      (* { simpl; destruct op; simpl in *; *)
      (*   [inverts H0; simpl; *)
      (*    introv; rewrite !in_app_iff; intros [? | [? | []]]; *)
      (*    [forwards* (? & ? & ? & ?): Hwr1| forwards* (? & ? & ? & ?): Hwr2]; *)
      (*    do 2 eexists; splits; eauto; try omega; *)
      (*    [forwards*: (>>compile_don't_decrease Hceq2); omega| *)
      (*     forwards*: (>>compile_don't_decrease Hceq1); omega]..]. } *)
      { simpl; destruct op; simpl in *;
        [inverts H0; simpl; simplify..];
        lazymatch goal with
        | [H : context [In (Var (str_of_pnat _ _)) (fv_E e1)] |- _] =>
          forwards*: Hres1
        | [H : context [In (Var (str_of_pnat _ _)) (fv_E e2)] |- _] =>
          forwards*: Hres2
        end;
        first [forwards*: (>>compile_don't_decrease Hceq2); omega | forwards*: (>>compile_don't_decrease Hceq1); omega]. }
      eapply Hbackward.
      Focus 2.
      { unfold assn_of_svs, assn_of_avs; intros;
        sep_rewrite_in (SE.union_assns) H; sep_rewrite_in (SA.union_assns) H;
        rewrite !fold_assn_svs, !fold_assn_avs in H;
        sep_rewrite_in pure_star H; sep_normal_in H.
        assert (((!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) **
                 !(assn_of_svs seval_env svar_env (SE.SE.diff (free_sv se2) (free_sv se1))) **
                 assn_of_avs (SA.SE.diff (free_av se2) (free_av se1))) s h).
        { sep_normal; repeat sep_cancel. }
        apply H1. } Unfocus.
      assert (c = (cs1 ;; cs2 ;; fst (compile_op op e1 e2) )); [|substs].
      { destruct op; simpl in *; inverts H0; eauto. }
      eapply rule_seq; [eapply rule_frame; eauto|].
      { prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs];
        introv; repeat autorewrite with setop; intros ? ? ?;
          forwards* (? & ? & ? & ?): (>> compile_wr_vars Hceq1); des; substs.
        - forwards*: Hsvar; autorewrite with setop; eauto. omega.
        - forwards*: Havar1; autorewrite with setop; eauto.
          simpl in *; rewrite prefix_nil in *; congruence.
        - forwards*: Havar2; autorewrite with setop; eauto.
          rewrite <-H3 in *; simpl in *; rewrite prefix_nil in *; congruence. }
      eapply Hbackward.
      Focus 2. {
        intros s h H.
        assert ((!(e1 :: Datatypes.nil ==t vs_of_sval v1) **
                 !(assn_of_svs seval_env svar_env (SE.union (free_sv se1) (free_sv se2))) **
                 assn_of_avs (SA.union (free_av se1) (free_av se2))) s h).
        { unfold assn_of_svs, assn_of_avs;
          sep_rewrite SE.union_assns; sep_rewrite SA.union_assns;
          sep_rewrite pure_star; sep_normal; sep_normal_in H;
          rewrite !fold_assn_svs, !fold_assn_avs; repeat sep_cancel. }
        sep_rewrite_in SE.union_comm H1; sep_rewrite_in SA.union_comm H1;
          unfold assn_of_svs, assn_of_avs in H1;
          sep_rewrite_in SE.union_assns H1; sep_rewrite_in SA.union_assns H1;
            rewrite !fold_assn_svs, !fold_assn_avs in H1.
        instantiate (1 :=
         (!(assn_of_svs seval_env svar_env (free_sv se2)) ** assn_of_avs (free_av se2)) **
         !(e1 :: Datatypes.nil ==t vs_of_sval v1) **
         !(assn_of_svs seval_env svar_env (SE.SE.diff (free_sv se1) (free_sv se2))) **
         assn_of_avs (SA.SE.diff (free_av se1) (free_av se2))).
        sep_normal; sep_rewrite_in pure_star H1; sep_normal_in H1; repeat sep_cancel. } Unfocus.
      eapply rule_seq; [eapply rule_frame; eauto|].
      { prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs | apply inde_eq_tup; rewrite Forall_forall];
        simpl; introv; repeat autorewrite with setop; intros; simplify;
        forwards* (? & ? & ? & ?): (>>compile_wr_vars Hceq2); substs.
        - forwards*: Hres1; omega.
        - forwards*: Hsvar; autorewrite with setop; jauto.
          forwards*: (>>compile_don't_decrease se1). omega.
        - forwards*: Havar1; autorewrite with setop; jauto.
          simpl in *; rewrite prefix_nil in *; congruence.
        - forwards*: Havar2; autorewrite with setop; jauto.
          rewrite <-H2 in H4; simpl in *; rewrite prefix_nil in *; congruence. }
      (* TODO: modular lemma for compile_op *)
      assert (Heq: fst (compile_op op e1 e2) = Cskip); [|rewrite Heq; clear Heq ].
      { unfold compile_op; destruct op; eauto. }
      eapply Hforward; eauto using rule_skip.
      intros s h H.
      sep_rewrite SE.union_comm; sep_rewrite SA.union_comm;
        unfold assn_of_svs, assn_of_avs;
        sep_rewrite SE.union_assns; sep_rewrite SA.union_assns.
      rewrite !fold_assn_svs, !fold_assn_avs;
        sep_rewrite pure_star; sep_normal; sep_normal_in H;
          sep_split_in H; sep_split; eauto; sep_cancel.
      asserts_rewrite (es = snd (compile_op op e1 e2)).
      { destruct op; simpl in *; inverts* H0. }
      destruct op, v1, v2; simpl in *; inverts H9;
        sep_split_in HP0; sep_split_in HP1; unfold_conn_in (HP3, HP4); simpl in *;
          sep_split; eauto; unfold_conn; simpl; try congruence;
      rewrite HP3, HP4.
      destruct (Z.eqb_spec n0 n1); destruct (eq_dec n0 n1); eauto; congruence.
      destruct (Z.ltb_spec0 n0 n1); destruct (Z_lt_dec n0 n1); eauto; congruence.
    - unfoldM'.
      Lemma p2 {A B} (x : A * B) : x = (fst x, snd x). destruct x; auto. Qed.
      destruct (compile_sexp _ se _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      rewrite (p2 (avar_env x)) in *.
      destruct (freshes (length _) _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hcompile].
      destruct es1 as [|? [|? ?]]; inverts Hcompile.
      inverts Htyp as Htyp Hatyp; inverts Heval as Heval Haeval Hle Hgt.
      forwards* (Hres & Htri): IHse.
      { intros; applys* Havar1; autorewrite with setop; eauto. }
      { intros; applys* Havar2; autorewrite with setop; eauto. }
      assert (Hlenfv : length fvs1 = length (snd (avar_env x))).
      { forwards*: (>>freshes_len Hfeq1); simplify; rewrite Heq in *; eauto. }
      splits.
      (* { introv; simpl; rewrite gen_read_writes. *)
      (*   2: simplify; eauto. *)
      (*   rewrite in_app_iff; intros [? | ?]. *)
      (*   - forwards* (? & ? & ? & ?): Hwr; do 2 eexists; splits*; try omega. *)
      (*     forwards*: (>>freshes_vars Hfeq1); omega. *)
      (*   - forwards* (? & Hgenv): (>>freshes_vars Hfeq1). *)
      (*     forwards* (? & ? & ?): Hgenv. *)
      (*     do 2 eexists; splits*; try omega. *)
      (*     forwards*: (>>compile_don't_decrease). } *)
      { intros; simplify;
        forwards*: (>>freshes_incr Hfeq1).
        forwards* (? & ? & ?): (>>freshes_vars Hfeq1).
        forwards* (? & ?): (>>var_pnat_inj H1); omega. }
      eapply Hbackward.
      Focus 2. {
        intros s h H.
        unfold assn_of_svs, assn_of_avs in H.
        Hint Rewrite SE.singleton_spec SA.singleton_spec: setop.
        Lemma add_union x s :
          SA.add x s == SA.union (SA.singleton x) s.
        Proof.
          simpl; unfold SA.Equal; introv.
          autorewrite with setop; split; eauto.
        Qed.
        sep_rewrite_in add_union H; sep_rewrite_in SA.union_comm H.
        sep_rewrite_in SA.union_assns H.
        rewrite !fold_assn_svs, !fold_assn_avs in H.
        instantiate (1 :=
          (!(assn_of_svs seval_env svar_env (free_sv se)) **  assn_of_avs (free_av se)) **
            assn_of_avs (SA.SE.diff (SA.singleton x) (free_av se))).
        sep_normal; sep_normal_in H; repeat sep_cancel. } Unfocus.
      eapply rule_seq; [eapply rule_frame; eauto|].
      { prove_inde; apply inde_assn_of_avs; unfold not; intros;
        forwards* (? & ? & ? & ?) : (>>compile_wr_vars Hceq1); substs;
        intros; [forwards*: Havar1 | forwards*: Havar2]; autorewrite with setop in *; jauto.
        simpl in *; rewrite prefix_nil in *; congruence.
        rewrite <-H2 in *; simpl in *; rewrite prefix_nil in *; congruence. }
      eapply Hbackward.
      Focus 2.
      { intros s h H.
        sep_normal_in H; sep_split_in H; simpl in *.
        sep_split_in HP0.
        assert (assn_of_avs (SA.add x (SA.remove x (free_av se))) s h).
        { Lemma add_remove x s :
            SA.add x (SA.remove x s) == SA.add x s.
          Proof.
            simpl; unfold SA.Equal; introv; autorewrite with setop; split;
              intros.
            - destruct H as [? | [? ?]]; eauto.
            - destruct (eq_dec a x); eauto.
              destruct H; eauto.
          Qed.
          sep_rewrite add_remove; sep_rewrite add_union; sep_rewrite SA.union_comm.
          unfold assn_of_avs; sep_rewrite SA.union_assns.
          apply H. }
        unfold assn_of_avs in H0;
          sep_rewrite_in SA.add_equiv H0; [|autorewrite with setop; intros [? ?]; congruence].
        rewrite Haeval in H0.
        sep_rewrite_in (is_array_tup_unfold (S.es2gls (S.vars2es (snd (avar_env x)))) (Z.to_nat ix)) H0.
        Focus 2. {
          simpl; intros; unfold S.es2gls; simplify.
          forwards* Htyv: (>> Haectx (VZ 0) i).
          unfold val in *; rewrites* (>>has_type_val_len Htyv).
          rewrites* (>>Havctx). } Unfocus.
        2: zify; rewrite Z2Nat.id; omega.
        simpl in H0.
        assert ((Zn (Z.to_nat ix) === e) s (emp_ph loc)).
        { unfold_conn_in HP1; unfold_conn; simpl in *; rewrite Z2Nat.id; eauto. }
        sep_rewrite_in S.mps_eq1_tup' H0; [|exact H1].
        clear HP0; sep_combine_in H0; sep_normal_in H0.
        sep_lift_in H0 2.
        apply H0. } Unfocus.
      eapply Hforward; [eapply rule_frame; [apply S.gen_read_correct|]; eauto|].
      { simpl; intros.
        forwards* (? & ? & ?): (>>freshes_vars Hfeq1).
        simplify; eauto.
        forwards*: Hres; omega. }
      { unfold not; intros; simplify.
        forwards* (? & ? & ?): (>>freshes_vars Hfeq1); substs.
        forwards*: Havar1; autorewrite with setop; eauto.
        simpl in *; rewrite prefix_nil in *; congruence. }
      { forwards*: freshes_disjoint. }
      { simplify; eauto. }
      { simpl; intros; unfold S.es2gls; simplify.
        forwards* Htyv: (>> Haectx (VZ 0) (Z.to_nat ix)).
        zify; rewrite Z2Nat.id; omega.
        unfold val in *; rewrites* (>>has_type_val_len Htyv).
        unfold val in *; forwards*: Havctx.
        congruence. }
      { rewrites* S.gen_read_writes; [|simplify; eauto].
        unfold S.es2gls.
        prove_inde; simplify; eauto;
          try (apply inde_assn_of_svs; unfold not; intros);
          try (apply inde_assn_of_avs; unfold not; intros); try (split; intros);
          forwards* (? & ? & ?): (>>freshes_vars Hfeq1); substs;
        try now (match goal with
             | [H : In ?y (snd (avar_env x)) |- _] =>
               forwards*: (Havar1 x y); autorewrite with setop; eauto; eauto;
               simpl in *; rewrite prefix_nil in *; congruence
             | [Heq : fst (avar_env x) = Var (str_of_pnat _ _) |- _] =>
               forwards*: (Havar2 x); autorewrite with setop; eauto;
               rewrite Heq in *; simpl in *; rewrite prefix_nil in *; congruence
             | [H : In _ (fv_E e) |- _ ] =>
               forwards*: Hres; autorewrite with setop; eauto; omega
             end).
        forwards*: Hsvar.
        forwards*: (>>compile_don't_decrease Hceq1); omega.
        forwards*: Havar1; autorewrite with setop in *; jauto.
        simpl in *; rewrite prefix_nil in *; congruence.
        forwards*: Havar2; autorewrite with setop in *; jauto.
        rewrite H2 in *; simpl in *; rewrite prefix_nil in *; congruence. }
      intros; sep_normal_in H; sep_split_in H; sep_split; eauto.
      sep_rewrite_r add_remove.
      unfold assn_of_avs; sep_rewrite SA.add_equiv; [|autorewrite with setop; intros [? ?]; congruence].
      rewrite Haeval.
      apply scC; sep_cancel.
      sep_rewrite (is_array_tup_unfold (S.es2gls (S.vars2es (snd (avar_env x)))) (Z.to_nat ix)).
      Focus 2. {
        simpl; intros; unfold S.es2gls; simplify.
        forwards* Htyv: (>> Haectx (VZ 0) i).
        unfold val in *; rewrites* (>>has_type_val_len Htyv).
        rewrites* (>>Havctx). } Unfocus.
      2: zify; rewrite Z2Nat.id; omega.
      unfold S.es2gls in *; simpl.
      assert ((Zn (Z.to_nat ix) === e) s (emp_ph loc)).
      { unfold_conn_in HP1; unfold_conn; simpl in *; rewrite Z2Nat.id; eauto. }
      sep_rewrite S.mps_eq1_tup'; [|exact H1].
      sep_normal; sep_split; repeat sep_cancel.
    - rewrite (p2 (avar_env x)) in *.
      inverts Hcompile.
      inverts Heval.
      split.
      { intros; simplify.
        forwards*: Havar2; autorewrite with setop; eauto.
        rewrite H0 in *; simpl in *; rewrite prefix_nil in *; try congruence. }
      simpl; eapply Hforward; eauto using rule_skip.
      intros.
      sep_split; sep_split_in H; intros; repeat sep_cancel.
      sep_split; eauto using emp_emp_ph.
      unfold assn_of_avs in *; sep_rewrite_in (SA.add_equiv') H.
      2: instantiate (1 := x); autorewrite with setop; eauto.
      sep_rewrite_in (SA.add_equiv) H; [|autorewrite with setop; intros [? ?]; congruence]; try rewrite H1 in H.
      sep_normal_in H; sep_split_in H; eauto.
    - unfoldM'.
      destruct (Sx.typ_of_sexp se) eqn:Heqty; try now inverts Hcompile.
      destruct (compile_sexp _ se _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (le_dec _ _); inverts Hcompile.
      inverts Htyp as Htyp Hlt.
      inverts Heval as Heval Hlt'.
      forwards* (Hres & Htri): IHse.
      splits*.
      Lemma firstn_in (A: Type) n (x : A) xs  : In x (firstn n xs) -> In x xs.
      Proof.
        revert xs; induction n; simpl; [destruct 1|].
        destruct xs; simpl; eauto.
        simpl in *; intros [? | ?]; eauto.
      Qed.

      Lemma skipn_in (A : Type) n (x : A) xs : In x (skipn n xs) -> In x xs.
      Proof.
        revert xs; induction n; simpl; eauto.
        destruct xs; simpl; eauto.
      Qed.
      Hint Resolve firstn_in skipn_in.
      intros; forwards*: Hres.
      eapply Hforward; eauto.
      simpl; intros s h H; sep_split_in H; sep_split; eauto.
      forwards*: type_preservation.
      forwards*: compiler_preserve.
      forwards*: (>>has_type_val_len H0).
      assert (Hlen : length es1 = length (vs_of_sval (VTup tup))) by congruence.
      inverts H0.
      rewrites* (>>typ_of_sexp_ok) in Heqty; inverts Heqty.
      revert H5 Hlt Hlen HP0.
      clear.
      intros Hty; revert i es1.
      induction Hty; simpl; introv Hlt Hlen Heq.
      + destruct es1; simpl in *; try congruence; intros; omega.
      + destruct i; simpl.
        * unfold len_at_i; simpl.
          forwards*: (>>has_type_val_len H); rewrite <-H0.
          revert Heq; clear; revert es1; induction (vs_of_sval x); introv.
          { intros; simpl; apply emp_emp_ph. }
          { destruct es1; simpl; eauto.
            intros H; sep_split_in H; sep_split; eauto. }
        * unfold len_at_i; simpl.
          forwards*: (>>has_type_val_len H).
          assert (exists es es1', es1 = es ++ es1' /\ length es = len_of_ty y) as
              (es & es1' & ? & Hlen'); [|substs].
          { exists (firstn (len_of_ty y) es1) (skipn (len_of_ty y) es1).
            split; eauto using firstn_skipn.
            rewrite firstn_length, Nat.min_l; eauto.
            rewrite app_length in *; omega. }
          Lemma eq_tup_app es1 es2 es1' es2' stk :
            length es1 = length es1' ->
            (es1 ++ es2 ==t es1' ++ es2') stk (emp_ph loc) ->
            (es1 ==t es1') stk (emp_ph loc) /\
            (es2 ==t es2') stk (emp_ph loc).
          Proof.
            revert es2 es1' es2'; induction es1; introv Hlen Heq.
            - destruct es1'; simpl in *; try congruence.
              split; eauto using emp_emp_ph.
            - destruct es1'; simpl in *; try congruence.
              sep_split_in Heq.
              forwards*: IHes1.
              split; sep_split; jauto.
          Qed.
          forwards* (? & ?): (>>eq_tup_app Heq).
          { unfold val; rewrite H0; eauto. }
          forwards*: (>>IHHty i); try omega.
          { simpl; rewrite !app_length in Hlen; omega. }
          Lemma skipn_app (A : Type) n (xs ys : list A) :
            skipn n (xs ++ ys) = if lt_dec n (length xs) then (skipn n xs) ++ ys else skipn (n - length xs) ys.
          Proof.
            revert xs ys; induction n; simpl; introv.
            - destruct lt_dec; eauto.
              destruct xs; simpl in *; try omega; eauto.
            - introv; destruct xs; simpl; eauto.
              rewrite IHn; repeat destruct lt_dec; try omega; eauto.
          Qed.
          unfold val, len_until_i in *; simpl in *; rewrite skipn_app; destruct lt_dec; try omega.
          unfold val in *; rewrite Hlen', <-H0, minus_plus.
          eauto.
    - assert (ty = ty0); [|substs].
      { forwards*: typ_of_sexp_ok. }
      revert n m c es0 sv ty0 Hsvar Htyp Heval Hcompile; induction H; introv Hsvar Htyp Heval Hcompile.
      + inverts Hcompile; simpl.
        inverts Htyp as Htyp; inverts Htyp.
        inverts Heval as Heval; inverts Heval.
        splits; try now destruct 1.
        eapply Hforward; eauto using rule_skip.
        simpl; intros; sep_split_in H; sep_split; repeat sep_cancel.
      + inverts Heval as Heval; inverts Heval as Heval0 Heval.
        inverts Htyp as Htyp; inverts Htyp as Htyp0 Htyp.
        unfoldM'.
        destruct (compile_sexp _ x _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
        lazymatch type of Hcompile with
        | context [let (_, _) := ?X in _] =>
          destruct X as [[(cs' & es') | ?] n''] eqn:Hceq2; inversion Hcompile
        end; substs.
        assert (Hnn' : n <= n').
        { forwards*: compile_don't_decrease. }
        assert (Hn'm : n' <= m).
        { revert Hceq2; clear; intros Hceq2.
          revert es' cs' n' m Hceq2; induction l; introv Hceq.
          - inverts Hceq; eauto.
          - unfoldM'.
            destruct (compile_sexp _ _ _ _)  as [[(cs1 & es1) | ?] k] eqn:Hceq1; [|inversion Hceq].
            lazymatch type of Hceq with
              | context [let (_, _) := ?X in _] =>
                destruct X as [[(cs'' & es'') | ?] n'''] eqn:Hceq2; inversion Hceq
            end; substs.
            forwards*: compile_don't_decrease.
            forwards*: IHl.
            omega. }
        forwards* (Hres & Htri): IHForall; try now constructor; eauto.
        { intros.
          forwards*: Havar1; simpl; autorewrite with setop; eauto. }
        { intros.
          forwards*: Havar2; simpl; autorewrite with setop; eauto. }
        { intros.
          forwards*: Hsvar; simpl; autorewrite with setop; eauto.
          forwards*: compile_don't_decrease; omega. }
        forwards* (Hres0 & Htri0): H.
        { intros.
          forwards*: Hsvar; simpl; autorewrite with setop; eauto. }
        { intros.
          forwards*: Havar1; simpl; autorewrite with setop; eauto. }
        { intros.
          forwards*: Havar2; simpl; autorewrite with setop; eauto. }
        splits.
        (* { introv; simpl; rewrite in_app_iff; intros [? | ?]; *)
        (*   [ forwards* (? & ? & ? & ?): Hwr0 | forwards*(? & ? & ? & ?): Hwr]; do 2 eexists; splits*; *)
        (*   omega. } *)
        { introv; rewrite in_app_iff; intros [? | ?] ?;
          [ forwards*: Hres0 | forwards*: Hres]; try omega. }
        simpl.
        eapply Hbackward.
        Focus 2. {
          unfold assn_of_svs, assn_of_avs; intros s h Hsat.
          sep_rewrite_in SE.union_assns Hsat; sep_rewrite_in pure_star Hsat.
          sep_rewrite_in SA.union_assns Hsat.
          rewrite !fold_assn_svs, !fold_assn_avs in Hsat.
          instantiate (1 :=
            ((!(assn_of_svs seval_env svar_env (free_sv x)) ** assn_of_avs (free_av x)) **
             !(assn_of_svs seval_env svar_env
               (SE.SE.diff (fold_right (fun (e : Sx.SExp) (xs : SE.t) => SE.union (free_sv e) xs) SE.empty l) (free_sv x))) **
          assn_of_avs (SA.SE.diff (fold_right (fun (e : Sx.SExp) (xs : SA.t) => SA.union (free_av e) xs) SA.empty l) (free_av x)))).
          sep_normal; sep_normal_in Hsat; repeat sep_cancel. } Unfocus.
        eapply rule_seq; [eapply rule_frame; eauto|].
        { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs];
          introv; autorewrite with setop; intros ? ? ?;
          forwards* (? & ? & ? & ?): (>>compile_wr_vars Hceq1); des; substs.
          - forwards*: Hsvar; simpl; autorewrite with setop; eauto; omega.
          - forwards*: Havar1; simpl; autorewrite with setop; eauto.
            simpl in *; rewrite prefix_nil in *; congruence.
          - forwards*: Havar2; simpl; autorewrite with setop; eauto.
            rewrite <-H4 in *; simpl in *; rewrite prefix_nil in *; congruence. }
        eapply Hbackward.
        Focus 2. {
          intros s h Hsat.
          assert (Hsat' : (!(es1 ==t vs_of_sval v) **
                   !(assn_of_svs seval_env svar_env
                     (SE.union (free_sv x) (fold_right (fun (e : Sx.SExp) (xs : SE.t) => SE.union (free_sv e) xs) SE.empty l))) **
                    assn_of_avs (SA.union (free_av x) (fold_right (fun (e : Sx.SExp) (xs : SA.t) => SA.union (free_av e) xs) SA.empty l)))
                    s h).
          { unfold assn_of_svs, assn_of_avs in *.
            sep_rewrite SE.union_assns; sep_rewrite SA.union_assns; sep_rewrite pure_star.
            sep_normal_in Hsat; sep_normal; repeat sep_cancel. }
          sep_rewrite_in SE.union_comm Hsat'; sep_rewrite_in SA.union_comm Hsat'.
          unfold assn_of_svs, assn_of_avs in *.
          sep_rewrite_in SE.union_assns Hsat';
          sep_rewrite_in SA.union_assns Hsat'; sep_rewrite_in pure_star Hsat'.
          rewrite !fold_assn_svs, !fold_assn_avs in Hsat'.
          instantiate (1 :=
            ((!(assn_of_svs seval_env svar_env
                            (fold_right (fun (e : Sx.SExp) (xs : SE.t) => SE.union (free_sv e) xs) SE.empty l)) **
              assn_of_avs (fold_right (fun (e : Sx.SExp) (xs : SA.t) => SA.union (free_av e) xs) SA.empty l)) **
             !(es1 ==t vs_of_sval v) **
             !(assn_of_svs seval_env svar_env
                  (SE.SE.diff (free_sv x) (fold_right (fun (e : Sx.SExp) (xs : SE.t) => SE.union (free_sv e) xs) SE.empty l))) **
             assn_of_avs (SA.SE.diff (free_av x)
                                     (fold_right (fun (e : Sx.SExp) (xs : SA.t) => SA.union (free_av e) xs) SA.empty l)))).
         sep_normal; sep_normal_in Hsat'; repeat sep_cancel. } Unfocus.
        eapply Hforward; [eapply rule_frame; eauto|].
        { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify];
          introv; autorewrite with setop; try intros ? ? ?;
          forwards* (? & ? & ? & ?): (>> compile_sexps_wr_vars); des; substs.
          - forwards*: Hres0; omega.
          - forwards*: Hsvar; simpl; autorewrite with setop; eauto; omega.
          - forwards*: Havar1; simpl; autorewrite with setop; eauto.
            simpl in *; rewrite prefix_nil in *; congruence.
          - forwards*: Havar2; simpl; autorewrite with setop; eauto.
            rewrite <-H4 in *; simpl in *; rewrite prefix_nil in *; congruence. }
        intros s h Hsat.
        sep_rewrite SE.union_comm; sep_rewrite SA.union_comm;
          unfold assn_of_svs, assn_of_avs in *;
          sep_rewrite SE.union_assns;
          sep_rewrite SA.union_assns; sep_rewrite pure_star.
        sep_normal_in Hsat; sep_normal; repeat sep_cancel.
        sep_split_in H4; sep_split; eauto; simpl in *.
        Lemma eq_tup_app' es1 es2 es1' es2' stk :
          (es1 ==t es1') stk (emp_ph loc) ->
          (es2 ==t es2') stk (emp_ph loc) ->
          (es1 ++ es2 ==t es1' ++ es2') stk (emp_ph loc).
        Proof.
          revert es2 es1' es2'; induction es1; introv Heq1 Heq2.
          - destruct es1'; simpl in *; eauto; destruct Heq1.
          - destruct es1'; simpl in *; [destruct Heq1|].
            sep_split_in Heq1.
            forwards*: IHes1.
            sep_split; eauto.
        Qed.
        apply eq_tup_app'; eauto.
    - unfoldM'.
      destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n''] eqn:Hceq2; [|inversion Hcompile].
      destruct (compile_sexp _ se3 _ _) as [[(cs3 & es3) | ?] n'''] eqn:Hceq3; [|inversion Hcompile].
      destruct (freshes _ _) as [[fvs1 | ?] n''''] eqn:Hfeq1; [|inversion Hcompile].
      destruct es1 as [| e [| ? ?]]; inverts Hcompile.
      inverts Htyp as Htyp1 Htyp2 Htyp3.
      splits.
      { intros; simplify.
        forwards* (? & ? & ?): (>>freshes_vars Hfeq1).
        apply var_pnat_inj in H0 as (? & ?); substs.
        forwards*: (>>freshes_incr); omega. }
      assert (n <= n' /\ n' <= n'' /\ n'' <= n''' /\ n''' + 1 = m).
      { splits; [forwards*: (>>compile_don't_decrease Hceq1) |
                 forwards*: (>>compile_don't_decrease Hceq2) |
                 forwards*: (>>compile_don't_decrease Hceq3) |
                 forwards*: (>>freshes_incr Hfeq1) ]. }
      inverts Heval as Heval1 Heval2.
      + forwards* (Hres1 & Htri1): IHse1.
        { intros; forwards*: Hsvar; autorewrite with setop; eauto. }
        { intros; forwards*: Havar1; autorewrite with setop; eauto. }
        { intros; forwards*: Havar2; autorewrite with setop; eauto. }
        forwards* (Hres2 & Htri2): IHse2.
        { intros; forwards*: Hsvar; autorewrite with setop; eauto; omega. }
        { intros; forwards*: Havar1; autorewrite with setop; eauto. }
        { intros; forwards*: Havar2; autorewrite with setop; eauto. }
        
        eapply Hbackward.
        Focus 2. {
          intros s h Hsat.
          unfold assn_of_svs, assn_of_avs in Hsat.
          sep_rewrite_in SE.union_assns Hsat.
          sep_rewrite_in SA.union_assns Hsat.
          sep_rewrite_in pure_star Hsat.
          rewrite !fold_assn_avs, !fold_assn_svs in Hsat.
          instantiate (1 := (
             (!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) **
             !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se2) (free_sv se3)) (free_sv se1))) **
             assn_of_avs (SA.SE.diff (SA.union (free_av se2) (free_av se3)) (free_av se1)))).
          sep_normal; sep_normal_in Hsat; repeat sep_cancel. } Unfocus.
        eapply rule_seq; [eapply rule_frame; eauto|].
        { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify];
          introv; autorewrite with setop; intros ? ? ?; des.
          - destruct H1;
              forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
                forwards*: Hsvar; autorewrite with setop; eauto; omega.
          - destruct H1;
              forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
                forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence.
          - destruct H1; forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; forwards*: Havar2;
              autorewrite with setop in *; eauto.
            rewrite <- H7 in *; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence.
            substs; rewrite <- H7 in *; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence. }
        eapply Hforward; [eapply rule_if_disj|]; simpl in *.
        eapply Hbackward.
        Focus 2. {
          intros s h Hsat.
          assert ((!(assn_of_svs seval_env svar_env (SE.union (free_sv se1) (SE.union (free_sv se2) (free_sv se3)))) **
                    assn_of_avs (SA.union (free_av se1) (SA.union (free_av se2) (free_av se3)))) s h).
          { unfold assn_of_svs, assn_of_avs in *.
            sep_rewrite SE.union_assns; sep_rewrite pure_star.
            sep_rewrite SA.union_assns.
            sep_normal_in Hsat; sep_normal; sep_split_in Hsat; sep_split; repeat sep_cancel. }
          Lemma se_union_assoc s1 s2 s3 :
            SE.union (SE.union s1 s2) s3 == SE.union s1 (SE.union s2 s3).
          Proof.
            simpl; unfold SE.Equal; introv; autorewrite with setop.
            split; intros; eauto.
            destruct H as [[? | ?] | ?]; eauto.
            destruct H as [? | [? | ?]]; eauto.
          Qed.
          Lemma sa_union_assoc s1 s2 s3 :
            SA.union (SA.union s1 s2) s3 == SA.union s1 (SA.union s2 s3).
          Proof.
            simpl; unfold SA.Equal; introv; autorewrite with setop.
            split; intros; eauto.
            destruct H as [[? | ?] | ?]; eauto.
            destruct H as [? | [? | ?]]; eauto.
          Qed.
          sep_rewrite_in (SE.union_comm (free_sv se1)) H0.
          sep_rewrite_in se_union_assoc H0.
          sep_rewrite_in (SA.union_comm (free_av se1)) H0.
          sep_rewrite_in sa_union_assoc H0.
          unfold assn_of_svs, assn_of_avs in H0.
          sep_rewrite_in SE.union_assns H0; sep_rewrite_in pure_star H0.
          sep_rewrite_in SA.union_assns H0.
          rewrite !fold_assn_svs, !fold_assn_avs in H0.
          instantiate (1 :=
            ((!(assn_of_svs seval_env svar_env (free_sv se2)) ** assn_of_avs (free_av se2)) **
            !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se3) (free_sv se1)) (free_sv se2))) **
            assn_of_avs (SA.SE.diff (SA.union (free_av se3) (free_av se1)) (free_av se2)))).
          sep_normal; sep_normal_in H0; repeat sep_cancel. } Unfocus.
        eapply rule_seq; [eapply rule_frame; eauto|].
        { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify];
          introv; autorewrite with setop; try intros ? [? ?]; try split; try intros ?.
          - destruct H1;
              forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
                forwards*: Hsvar; autorewrite with setop; eauto; omega.
          - destruct H1;
              forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
                forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence.
          - destruct H1;
              forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
            forwards*: Havar2; autorewrite with setop; eauto.
            rewrite <-H4 in *; simpl in *; rewrite prefix_nil in *; congruence.
            rewrite <-H4 in *; simpl in *; rewrite prefix_nil in *; congruence. }
        eapply Hbackward.
        Focus 2. {
          intros s h Hsat.
          instantiate (1 :=
            !(es2 ==t vs_of_sval sv) **
            !(assn_of_svs seval_env svar_env (free_sv se2)) ** assn_of_avs (free_av se2) **
            !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se3) (free_sv se1)) (free_sv se2))) **
            assn_of_avs (SA.SE.diff (SA.union (free_av se3) (free_av se1)) (free_av se2))).
          sep_normal_in Hsat; sep_normal; repeat sep_cancel. } Unfocus.
        eapply rule_frame; [apply read_tup_correct|].
        { unfold not; intros.
          forwards* (? & ? & ?): freshes_vars; substs.
          forwards*: (Hres2); omega. }
        { forwards*: freshes_disjoint. }
        { forwards*: (>>type_preservation Htyp2).
          unfold val in * ; rewrites* (>> has_type_val_len H0).
          forwards*: (>>compiler_preserve Hceq2). }
        { forwards*: (>>freshes_len Hfeq1). }
        { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs];
          introv; autorewrite with setop; unfold not; intros; forwards*: (read_tup_writes');
          forwards* (? & ? & ?): (>>freshes_vars Hfeq1); substs.
          - forwards*: Hsvar; autorewrite with setop; eauto; omega.
          - forwards*: Havar1; autorewrite with setop; eauto.
            simpl in *; rewrite prefix_nil in *; congruence.
          - forwards*: Havar2; autorewrite with setop; eauto.
            rewrite H4 in *; simpl in *; rewrite prefix_nil in *; congruence.
          - forwards*: Hsvar; autorewrite with setop.
            destruct H1 as ([? | ?] & _); eauto.
            omega.
          - forwards*: Havar1; autorewrite with setop.
            destruct H1 as ([? | ?] & _); eauto.
            simpl in *; rewrite prefix_nil in *; congruence.
          - forwards*: Havar2; autorewrite with setop.
            destruct H1 as ([? | ?] & _); eauto.
            rewrite H4 in *; simpl in *; rewrite prefix_nil in *; congruence. }
        eapply Hbackward.
        Focus 2. {
          intros s h Hsat.
          sep_normal_in Hsat; sep_split_in Hsat.
          sep_split_in HP0.
          unfold_pures.
          instantiate (1 := FalseP).
          congruence. } Unfocus.
        instantiate (1 := FalseP).
        intros x; destruct 1.
        intros s h [Hsat | []].
        sep_rewrite (SE.union_comm (free_sv se1)).
        sep_rewrite se_union_assoc.
        sep_rewrite (SA.union_comm (free_av se1)).
        sep_rewrite sa_union_assoc.
        unfold assn_of_svs, assn_of_avs in *; sep_rewrite SE.union_assns; sep_rewrite SA.union_assns; sep_rewrite pure_star.
        sep_normal_in Hsat; sep_normal; repeat sep_cancel.
      + forwards* (Hres1 & Htri1): IHse1.
        { intros; forwards*: Hsvar; autorewrite with setop; eauto. }
        { intros; forwards*: Havar1; autorewrite with setop; eauto. }
        { intros; forwards*: Havar2; autorewrite with setop; eauto. }
        forwards* (Hres3 & Htri3): IHse3.
        { intros; forwards*: Hsvar; autorewrite with setop; eauto; omega. }
        { intros; forwards*: Havar1; autorewrite with setop; eauto. }
        { intros; forwards*: Havar2; autorewrite with setop; eauto. }
        
        eapply Hbackward.
        Focus 2. {
          intros s h Hsat.
          unfold assn_of_svs, assn_of_avs in Hsat.
          sep_rewrite_in SE.union_assns Hsat.
          sep_rewrite_in SA.union_assns Hsat.
          sep_rewrite_in pure_star Hsat.
          rewrite !fold_assn_avs, !fold_assn_svs in Hsat.
          instantiate (1 := (
             (!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) **
             !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se2) (free_sv se3)) (free_sv se1))) **
             assn_of_avs (SA.SE.diff (SA.union (free_av se2) (free_av se3)) (free_av se1)))).
          sep_normal; sep_normal_in Hsat; repeat sep_cancel. } Unfocus.
        eapply rule_seq; [eapply rule_frame; eauto|].
        { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify];
          introv; autorewrite with setop; try intros ? [? ?] ?.
          - destruct H1;
              forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
                forwards*: Hsvar; autorewrite with setop; eauto; omega.
          - destruct H1;
              forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
                forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence.
          - destruct H1; forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
            forwards*: Havar2; autorewrite with setop; eauto; simpl in *.
            rewrite <- H4 in *; simpl in *; rewrite prefix_nil in *; congruence.
            rewrite <- H4 in *; simpl in *; rewrite prefix_nil in *; congruence. }
        eapply Hforward; [eapply rule_if_disj|]; simpl in *.
        eapply Hbackward.
        Focus 2. {
          intros s h Hsat.
          sep_normal_in Hsat; sep_split_in Hsat.
          sep_split_in HP0.
          unfold_pures.
          instantiate (1 := FalseP).
          congruence. } Unfocus.
        instantiate (1 := FalseP).
        intros x; destruct 1.

        eapply Hbackward.
        Focus 2. {
          intros s h Hsat.
          assert ((!(assn_of_svs seval_env svar_env (SE.union (free_sv se1) (SE.union (free_sv se2) (free_sv se3)))) **
                    assn_of_avs (SA.union (free_av se1) (SA.union (free_av se2) (free_av se3)))) s h).
          { unfold assn_of_svs, assn_of_avs in *.
            sep_rewrite SE.union_assns; sep_rewrite pure_star.
            sep_rewrite SA.union_assns.
            sep_normal_in Hsat; sep_normal; sep_split_in Hsat; sep_split; repeat sep_cancel. }
          sep_rewrite_in (SE.union_comm (free_sv se2)) H0.
          sep_rewrite_in (SE.union_comm (free_sv se1)) H0.
          sep_rewrite_in se_union_assoc H0.
          sep_rewrite_in (SA.union_comm (free_av se2)) H0.
          sep_rewrite_in (SA.union_comm (free_av se1)) H0.
          sep_rewrite_in sa_union_assoc H0.
          unfold assn_of_svs, assn_of_avs in H0.
          sep_rewrite_in SE.union_assns H0; sep_rewrite_in pure_star H0.
          sep_rewrite_in SA.union_assns H0.
          rewrite !fold_assn_svs, !fold_assn_avs in H0.
          instantiate (1 :=
            ((!(assn_of_svs seval_env svar_env (free_sv se3)) ** assn_of_avs (free_av se3)) **
            !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se2) (free_sv se1)) (free_sv se3))) **
            assn_of_avs (SA.SE.diff (SA.union (free_av se2) (free_av se1)) (free_av se3)))).
          sep_normal; sep_normal_in H0; repeat sep_cancel. } Unfocus.
        eapply rule_seq; [eapply rule_frame; eauto|].
        { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify];
          introv; autorewrite with setop; try intros ? [? ?] ?.
          - destruct H1;
              forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
                forwards*: Hsvar; autorewrite with setop; eauto; omega.
          - destruct H1;
              forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
                forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence.
          - substs; destruct H1; forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs;
              forwards*: Havar2; autorewrite with setop; eauto.
            rewrite <-H3 in *; simpl in *; rewrite prefix_nil in *; congruence.
            rewrite <-H3 in *; simpl in *; rewrite prefix_nil in *; congruence. }
        eapply Hbackward.
        Focus 2. {
          intros s h Hsat.
          instantiate (1 :=
            !(es3 ==t vs_of_sval sv) **
            !(assn_of_svs seval_env svar_env (free_sv se3)) ** assn_of_avs (free_av se3) **
            !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se2) (free_sv se1)) (free_sv se3))) **
            assn_of_avs (SA.SE.diff (SA.union (free_av se2) (free_av se1)) (free_av se3))).
          sep_normal_in Hsat; sep_normal; repeat sep_cancel. } Unfocus.
        eapply rule_frame; [apply read_tup_correct|].
        { unfold not; intros.
          forwards* (? & ? & ?): freshes_vars; substs.
          forwards*: (Hres3); omega. }
        { forwards*: freshes_disjoint. }
        { forwards*: (>>type_preservation Htyp3).
          unfold val in * ; rewrites* (>> has_type_val_len H0).
          forwards*: (>>compiler_preserve Hceq3). }
        { forwards*: (>>freshes_len Hfeq1).
          forwards*: (>>compiler_preserve Hceq3).
          forwards*: (>>compiler_preserve Hceq2).
          congruence. }
        { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs];
          introv; autorewrite with setop; unfold not; intros; forwards*: (read_tup_writes');
          forwards* (? & ? & ?): (>>freshes_vars Hfeq1); substs.
          - forwards*: Hsvar; autorewrite with setop; eauto; omega.
          - forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence.
          - forwards*: Havar2; autorewrite with setop; eauto; simpl in *.
            rewrite H4 in *; simpl in *; rewrite prefix_nil in *; congruence.
          - forwards*: Hsvar; autorewrite with setop.
            destruct H1 as ([? | ?] & _); eauto.
            omega.
          - forwards*: Havar1; autorewrite with setop.
            destruct H1 as ([? | ?] & _); eauto.
            simpl in *; rewrite prefix_nil in *; congruence.
          - forwards*: Havar2; autorewrite with setop; eauto; simpl in *.
            destruct H1 as ([? | ?] & _); eauto.
            rewrite H4 in *; simpl in *; rewrite prefix_nil in *; congruence. }
        intros s h [[] | Hsat].
        sep_rewrite (SE.union_comm (free_sv se2)).
        sep_rewrite (SE.union_comm (free_sv se1)).
        sep_rewrite se_union_assoc.
        sep_rewrite (SA.union_comm (free_av se2)).
        sep_rewrite (SA.union_comm (free_av se1)).
        sep_rewrite sa_union_assoc.
        unfold assn_of_svs, assn_of_avs in *; sep_rewrite SE.union_assns; sep_rewrite SA.union_assns; sep_rewrite pure_star.
        sep_normal_in Hsat; sep_normal; repeat sep_cancel.
  Qed.
End CorrectnessProof.