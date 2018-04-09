Require Import Monad SkelLib Computation ZArith TypedTerm Program DepList.
Require Import CUDALib Correctness.
Require Import Compiler Ext Extract Host CompilerProof LibTactics.
Open Scope Z_scope.

Notation AVFusedEnv0 GA1 GA2 := (hlist (fun typ => sum (member typ GA2) (Skel.Func GA2 (Skel.Fun1 Skel.TZ typ) * Skel.LExp GA2 Skel.TZ)) GA1).
Notation AVFusedEnv GA := (AVFusedEnv0 GA GA).

Axiom sorry : forall {T : Type}, T.

Import Skel.

Fixpoint insertAt {T} (t : T) (G : list T) (n : nat) {struct n} : list T :=
  match n with
  | O => t :: G
  | S n' => match G with
            | nil => t :: G
            | t' :: G' => t' :: insertAt t G' n'
            end
  end.

Fixpoint liftVar {A} {t : A} {G} (x : member t G) t' n : member t (insertAt t' G n) :=
  match x with
    | HFirst => match n return member t (insertAt t' (t :: _) n) with
                     | O => HNext HFirst
                     | _ => HFirst
                   end
    | @HNext _ _ t'' G' x' => match n return member t (insertAt t' (t'' :: G') n) with
                           | O => HNext (HNext x')
                           | S n' => HNext (liftVar x' t' n')
                         end
  end.

Fixpoint liftVar_many {A} {t : A} {G} (x : member t G) G' : member t (G ++ G') :=
  match x with
  | HFirst => HFirst
  | @HNext _ _ t'' G' x' => HNext (liftVar_many x' _)
  end.

Fixpoint insertAtS {A ls f} (t : A) (x : f t) (n : nat) {struct n}
  : hlist f ls -> hlist f (insertAt t ls n) :=
  match n with
    | O => fun s => x ::: s
    | S n' => match ls return hlist f ls
                             -> hlist f (insertAt t ls (S n')) with
                | nil => fun s => x ::: s
                | t' :: G' => fun s => hhd s ::: insertAtS t x n' (htl s)
              end
  end.

Fixpoint lift_sexp {GA GS} {resTy} ty (se : SExp GA GS resTy) n : SExp GA (insertAt ty GS n) resTy :=
  match se with
  | ENum n => ENum n
  | EVar _ _ _ m => EVar _ _ _ (liftVar m ty n)
  | EBin _ _ _ _ _ op e1 e2 => EBin _ _ _ _ _ op (lift_sexp ty e1 n) (lift_sexp ty e2 n)
  | EA _ _ _ m se => EA _ _ _ m (lift_sexp ty se n)
  | ELen _ _ _ m => ELen _ _ _ m
  | EIf _ _ _ e1 e2 e3 => EIf _ _ _ (lift_sexp ty e1 n) (lift_sexp ty e2 n) (lift_sexp ty e3 n)
  | ECons _ _ _ _ e1 e2 => ECons _ _ _ _ (lift_sexp ty e1 n) (lift_sexp ty e2 n)
  | EPrj1 _ _ _ _ e => EPrj1 _ _ _ _ (lift_sexp ty e n)
  | EPrj2 _ _ _ _ e => EPrj2 _ _ _ _ (lift_sexp ty e n)
  | ELet _ _ _ _ e1 e2 => ELet _ _ _ _ (lift_sexp ty e1 n) (lift_sexp ty e2 (S n))
  end.

Fixpoint lift_many_sexp {GA GS} {resTy} (se : SExp GA GS resTy) GS' : SExp GA (GS ++ GS') resTy :=
  match se with
  | ENum n => ENum n
  | EVar _ _ _ m => EVar _ _ _ (liftVar_many m GS')
  | EBin _ _ _ _ _ op e1 e2 => EBin _ _ _ _ _ op (lift_many_sexp e1 GS') (lift_many_sexp e2 GS')
  | EA _ _ _ m se => EA _ _ _ m (lift_many_sexp se GS')
  | ELen _ _ _ m => ELen _ _ _ m
  | EIf _ _ _ e1 e2 e3 => EIf _ _ _ (lift_many_sexp e1 GS') (lift_many_sexp e2 GS') (lift_many_sexp e3 GS')
  | ECons _ _ _ _ e1 e2 => ECons _ _ _ _ (lift_many_sexp e1 GS') (lift_many_sexp e2 GS')
  | EPrj1 _ _ _ _ e => EPrj1 _ _ _ _ (lift_many_sexp e GS')
  | EPrj2 _ _ _ _ e => EPrj2 _ _ _ _ (lift_many_sexp e GS')
  | ELet _ _ _ _ e1 e2 => ELet _ _ _ _ (lift_many_sexp e1 GS') (lift_many_sexp e2 GS')
  end.

Lemma insertAtS_liftVar A ls f (hls : hlist f ls) (t : A)(m : member t ls) v (x : f v) :
  forall n,
    hget (insertAtS v x n hls) (liftVar m v n) =
    hget hls m.
Proof.
  dependent induction hls; dependent destruction m; simpl.
  destruct n; eauto.
  destruct n; eauto.
  simpl; eauto.
Qed.

Lemma lift_sexp_ok GA GS resTy (se : SExp GA GS resTy) :
  forall aeenv seenv ty v n, 
    sexpDenote (lift_sexp ty se n) aeenv (insertAtS ty v n seenv) = sexpDenote se aeenv seenv.
Proof.
  induction se; simpl; intros;
    unfold ret, bind; simpl; unfold bind_opt;
      (try rewrites* IHse); (try rewrites* IHse1); (try rewrites* IHse2);
        (try rewrites* IHse3); jauto.
  2:destruct sexpDenote; jauto.
  2:forwards*: (>>IHse2 aeenv (t ::: seenv) ty v (S n)).
  rewrites* insertAtS_liftVar.
Qed.  

Lemma liftVar_many_ok A (ls : list A) f (hls : hlist f ls) t (m : member t ls) :
  forall ls' hls',
    hget hls m = hget (hls +++ hls') (liftVar_many m ls').
Proof.
  dependent induction hls; dependent destruction m; simpl; eauto.
Qed.
    
Lemma lift_many_sexp_ok GA GS resTy (se : SExp GA GS resTy) :
  forall aeenv GS' seenv seenv', 
    sexpDenote (lift_many_sexp se GS') aeenv (seenv +++ seenv') = sexpDenote se aeenv seenv.
Proof.
  induction se; simpl; intros;
    unfold ret, bind; simpl; unfold bind_opt;
      (try rewrites* IHse); (try rewrites* IHse1); (try rewrites* IHse2);
        (try rewrites* IHse3); jauto.
  rewrites* <-(>>liftVar_many_ok).
  destruct sexpDenote; jauto.
  forwards*: (>>IHse2 (t ::: seenv)).
Qed.  

Fixpoint shift_lexp_GA {GA resTy} ty (le : LExp GA resTy) : LExp (ty :: GA) resTy :=
  match le in LExp _ resTy  return LExp (ty :: GA) resTy with
  | LNum _ n => LNum _ n
  | LMin _ le1 le2 => LMin _ (shift_lexp_GA _ le1) (shift_lexp_GA _ le2)
  | LLen _ t m => LLen _ t (HNext m)
  end.

Lemma shift_lexp_GA_ok GA resTy ty (le : LExp GA resTy) :
  forall arr aeenv,
    lexpDenote _ _ (shift_lexp_GA ty le) (arr ::: aeenv) =
    lexpDenote _ _ le aeenv.
Proof.
  dependent induction le; simpl; introv; eauto.
  rewrites* IHle1; rewrites* IHle2.
Qed.

Definition shift_fused_env {GA GA' typ} (avfenv : AVFusedEnv0 GA GA') : AVFusedEnv0 GA (typ :: GA') :=
  hmap (fun typ' darr =>
    match darr with
    | inl m => inl (liftVar m typ 0)
    | inr (f, lexp) => inr (shift_func_GA typ f, shift_lexp_GA typ lexp)
    end) avfenv.

Definition body_of_func1 {GA ty1 ty2} (f : Func GA (Fun1 ty1 ty2)) : SExp GA [ty1] ty2 :=
  match f in Func _ fty return (match fty with
                                | Fun1 ty1 ty2 => SExp _ [ty1] ty2
                                | Fun2 _ _ _ =>  unit end) with
  | F1 _ _ _ body => body
  | _ => tt
  end.


Definition fuse_f1 {GA ty1 ty2 ty3}
  (f : Func GA (Fun1 ty1 ty2)) (g : Func GA (Fun1 ty2 ty3)) : Func GA (Fun1 ty1 ty3) :=
     let body_f := body_of_func1 f in
     let body_g := lift_sexp ty1 (body_of_func1 g) 1 in
     F1 GA ty1 ty3
        (ELet _ _ _ _ body_f body_g).

Definition darr_of_skelapp {GA resTy}  (skel : SkelE GA resTy) :
  option (Func GA (Fun1 TZ resTy) * LExp GA TZ) :=
  match skel with
  | Reduce _ _ _ _ => None
  | Map _ _ _ f arr =>
    let (g, le) := darr_of_arr arr in
    let f := fuse_f1 (F1 _ _ _ g) f in
    Some (f, le)
  | Seq _ n l =>
    let f := F1 _ TZ TZ (EBin _ _ _ _ _ Eplus (lexp2sexp _ _ n _) (EVar _ _ _ HFirst)) in
    Some (f, l)
  | Zip _ _ _ a1 a2 =>
    let (body1, len1) := darr_of_arr a1 in
    let (body2, len2) := darr_of_arr a2 in
    Some (Skel.F1 _ _ _ (Skel.ECons _ _ _ _ body1 body2), Skel.LMin _ len1 len2)
  end.

Fixpoint fuse_se {GA GA' GS resTy} (se : SExp GA GS resTy) : AVFusedEnv0 GA GA' -> SExp GA' GS resTy :=
  match se with
  | ENum n => fun avfenv => ENum n
  | EVar _ _ _ m => fun avfenv =>  EVar _ _ _ m
  | EBin _ _ _ _ _ op e1 e2 =>
    fun avfenv => EBin _ _ _ _ _ op (fuse_se e1 avfenv) (fuse_se e2 avfenv)
  | EA _ _ _ m se =>
    fun avfenv =>
      let se := fuse_se se avfenv in
      match hget avfenv m with
      | inl m => EA _ _ _ m se
      | inr (f, len) =>
        let body := body_of_func1 f in
        ELet _ _ _ _ se (lift_many_sexp body _)
      end
  | ELen _ _ _ m =>
    fun avfenv =>
      match hget avfenv m with
      | inl m => ELen _ _ _ m
      | inr (f, len) => lexp2sexp _ _ len _
      end
  | EIf _ _ _ e1 e2 e3 =>
    fun avfenv =>
      EIf _ _ _ (fuse_se e1 avfenv) (fuse_se e2 avfenv) (fuse_se e3 avfenv)
  | ECons _ _ _ _ e1 e2 =>
    fun avfenv =>
      ECons _ _ _ _ (fuse_se e1 avfenv) (fuse_se e2 avfenv) 
  | EPrj1 _ _ _ _ e =>
    fun avfenv => EPrj1 _ _ _ _ (fuse_se e avfenv)
  | EPrj2 _ _ _ _ e =>
    fun avfenv => EPrj2 _ _ _ _ (fuse_se e avfenv)
  | ELet _ _ _ _ e1 e2 =>
    fun avfenv => ELet _ _ _ _ (fuse_se e1 avfenv) (fuse_se e2 avfenv) 
  end.

Definition fuse_func {GA GA' fty} (func : Func GA fty) : AVFusedEnv0 GA GA' -> Func GA' fty :=
  match func with
  | F1 _ _ _ se => fun avfenv => F1 _ _ _ (fuse_se se avfenv)
  | F2 _ _ _ _ se => fun avfenv => F2 _ _ _ _ (fuse_se se avfenv)
  end.

Fixpoint fuse_le {GA GA' resTy} (le : LExp GA resTy) : AVFusedEnv0 GA GA' -> LExp GA' resTy :=
  match le with
  | LNum _ n => fun _ => LNum _ n
  | LLen _ _ m =>
    fun avfenv =>
      match hget avfenv m with
      | inl m => LLen _ _ m
      | inr (f, l) => l
      end
  | LMin _ l1 l2 =>
    fun avfenv =>
      LMin _ (fuse_le l1 avfenv) (fuse_le l2 avfenv)
  end.

Definition fuse_ae {GA GA' resTy} (ae : AE GA resTy) : AVFusedEnv0 GA GA' -> AE GA' resTy :=
  match ae with
  | VArr _ _ m =>
    fun avfenv =>
      match hget avfenv m with
      | inl m => VArr _ _ m
      | inr (f, len) => DArr _ _ f len
      end
  | DArr _ _ f l =>
    fun avfenv => DArr _ _ (fuse_func f avfenv) (fuse_le l avfenv)
  end.

Definition fuse_skel {GA GA' resTy} (skel : SkelE GA resTy) : AVFusedEnv0 GA GA' -> SkelE GA' resTy :=
  match skel with
  | Reduce _ _ f ae => fun avfenv => Reduce _ _ (fuse_func f avfenv) (fuse_ae ae avfenv)
  | Map _ _ _ f ae => fun avfenv => Map _ _ _ (fuse_func f avfenv) (fuse_ae ae avfenv)
  | Seq _ n l => fun avfenv => Seq _ (fuse_le n avfenv) (fuse_le l avfenv)
  | Zip _ _ _ ae1 ae2 => fun avfenv => Zip _ _ _ (fuse_ae ae1 avfenv) (fuse_ae ae2 avfenv)
  end.

Fixpoint simple_fusion {GA GA' typ} (p : AS GA typ) : AVFusedEnv0 GA GA' -> AS GA' typ :=
  match p with
  | ALet _ tyapp tyres skel res =>
    fun avfenv =>
      let skel := fuse_skel skel avfenv in
      if true then
        match darr_of_skelapp skel with
        | Some darr => simple_fusion res (inr darr ::: avfenv)
        | None => ALet _ _ _ skel (simple_fusion res (inl HFirst ::: shift_fused_env avfenv))
        end
      else
        ALet _ _ _ skel (simple_fusion res (inl HFirst ::: shift_fused_env avfenv))
  | ARet _ t x =>
    fun avfenv =>
      match hget avfenv x with
      | inl m => ARet _ _ m
      | inr (f, l) =>
        ALet _ _ _ (Map _ _ _ (F1 _ _ _ (EVar _ _ _ HFirst)) (DArr _ _ f l))
             (ARet _ _ HFirst)
      end
  end.

Lemma fuse_le_correct GA GA' typ (le : LExp GA typ) :
  forall (avfenv : AVFusedEnv0 GA GA') (aeenv : AEvalEnv GA) (aeenv' : AEvalEnv GA'),
    (forall ty (m : member ty GA) m',
        hget avfenv m = inl m' -> hget aeenv' m' = hget aeenv m)
    -> (forall ty (m : member ty GA) f le,
           hget avfenv m = inr (f, le) ->
           aeDenote _ _ (DArr _ _ f le) aeenv' = ret (hget aeenv m))
    -> lexpDenote _ _ (fuse_le le avfenv) aeenv' = lexpDenote _ _ le aeenv.
Proof.
  induction le; introv Henv1 Henv2; simpl; eauto.
  - destruct (hget avfenv m) as [|[? ?]]eqn:Heq;
      [forwards*: Henv1; simpl; congruence|].
    forwards*: Henv2; simpl in *.
    destruct Z_le_dec; [|inverts H].
    rewrites* (>>mapM_length H); rewrite seq_length, Z2Nat.id; eauto.
  - rewrites* (>>IHle1 Henv1 Henv2).
    rewrites* (>>IHle2 Henv1 Henv2).
Qed.

Lemma fuse_sexp_correct GA GA' GS typ (se : SExp GA GS typ) :
  forall (avfenv : AVFusedEnv0 GA GA') (seenv : SEvalEnv GS) (aeenv : AEvalEnv GA) (aeenv' : AEvalEnv GA'),
    (forall ty (m : member ty GA) m',
        hget avfenv m = inl m' -> hget aeenv' m' = hget aeenv m)
    -> (forall ty (m : member ty GA) f le,
           hget avfenv m = inr (f, le) ->
           aeDenote _ _ (DArr _ _ f le) aeenv' = ret (hget aeenv m))
    -> forall res, sexpDenote se aeenv seenv = Some res
    -> sexpDenote (fuse_se se avfenv) aeenv' seenv = Some res.
Proof.
  induction se; introv Henv1 Henv2; simpl in *; eauto.
  all: unfold ret, bind; simpl; unfold bind_opt; introv Heq;
    (repeat let Hfv := fresh in
           match type of Heq with
           | context [match sexpDenote ?se ?aeenv ?seenv with Some _ => _ | None => _ end] => destruct (sexpDenote se aeenv seenv) as [?|] eqn:Hfv; [|inverts Hfv; try congruence] end); inverts Heq;
    try now(try rewrites* (>>IHse seenv Henv1 Henv2);
            try rewrites* (>>IHse1 seenv Henv1 Henv2);
            try rewrites* (>>IHse2 seenv Henv1 Henv2);
            try rewrites* (>>IHse3 seenv Henv1 Henv2)).
  - destruct (hget avfenv m) as [|[f l]] eqn:Henv;
    simpl; unfold bind, ret; simpl; unfold bind_opt.
    + rewrites* (>>IHse); rewrites* (>>Henv1).
    + rewrites* (>>IHse); destruct sexpDenote; [|congruence].
      forwards*: (>>Henv2).
      dependent destruction f; simpl in *.
      rewrites* (>>lift_many_sexp_ok ((t0 : typDenote TZ) ::: HNil) seenv).
      destruct Z_le_dec; [|unfold ret in *; simpl in *; congruence].
      forwards*HeqLen: (>>mapM_length).
      forwards*Hval: (>>mapM_some (Z.to_nat t0) (0 : typDenote TZ) (@defval' t) H0).
      rewrite seq_length in *.
      rewrite <-HeqLen in Hval.
      forwards*(? & ? & ?): (>>SeqCompiler.nth_error_lt_nat); substs.
      rewrites Nat2Z.id in *; destruct lt_dec; try omega.
      rewrite seq_nth in Hval; rewrite <-HeqLen in Hval; destruct lt_dec; try omega.
      rewrite Z.add_0_l in Hval; rewrite <-Hval.
      rewrites (>>nth_error_some' (@defval' t)); try omega.
      rewrite Nat2Z.id; eauto.
  - destruct (hget avfenv m) as [|[f l]] eqn:Henv;
    simpl; unfold bind, ret; simpl; unfold bind_opt.
    + rewrites* (>>Henv1).
    + forwards*: (>>Henv2).
      rewrite lexp2sexp_ok.
      destruct Z_le_dec; [|unfold ret in *; inverts H].
      forwards*Hlen: mapM_length.
      rewrite seq_length in Hlen; rewrite Hlen, Z2Nat.id; eauto.
  - rewrites* (>>IHse1 seenv Henv1 Henv2 H).
    destruct t0; [rewrites* (>>IHse2 seenv Henv1 Henv2 H1)|rewrites* (>>IHse3 seenv Henv1 Henv2 H1)].
  - rewrites* (>>IHse1 seenv Henv1 Henv2 H).
    rewrites* (>>IHse2 (t ::: seenv) Henv1 Henv2 H1).
Qed.

Lemma mapM_eq A B (f g : A -> option B) ls :
  (forall x, List.In x ls -> f x = g x)
  -> mapM f ls = mapM g ls.
Proof.
  induction ls; simpl; eauto.
  intros.
  unfold mapM in *; simpl; unfold ret, bind; simpl; unfold bind_opt.
  rewrite H; eauto.
  destruct g; eauto.
  rewrite IHls; eauto.
Qed.

Lemma fuse_ae_correct GA GA' typ (ae : AE GA typ) :
  forall (avfenv : AVFusedEnv0 GA GA') (aeenv : AEvalEnv GA) (aeenv' : AEvalEnv GA'),
    (forall ty (m : member ty GA) m',
        hget avfenv m = inl m' -> hget aeenv' m' = hget aeenv m)
    -> (forall ty (m : member ty GA) f le,
           hget avfenv m = inr (f, le) -> aeDenote _ _ (DArr _ _ f le) aeenv' = ret (hget aeenv m))
    -> forall res,
        aeDenote _ _ ae aeenv = Some res
        -> aeDenote _ _ (fuse_ae ae avfenv) aeenv' = Some res.
Proof.
  destruct ae; simpl; introv Henv1 Henv2 Hres; eauto.
  - destruct (hget avfenv m) as [m' | [f le] ] eqn:Heq; simpl in *.
    + forwards*: (>>Henv1); congruence.
    + forwards*: (>>Henv2); congruence.
  - rewrites* (>>fuse_le_correct).
    destruct Z_le_dec; eauto.
    dependent destruction f; simpl in *.
    rewrite <- Hres.
    apply mapM_eq; intros i H.
    unfold seq in H; apply seq'_In in H.
    forwards*: (>>mapM_some (Z.to_nat i) i (@defval' cod) Hres).
    rewrite seq_length, Z2Nat.id in *; try omega.
    destruct lt_dec; try omega.
    2: rewrite <-Z2Nat.inj_lt in *; try omega.
    rewrite seq_nth in H0; destruct lt_dec; try omega.
    rewrite Z.add_0_l, Z2Nat.id in *; try omega.
    rewrites* (>>fuse_sexp_correct).
Qed.

Lemma shift_sexp_GA_ok GA GS resTy ty (se : SExp GA GS resTy) :
  forall aeenv seenv arr,
    sexpDenote (shift_sexp_GA ty se) (arr ::: aeenv) seenv =
    sexpDenote se aeenv seenv.
Proof.
  introv; induction se; simpl; eauto;
    try (now (rewrite IHse1; f_equal; extensionality l; rewrite IHse2; eauto));
    try (now (rewrite IHse; f_equal; eauto)).
  unfold bind, ret; simpl; unfold Monad.bind_opt.
  rewrite IHse1.
  destruct (Skel.sexpDenote se1 _ _); eauto.
  destruct t0; eauto.
Qed.    

Lemma mapM_some_in A B ls :forall ls' (f : A -> option B) x,
  mapM f ls = Some ls'
  -> List.In x ls
  -> exists y, f x = Some y.
Proof.
  induction ls; simpl; try tauto.
  unfold mapM in *; simpl; unfold ret, bind; simpl; unfold bind_opt.
  introv H HeqHin; substs.
  destruct (f a) eqn:Heq; [|inverts H].
  destruct HeqHin; substs.
  - exists b; eauto.
  - destruct sequence eqn:Heq'; inverts H.
    forwards*: IHls.
Qed.

Lemma fuse_skel_correct GA GA' resTyp (skel : SkelE GA resTyp) :
  forall (avfenv : AVFusedEnv0 GA GA') (aeenv : AEvalEnv GA) (aeenv' : AEvalEnv GA'),
    (forall ty (m : member ty GA) m',
        hget avfenv m = inl m' -> hget aeenv' m' = hget aeenv m)
    -> (forall ty (m : member ty GA) f le,
           hget avfenv m = inr (f, le) ->
           aeDenote _ _ (DArr _ _ f le) aeenv' = ret (hget aeenv m))
    -> skelE_wf _ _ skel
    -> forall res,
        skelDenote _ _ skel aeenv = Some res
        -> skelDenote _ _ (fuse_skel skel avfenv) aeenv' = Some res.
Proof.
  dependent destruction skel; simpl; eauto; introv Henv1 Henv2 Hwf;
    unfold ret, bind; simpl; unfold bind_opt;
  intros res Hres.
  - dependent destruction f; simpl.
    destruct aeDenote eqn:heq; inversion Hres.
    rewrites* (>>fuse_ae_correct).
    apply mapM_eq; intros i Hin.
    forwards*(? & ?): mapM_some_in.
    rewrites* (>>fuse_sexp_correct).
  - destruct aeDenote eqn:heq; inversion Hres.
    rewrites* (>>fuse_ae_correct).
    f_equal.
    inverts Hwf; substs.
    dependent destruction f; simpl in *.
    extensionality x; extensionality y.
    rewrites* (>>fuse_sexp_correct).
  - repeat rewrites* (>>fuse_le_correct).
  - destruct aeDenote eqn:heq; [|inversion Hres].
    destruct (aeDenote GA t2) eqn:heq'; inverts Hres.
    repeat rewrites* (>>fuse_ae_correct).
Qed.  

Lemma darr_of_skelapp_ok GA resTy (skel : SkelE GA resTy) :
  forall f le,
    darr_of_skelapp skel = Some (f, le)
    -> forall aeenv res,
      skelDenote _ _ skel aeenv = Some res
      -> aeDenote _ _ (DArr _ _ f le) aeenv = Some res.
Proof.
  dependent destruction skel; simpl; introv Hsome; introv; try congruence.
  - intros <-.
    destruct darr_of_arr as [g le'] eqn:Heq; inverts Hsome.
    forwards*Heq': darr_of_arr_ok; rewrites Heq'; simpl.
    destruct Z_le_dec; eauto.
    unfold bind, ret; simpl; unfold bind_opt.
    clear.
    generalize (seq 0 (lexpDenote GA TZ le aeenv)); intros l; simpl in *.
    induction l; simpl; eauto.
    unfold mapM in *; simpl in *.
    unfold bind, ret; simpl; unfold bind_opt.
    destruct (sexpDenote g); simpl; eauto.
    rewrite IHl.
    destruct (sequence (List.map (fun i : Z => sexpDenote g aeenv ((i : typDenote TZ) ::: HNil)) l)).
    2: destruct sexpDenote; eauto.
    simpl; unfold bind, ret; simpl; unfold bind_opt.
    destruct (sequence (List.map (funcDenote GA (Fun1 dom cod) f aeenv) l0)).
    2: repeat destruct sexpDenote, funcDenote; eauto.
    dependent destruction f; simpl.
    forwards*Heq: (>>lift_sexp_ok s (t ::: HNil) 1%nat); simpl in *; rewrite Heq; eauto.
  - inverts Hsome; simpl.
    destruct Z_le_dec; eauto.
    unfold seq, mapM, bind, ret; simpl; unfold bind_opt.
    assert (forall n,
        sequence
          (List.map
             (fun i : Z =>
                match sexpDenote (lexp2sexp GA TZ l [TZ]) aeenv ((i : typDenote TZ) ::: HNil) with
                | Some a => Some (a + i)
                | None => None
                end) (seq' n (Z.to_nat (lexpDenote GA TZ le aeenv)))) =
        Some (seq' (lexpDenote GA TZ l aeenv + n) (Z.to_nat (lexpDenote GA TZ le aeenv)))).
    { induction Z.to_nat; introv; simpl; eauto.
      unfold bind, ret; simpl; unfold bind_opt; simpl.
      rewrite lexp2sexp_ok; simpl.
      rewrite IHn.
      do 3 f_equal.
      omega. }
    rewrite H; rewrites* Z.add_0_r.
  - destruct (darr_of_arr a0) as [body1 len1] eqn:Heq1.
    destruct (darr_of_arr a) as [body2 len2] eqn:Heq2.
    inverts Hsome; simpl in *.
    rewrites* (>>darr_of_arr_ok body1).
    rewrites* (>>darr_of_arr_ok body2).
    simpl.
    Require Import Psatz.
    repeat destruct Z_le_dec;
      [|rewrite Z.min_glb_iff in *; try lia;
        unfold bind, ret; simpl; unfold bind_opt; eauto;
        destruct mapM; eauto..].
    intros Heq.
    destruct (mapM _ (SkelLib.seq _ _)) eqn:Hmap1; [|unfold bind in Heq; simpl in *; congruence].
    destruct (mapM _ (SkelLib.seq 0 (Skel.lexpDenote GA Skel.TZ len1 aeenv))) eqn:Hmap2;
      unfold bind in Heq; simpl in *; [|congruence].
    inverts Heq.
    destruct (mapM _ (SkelLib.seq _ (Z.min _ _))) eqn:Hmap3; unfold bind, ret; simpl.
    + f_equal.
      forwards* Hlen1: (>>SkelLib.mapM_length Hmap1); rewrite SkelLib.seq_length in Hlen1.
      forwards* Hlen2: (>>SkelLib.mapM_length Hmap2); rewrite SkelLib.seq_length in Hlen2.
      forwards* Hlen3: (>>SkelLib.mapM_length Hmap3); rewrite SkelLib.seq_length in Hlen3.
      rewrite Z2Nat.inj_min in Hlen3.
      unfold SkelLib.zip.
      apply (@CSLTactics.eq_from_nth _ (@defval' (Skel.TTup t1 t2))).
      { simpl; rewrite (List.combine_length l2 l3); nia. }
      { intros.

        rewrite (nth_combine _ _ l2 l3); destruct Sumbool.sumbool_and; try nia.
        2: simpl in *; rewrite Hlen3, Nat.min_glb_lt_iff in H; omega.
        simpl.
        forwards*Hmap1': (>>SkelLib.mapM_some i (0%Z) (@defval' t1) Hmap1).
        rewrite !SkelLib.seq_length in Hmap1'; destruct lt_dec; try omega.
        rewrite SkelLib.seq_nth in Hmap1'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap1'.
        forwards*Hmap2': (>>SkelLib.mapM_some i (0%Z) (@defval' t2) Hmap2).
        rewrite !SkelLib.seq_length in Hmap2'; destruct lt_dec; try omega.
        rewrite SkelLib.seq_nth in Hmap2'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap2'.
        forwards*Hmap3': (>>SkelLib.mapM_some i (0%Z) (@defval' t1, @defval' t2) Hmap3).
        rewrite !SkelLib.seq_length in Hmap3'; destruct lt_dec; try omega.
        * rewrite SkelLib.seq_nth in Hmap3'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap3'.
          rewrite <-Hmap1' in Hmap3'; unfold bind in Hmap3'; simpl in Hmap3'.
          unfold Monad.bind_opt in Hmap3'; simpl in Hmap3.
          rewrite <-Hmap2' in Hmap3'; simpl in Hmap3'.
          inverts Hmap3'; eauto.
        * rewrite Z2Nat.inj_min, Nat.min_glb_lt_iff in *; omega. }

      + forwards*: (>>mapM_none 0%Z).
        destruct H as [i [Heq3 Hleni]].
        rewrite SkelLib.seq_length, Z2Nat.inj_min, Nat.min_glb_lt_iff in Hleni.
        forwards*Hmap1': (>>SkelLib.mapM_some i (0%Z) (@defval' t1) Hmap1).
        rewrite !SkelLib.seq_length in Hmap1'; destruct lt_dec; try omega.
        rewrite SkelLib.seq_nth in Hmap1'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap1'.
        forwards*Hmap2': (>>SkelLib.mapM_some i (0%Z) (@defval' t2) Hmap2).
        rewrite !SkelLib.seq_length in Hmap2'; destruct lt_dec; try omega.
        rewrite SkelLib.seq_nth in Hmap2'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap2'.
        rewrite SkelLib.seq_nth in Heq3; destruct lt_dec; rewrite Z2Nat.inj_min in *; simpl; try omega.
        2: rewrite Nat.min_glb_lt_iff in *; omega.
        rewrite Z.add_0_l in Heq3.
        unfold bind in Heq3; simpl in Heq3; unfold Monad.bind_opt in Heq3.
        rewrite <-Hmap1' in Heq3.
        rewrite <-Hmap2' in Heq3.
        unfold ret in Heq3; simpl in Heq3; congruence.
Qed.

Lemma simple_fusion_correct GA typ (p : AS GA typ) : forall GA',
  forall (avfenv : AVFusedEnv0 GA GA') (aeenv : AEvalEnv GA) (aeenv' : AEvalEnv GA'),
    (forall ty (m : member ty GA) m',
        hget avfenv m = inl m' -> hget aeenv' m' = hget aeenv m)
    -> (forall ty (m : member ty GA) f le,
           hget avfenv m = inr (f, le) ->
           aeDenote _ _ (DArr _ _ f le) aeenv' = ret (hget aeenv m))
    -> skel_as_wf _ _ p
    -> forall res,
      asDenote _ _ p aeenv = Some res
      -> asDenote _ _ (simple_fusion p avfenv) aeenv' = Some res.
Proof.
  dependent induction p; simpl; eauto; introv Henv1 Henv2 Hwf.
  - unfold bind, ret; simpl; unfold bind_opt; simpl.
    introv Heq.
    destruct (skelDenote GA t1) eqn:Heq1; [|inverts Heq].
    inverts Hwf.
    destruct darr_of_skelapp as [[f' le']|] eqn:Hdarr; simpl.
    + (* Can be fused to other funcs *)
      intros; forwards*: IHp.
      (* Prove invariant Henv1 & Henv2 is preserved *)
      * intros.
        dependent destruction m; simpl in *; jauto.
        inverts H.
      * intros.
        dependent destruction m; simpl in *; jauto.
        inverts H.
        forwards*Happ: darr_of_skelapp_ok.
        rewrites* <-(>>fuse_skel_correct Heq1).
    + (* Cannot be fused *)
      unfold bind, ret; simpl; unfold bind_opt.
      rewrites* (>>fuse_skel_correct Heq1).
      rewrites* (>>IHp).
      * intros.
        dependent destruction m; simpl in *; jauto.
        inverts H; eauto.
        dependent destruction m'; simpl in *; jauto.
        unfold shift_fused_env in H; rewrite hget_hmap in H.
        destruct (hget avfenv m) as [|[? ?]]; [|inverts H].
        dependent destruction m0; inverts H.
        forwards*: Henv1.
        unfold shift_fused_env in H; rewrite hget_hmap in H.
        destruct (hget avfenv m) as [|[? ?]] eqn:Henv; inverts H.
        dependent destruction m0; simpl in *; inverts* H1.
      * intros.
        dependent destruction m; inverts H; simpl.
        unfold shift_fused_env in *; rewrite hget_hmap in *.
        destruct hget as [|[? ?]] eqn:?; inverts H1.
        forwards*: Henv2.
        rewrite shift_lexp_GA_ok.
        rewrite <-H.
        destruct Z_le_dec; eauto.
        apply mapM_eq.
        intros.
        unfold seq in *; apply seq'_In in H0.
        dependent destruction f0; simpl.
        rewrites* shift_sexp_GA_ok.
  - introv Hres; destruct (hget avfenv m) as [|[f' le']] eqn:Heq; eauto.
    { simpl; rewrites* (>>Henv1). }
    simpl; unfold bind, ret; simpl; unfold bind_opt.
    rewrites* (>>Henv2).
    rewrite Hres.
    rewrite mapM_total.
    rewrites* List.map_id.
Qed.