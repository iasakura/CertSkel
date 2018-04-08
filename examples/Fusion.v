Require Import Monad SkelLib Computation ZArith TypedTerm Program DepList.
Require Import CUDALib Correctness.
Require Import Compiler Ext Extract Host CompilerProof LibTactics.
Open Scope Z_scope.

Notation AVFusedEnv0 GA1 GA2 := (hlist (fun typ => option (Skel.Func GA2 (Skel.Fun1 Skel.TZ typ) * Skel.LExp GA2 Skel.TZ)) GA1).
Notation AVFusedEnv GA := (AVFusedEnv0 GA GA).

Axiom sorry : forall {T : Type}, T.

Import Skel.

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

Definition shift_fused_env {GA typ} (avfenv : AVFusedEnv0 (typ :: GA) GA) : AVFusedEnv (typ :: GA) :=
  hmap (fun typ' darr =>
    match darr with
    | None => None
    | Some (f, lexp) => Some (shift_func_GA typ f, shift_lexp_GA typ lexp)
    end) avfenv.

Definition body_of_func1 {GA ty1 ty2} (f : Func GA (Fun1 ty1 ty2)) : SExp GA [ty1] ty2 :=
  match f in Func _ fty return (match fty with
                                | Fun1 ty1 ty2 => SExp _ [ty1] ty2
                                | Fun2 _ _ _ =>  unit end) with
  | F1 _ _ _ body => body
  | _ => tt
  end.

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

Definition fuse_ae {GA resTy} (ae : AE GA resTy) : AVFusedEnv GA -> AE GA resTy :=
  match ae with
  | VArr _ _ m =>
    fun avfenv =>
      match hget avfenv m with
      | None => VArr _ _ m
      | Some (f, len) => DArr _ _ f len
      end
  | DArr _ _ f l =>
    fun avfenv => DArr _ _ f l
  end.

Definition fuse_skel {GA resTy} (skel : SkelE GA resTy) : AVFusedEnv GA -> SkelE GA resTy :=
  match skel with
  | Reduce _ _ f ae => fun avfenv => Reduce _ _ f (fuse_ae ae avfenv)
  | Map _ _ _ f ae => fun avfenv => Map _ _ _ f (fuse_ae ae avfenv)
  | Seq _ n l => fun _ => Seq _ n l
  | Zip _ _ _ ae1 ae2 => fun avfenv => Zip _ _ _ (fuse_ae ae1 avfenv) (fuse_ae ae2 avfenv)
  end.

Fixpoint simple_fusion {GA typ} (p : AS GA typ) : AVFusedEnv GA -> AS GA typ :=
  match p with
  | ALet _ tyapp tyres skel res =>
    fun avfenv =>
      let skel := fuse_skel skel avfenv in
      let darr := darr_of_skelapp skel in
      let res := simple_fusion res (shift_fused_env (darr ::: avfenv)) in
      ALet _ tyapp tyres skel res
  | ARet _ t x =>
    fun avfenv =>
      ARet _ t x
  end.

Lemma fuse_ae_correct GA typ (ae : AE GA typ) :
  forall (avfenv : AVFusedEnv GA) (aeenv : AEvalEnv GA),
    (forall (m : member typ GA) f le,
        hget avfenv m = Some (f, le)
        -> aeDenote _ _ (DArr _ _ f le) aeenv = ret (hget aeenv m))
    -> aeDenote _ _ (fuse_ae ae avfenv) aeenv = aeDenote _ _ ae aeenv.
Proof.
  destruct ae; simpl; introv; eauto.
  destruct (hget avfenv m) as [[f le] | ] eqn:Heq; eauto.
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
  
Lemma fuse_skel_correct GA resTyp (skel : SkelE GA resTyp) :
  forall (avfenv : AVFusedEnv GA) (aeenv : AEvalEnv GA),
    (forall typ (m : member typ GA) f le,
        hget avfenv m = Some (f, le)
        -> aeDenote _ _ (DArr _ _ f le) aeenv = ret (hget aeenv m))
    -> skelDenote _ _ (fuse_skel skel avfenv) aeenv = skelDenote _ _ skel aeenv.
Proof.
  dependent destruction skel; simpl; eauto; introv Henv;
    repeat rewrites* fuse_ae_correct.
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

Lemma simple_fusion_correct GA typ (p : AS GA typ) :
  forall (avfenv : AVFusedEnv GA) (aeenv : AEvalEnv GA),
    (forall typ (m : member typ GA) f le,
        hget avfenv m = Some (f, le)
        -> aeDenote _ _ (DArr _ _ f le) aeenv = ret (hget aeenv m))
    -> forall res, 
      asDenote _ _ p aeenv = Some res
      -> asDenote _ _ (simple_fusion p avfenv) aeenv = Some res.
Proof.
  dependent induction p; simpl; eauto; introv Henv.
  unfold bind, ret; simpl; unfold bind_opt; simpl.
  rewrites* fuse_skel_correct.
  destruct (skelDenote GA t1 s) eqn:Heq; eauto.
  intros; forwards*: IHp.
  introv Hget.
  dependent destruction m; simpl in *.
  - destruct darr_of_skelapp as [[f' le']|] eqn:Hdarr; inverts Hget.
    rewrite shift_lexp_GA_ok.
    forwards*Happ: darr_of_skelapp_ok.
    rewrites* <-(>>fuse_skel_correct avfenv) in Heq.
    simpl in *.
    unfold ret; simpl; rewrite <-Happ.
    destruct Z_le_dec; eauto.
    f_equal; extensionality x.
    dependent destruction f'; simpl.
    rewrites* shift_sexp_GA_ok.
  - rewrite hget_hmap in Hget.
    destruct (hget avfenv m) as [[f' le']|] eqn:Heq'; inverts Hget.
    rewrites* <-(>>Henv).
    rewrites shift_lexp_GA_ok.
    asserts_rewrite*
    ((fun i : Z =>
        funcDenote (t1 :: GA) (Fun1 TZ typ) (shift_func_GA t1 f') (a ::: aeenv) i) =
     (fun i : Z => funcDenote GA (Fun1 TZ typ) f' aeenv i)).
    extensionality i.
    dependent destruction f'; simpl.
    rewrites* shift_sexp_GA_ok.
Qed.

