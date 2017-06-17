Require Import PeanoNat String List LibTactics GPUCSL TypedTerm Monad Grid.
Require Import Grid Host DepList CUDALib CSLLemma CSLTactics CodeGen Compiler mkMap mkReduce 
        Correctness MonadRules CodeGenM SeqCompilerProof Program Psatz.
Import Utils.
    
Open Scope list_scope.

Lemma genenv_ok GA : aenv_ok (remove_typeinfo (gen_params GA)).
Proof.
  unfold aenv_ok, gen_params.
  generalize 0; induction GA; intros s.
  - split; introv; inverts m.
  - split; introv; dependent destruction m; simpl; eauto;
    forwards* [IH1 IH2]: (IHGA (S s)).
    clear.
    unfold arr_name.
    generalize 0.
    induction a; simpl.
    + intros ? [?|[]]; substs; simpl; eauto.
    + intros ? [?|[]]; substs; simpl; eauto.
    + intros ?; rewrite in_app_iff; intros [? | ?]; eauto.
Qed.

Lemma eval_compile_AE_len GA typ (arr : Skel.AE GA typ) (avenv : AVarEnv GA) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA) vs :
  Skel.aeDenote _ _ arr aeenv = Some vs
  -> evalExp (arrInvVar avenv apenv aeenv) (compile_AE_len arr avenv) (Zn (length vs)).
Proof.
  unfold Skel.aeDenote.
  dependent destruction arr; simpl.
  intros Heq; inverts Heq.
  - induction GA; dependent destruction m; dependent destruction avenv; dependent destruction apenv; 
    dependent destruction aeenv; simpl; unfold arrInvVar; simpl; destruct p.
    + evalExp.
    + apply evalExp_app_ig, IHGA.
  - destruct Z_le_dec; try congruence.
    intros H; forwards*Hlen: SkelLib.mapM_length.
    rewrite SkelLib.seq_length in Hlen.
    rewrite Hlen.
    rewrites* Z2Nat.id.
    clear.
    dependent induction l; simpl; constructor; eauto.
    eapply alen_in.
    instantiate (1 := snd (hget avenv m)); destruct (hget avenv m); eauto.
Qed.

Lemma hasDefval_vals typ : hasDefval (vals typ).
Proof.
  unfold vals; induction typ; constructor; simpl.
  apply 0%Z.
  apply 0%Z.
  apply (default, default).
Qed.

Lemma flatten_aenv_avars_length GA (avenv : AVarEnv GA) :
  length (flatten_aenv avenv) = length (flatten_avars (gen_params GA)).
Proof.
  unfold gen_params.
  generalize 0.
  induction GA; dependent destruction avenv; simpl; eauto.
  intros n; destruct p; simpl; rewrite !app_length, !flatTup_length, (IHGA _ (S n)); eauto.
Qed.

Lemma evalExpseq_cons2 x v E es vs :
  evalExpseq E es vs
  -> evalExpseq (x |-> v :: E) es vs .
Proof.
  induction 1; constructor; eauto.
  apply evalExp_cons_ig; eauto.
Qed.

Lemma evalExpseq_cons E e v es vs :
  evalExp E e v -> evalExpseq E es vs -> evalExpseq E (e :: es) (v :: vs).
Proof. constructor; eauto. Qed.

Lemma evalExpseq_flatTupxs E ty (xs : vars ty) vs :
  incl (xs |=> vs) E
  -> evalExpseq E (map Evar (flatTup xs)) (flatTup vs).
Proof.
  induction ty; simpl; [do 2 constructor; apply H; simpl; eauto..|].
  intros.
  rewrite map_app; apply evalExpseq_app; [apply IHty1 | apply IHty2];
  unfold incl in *; intros x ?; forwards*: (>>H x); rewrite in_app_iff; eauto.
Qed.

Lemma evalExpseq_app1 E1 E2 es vs :
  evalExpseq E1 es vs -> evalExpseq (E1 ++ E2) es vs.
Proof.
  induction 1; try constructor; eauto.
  apply evalExp_app1; eauto.
Qed.
Lemma evalExp_app2 E1 E2 e v :
  evalExp E2 e v -> evalExp (E1 ++ E2) e v.
Proof.
  induction 1; constructor; eauto.
  rewrite in_app_iff; eauto.
Qed.

Lemma evalExpseq_app2 E1 E2 es vs :
  evalExpseq E2 es vs -> evalExpseq (E1 ++ E2) es vs.
Proof.
  induction 1; try constructor; eauto.
  apply evalExp_app2; eauto.
Qed.

Fixpoint flatten_aeenv {GA} (aeenv : AEvalEnv GA) : APtrEnv GA -> list val :=
  match aeenv with
  | HNil => fun _ => nil
  | l ::: aeenv => fun apenv =>
    match apenv in hlist _ GA return (match GA with
                                      | nil => Empty_set -> list val
                                      | _ :: GA' => (APtrEnv GA' -> list val) -> list val
                                      end) with 
    | HNil => fun none => match none with end
    | p ::: apenv => fun rec => SkelLib.len l :: flatTup p ++ rec apenv
    end (flatten_aeenv aeenv)
  end%list.

Lemma evalExpseq_arrInv GA (avenv : AVarEnv GA) apenv aeenv :
  evalExpseq (arrInvVar avenv apenv aeenv) (map Evar (flatten_aenv avenv)) (flatten_aeenv aeenv apenv).
Proof.
  unfold arrInvVar; induction GA; 
  dependent destruction avenv; dependent destruction apenv; dependent destruction aeenv; simpl.
  constructor.
  destruct p; simpl.
  apply evalExpseq_cons; [evalExp|].
  rewrite map_app.
  apply evalExpseq_cons2.
  apply evalExpseq_app.
  - apply evalExpseq_app1.
    applys* evalExpseq_flatTupxs.
  - applys* evalExpseq_app2.
Qed.

Lemma out_params_fst pref ty n :
  maptys fst (arr_params pref ty n) = locals pref ty n.
Proof.
  revert n; induction ty; simpl; eauto.
  intros; simpl.
  unfold arr_params in *; rewrite IHty1, IHty2; eauto.
Qed.  

Lemma out_name_fst ty :
  maptys fst (out_name ty) = locals ("_arrOut") ty 0. 
Proof.
  apply out_params_fst.
Qed.  

Lemma arr_name_fst n ty :
  maptys fst (arr_name n ty) = locals ("_arrIn" ++ nat2str n) ty 0.
Proof.
  apply out_params_fst.
Qed.

Lemma out_name_locals typ :
  map fst (flatTup (out_name typ)) = flatTup (outArr typ).
Proof.
  rewrite <-flatTup_map, out_name_fst; eauto.
Qed.

Lemma subst_env_app E1 E2 xs vs : 
  subst_env (E1 ++ E2) xs vs <-> (subst_env E1 xs vs /\ subst_env E2 xs vs)%list.
Proof.
  induction E1 as [|[? ?] ?]; simpl; tauto.
Qed.

Lemma subst_env_cons2 E x xs v vs :
  ~In x (map ent_e E)
  -> subst_env E xs vs
  -> subst_env E (x :: xs) (v :: vs).
Proof.
  induction E as [|[? ?] ?]; simpl; eauto.
  destruct var_eq_dec; substs; try tauto.
Qed.

Lemma subst_env_app1 E xs1 xs2 vs1 vs2 :
  subst_env E xs1 vs1
  -> subst_env E (xs1 ++ xs2) (vs1 ++ vs2).
Proof.
  induction E as [|[? ?] ?]; simpl; eauto.
  intros [? ?]; split; eauto.
  revert H; clear; revert xs2 vs1 vs2; clear.
  induction xs1; simpl; intros; try tauto.
  destruct vs1; try tauto.
  destruct var_eq_dec; substs; simpl; eauto.
Qed.

Lemma subst_env_app2 E xs1 xs2 vs1 vs2 :
  length xs1 = length vs1
  -> disjoint (map ent_e E) xs1
  -> subst_env E xs2 vs2
  -> subst_env E (xs1 ++ xs2) (vs1 ++ vs2).
Proof.
  induction E as [|[? ?] ?]; simpl; eauto.
  intros Hlen [? ?] [? ?]; split; eauto.
  revert Hlen H H1; clear; revert xs2 vs1 vs2.
  induction xs1; simpl; introv; destruct vs1; simpl; try congruence; eauto.
  intros Heq Hdis Hsubst; destruct var_eq_dec; try tauto; eauto.
Qed.

Lemma subst_env_flatTup typ (xs : vars typ) vs :
  disjoint_list (flatTup xs)
  -> subst_env (xs |=> vs) (flatTup xs) (flatTup vs).
Proof.
  induction typ; simpl; [destruct var_eq_dec; tauto..|].
  intros Hdisj.
  apply subst_env_app; split.
  apply subst_env_app1; eauto using disjoint_list_proj1.
  apply subst_env_app2; [repeat rewrites* flatTup_length|..].
  apply disjoint_list_app_disjoint in Hdisj.
  rewrite map_flatTup; eauto using disjoint_comm.
  apply IHtyp2; eauto using disjoint_list_proj2.
Qed.

Lemma arrInvVar_nin GA (avenv : AVarEnv GA) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA) x :
  aenv_ok avenv 
  -> prefix "_" (str_of_var x) = false
  -> ~ In x (map ent_e (arrInvVar avenv apenv aeenv)).
Proof.
  intros ? ? ?.
  rewrite in_map_iff in *; destruct H1 as (? & ? & ?); substs.
  destruct x0.
  forwards* ?: aenv_ok_params; simpl in *; congruence.
Qed.

Lemma inp_len_name_arrInvVar GA (aeenv : AEvalEnv GA) (apenv : APtrEnv GA) :
  ~In inp_len_name (map ent_e (arrInvVar (remove_typeinfo (gen_params GA)) apenv aeenv)).
Proof.
  unfold gen_params.
  generalize 0.
  induction GA; dependent destruction aeenv; dependent destruction apenv; simpl; eauto.
  intros; rewrite map_app, in_app_iff.
  intros [Hin | [Hin | Hin]].
  - destruct n; cbv in Hin; congruence.
  - rewrite in_map_iff in Hin; destruct Hin as (? & ? & ?); substs.
    clear IHGA.
    revert H H0; generalize 0; clear.
    unfold arr_name; generalize 0.
    induction a; introv ? ? Hin; simpl in *;
    try (destruct Hin as [Hin|[]]; substs; cbv in H0; congruence).
    rewrite in_app_iff in Hin; destruct Hin; eauto.
  - forwards*: IHGA.
Qed.

Lemma arr_params_in x pref ty n :
  In x (flatTup (arr_params pref ty n))
  -> prefix pref (str_of_var (fst x)) = true.
Proof.
  revert n; induction ty; simpl; [intros n [H|[]]; subst; simpl; apply prefix_cat..|].
  intros n; rewrite in_app_iff; intros [? | ?]; eauto.
Qed.

Lemma prefix_ex (s1 s2 : string) : prefix s1 s2 = true <-> exists s, s2 = (s1 ++ s)%string.
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
      cutrewrite (String a0 s1 ++ s = String a0 (s1 ++ s))%string in H; [|auto].
      inversion H; congruence.
Qed.

Lemma out_name_arrInvVar GA (aeenv : AEvalEnv GA) (apenv : APtrEnv GA) typ :
  disjoint (map ent_e (arrInvVar (remove_typeinfo (gen_params GA)) apenv aeenv))
           (map fst (flatTup (out_name typ))).
Proof.
  unfold gen_params.
  generalize 0.
  unfold out_name; generalize 0.
  induction GA; dependent destruction aeenv; dependent destruction apenv; simpl; eauto.
  introv; rewrite map_app, !disjoint_app_l; simpl.
  splits.
  - clear IHGA; revert n0 n; induction typ; simpl; try (intros ? ? [H|[]]; cbv in H; congruence).
    intros; rewrite map_app, in_app_iff; intros [? | ?]; firstorder.
  - apply not_in_disjoint; intros ?.
    unfold arr_name; rewrite !in_map_iff; intros [? [? ?]] [? [? ?]]; substs.
    destruct x0; apply mpss_in in H0.
    rewrite flatTup_map in H0.
    rewrite in_map_iff in H0; destruct H0 as [? [? ?]]; substs.
    apply arr_params_in in H0.
    apply arr_params_in in H2; simpl in *.
    destruct x1, x; simpl in *; substs.
    rewrite prefix_ex in H0; destruct H0 as (? & ?).
    rewrite prefix_ex in H2; destruct H2 as (? & ?).
    rewrite H0 in H; simpl in *.
    rewrite string_app_assoc in H.
    cbv in H; congruence. 
  - apply IHGA.
Qed.

Lemma subst_env_params GA apenv aeenv :
  subst_env
    (arrInvVar (remove_typeinfo (gen_params GA)) apenv aeenv)
    (map fst (flatten_avars (gen_params GA))) (flatten_aeenv aeenv apenv).
Proof.
  unfold gen_params; generalize 0.
  induction GA; dependent destruction aeenv; dependent destruction apenv.
  - simpl; eauto.
  - intros n; split; simpl.
    + match goal with [|- if ?b then ?th else ?el] => destruct b end;
      simpl; try congruence; eauto.
    + simpl.
      apply subst_env_app; split.
      * apply subst_env_cons2.
        { rewrite arr_name_fst.
          rewrite map_flatTup.
          apply locals_not_in; eauto. }
        rewrite map_app; apply subst_env_app1.
        rewrite <-flatTup_map, !arr_name_fst.
        apply subst_env_flatTup.
        Lemma arr_name_disjoint n ty :
          disjoint_list (flatTup (maptys fst (arr_name n ty))).
        Proof.
          rewrite arr_name_fst.
          apply locals_disjoint_ls.
        Qed.
        apply locals_disjoint_ls.
      * apply subst_env_cons2; eauto.
        { intros Hc.
          apply in_map_iff in Hc; destruct Hc as (? & ? & ?).
          destruct x; simpl in *; substs.
          assert (HnSn : n < S n) by omega.
          revert H0 HnSn; generalize (S n); generalize n.
          clear; induction GA; simpl in *; eauto.
          introv; rewrite in_app_iff; intros [Hc | [Hc | Hc]]; substs.
          - inverts Hc.
            revert n0 H0; clear; induction n; simpl in *.
            destruct n0; simpl; intros.
            omega.
            cbv in H0; congruence.
            destruct n0; [cbv; congruence|].
            simpl; intros; eapply IHn.
            inverts H0; eauto.
            omega.
          - rewrite arr_name_fst in Hc; apply mpss_in in Hc.
            apply locals_not_in in Hc; eauto.
          - dependent destruction apenv.
            dependent destruction aeenv.
            simpl in Hc; eauto. }
        rewrite map_app; rewrite <-flatTup_map, arr_name_fst.
        apply subst_env_app2; [rewrite !flatTup_length; eauto|..].
        { assert (HnSn : n < S n) by omega.
          revert HnSn; generalize (S n); generalize n.
          clear IHGA; clear; induction GA; simpl in *; eauto.
          introv Hnn0; rewrite !map_app; splits.
          - apply locals_not_in; simpl; eauto.
          - apply disjoint_app_l; splits.
            + rewrite arr_name_fst, map_flatTup.
              apply locals_disjoint; simpl.
              revert n0 Hnn0; induction n; simpl.
              intros; destruct n0; simpl; eauto; omega.
              intros; destruct n0; simpl; eauto.
              apply IHn; omega.
              revert n0 Hnn0; induction n; simpl.
              intros; destruct n0; simpl; eauto; omega.
              intros; destruct n0; simpl; eauto.
              apply IHn; omega.
            + dependent destruction apenv; 
              dependent destruction aeenv; eauto. }
        apply IHGA; eauto. 
Qed.

Lemma has_no_vars_kernelInv' GA (aeenv : AEvalEnv GA) apenv res P q :
  has_no_vars (kernelInv' apenv aeenv res P q).
Proof.
  apply has_no_vars_assn.
Qed.

Require Import SetoidClass.
Lemma kernelInv'_combine GA R P E (avenv : AVarEnv GA) apenv aeenv R' P' p : 
  (Assn R P (E ++ arrInvVar avenv apenv aeenv) ** kernelInv' apenv aeenv R' P' p) ==
  kernelInv avenv apenv aeenv (R *** R') (P /\ P') E p.
Proof.
  unfold kernelInv', kernelInv.
  rewrite Assn_combine.
  split; revert s h; prove_imp.
  simpl in *; tauto.
Qed.

Lemma ls_app_cons A l (x : A) l' :
  l ++ x :: l' = (l ++ x :: nil) ++ l'.
Proof. rewrite <-app_assoc; eauto. Qed.

Lemma map_eval_invert GA dom cod aeenv f arr result :
  Skel.skelDenote GA cod (Skel.Map GA dom cod f arr) aeenv = Some result ->
  exists arr_res, 
    Skel.aeDenote _ _ arr aeenv = Some arr_res /\
    mapM (Skel.funcDenote _ _ f aeenv) arr_res = Some result.
Proof.
  intros eval_map_ok.
  simpl in *; unfold Monad.bind_opt in *.
  destruct Skel.aeDenote; simpl in *; inverts eval_map_ok; eexists; eauto.
Qed.

Lemma compile_map_ok GA dom cod ntrd nblk
      (avenv : AVarEnv GA) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA)
      (f : Skel.Func GA (Skel.Fun1 dom cod))
      (arr : Skel.AE GA dom) (result : Skel.aTypDenote cod)
      Gp E R P :
  ntrd <> 0 -> nblk <> 0
  -> Skel.skelDenote GA cod (Skel.Map GA dom cod f arr) aeenv = Some result
  -> CMsat (Ga (kernelInv avenv apenv aeenv (TT *** R) P E 1) Gp)
           (compile_map ntrd nblk avenv f arr)
           (fun res => Ga (Ex ps, kernelInv avenv apenv aeenv
                                            (arrays (val2gl ps) (arr2CUDA result) 1%Qc *** TT *** R)
                                            P
                                            (fst res |-> Zn (length result) :: snd res |=> ps ++ E) 1%Qc)
                          Gp).
Proof.
  intros Hntrd0 Hnblk0 Heval.
  forwards*(arr_res & (eval_arr & eval_map)): (>>map_eval_invert).

  unfold Skel.skelDenote in Heval.
  pose proof Heval as Heval'.
  unfold bind in Heval; simpl in Heval.

  unfold compile_map; simpl.
  eapply rule_bind_s.
  { applys (>>rule_gen_kernel_s).
    3: intros; applys (>>mkMap_ok (remove_typeinfo (gen_params GA))).
    simpl; eauto.
    simpl; eauto.
    apply genenv_ok.
    applys* (>> compile_AE_ok).
    applys* (>> compile_func_ok). }
  intros gen_map.
  eapply rule_bind_s.
  apply rule_fLet_s.
  { apply evalExp_app2; applys* eval_compile_AE_len. }
  intros outLen.
  eapply rule_bind_s.
  apply rule_fAllocs_s.
  { evalExp. }
  intros outs.
  eapply rule_code_ex_s.
  apply hasDefval_vals.
  intros ps.
  apply rule_code_ex_s.
  apply listA_hasDefval.
  intros vs.
  (* apply rule_ret_back_s. *)
  eapply rule_bind_s.
  { eapply rule_invokeKernel_s.
    - unfold K; rewrite !in_app_iff; simpl; eauto.
    - simpl; eauto.
    - simpl; rewrite !map_app, !app_length, !map_length, !flatTup_length; eauto.
      do 2 f_equal.
      rewrite flatten_aenv_avars_length; eauto.
    - repeat econstructor.
    - apply has_no_vars_kernelInv'.
    - do 3 (apply evalExpseq_cons; [evalExp|]).
      simpl; rewrite map_app; apply evalExpseq_app.
      apply evalExpseq_app1.
      apply evalExpseq_flatTupxs; eauto.
      apply evalExpseq_app2, evalExpseq_cons2.
      apply evalExpseq_app2; apply evalExpseq_arrInv.
    - eauto.
    - eauto.
    - simpl.
      rewrite !map_app.
      intros [? ?]; splits; eauto.
      + rewrite subst_env_app; split.
        * unfold outArr.
          repeat (apply subst_env_cons2; [rewrite map_flatTup; apply locals_not_in; simpl; eauto|]).  
          apply subst_env_app1.
          rewrite out_name_locals.
          apply subst_env_flatTup; apply locals_disjoint_ls.
        * do 2 (apply subst_env_cons2; [applys* arrInvVar_nin; apply genenv_ok|]).
          apply subst_env_cons2.
          apply inp_len_name_arrInvVar.
          apply subst_env_app2.
          rewrite map_length, !flatTup_length; eauto.
          apply out_name_arrInvVar.          
          apply subst_env_params.
    - intros [? ?]; splits; eauto.      
      instantiate (1 := vs).
      forwards*: SkelLib.mapM_length; congruence.
    - intros; rewrite <-res_assoc.
      repeat sep_cancel'.
      eauto. }
  introv; simpl.
  apply rule_ret_s; simpl.

  - unfold K; apply gassnInv_imp_s; simpl.
    unfold incl; introv; simpl; rewrite !in_app_iff; simpl; eauto.
    
    introv; unfold kernelInv, kernelInv'.
    rewrite fv_assn_sep_eq in *; intros (? & ? & (Hin1 & Hin2 & Heq)).
    rewrite !fv_assn_base_eq in *.
    (apply fv_assn_Ex_eq; intros); rewrite fv_assn_base_eq.
    simpl in *.
    simpl; repeat (rewrite !map_app in *; simpl in *).
    unfold incl in *; simpl in *; intros a Hin3.
    specialize (Hin1 a); specialize (Hin2 a); specialize (Heq a).
    repeat (rewrite !in_app_iff in *; simpl in *).
    rewrite !map_flatTup in *.
    tauto.

  - unfold K; simpl.
    introv. 
    rewrite ls_app_cons, app_assoc, kernelInv'_combine; revert s h; prove_imp.
    erewrite mapM_length; eauto.
Qed.

Lemma reduce_eval_invert GA typ aeenv f arr result :
  Skel.skelDenote GA typ (Skel.Reduce GA typ f arr) aeenv = Some result ->
  exists arr_res, 
    Skel.aeDenote _ _ arr aeenv = Some arr_res /\
    SkelLib.reduceM (Skel.funcDenote _ _ f aeenv) arr_res = Some result.
Proof.
  intros eval_reduce_ok.
  simpl in *; unfold Monad.bind_opt in *.
  destruct Skel.aeDenote; simpl in *; inverts eval_reduce_ok; eexists; eauto.
Qed.

Lemma compile_reduce_ok GA typ ntrd nblk
      (avenv : AVarEnv GA) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA)
      (f : Skel.Func GA (Skel.Fun2 typ typ typ)) f_tot
      (arr : Skel.AE GA typ) (result : Skel.aTypDenote typ)
      Gp R P E :
  ntrd <> 0 -> nblk <> 0
  -> (forall x y : Skel.typDenote typ, Skel.funcDenote GA (Skel.Fun2 typ typ typ) f aeenv x y = Some (f_tot x y))
  -> (forall x y : Skel.typDenote typ, f_tot x y = f_tot y x)
  -> (forall x y z : Skel.typDenote typ, f_tot (f_tot x y) z = f_tot x (f_tot y z))
  -> Skel.skelDenote GA typ (Skel.Reduce GA typ f arr) aeenv = Some result
  -> CMsat (Ga (kernelInv avenv apenv aeenv (TT *** R) P E 1) Gp)
           (compile_reduce ntrd nblk avenv f arr)
           (fun res => Ga (Ex ps, kernelInv avenv apenv aeenv
                                            (arrays (val2gl ps) (arr2CUDA result) 1%Qc *** TT  *** R)
                                            P
                                            (fst res |-> Zn (length result) :: snd res |=> ps ++ E) 1%Qc) Gp).
Proof.
  intros Hnt0 Hnb0 Htot Hcomm Hassoc Heval.
  forwards*(arr_res & (eval_arr & eval_map)): (>>reduce_eval_invert).  

  unfold compile_reduce.

  eapply rule_bind_s.
  { applys (>>rule_gen_kernel_s).
    3: intros; applys (>>mkReduce_ok (remove_typeinfo (gen_params GA))).
    simpl; eauto.
    simpl; eauto.
    apply genenv_ok.
    applys* compile_AE_ok.
    applys* (>>compile_func_ok (Skel.Fun2 typ typ typ)). }
  
  intros gen_reduce.
  eapply rule_bind_s.
  { apply rule_fLet_s.
    apply evalExp_app2.
    applys* eval_compile_AE_len. }
  intros inLen.
  eapply rule_bind_s.
  { apply rule_fAllocs_s; evalExp. }
  intros temps.
  apply rule_code_ex_s.
  apply hasDefval_vals.
  intros ps.
  apply rule_code_ex_s.
  apply listA_hasDefval.
  intros vs.
  eapply rule_bind_s.
  { eapply rule_invokeKernel_s.
    - remember (S (Nat.log2 ntrd)).
      unfold K; rewrite !in_app_iff; simpl; substs; eauto.
    - simpl; eauto.
    - simpl; rewrite !map_app, !app_length, !map_length, !flatTup_length; eauto.
      do 2 f_equal.
      rewrite flatten_aenv_avars_length; eauto.
    - repeat econstructor.
    - Lemma has_no_vars_Ex T (P : T -> assn) :
        (forall x, has_no_vars (P x))
        -> has_no_vars (Ex x, P x).
      Proof.
        unfold has_no_vars, Bdiv.indeP; simpl.
        intros.
        constructor; eauto.
      Qed.
      apply has_no_vars_Ex; intros.
      apply has_no_vars_kernelInv'.
    - do 2 (apply evalExpseq_cons; [evalExp|]).
      simpl; rewrite map_app.
      apply evalExpseq_cons; [evalExp|].
      apply evalExpseq_app.
      { apply evalExpseq_flatTupxs.
        apply incl_appl; eauto. }
      apply evalExpseq_app2, evalExpseq_cons2.
      apply evalExpseq_app2; apply evalExpseq_arrInv.
    - eauto.
    - eauto.
    - simpl.
      rewrite !map_app.
      intros [? ?]; splits; eauto.
      + rewrite subst_env_app; split.
        * unfold outArr.
          repeat (apply subst_env_cons2; [rewrite map_flatTup; apply locals_not_in; simpl; eauto|]).  
          apply subst_env_app1.
          rewrite out_name_locals.
          apply subst_env_flatTup; apply locals_disjoint_ls.
        * do 2 (apply subst_env_cons2; [applys* arrInvVar_nin; apply genenv_ok|]).
          apply subst_env_cons2.
          apply inp_len_name_arrInvVar.
          apply subst_env_app2.
          rewrite map_length, !flatTup_length; eauto.
          apply out_name_arrInvVar.          
          apply subst_env_params.
    - intros [? ?]; splits; [..|splits]; eauto.
      forwards*: (Nat.log2_spec ntrd); simpl; omega.
      instantiate (1 := vs); omega.
    - intros; rewrite <-res_assoc.
      repeat sep_cancel'; eauto. }
  introv.

  eapply rule_equiv_mono_pre_s.
  { introv; unfold K.
    rewrite ex_lift_l.
    intros [? Hsat]; fold_sat_in Hsat.
    simpl in Hsat.
    rewrite ls_app_cons in Hsat.
    rewrite app_assoc in Hsat.
    rewrite kernelInv'_combine in *.
    ex_intro x Hsat; simpl in Hsat.
    apply Hsat. }
  { unfold K; introv H.
    apply fv_assn_sep_eq in H as (ys & zs & Hys & Hzs & Heq).
    rewrite fv_assn_base_eq in Hys.
    rewrite fv_assn_Ex_eq in *.
    intros v'; specialize (Hzs v').
    apply fv_assn_base_eq in Hzs; simpl in Hzs.
    apply fv_assn_base_eq; simpl in *.
    rewrite <-!app_assoc; simpl.
    unfold incl; firstorder. }
  apply rule_code_ex_s.
  Lemma hasDefval_aTypDenote typ : hasDefval (Skel.aTypDenote typ).
  Proof.
    induction typ; simpl; constructor; try now (apply nil).
  Qed.
  apply hasDefval_aTypDenote.
  intros vs1.
  
  remember (S (Nat.log2 ntrd)).
  assert (SkelLib.reduceM (fun x0 y : Skel.typDenote typ => Some (f_tot x0 y))
                          (firstn (min ((Datatypes.length arr_res + ntrd - 1) / ntrd) nblk) vs1) =
          SkelLib.reduceM (fun x0 y : Skel.typDenote typ => Some (f_tot x0 y)) arr_res ->
          Skel.skelDenote (typ :: GA) typ
                          (Skel.Reduce (typ :: GA) typ (shift_func_GA typ f) (Skel.VArr _ _ HFirst))
                          ((firstn (min ((Datatypes.length arr_res + ntrd - 1) / ntrd) nblk) vs1) ::: aeenv) =
          Some result).
  { simpl; unfold bind; simpl.
    Lemma shift_func_GA_ok GA typ typ' f arr aeenv :
      Skel.funcDenote (typ :: GA) (Skel.Fun2 typ' typ' typ') (shift_func_GA typ f) (arr ::: aeenv) =
      Skel.funcDenote GA (Skel.Fun2 typ' typ' typ') f aeenv.
    Proof.
      dependent destruction f; simpl.
      extensionality x; extensionality y.
      generalize (y ::: x ::: HNil).
      generalize dependent (typ' :: typ' :: nil).
      clear x y.
      introv; induction s; simpl; eauto;
      try (now (rewrite IHs1; f_equal; extensionality l; rewrite IHs2; eauto));
      try (now (rewrite IHs; f_equal; eauto)).
      unfold bind, ret; simpl; unfold Monad.bind_opt.
      rewrite IHs1.
      destruct (Skel.sexpDenote _ _ _ s1 _ _); eauto.
      destruct t0; eauto.
    Qed.
    rewrite shift_func_GA_ok; eauto; simpl.
    assert (Hfeq : Skel.funcDenote GA _ f aeenv = fun x y => Some (f_tot x y)) by
        (extensionality l; extensionality l'; eauto); eauto.
    rewrite Hfeq; eauto. 
    congruence. }

  eapply rule_bind_s.
  { apply rule_gen_kernel_s.
    3: intros; applys (>>mkReduce_ok (remove_typeinfo (gen_params (typ :: GA)))); eauto.
    simpl; eauto.
    reflexivity.
    Opaque gen_params flatten_aeenv flatten_aenv.
    apply genenv_ok.
    applys* (>>compile_AE_ok (Skel.VArr (typ :: GA) typ HFirst)).
    applys* (>>compile_func_ok (Skel.Fun2 typ typ typ)). }
  intros gen_kernel'.
  eapply rule_bind_s.
  { apply rule_fLet_s.
    evalExp.
    apply evalExp_app2.
    apply evalExp_cons.
    apply evalExp_app2.
    applys* eval_compile_AE_len. }
  intros tempLen.
  eapply rule_bind_s.
  { apply rule_fLet_s; evalExp. }
  intros outLen.
  eapply rule_bind_s.
  { apply rule_fAllocs_s.
    instantiate (1 := 1).
    evalExp. }
  intros outs.
  eapply rule_code_ex_s.
  apply hasDefval_vals.
  intros ps'.
  apply rule_code_ex_s.
  apply listA_hasDefval.
  intros vs'.

  eapply rule_bind_s.
  { eapply rule_invokeKernel_s.
    - unfold K; rewrite !in_app_iff; simpl; substs; eauto.
    - eauto.
    - simpl. rewrite !map_app, !app_length, !map_length.
      simpl; rewrite !app_length; rewrite !flatTup_length.
      do 4 f_equal; eauto.
      Transparent gen_params.
      simpl.
      rewrite flatten_aenv_avars_length.
      rewrite app_length, flatTup_length.
      do 2 f_equal.
      Lemma flatten_gen_params_length GA n m :
        length (flatten_avars (hmake_idx n (fun i ty => (len_name i, Int, arr_name i ty)) GA)) =
        length (flatten_avars (hmake_idx m (fun i ty => (len_name i, Int, arr_name i ty)) GA)).
      Proof.
        revert n m; induction GA; simpl; eauto.
        introv.
        rewrite !app_length, !flatTup_length.
        erewrite IHGA; eauto.
      Qed.
      apply flatten_gen_params_length.
      Opaque gen_params.
    - repeat econstructor.
    - apply has_no_vars_Ex; intros.
      apply has_no_vars_kernelInv'.
    - instantiate (3 := 1).
      do 2 (apply evalExpseq_cons; [evalExp|]).
      simpl; rewrite map_app; simpl; rewrite map_app.
      apply evalExpseq_cons; [evalExp|].
      apply evalExpseq_app.
      { apply evalExpseq_flatTupxs.
        apply incl_appl; eauto. }
      apply evalExpseq_cons; [evalExp|].
      apply evalExpseq_app.
      { apply evalExpseq_flatTupxs.
        apply incl_appr, incl_tl, incl_tl.
        apply incl_appl; eauto. 
        apply incl_appl; eauto.
        apply incl_appl; eauto. }
      apply evalExpseq_app2, evalExpseq_cons2, evalExpseq_cons2, evalExpseq_app2, evalExpseq_arrInv.    
    - eauto.
    - eauto.
    - simpl.
      rewrite !map_app.
      intros (? & [? ?] & ?); splits; jauto.
      + instantiate (1 := 1); eauto.
      + instantiate (1 := (firstn
            (Init.Nat.min ((Datatypes.length arr_res + ntrd - 1) / ntrd)
               nblk) vs1)).
        rewrite firstn_length'.
        destruct H1 as (vslen & _).
        destruct le_dec.
        * rewrite Nat2Z.inj_min.
          rewrite div_Zdiv; eauto.
          do 3 f_equal.
          zify; omega.
        * destruct H3 as (? & Hlen).
          rewrite Hlen in *; false; eauto using Nat.le_min_r.
      + rewrite subst_env_app; split.
        * unfold outArr.
          repeat (apply subst_env_cons2; [rewrite map_flatTup; apply locals_not_in; simpl; eauto|]).  
          apply subst_env_app1.
          rewrite out_name_locals.
          apply subst_env_flatTup; apply locals_disjoint_ls.
        * do 2 (apply subst_env_cons2; [applys* arrInvVar_nin; apply genenv_ok|]).
          apply subst_env_cons2.
          apply inp_len_name_arrInvVar.
          apply subst_env_app2.
          rewrite map_length, !flatTup_length; eauto.
          apply out_name_arrInvVar.
          instantiate (2 := ps ::: apenv).
          lets: (subst_env_params (typ :: GA) (ps ::: apenv) 
                                  (firstn (min ((Datatypes.length arr_res + ntrd - 1) / ntrd) nblk) vs1 ::: aeenv)).
          Transparent flatten_aeenv.
          simpl in H4.
          unfold SkelLib.len in H4; rewrite firstn_length' in H4.
          destruct H3 as (_ & Hlen).
          destruct le_dec.
          2: rewrite Hlen in *; false; eauto using Nat.le_min_r.
          rewrite Nat2Z.inj_min in H4.
          rewrite div_Zdiv in H4; eauto.
          cutrewrite (Zn (length arr_res + ntrd - 1) = Zn (length arr_res) + (Zn ntrd - 1))%Z in H4; [|zify; omega].
          apply H4.
    - intros (? & [? ?] & ? & ?).
      instantiate (1 := vs').
      instantiate (1 := f_tot).
      splits; [..|splits]; jauto; try (zify; omega).
      + simpl; forwards*: (Nat.log2_spec nblk); simpl; (zify; omega).
      + rewrite shift_func_GA_ok; jauto.
        rewrite H3, eval_map; eauto.
      + rewrite shift_func_GA_ok; eauto.
    - intros (? & [? ?] & ?).
      introv; rewrite <-!res_assoc; revert h.
      simpl; repeat sep_auto'.
      rewrite res_CA.
      sep_cancel'.
      unfold arrInvRes in *; simpl.
      rewrite <-res_assoc, res_CA.
      sep_cancel'.
      Require Import SetoidClass.
      Lemma arrays_split n ty (ps : locs ty) (arr : list (vals ty)) p :
        arrays ps arr p == (arrays ps (firstn n arr) p *** arrays (locs_off ps (Zn n)) (skipn n arr) p).
      Proof.
        revert ps arr; induction n; introv; simpl.
        - rewrite emp_unit_l_res, locs_off0; reflexivity.
        - destruct arr.
          + rewrite emp_unit_l_res; reflexivity.
          + simpl; rewrite <-res_assoc, IHn.
            rewrite Zpos_P_of_succ_nat.
            rewrite <-locs_offS; reflexivity.
      Qed.
      rewrite (arrays_split (min ((Datatypes.length arr_res + ntrd - 1) /ntrd) nblk)) in H4; eauto.
      unfold arr2CUDA in *.
      Lemma firstn_map A B (f : A -> B) xs n :
        firstn n (map f xs) = map f (firstn n xs).
      Proof.
        revert xs; induction n; intros [|? ?]; simpl; congruence.
      Qed.
      rewrite firstn_map in H4.
      sep_cancel'.
      apply H4. }
  introv.
  unfold K in *.
  apply rule_ret_s.
  introv.
  applys* gassnInv_imp_s; simpl.
  - unfold incl; introv; rewrite !in_app_iff; eauto.
  - unfold K, kernelInv, kernelInv'; introv; repeat rewrite fv_assn_base_eq.
    intros.
    inverts H0.
    rewrite fv_assn_Ex_eq in *; intro.
    rewrite fv_assn_base_eq in *.
    intros a ?; apply H6.
    rewrite !map_app, !in_app_iff in *; simpl in *.
    rewrite map_app in *.
    rewrite map_flatTup in *.
    destruct H0 as [[? | ?] | ?]; eauto;
    forwards*: (>>H3 a);
    repeat first [rewrite !in_app_iff in * | rewrite !map_app in * | simpl].
    + eauto 10.
    + destruct H0; eauto 10.
    + eauto 10.
  - simpl; intros s h Hsat.
    rewrite ex_lift_l in Hsat; destruct Hsat as [res Hsat].
    fold_sat_in Hsat.
    unfold kernelInv' in Hsat.
    rewrite Assn_combine in Hsat.
    revert s h Hsat; prove_imp.
    + cutrewrite (length result = 1); eauto.
      { unfold SkelLib.reduceM in eval_map.
        destruct fold_right; simpl in *; inverts eval_map; eauto. } 
    + unfold arrInvRes in *; simpl in *; repeat rewrite <-res_assoc in *; do 2 sep_cancel'.
      2: rewrite res_comm; sep_cancel'; apply I.
      Lemma firstn_same A n (ls : list A) :
        length ls <= n -> firstn n ls = ls.
      Proof.
        revert n; induction ls; intros [|n]; intros; simpl in *; try omega; eauto.
        rewrite IHls; eauto; omega.
      Qed.
      clear H0.
      destruct res as [|r1 [|? ?]]; simpl in *; try omega.
      rewrite shift_func_GA_ok, H1, eval_map in *.
      rewrite firstn_same in H5.
      { unfold SkelLib.reduceM, ret in H5; simpl in *.
        inverts* H5. }
      simpl.
      apply Min.min_glb; eauto.
      rewrite firstn_length'.
      apply Nat.div_le_lower_bound; eauto.
      rewrite Nat.mul_1_r.
      assert (1 <= length arr_res).
      { destruct arr_res as [|? [|? ?]]; simpl in *; try omega.
        cbv in eval_map; congruence. }
      destruct le_dec; [|false; rewrite Nat.le_min_r in *; omega].
      cut (1 <= min ((length arr_res + ntrd - 1) / ntrd) nblk); [intros; omega|].
      apply Nat.min_glb; [|omega].
      apply Nat.div_le_lower_bound; eauto.
      rewrite Nat.mul_1_r.
      omega.
Qed.

Inductive skelE_wf GA : forall fty, Skel.SkelE GA fty -> Prop := 
| wf_Map dom cod (f : Skel.Func GA (Skel.Fun1 dom cod)) ae :
    skelE_wf GA cod (Skel.Map _ _ _ f ae)
| wf_Reduce typ (f : Skel.Func GA (Skel.Fun2 typ typ typ)) ae f_tot :
    (forall aeenv (x y : Skel.typDenote typ), Skel.funcDenote GA (Skel.Fun2 typ typ typ) f aeenv x y = Some (f_tot x y))
    -> (forall x y : Skel.typDenote typ, f_tot x y = f_tot y x)
    -> (forall x y z : Skel.typDenote typ, f_tot (f_tot x y) z = f_tot x (f_tot y z))
    -> skelE_wf GA typ (Skel.Reduce _ _ f ae)
| wf_Seq start l : skelE_wf GA Skel.TZ (Skel.Seq GA start l)
| wf_Zip t1 t2 ae1 ae2 : skelE_wf GA (Skel.TTup t1 t2) (Skel.Zip _ t1 t2 ae1 ae2).

Lemma mapM_total A B (f : A -> B) (l : list A) : mapM (fun i => Some (f i)) l = Some (map f l).
Proof.
  induction l; simpl; eauto.
  unfold mapM in *; simpl.
  unfold bind; simpl in *; unfold Monad.bind_opt in *.
  rewrite IHl; eauto.
Qed.
Lemma mapM_eq A B (f g : A -> option B) (l : list A) :
  (forall x, f x = g x) -> mapM f l = mapM g l.
Proof.
  induction l; simpl; intros; eauto.
  unfold mapM in *; simpl.
  unfold bind; simpl in *; unfold Monad.bind_opt in *.
  rewrite IHl, H; eauto.
Qed.

Lemma lexp2sexp_ok GA typ le GS aeenv seenv :
  Skel.sexpDenote GA GS typ (lexp2sexp GA typ le GS) aeenv seenv = Some (Skel.lexpDenote GA typ le aeenv).
Proof.
  dependent induction le; simpl; eauto.
  rewrite IHle1.
  unfold bind; simpl; unfold Monad.bind_opt; simpl.
  rewrite IHle2; eauto.
Qed.

Lemma zip_AE_ok GA typ1 typ2 (arr1 : Skel.AE GA typ1) (arr2 : Skel.AE GA typ2) aeenv :
  Skel.aeDenote _ _ (zip_AE arr1 arr2) aeenv =
  (do! a1 <- Skel.aeDenote _ _ arr1 aeenv in
   do! a2 <- Skel.aeDenote _ _ arr2 aeenv in
   ret (SkelLib.zip a1 a2)).
Proof.
  unfold zip_AE.
  Lemma darr_of_arr_ok GA typ (arr : Skel.AE GA typ) f len :
    darr_of_arr arr = (f, len)
    -> Skel.aeDenote _ _ arr = Skel.aeDenote _ _ (Skel.DArr _ _ (Skel.F1 _ _ _ f) len).
  Proof.
    destruct arr; intros H; inverts H; simpl.
    - extensionality l.
      destruct Z_le_dec; [|false; forwards*: Zle_0_nat].

      Lemma mapM_ex_some A B (f : A -> option B) l :
        Forall (fun x => exists t, x = Some t) (map f l) 
        -> exists t, mapM f l = Some t.
      Proof.
        induction l; simpl; intros H; inverts H.
        - eexists; reflexivity.
        - destruct H2.
          destruct IHl; eauto.
          exists (x :: x0).
          unfold mapM; simpl.
          unfold bind; simpl; unfold Monad.bind_opt.
          rewrite H.
          unfold mapM in H0; rewrite H0; eauto.
      Qed.
      forwards* (res & Hres): (>>mapM_ex_some
                                 (fun i : val => do! v <- ret i in SkelLib.nth_error (hget l m) v)
                                 (SkelLib.seq 0 (G.Zn (Datatypes.length (hget l m))))).
      rewrite Forall_forall; intros.
      rewrite in_map_iff in H; destruct H as (? & ? & ?).
      unfold SkelLib.seq in H0.
      Lemma option_ret_LI A B (v : A) (f : A -> option B) :
        (do! x <- ret v in f x) = f v.
      Proof.
        unfold ret, bind; simpl; eauto.
      Qed.
      rewrite option_ret_LI in H.
      Lemma seq'_In i s n :
        In i (SkelLib.seq' s n) -> (s <= i < s + Zn n)%Z.
      Proof.
        revert s; induction n; simpl; try tauto.
        intros.
        rewrite Zpos_P_of_succ_nat.
        destruct H; [substs; nia|].
        apply IHn in H.
        omega.
      Qed.
      apply seq'_In in H0.
      forwards*: (>>nth_error_some' (hget l m) x0 (@defval' t)).
      rewrite Nat2Z.id in *.
      omega.
      substs; eexists; eauto.
      unfold SkelLib.comp in *.
      rewrite Hres.
      unfold ret; simpl; f_equal.
      forwards*: SkelLib.mapM_length.
      rewrite seq_length, Nat2Z.id in H.
      apply (@eq_from_nth _ defval'); eauto.
      intros.
      forwards*: (>>SkelLib.mapM_some i (0%Z) (@defval' t) Hres).
      rewrite seq_length, Nat2Z.id, option_ret_LI, SkelLib.seq_nth, Nat2Z.id in H1.
      destruct lt_dec; [|omega].
      rewrites (>>SkelLib.nth_error_some' (@defval' t)) in H1; [omega|].
      inverts H1; eauto.
      rewrite Z.add_0_l, Nat2Z.id in H3; eauto.
    - dependent destruction f0; inverts H1; simpl.
      extensionality x; simpl.
      eauto.
  Qed.
  destruct (darr_of_arr arr1) as [body1 len1] eqn:Heq1.
  destruct (darr_of_arr arr2) as [body2 len2] eqn:Heq2.
  rewrites* (>>darr_of_arr_ok Heq1).
  rewrites* (>>darr_of_arr_ok Heq2).
  simpl.
  repeat (destruct Z_le_dec; try rewrite Z.min_glb_iff in *; try lia); simpl; eauto.
  2: destruct mapM; simpl; eauto.
Abort.

Lemma compile_skel_ok GA ntrd nblk typ
      (avenv : AVarEnv GA) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA)
      (result : Skel.aTypDenote typ)
      Gp skelE R P E:
  ntrd <> 0 -> nblk <> 0
  -> skelE_wf GA _ skelE 
  -> Skel.skelDenote GA typ skelE aeenv = Some result
  -> CMsat (Ga (kernelInv avenv apenv aeenv (TT *** R) P E 1) Gp)
           (compile_Skel ntrd nblk skelE avenv)
           (fun res => Ga (Ex ps, kernelInv avenv apenv aeenv
                                            (arrays (val2gl ps) (arr2CUDA result) 1%Qc *** TT *** R)
                                            P
                                            (fst res |-> Zn (length result)  :: snd res |=> ps ++ E) 1%Qc) Gp).
Proof.
  destruct skelE; simpl; eauto using compile_map_ok, compile_reduce_ok.
  - intros.
    inverts H1.
    intros; applys* compile_reduce_ok.
  - intros; applys* compile_map_ok.
    inverts H2; simpl.
    destruct Z_le_dec; eauto.
    erewrite mapM_eq.
    Focus 2. {
      intros.
      rewrite lexp2sexp_ok.
      unfold bind; simpl; unfold Monad.bind_opt; simpl.
      reflexivity. } Unfocus.
    rewrite !mapM_total.
    unfold bind; simpl.
    rewrite !mapM_total.
    rewrite !map_id.
    unfold ret; simpl; f_equal.
    applys* (>>eq_from_nth 0%Z).
    rewrite map_length, !seq_length; eauto.
    introv; rewrite map_length, !seq_length; intros.
    rewrites (>>nth_map 0%Z).
    { rewrite seq_length; eauto. }
    rewrite !seq_nth.
    destruct lt_dec; omega.
  - intros; applys* compile_map_ok.
    simpl in *.
    unfold zip_AE; simpl.
    destruct (darr_of_arr a) as [body1 len1] eqn:Heq1.
    destruct (darr_of_arr a0) as [body2 len2] eqn:Heq2.
    simpl.
    rewrites* (>>darr_of_arr_ok Heq1) in H2.
    rewrites* (>>darr_of_arr_ok Heq2) in H2.
    simpl in *.
    destruct Z_le_dec.
    
    repeat (destruct Z_le_dec; try rewrite Z.min_glb_iff in *; try lia); simpl; eauto.
    2: destruct mapM; unfold bind in *; simpl in *; eauto.
    2: destruct mapM; unfold bind in *; simpl in *; try congruence.
    destruct (mapM _ (SkelLib.seq _ _)) eqn:Hmap1; [|unfold bind in H2; simpl in *; congruence].
    destruct (mapM _ (SkelLib.seq 0 (Skel.lexpDenote GA Skel.TZ len2 aeenv))) eqn:Hmap2;
      unfold bind in H2; simpl in *; [|congruence].
    inverts H2.
    destruct (mapM _ (SkelLib.seq _ (Z.min _ _))) eqn:Hmap3; unfold bind, ret; simpl.
    + rewrite mapM_total, map_id.
      f_equal.
      forwards* Hlen1: (>>SkelLib.mapM_length Hmap1); rewrite SkelLib.seq_length in Hlen1.
      forwards* Hlen2: (>>SkelLib.mapM_length Hmap2); rewrite SkelLib.seq_length in Hlen2.
      forwards* Hlen3: (>>SkelLib.mapM_length Hmap3); rewrite SkelLib.seq_length in Hlen3.
      rewrite Z2Nat.inj_min in Hlen3.
      unfold SkelLib.zip.
      apply (@eq_from_nth _ (@defval' (Skel.TTup t1 t2))).
      { simpl; rewrite (combine_length l2 l3); nia. }
      { intros.
        Lemma nth_combine A B (l1 : list A) (l2 : list B) i d :
          nth i (combine l1 l2) d =
          if Sumbool.sumbool_and _ _ _ _ (lt_dec i (length l1)) (lt_dec i (length l2))
          then (nth i l1 (fst d), nth i l2 (snd d)) 
          else d.
        Proof.
          revert i l2; induction l1; intros [|i] [|? l2]; simpl; eauto; destruct lt_dec; eauto.
          specialize (IHl1 i l2); simpl in *; destruct Sumbool.sumbool_and, lt_dec; eauto; try omega.
          specialize (IHl1 i l2); simpl in *; destruct Sumbool.sumbool_and, lt_dec; eauto; try omega.
        Qed.          

        rewrite (nth_combine _ _ l2 l3); destruct Sumbool.sumbool_and; try nia.
        2: simpl in *; rewrite Hlen3, Nat.min_glb_lt_iff in H2; omega.
        simpl.
        forwards*Hmap1': (>>SkelLib.mapM_some i (0%Z) (@defval' t1) Hmap1).
        rewrite !SkelLib.seq_length in Hmap1'; destruct lt_dec; try omega.
        rewrite seq_nth in Hmap1'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap1'.
        forwards*Hmap2': (>>SkelLib.mapM_some i (0%Z) (@defval' t2) Hmap2).
        rewrite !SkelLib.seq_length in Hmap2'; destruct lt_dec; try omega.
        rewrite seq_nth in Hmap2'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap2'.
        forwards*Hmap3': (>>SkelLib.mapM_some i (0%Z) (@defval' t1, @defval' t2) Hmap3).
        rewrite !SkelLib.seq_length in Hmap3'; destruct lt_dec; try omega.
        * rewrite seq_nth in Hmap3'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap3'.
          rewrite <-Hmap1' in Hmap3'; unfold bind in Hmap3'; simpl in Hmap3'.
          unfold Monad.bind_opt in Hmap3'; simpl in Hmap3.
          rewrite <-Hmap2' in Hmap3'; simpl in Hmap3'.
          inverts Hmap3'; eauto.
        * rewrite Z2Nat.inj_min, Nat.min_glb_lt_iff in *; omega. }
    + Lemma mapM_none A B (f : A -> option B) (l : list A) d :
        mapM f l = None
        -> exists i, f (nth i l d) = None /\ i < length l.
      Proof.
        unfold mapM; induction l; unfold ret, bind; simpl; eauto.
        - unfold ret, bind; simpl; congruence.
        - destruct (f a) eqn:Heq.
          2: intros; exists 0; splits; eauto; omega.
          unfold bind; simpl; unfold Monad.bind_opt.
          destruct sequence; eauto.
          + unfold ret; simpl; congruence.
          + destruct IHl; eauto.
            intros; exists (S x); simpl; splits; jauto.
            omega.
      Qed.
      forwards*: (>>mapM_none 0%Z).
      destruct H2 as [i [Heq3 Hleni]].
      rewrite seq_length, Z2Nat.inj_min, Nat.min_glb_lt_iff in Hleni.
      forwards*Hmap1': (>>SkelLib.mapM_some i (0%Z) (@defval' t1) Hmap1).
      rewrite !SkelLib.seq_length in Hmap1'; destruct lt_dec; try omega.
      rewrite seq_nth in Hmap1'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap1'.
      forwards*Hmap2': (>>SkelLib.mapM_some i (0%Z) (@defval' t2) Hmap2).
      rewrite !SkelLib.seq_length in Hmap2'; destruct lt_dec; try omega.
      rewrite seq_nth in Hmap2'; destruct lt_dec; try omega; simpl in *; rewrite Z.add_0_l in Hmap2'.
      rewrite seq_nth in Heq3; destruct lt_dec; rewrite Z2Nat.inj_min in *; simpl; try omega.
      2: rewrite Nat.min_glb_lt_iff in *; omega.
      rewrite Z.add_0_l in Heq3.
      unfold bind in Heq3; simpl in Heq3; unfold Monad.bind_opt in Heq3.
      rewrite <-Hmap1' in Heq3.
      rewrite <-Hmap2' in Heq3.
      unfold ret in Heq3; simpl in Heq3; congruence.
Qed.            

Inductive skel_as_wf GA : forall fty, Skel.AS GA fty -> Prop :=
| wf_ALet t1 t2 (skel : Skel.SkelE GA t1) (skel_as : Skel.AS (t1 :: GA) t2) :
    skelE_wf GA _ skel
    -> (skel_as_wf (t1 :: GA) _ skel_as)
    -> skel_as_wf GA _ (Skel.ALet _ _ _ skel skel_as)
| wf_ARet t m : skel_as_wf GA t (Skel.ARet _ _ m).

Lemma compile_res_ok GA typ ntrd nblk
      (avenv : AVarEnv GA) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA)
      (arr : Skel.AE GA typ) (result : Skel.aTypDenote typ)
      Gp outs outp vs :
  ntrd <> 0 -> nblk <> 0
  -> length result <= length vs
  -> Skel.aeDenote GA typ arr aeenv = Some result
  -> CMsat (Ga (kernelInv avenv apenv aeenv (TT *** arrays (val2gl outp) vs 1)
                          True
                          (outs |=> outp) 1) Gp)
           (compile_res ntrd nblk avenv arr outs)
           (fun res => Ga (kernelInv avenv apenv aeenv
                                     (TT *** arrays (val2gl outp) (arr2CUDA result ++ skipn (length result) vs) 1%Qc)
                                     True
                                     (res |-> Zn (length result) :: outs |=> outp) 1%Qc) Gp).
Proof.
  intros Hntrd0 Hnblk0 Hlen Heq1.

  assert (Heval : Skel.skelDenote GA typ (Skel.Map GA typ typ (Skel.F1 GA typ typ (Skel.EVar GA [typ] typ HFirst)) arr) aeenv =
                  Some result).
  { simpl.
    rewrite Heq1.
    unfold bind; simpl.
    rewrite mapM_total, map_id; eauto. }
  pose proof Heval as Heval'.
  (* destruct (Skel.aeDenote _ _ _ _) as [inp|] eqn:Heq1; [|inverts Heval]. *)
  (* simpl in Heval. *)
  (* destruct (SkelLib.mapM _ inp) as [out|] eqn:Heq2; inverts Heval. *)
  
  unfold compile_res.
  remember (Skel.F1 GA typ typ (Skel.EVar GA [typ] typ HFirst)).
  eapply rule_bind_s.
  { applys (>>rule_gen_kernel_s).
    3: intros; applys (>>mkMap_ok (remove_typeinfo (gen_params GA))).
    simpl; eauto.
    simpl; eauto.
    apply genenv_ok.
    applys* compile_AE_ok.
    applys* (>> compile_func_ok). }
  intros gen_map.
  eapply rule_bind_s.
  apply rule_fLet_s.
  { apply evalExp_app2; applys* eval_compile_AE_len. }
  intros outLen.
  (* apply rule_fAllocs. *)
  (* { evalExp. } *)
  (* intros outs. *)
  (* eapply rule_code_ex. *)
  (* apply hasDefval_vals. *)
  (* intros ps. *)
  (* apply rule_code_ex. *)
  (* apply listA_hasDefval. *)
  (* intros vs. *)
  eapply rule_bind_s.
  { eapply rule_invokeKernel_s.
    - unfold K; rewrite !in_app_iff; simpl; eauto.
    - simpl; eauto.
    - simpl; rewrite !map_app, !app_length, !map_length, !flatTup_length; eauto.
      do 2 f_equal.
      rewrite flatten_aenv_avars_length; eauto.
    - repeat econstructor.
    - apply has_no_vars_kernelInv'.
    - simpl.
      do 3 (apply evalExpseq_cons; [evalExp|]).
      simpl; rewrite map_app; apply evalExpseq_app.
      (* apply evalExpseq_app1. *)
      apply evalExpseq_flatTupxs, incl_tl, incl_appl; eauto.
      apply evalExpseq_cons2.
      apply evalExpseq_app2; apply evalExpseq_arrInv.
    - eauto.
    - eauto.
    - simpl.
      rewrite !map_app.
      intros _; splits; eauto.
      + rewrite subst_env_app; split.
        * unfold outArr.
          repeat (apply subst_env_cons2; [rewrite map_flatTup; apply locals_not_in; simpl; eauto|]).  
          apply subst_env_app1.
          rewrite out_name_locals.
          apply subst_env_flatTup; apply locals_disjoint_ls.
        * do 2 (apply subst_env_cons2; [applys* arrInvVar_nin; apply genenv_ok|]).
          apply subst_env_cons2.
          apply inp_len_name_arrInvVar.
          apply subst_env_app2.
          rewrite map_length, !flatTup_length; eauto.
          apply out_name_arrInvVar.          
          apply subst_env_params.
    - intros _; splits; eauto.      
      instantiate (1 := result).
      unfold Skel.skelDenote in Heval; rewrite Heq1 in Heval; apply Heval.
      instantiate (1 := firstn (length result) vs).
      rewrite firstn_length; destruct lt_dec; try omega.
    - intros; rewrite <-res_assoc.
      rewrites (>>arrays_split (length result)) in H0.
      repeat sep_cancel'.
      eauto. }
  introv; simpl.

  apply rule_ret_s.
  unfold K.
  introv.

  - unfold K; apply gassnInv_imp_s; simpl.
    unfold incl; introv; simpl; rewrite !in_app_iff; simpl; eauto.
    
    introv; unfold kernelInv, kernelInv'.
    rewrite fv_assn_sep_eq in *; intros (? & ? & (Hin1 & Hin2 & Heq)).
    rewrite !fv_assn_base_eq in *.
    simpl in *.
    simpl; repeat (rewrite !map_app in *; simpl in *).
    unfold incl in *; simpl in *; intros a Hin3.
    specialize (Hin1 a); specialize (Hin2 a); specialize (Heq a).
    repeat (rewrite !in_app_iff in *; simpl in *).
    rewrite !map_flatTup in *.
    tauto.

  - unfold K; simpl.
    introv. 
    rewrite app_comm_cons, kernelInv'_combine; revert s h; prove_imp.
    rewrites (>>arrays_split (length result)).
    rewrite <-!res_assoc in *.
    repeat sep_cancel'.
    rewrite firstn_app.
    cutrewrite (length result = length (arr2CUDA result)); [|unfold arr2CUDA; rewrites* map_length ].
    rewrite firstn_length_self.
    rewrite minus_diag; simpl.
    rewrite app_nil_r; eauto.
    Lemma skipn_app A n (ls1 ls2 : list A) :
      skipn n (ls1 ++ ls2) = skipn n ls1 ++ skipn (n - length ls1) ls2.
    Proof.
      revert n ls2; induction ls1; simpl; intros [|n] [|? ls2]; eauto.
    Qed.
    rewrite skipn_app.
    cutrewrite (length result = length (arr2CUDA result)); [|unfold arr2CUDA; rewrites* map_length ].
    Lemma drop_oversize:
      forall (T : Type) (n : nat) (s : list T ), length s <= n -> skipn n s = nil.
    Proof.
      induction n; destruct s; simpl; intros; try omega; eauto.
      apply IHn; omega.
    Qed.
    rewrites (>>drop_oversize (arr2CUDA result)); simpl; eauto.
    rewrite minus_diag; simpl; eauto.
Qed.
        
Theorem compile_AS_ok GA ntrd nblk typ
      (avenv : AVarEnv GA) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA)
      (result : Skel.aTypDenote typ)
      Gp skel_as (outs : vars typ) outp vs :
  ntrd <> 0 -> nblk <> 0
  -> length result <= length vs
  -> skel_as_wf GA _ skel_as
  -> Skel.asDenote GA typ skel_as aeenv = Some result
  -> CMsat (Ga (kernelInv avenv apenv aeenv 
                          (TT *** arrays (val2gl outp) vs 1)
                          True
                          (outs |=> outp) 1) Gp)
           (compile_AS ntrd nblk skel_as outs avenv)
           (fun res => Ga (kernelInv avenv apenv aeenv
                                     (TT *** arrays (val2gl outp) (arr2CUDA result ++ skipn (length result) vs) 1%Qc)
                                     True
                                     (res |-> Zn (length result) :: outs |=> outp) 1%Qc) Gp).
Proof.
  dependent induction skel_as; simpl.
  - intros.
    inverts H2.
    destruct Skel.skelDenote eqn:Heq; [|inverts H3].
    unfold bind in *; simpl in H3; unfold Monad.bind_opt in H3; simpl in H3.
    destruct Skel.asDenote eqn:Heq'; inverts H3.
    eapply rule_bind_s.
    { unfold K.
      applys* compile_skel_ok. }
    intros.
    apply rule_code_ex_s.
    { apply hasDefval_vals. }
    intros ps; unfold K.
    eapply rule_equiv_mono_pre_s.
    { intros stk h Hsat.
      instantiate (1 := kernelInv (v ::: avenv) (ps ::: apenv) (a ::: aeenv) (TT *** arrays (val2gl outp) vs 1) True (outs |=> outp) 1).
      unfold kernelInv in Hsat |- *; revert stk h Hsat; prove_imp.
      - unfold arrInvVar in *; simpl in *.
        destruct v; simpl in *.
        rewrite in_app_iff in H4.
        eauto.
        destruct H4 as [? | [? | ?]]; eauto.
      - unfold arrInvRes in *; simpl.
        rewrite <-res_assoc.
        repeat sep_cancel'. }
    { introv.
      unfold kernelInv; rewrite !fv_assn_base_eq; simpl.
      intros Hincl t Hin; apply Hincl; simpl in *.
      unfold arrInvVar in Hin; simpl in *.
      destruct v; simpl in *.
      rewrite map_app, in_app_iff in *.
      simpl in Hin.
      rewrite map_app, in_app_iff in *.
      destruct Hin as [? | [? | [? | ?]]]; eauto. }
    eapply rule_backward_s; [apply IHskel_as; eauto|..].
    + simpl; eauto.
    + introv; apply gassnInv_imp_s; simpl; eauto.
      introv Hfv.
      unfold kernelInv in *; simpl in *; rewrite !fv_assn_base_eq in *; simpl.
      intros var Hin; apply Hfv.
      unfold arrInvVar in Hin; simpl in *.
      destruct v; simpl in *.
      rewrite map_app, in_app_iff in *.
      simpl.
      rewrite map_app, in_app_iff.
      destruct Hin as [? | [? | ?]]; eauto.
    + intros ? stk h Hsat; revert stk h Hsat; prove_imp.
      * unfold arrInvVar in *; simpl.
        rewrite in_app_iff; eauto.
      * unfold arrInvRes in *; simpl in *.
        rewrite <-res_assoc in H3; sep_cancel'.
        rewrite res_comm.
        sep_cancel'.
        eauto.
  - intros.
    applys* compile_res_ok.
Qed.

Lemma fc_ok_M_app2 M1 M2 G :
  disjoint (map fst M1) (map fst M2)
  -> fc_ok M2 G -> fc_ok (M1 ++ M2) G.
Proof.
  induction G as [|[? ?] ?]; simpl; eauto.
  intros; split; jauto.
  apply fn_ok_ignore; jauto.
  intros Hin.
  forwards*: (>>disjoint_not_in_r H); simpl; eauto.
  Lemma fn_ok_In M fn fs :
    Host.fn_ok M fn fs -> In fn (map fst M).
  Proof.
    unfold Host.fn_ok.
    intros; destruct func_disp eqn:Heq; try tauto.
    intros; forwards*: (func_disp_in').
  Qed.
  forwards*: fn_ok_In.
Qed.

Definition CSLfd_simp M P fd Q n := 
  match fd with
  | Host f => CSLhfun_n_simp M P f Q n
  | Kern k => CSLkfun_n_simp P k (Q 0%Z) n
  end.

Definition CSLf_simp M P f Q n :=
  match func_disp M f with
  | None => False
  | Some fd => CSLfd_simp M P fd Q n
  end.

Definition CSLfd M G P fd Q := with_ctx M G (fun n => CSLfd_simp M P fd Q n).
Definition CSLf M G P f Q := with_ctx M G (fun n => CSLf_simp M P f Q n).

Inductive ftri_inhabitant : FTri -> Prop :=
| FAll_inhabitant T (f : T -> FTri) :
    hasDefval T ->
    (forall x, ftri_inhabitant (f x)) ->
    ftri_inhabitant (FAll T f)
| FDbl_inhabitant P Q : ftri_inhabitant (FDbl P Q).

Lemma CSLf_interp_f M G f tag params ftri :
  ftri_inhabitant ftri
  -> interp_ftri ftri (fun P Q => CSLf M G P f Q)
  -> interp_f M G f (FS tag params ftri).
Proof.
  unfold interp_f, CSLf, with_ctx, interp_f_n, CSLf_simp, interp_fd_simp, CSLfd_simp,
  interp_hfun_n_simp, interp_kfun_n_simp.
  induction 1; simpl in *; intros. 
  - destruct func_disp as [[? | ?]|]; [intros x; forwards*: (>>H x)..|].
    specialize (H1 default); eauto.
  - apply H; eauto.
Qed.

Global Instance hlist_hasDefval A f (G : list A) : (forall (x : A), hasDefval (f x)) -> hasDefval (hlist f G).
Proof.
  constructor.
  induction G.
  - apply HNil.
  - apply (default ::: IHG).
Qed.

Lemma CSLh_CSLhfun M G params body ret v P Q' Q :
  CSLh M G P body Q'
  -> (forall s h, sat s h Q' -> s ret = v)  
  -> Q' |= Q v
  -> CSLhfun M G P (Hf params body ret) Q.
Proof.
  unfold CSLh, CSLhfun, with_ctx, CSLh_n_simp, CSLhfun_n_simp; intros; simpl.
  forwards*: H.
  
  Lemma safe_nh_safe_nhfun M n s h body ret Q' Q v :
    safe_nh M n s h body Q'
    -> (forall s h, sat s h Q' -> s ret = v)
    -> Q' |= Q v
    -> safe_nhfun M n s h body ret Q.
  Proof.
    revert s h body; induction n; simpl; eauto.
    introv (Hskip & Hsafe & Hstep) Hret HQ; splits; jauto.
    - intros; forwards*: Hskip.
      erewrite Hret; eauto.
    - introv Hdis Htoh Hexec; forwards*(h'' & ? & ? & ?): Hstep.
  Qed.

  eapply safe_nh_safe_nhfun; eauto.
Qed.

Lemma CSLhfun_pure_prem M G R (P : Prop) E hf Q :
  (P -> CSLhfun M G (Assn R P E) hf Q)
  -> CSLhfun M G (Assn R P E) hf Q.
Proof.
  intros H.
  intros n Hctx vs s h Hbind Hsat.
  unfold sat in Hsat; simpl in Hsat.
  unfold CSLhfun, with_ctx, CSLhfun_n_simp in H.
  applys* (>>H vs).
Qed.

Lemma CSLfd_host M G P hf Q:
  CSLhfun M G P hf Q -> CSLfd M G P (Host hf) Q.
Proof.
  eauto.
Qed.

Lemma fnOk'_In fn fns m :
  fnOk' fns m -> In fn fns -> exists n, fn = kname n /\ n < m.
Proof.
  unfold fnOk'; rewrite Forall_forall; eauto.
Qed.

Theorem compile_prog_ok GA typ ntrd nblk (p : Skel.AS GA typ) :
  ntrd <> 0 -> nblk <> 0
  -> skel_as_wf GA typ p 
  -> interp_f (compile_prog ntrd nblk p) nil "__main"
    {| fs_tag := Hfun;
       fs_params := inp_len_name :: flatTup (outArr typ) ++ map fst (flatten_avars (gen_params (List.rev GA)));
       fs_tri := 
         All aeenv apenv outp result vs,
         FDbl (kernelInv (remove_typeinfo (gen_params GA)) apenv aeenv
                         (TT *** arrays (val2gl outp) vs 1)
                         (Skel.asDenote GA typ p aeenv = Some result /\ length result <= length vs)
                         (outArr typ |=> outp) 1)
              (fun l => kernelInv' apenv aeenv
                                   (TT *** arrays (val2gl outp) (arr2CUDA result ++ skipn (length result) vs) 1%Qc)
                                   (l = Zn (length result)) 1%Qc) |}.
Proof.
  intros.
  apply CSLf_interp_f.
  repeat constructor.
  { apply hlist_hasDefval; intros.
    constructor; apply nil. }
  { apply hlist_hasDefval; intros.
    constructor; apply defval. }
  { apply defval. }
  simpl.
  intros aeenv apenv outp result vs.

  intros.
  unfold compile_prog.
  destruct compile_AS as [res [[[n m] ss] kers]] eqn:Heq.

  apply CSLfd_host.

  apply CSLhfun_pure_prem; intros [? ?].

  forwards Hok: (>>compile_AS_ok ntrd nblk (remove_typeinfo (gen_params GA)) apenv aeenv (outArr typ) outp);
    [eauto | eauto | ..]; eauto.
  forwards* (Hfc_ok & Hdisj & Hfn & Hsat & Hcsl): (>>ST_ok_exec_s (@nil fdecl) Hok); try now constructor.
  { eexists; unfold kernelInv; rewrite fv_assn_base_eq.
    splits; eauto.
    introv; rewrite map_app, in_app_iff, map_flatTup.
    intros [Hin | Hin] Hc; substs.
    - unfold outArr in Hin.
      apply locals_not_in in Hin; eauto.
    - forwards*: (>>arrInvVar_nin Hin).
      apply genenv_ok. }
  simpl in *.

  eapply CSLh_CSLhfun.
  applys* (>>CSLh_n_weaken kers); simpl; eauto.
  - split; jauto.
    intros Hin; forwards*(? & Hfn' & _): fnOk'_In.
    unfold kname in Hfn'; cbv in Hfn'; congruence.    
  - eapply rule_host_forward; [apply Hcsl|..]; unfold kernelInv; prove_imp.
  - applys* incl_tl.
  - introv Hsat'.
    unfold sat, kernelInv in Hsat'; simpl in Hsat'.
    jauto.
  - unfold kernelInv, kernelInv'; prove_imp; try tauto.
Qed.