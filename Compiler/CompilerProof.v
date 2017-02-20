Require Import LibTactics assertion_lemmas GPUCSL TypedTerm Monad
        Host DepList CUDALib CSLLemma CSLTactics CodeGen Compiler Skel_lemma mkMap mkReduce
        Correctness CodeGenM SeqCompilerProof Program.

Definition main_spec GA :=
  let ps := gen_params GA in
  let params := flatten_avars (hmap (fun ty x => ((fst (fst x), Int), toPtr (snd x))) ps) in
  {| fs_tag := Hfun; fs_params := map fst params;
     fs_tri := (All (apEnv : APtrEnv GA) (aeEnv : AEvalEnv GA),
                FDbl (kernelInv (remove_typeinfo ps) apEnv aeEnv Emp True nil 1)
                     ((fun _ _ => True) ** (kernelInv (remove_typeinfo ps) apEnv aeEnv Emp True nil 1))) |}.

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
  map fst (flatTup (out_name typ)) = flatTup (mkMap.outArr typ).
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

Lemma rule_ret_ignore (T : Type) xs fns P Q Gp (v : T) :
  P |= Q
  -> (forall xs, fv_assn P xs -> fv_assn Q xs)
  -> ST_ok (preST xs fns P Gp) (ret v) (fun _ => postST xs fns P Q Gp Gp).
Proof.
  unfold ST_ok, preST, postST.
  introv Hpq Hfv (? & ? & ? & ? & ? & ? & ? & ? & ? & ?) Heq. 
  inverts Heq.
  destruct H as (? & ? & ? & ?).
  rewrite !app_nil_r.
  splits; [..|splits]; jauto.
  eapply rule_host_backward; eauto.
  eapply rule_host_skip.
Qed.

Lemma compile_map_ok GA dom cod ntrd nblk
      (avenv : AVarEnv GA) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA)
      (f : Skel.Func GA (Skel.Fun1 dom cod))
      (arr : Skel.AE GA dom) (result : Skel.aTypDenote cod)
      xs fns Gp :
  ntrd <> 0 -> nblk <> 0
  -> Skel.skelDenote GA cod (Skel.Map GA dom cod f arr) aeenv = Some result
  -> ST_ok (preST xs fns (kernelInv avenv apenv aeenv Emp True nil 1) Gp)
           (compile_map ntrd nblk avenv f arr)
           (fun res => postST xs fns (kernelInv avenv apenv aeenv Emp True nil 1)
                              (Ex ps len, kernelInv avenv apenv aeenv
                                                    (arrays (val2gl ps) (arr2CUDA result) 1%Qc)
                                                    True
                                                    (fst res |-> len :: snd res |=> ps) 1%Qc) Gp Gp).
Proof.
  intros Hntrd0 Hnblk0 Heval.

  unfold Skel.skelDenote in Heval.
  pose proof Heval as Heval'.
  unfold bind in Heval; simpl in Heval.
  destruct (Skel.aeDenote _ _ _ _) as [inp|] eqn:Heq1; [|inverts Heval].
  simpl in Heval.
  destruct (SkelLib.mapM _ inp) as [out|] eqn:Heq2; inverts Heval.

  unfold compile_map; simpl.
  eapply rule_bind'.
  { applys (>>rule_gen_kernel).
    3: intros; applys (>>mkMap_ok (remove_typeinfo (gen_params GA))).
    simpl; eauto.
    simpl; eauto.
    apply genenv_ok. }
  intros gen_map.
  eapply rule_bind'.
  apply rule_fLet.
  { simpl; applys* eval_compile_AE_len. }
  intros outLen.
  eapply rule_bind'.
  apply rule_fAllocs.
  { evalExp. }
  intros outs.
  eapply rule_code_ex.
  apply hasDefval_vals.
  intros ps.
  apply rule_code_ex.
  apply listA_hasDefval.
  intros vs.
  apply rule_ret_back.
  eapply rule_bind'.
  { eapply rule_invokeKernel.
    - unfold K; rewrite !in_app_iff; simpl; eauto.
    - simpl; eauto.
    - simpl; rewrite !map_app, !app_length, !map_length, !flatTup_length; eauto.
      do 2 f_equal.
      rewrite flatten_aenv_avars_length; eauto.
    - repeat econstructor.
    - do 3 (apply evalExpseq_cons; [evalExp|]).
      simpl; rewrite map_app; apply evalExpseq_app.
      apply evalExpseq_app1.
      apply evalExpseq_flatTupxs; eauto.
      apply evalExpseq_app2, evalExpseq_cons2.
      apply evalExpseq_arrInv.
    - eauto.
    - eauto.
    - simpl.
      rewrite !map_app.
      intros [? ?]; splits; eauto.
      + unfold mkMap.arr_res.
        destruct mkMap.eval_arr_ok.
        rewrite Heq1 in e; inverts e; eauto.
      + rewrite subst_env_app; split.
        * unfold mkMap.outArr.
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
      applys* compile_AE_ok.
      forwards*: (>> compile_func_ok (Skel.Fun1 dom cod)).
      instantiate (1 := result).
      instantiate (1 := vs).
      forwards*: SkelLib.mapM_length; congruence.
    - intros; rewrite <-res_assoc.
      repeat sep_cancel'.
      eauto. }
  introv; simpl.
  
  unfold K.
  eapply rule_backward.
  apply rule_ret_ignore; eauto.
  introv.
  applys* postST_imp.
  prove_imp.
  rewrite <-res_assoc in *; repeat sep_cancel'.
  apply incl_appl; eauto.
  introv; rewrite fv_assn_base; intros.
  do 2 (apply fv_assn_Ex; intros); unfold kernelInv; rewrite fv_assn_base.
  eapply incl_tran in H; eauto.
  simpl; rewrite !map_app.
  unfold incl; introv; simpl; rewrite !in_app_iff; simpl; try tauto.
  intros.
  rewrite map_flatTup in *.
  tauto.
  

  Grab Existential Variables.
  rewrite <-Heq1 in Heval'; apply Heval'.
Qed.

Theorem compile_AS_ok GA ty ntrd nblk (p : Skel.AS GA ty) :
  let M := compile_prog ntrd nblk p in
  sat_FC M nil (("__main", main_spec GA) :: nil).
Proof.
  admit.
Qed.