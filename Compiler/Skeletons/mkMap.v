Require Import LibTactics Psatz.
Require Import GPUCSL SkelLib scan_lib CSLTactics.
Require Import CUDALib TypedTerm.
Require Import Skel_lemma CSLLemma CodeGen CUDALib Correctness CSLTactics.
Require Import Host.

Open Scope string_scope.

Section mkMap.

Variable ntrd nblk : nat.

Variable GA : list Skel.Typ.
Variable avar_env : AVarEnv GA.
Variable aptr_env : APtrEnv GA.
Variable aeval_env : AEvalEnv GA.
Hypothesis Haok : aenv_ok avar_env.

Variable dom cod : Skel.Typ.
Variable arr : Skel.AE GA dom.
Variable arr_c : var -> (cmd * vars dom).
Hypothesis arr_ok : ae_ok avar_env arr arr_c.

Variable f : Skel.Func GA (Skel.Fun1 dom cod).
Variable f_c : vars dom -> (cmd * vars cod).
Hypothesis f_ok : func_ok avar_env f f_c.

Variable result : Skel.aTypDenote cod.
Hypothesis eval_map_ok :
  Skel.skelDenote _ _ (Skel.Map _ _ _ f arr) aeval_env = Some result.

Lemma eval_arr_ok :
  { arr_res | Skel.aeDenote _ _ arr aeval_env = Some arr_res}.
Proof.
  simpl in *; unfold Monad.bind_opt in *.
  destruct Skel.aeDenote; simpl in *; inverts eval_map_ok; eexists; eauto.
Qed.

Definition arr_res : Skel.aTypDenote dom := let (a, _) := eval_arr_ok in a.

Definition eval_arr_ok' : Skel.aeDenote _ _ arr aeval_env = Some arr_res.
Proof.
  unfold arr_res; destruct eval_arr_ok; eauto.
Qed.

Lemma eval_f_ok : 
  { f_res | forall i, i < length arr_res ->
                      Skel.funcDenote _ _ f aeval_env (gets' arr_res i) = Some (f_res i)}.
Proof.
  simpl in *; unfold Monad.bind_opt in *.
  lets H: eval_arr_ok'; generalize arr_res H; intros arr_res H'; clear H.
  rewrite H' in eval_map_ok.
  exists (fun i : nat => nth i result (defval')).
  intros i Hi.
  forwards*: (>>mapM_some i (@defval' dom) (@defval' cod)).
  destruct lt_dec; eauto; lia.
Qed.

Definition f_res := let (f, _) := eval_f_ok in f.
Lemma eval_f_ok' : forall i, i < length arr_res -> Skel.funcDenote _ _ f aeval_env (gets' arr_res i) = Some (f_res i).
Proof.
  unfold f_res; destruct eval_f_ok; simpl; eauto.
Qed.

Definition outArr ty := locals "_arrOut" ty 0.

Notation out := (outArr cod).
Notation len := out_len_name.
Definition t := locals "t" dom 0.

Definition mkMap_cmd inv :=
  "i" :T Int ::= "tid" +C "bid" *C Zn ntrd ;;
  WhileI inv ("i" <C len) (
    fst (arr_c "i") ;;
    assigns t (ty2ctys dom) (v2e (snd (arr_c "i"))) ;;
    fst (f_c t) ;;
    writes (v2gl out +os "i") (v2e (snd (f_c t))) ;;
    "i" ::= Zn ntrd *C Zn nblk +C "i"
  )%exp.

Definition mkMap : kernel :=
  let arr_vars := gen_params GA in
  let params_in := flatten_avars arr_vars in
  let params_out := (out_len_name, Int) :: flatTup (out_name cod) in
  {| params_of := params_out ++ params_in;
     body_of := GCSL.Pr nil (mkMap_cmd FalseP) |}.

Notation RP n := (1 / injZ (Zn n))%Qc.
Notation p := (RP (nblk * ntrd)).

Variable outp : vals cod.
Variable outs : list (vals cod).
Hypothesis outs_length : length outs = length result.
Definition outRes (ls : list (vals cod)) := arrays (val2gl outp) ls 1.
Definition outEnv := out |=> outp.

Section thread_ok.
Variable tid : Fin.t ntrd.
Variable bid : Fin.t nblk.

Notation arri a := (skip a (ntrd * nblk) (nf tid + nf bid * ntrd)).
Notation result' := (arr2CUDA result).

Definition inv'  :=
  Ex j i,
  (kernelInv avar_env aptr_env aeval_env 
             (arrays' (val2gl outp) (arri (firstn i result' ++ skipn i outs)) 1) 
             (i = j * (ntrd * nblk) + (nf tid + nf bid * nblk) /\
              i < length arr_res)
             (len |-> Zn (length arr_res) ::
              "i" |-> Zn i ::
              out |=> outp) p).

Ltac prove_not_local :=
  let x := fresh "x" in
  let H := fresh "H" in
  simpl; intros x H;
  des_disj H; substs;
  unfold is_param; simpl; try congruence.

Lemma remove_var_out ty ps x :
  prefix "_" x = false
  -> remove_var (outArr ty |=> ps) x = outArr ty |=> ps.
Proof.
  intros Hpref.
  apply remove_var_disjoint; simpl.
  unfold outArr; intros Hc.
  apply in_map_iff in Hc as (? & ? & ?); substs.
  destruct x0; simpl in *.
  apply mpss_in in H0.
  forwards* (j & Heq & ?): locals_pref; substs.
  inverts Heq; simpl in *; congruence.
Qed.

Lemma mkMap_cmd_ok BS : 
  CSL BS tid
      (kernelInv avar_env aptr_env aeval_env (arrays' (val2gl outp) (arri outs) 1)
                 True
                 ("tid" |-> Zn (nf tid)
                  :: "bid" |-> Zn (nf bid)
                  :: len |-> Zn (length arr_res)
                  :: out |=> outp) p)
      (mkMap_cmd inv')
      (kernelInv avar_env aptr_env aeval_env (arrays' (val2gl outp) (arri (arr2CUDA result)) 1) True nil p).
Proof.
  eapply rule_seq.
  applys* kernelInv_inner.
  prove_not_local. 
  hoare_forward.
  rewrite remove_var_out; eauto.
  unfold inv'; hoare_forward.
  hoare_forward.
Abort.
End thread_ok.
End mkMap.
