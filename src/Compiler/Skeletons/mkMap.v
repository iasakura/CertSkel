Require Import LibTactics Psatz.
Require Import GPUCSL SkelLib CSLTactics.
Require Import CUDALib TypedTerm.
Require Import Host.
Require Import CodeGen CUDALib Correctness Grid CSLTactics CSLLemma Utils.
Require Import String.
Import List.
Section mkMap.

Variable ntrd nblk : nat.

Hypothesis ntrd_neq_0: ntrd <> 0.
Hypothesis nblk_neq_0: nblk <> 0.

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
Variable arr_res : Skel.aTypDenote dom.
Hypothesis eval_arr_ok :
  Skel.aeDenote _ _ arr aeval_env = Some arr_res.
Variable result : Skel.aTypDenote cod.
Hypothesis eval_map_ok :
  Monad.mapM (Skel.funcDenote _ _ f aeval_env) arr_res = Some result.

Lemma eval_f_ok : 
  { f_res | forall i, i < length arr_res ->
                      Skel.funcDenote _ _ f aeval_env (gets' arr_res i) = Some (f_res i)}.
Proof.
  simpl in *; unfold Monad.bind_opt in *.
  lets H: eval_arr_ok; generalize arr_res H; intros ar H'; clear H.
  rewrite H' in eval_arr_ok; inverts eval_arr_ok.
  exists (fun i : nat => nth i result (defval')).
  intros i Hi.
  forwards*: (>>mapM_some i (@defval' dom) (@defval' cod)).
  destruct lt_dec; eauto; try first [nia | tauto].
Qed.

Definition f_res := let (f, _) := eval_f_ok in f.
Lemma eval_f_ok' : forall i, i < length arr_res -> Skel.funcDenote _ _ f aeval_env (gets' arr_res i) = Some (f_res i).
Proof.
  unfold f_res; destruct eval_f_ok; simpl; eauto.
Qed.

Notation out := (outArr cod).
Notation len := inp_len_name.
Notation t := (locals "t" dom 0).

Definition mkMap_cmd inv :=
  "i" :T Int ::= "tid" +C "bid" *C "ntrd" ;;
  WhileI inv ("i" <C len) (
    assigns_get t arr_c "i" ;;
    writes_call1 (v2gl out +os "i") f_c t ;;
    "i" ::= "ntrd" *C "nblk" +C "i"
  ).

Definition mkMap_prog :=
  Pr nil (mkMap_cmd Emp_assn).

Definition mkMap : kernel :=
  let arr_vars := gen_params GA in
  let params_in := flatten_avars arr_vars in
  let params_out := (inp_len_name, Int) :: flatTup (out_name cod) in
  {| params_of := params_out ++ params_in;
     body_of := mkMap_prog |}.

Notation p := (RP (nblk * ntrd)).

Variable outp : vals cod.
Variable outs : list (vals cod).
Hypothesis outs_length : length outs = length result.
Definition outRes (ls : list (vals cod)) := arrays (val2gl outp) ls 1.
Definition outEnv := out |=> outp.

Notation result' := (arr2CUDA result).

Section thread_ok.
Variable tid : Fin.t ntrd.
Variable bid : Fin.t nblk.


Lemma tid_bid : nf tid + nf bid * ntrd < ntrd * nblk.
Proof.
  pose proof ntrd_neq_0; pose proof nblk_neq_0.
  assert (nf tid < ntrd) by eauto.
  assert (nf bid < nblk) by eauto.
  forwards*: (>>id_lt_nt_gr H1 H2).
  lia.
Qed.

Notation arri a := (skip a (ntrd * nblk) (nf tid + nf bid * ntrd)).

Definition inv'  :=
  Ex j i,
  (kernelInv avar_env aptr_env aeval_env 
             (arrays' (val2gl outp) (arri (firstn i result' ++ skipn i outs)) 1) 
             (i = j * (ntrd * nblk) + (nf tid + nf bid * ntrd) /\
              i < length arr_res + ntrd * nblk)
             (len |-> Zn (length arr_res) ::
              "i" |-> Zn i ::
              "nblk" |-> Zn nblk ::
              "ntrd" |-> Zn ntrd ::
              out |=> outp) p).

Ltac t :=
  autorewrite with pure; simpl;
  abstract (repeat match goal with
                   | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia); try lia
                   | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia); try lia
                   end;
             do 2 f_equal; lia). 


Lemma ok1 n m j : n + (j * n + m) = (S j) * n + m. nia. Qed.
Lemma ok2 n m : m = 0 * n + m. nia. Qed.
Lemma ntrd_nblk_neq_0 : ntrd * nblk <> 0. pose ntrd_neq_0; pose nblk_neq_0; nia. Qed.

Hint Resolve ok1 ok2 tid_bid ntrd_nblk_neq_0 : pure_lemma.

Lemma loop_inv_ok i j vs (varr vout : list (vals cod)) v:
  i = j * (ntrd * nblk) + (nf tid + nf bid * ntrd) ->
  vs = firstn i varr ++ skipn i vout ->
  (Zn i < Zn (length varr))%Z ->
  length varr = length vout ->
  v = gets varr i ->
  arri (set_nth i vs v) =
  arri (firstn (ntrd * nblk + i) varr ++ skipn (ntrd * nblk + i) vout).
Proof.
  intros; substs.
  applys (>>(@eq_from_nth) (@None (vals cod))).
  { t. }
  { intros i; repeat autorewrite with pure; simpl in *.
    destruct lt_dec; [|false; lia]; intros H.
    assert (i = j * (ntrd * nblk) + (nf tid + nf bid * ntrd) ->
            i mod (ntrd * nblk) = nf tid + nf bid * ntrd) by (intros; substs; prove_mod_eq).
    assert (ntrd * nblk <> 0) by eauto with pure_lemma.
    assert (j * (ntrd * nblk) + (nf tid + nf bid * ntrd) < i < S j * (ntrd * nblk) + (nf tid + nf bid * ntrd) ->
            i mod (ntrd * nblk) <> nf tid + nf bid * ntrd).
    { intros; applys (>>mod_between j); eauto with pure_lemma. }
    
    Time t. }
Qed.

Lemma before_loop_ok (varr vout : list (vals cod)) :
  nf tid < ntrd ->
  nf tid + nf bid * ntrd < ntrd * nblk ->
  length varr = length vout ->
  arri vout =
  arri (firstn (nf tid + nf bid * ntrd) varr ++ skipn (nf tid + nf bid * ntrd) vout).
Proof.
  intros; applys (>>(@eq_from_nth) (@None (vals cod))).
  { t. }
  { intros.
    repeat autorewrite with pure; simpl in *.
    assert (i < nf tid + nf bid * ntrd -> (i mod (ntrd * nblk)) <> nf tid + nf bid * ntrd).
    { intros; rewrite Nat.mod_small; eauto; try lia. }
    Time t. }
Qed.

Lemma after_loop_ok (varr vout : list (vals cod)) vs i :
  ~(Zn i < Zn (length varr))%Z ->
  length varr = length vout ->
  vs = firstn i varr ++ skipn i vout ->
  arri vs = arri varr.
Proof.
  intros; substs; eapply (@eq_from_nth _ None).
  { t. }
  intros i'; repeat autorewrite with pure; simpl; intros ?.
  Time t.
Qed.

Hint Resolve loop_inv_ok before_loop_ok after_loop_ok : pure_lemma.

Lemma result_nth i :
  i < length result -> gets' result i = f_res i.
Proof.
  simpl in *; unfold Monad.bind_opt in *.
  generalize arr_res eval_f_ok'  eval_arr_ok eval_map_ok; intros arr_res' ? Heq.
  (* rewrite Heq;  *)
  intros.
  forwards*: (>>mapM_some i (@defval' dom)).
  forwards*: mapM_length; eauto.
  destruct lt_dec; [|clear H1; lia ].
  rewrite H in H1; eauto.
  inverts H1.
  eauto.
Qed.

Lemma mkMap_cmd_ok BS : 
  CSL BS tid
      (kernelInv
         avar_env aptr_env aeval_env
         (arrays' (val2gl outp) (arri outs) 1)
         True
         ("tid" |-> Zn (nf tid) ::
          "bid" |-> Zn (nf bid) ::
          "nblk" |-> Zn nblk ::
          "ntrd" |-> Zn ntrd ::
          len |-> Zn (length arr_res) ::
          out |=> outp) p)
      (mkMap_cmd inv')
      (kernelInv'
         aptr_env aeval_env
         (arrays' (val2gl outp) (arri (arr2CUDA result)) 1)
         True p).
Proof.
  assert (Hlen: length arr_res = length result').
  { generalize arr_res eval_arr_ok eval_map_ok; simpl in *; unfold Monad.bind_opt in *; intros a Heq.
    intros H.
    forwards*: mapM_length; eauto.
    unfold arr2CUDA; rewrite map_length; eauto. }
  assert (Hlen' : length outs = length result').
  { unfold arr2CUDA; rewrite map_length; eauto. }
  forwards*: (>>nf_lt tid).
  forwards*: (tid_bid).
  eapply rule_seq.
  hoare_forward_prim'; simplify_remove_var.
  unfold inv'.

  hoare_forward; simplify_remove_var.
  hoare_forward; simplify_remove_var.
  eapply rule_seq.
  applys (>>writes_call1_ok);
    [eauto| | eauto| eauto| prove_not_local| evalExps| evalLExps| evalExp| eauto |..].
  intros; apply eval_f_ok'; lia.
  2: intros; sep_cancel'; eauto.
  intros; simpl; prove_pure.

  hoare_forward; simplify_remove_var.

  unfold kernelInv; prove_imp.
  eapply loop_inv_ok; eauto; prove_pure.
  unfold arr2CUDA; rewrites (>>nth_map (@defval cod)); prove_pure.
  rewrite result_nth; eauto; lia.
  prove_imp; eauto with pure_lemma.
  unfold kernelInv; simpl in *.
  prove_imp; eauto with pure_lemma; try tauto.
  eapply after_loop_ok; [..|eauto]; prove_pure.
Qed.
End thread_ok.

Section block_ok.
Variable bid : Fin.t nblk.

Definition ith_pre (tid : Fin.t ntrd) :=
  (kernelInv
     avar_env aptr_env aeval_env
     (arrays' (val2gl outp) (skip outs (ntrd * nblk) (nf tid + nf bid * ntrd)) 1)
     True
     ("bid" |-> Zn (nf bid) ::
      "nblk" |-> Zn nblk ::
      "ntrd" |-> Zn ntrd ::
      len |-> Zn (length arr_res) ::
      out |=> outp) p).

Definition ith_post (tid : Fin.t ntrd) :=
  (kernelInv'
     aptr_env aeval_env
     (arrays' (val2gl outp) (skip (arr2CUDA result) (ntrd * nblk) (nf tid + nf bid * ntrd)) 1)
     True
     p).

Definition jth_pre : assn :=
  kernelInv
    avar_env aptr_env aeval_env 
    (fin_star ntrd (fun i => arrays' (val2gl outp) (skip outs (ntrd * nblk) (i + (nf bid) * ntrd)) 1))
    True
    ("nblk" |-> Zn nblk ::
     "ntrd" |-> Zn ntrd ::
     len |-> Zn (length arr_res) ::
     out |=> outp) (p * injZ (Zn ntrd)).

Definition jth_post : assn :=
  kernelInv'
    aptr_env aeval_env 
    (fin_star ntrd (fun i => arrays' (val2gl outp) (skip result' (ntrd * nblk) (i + (nf bid) * ntrd)) 1))
    True (p * injZ (Zn ntrd)).

Definition E := fun x : var =>
  if prefix "_" (str_of_var x) then Lo
  else if var_eq_dec "bid" x then Lo
  else if var_eq_dec "ntrd" x then Lo
  else if var_eq_dec "nblk" x then Lo
  else Hi.

Definition BS (n : nat) := default ntrd.

Lemma mkMap_cmd_ok_b :
  CSLp ntrd E
       (jth_pre ** Assn Emp True ("bid" |-> Zn (nf bid) :: nil))
       (mkMap_cmd Emp_assn)
       jth_post.
Proof.
  unfold jth_pre, jth_post.
  applys (>>rule_block BS E (MyVector.init ith_pre) (MyVector.init ith_post)); eauto;
  unfold BS, ith_pre, ith_post.
  - unfold default; split; intros; simpl; rewrite MyVector.init_spec; prove_low_assn.
  - unfold default; split; intros; simpl; rewrite MyVector.init_spec; prove_precise.
  - intros s h; rewrite kernelInv_var_in; revert s h; prove_istar_imp.
  - prove_istar_imp.
  - unfold E; introv; rewrite MyVector.init_spec; prove_low_assn.
  - unfold E; introv; rewrite MyVector.init_spec.
    apply low_assn_vars; simpl in *; tauto.
  - unfold E, mkMap_cmd.
    instantiate (1 := Hi).
    unfold assigns_get, writes_call1; repeat prove_typing_cmd.
  - intros; rewrite !MyVector.init_spec.
    eapply rule_conseq; eauto using mkMap_cmd_ok.
    unfold kernelInv; introv; rewrite assn_var_in; revert s h; prove_imp.    
Qed.

End block_ok.    

Require Import QArith.
Close Scope Q_scope.
Lemma n_neq_0_Q n :
  n <> 0 -> ~(inject_Z (Zn n) == 0)%Q.
Proof.
  intros.
  destruct n; try lia.
  lets: (>>inject_Z_Sn_gt0 n).
  lra.
Qed.

Hint Resolve n_neq_0_Q.

Lemma mkMap_prog_ok :
  CSLg ntrd nblk
       (kernelInv avar_env aptr_env aeval_env
                  (arrays (val2gl outp) outs 1)
                  True
                  ("nblk" |-> Zn nblk ::
                   "ntrd" |-> Zn ntrd ::
                   len |-> Zn (length arr_res) :: 
                   out |=> outp) 1)
       mkMap_prog
       (kernelInv' aptr_env aeval_env 
                  (arrays (val2gl outp) result' 1)
                  True 1).
Proof.
  assert (Heq : (p * injZ (Zn ntrd) = 1 / injZ (Zn nblk))%Qc).
  { unfold injZ; Qc_to_Q.
    rewrite Nat2Z.inj_mul, inject_Z_mult. 
    field; eauto. }
  assert (Heq' : (1 = RP nblk * injZ (Zn nblk))%Qc).
  { unfold injZ; Qc_to_Q; field; eauto. }    
  applys* (>> rule_grid E (MyVector.init jth_pre) (MyVector.init jth_post));
  unfold jth_pre, jth_post; repeat rewrite Heq.
  - intros s h H; rewrite Heq' in H; revert s h H.
    prove_istar_imp.
    simpl_nested_istar.
    rewrite CodeGen.array'_ok.
    rewrite <-Heq' in *; eauto.
    intros; rewrite mult_comm; apply Nat.mod_upper_bound; nia.
  - unfold kernelInv; introv; rewrite !MyVector.init_spec.
    apply CSLp_preprocess; simpl.
    destruct locs; destruct vss; simpl; try lia.
    unfold sh_spec_assn; simpl.
    intros _ _; eapply rule_p_backward; [|intros; rewrite Assn_combine in *; eauto].
    apply rule_p_assn; intros.
    eapply rule_p_conseq; try applys (>>mkMap_cmd_ok_b bid); unfold jth_pre, jth_post, kernelInv.
    + intros s h Hsat; rewrite assn_var_in; revert s h Hsat; prove_imp.
      rewrite <-!res_assoc, Heq in *.
      repeat sep_cancel'.
    + intros s h Hsat.
      exists (@nil (list val)); fold_sat; rewrite sat_pure_l; splits; simpl; eauto.
      fold_sat; unfold sh_spec_assn'.
      revert s h Hsat; prove_imp; simpl in *; try tauto.
      rewrite <-!res_assoc, Heq in *; simpl in *.
      repeat sep_cancel'.
  - prove_istar_imp.
    simpl_nested_istar.
    rewrite <-Heq' in *.
    rewrite CodeGen.array'_ok  in *; eauto.
    intros; rewrite mult_comm; apply Nat.mod_upper_bound; nia.
  - intros; rewrite MyVector.init_spec.
    apply inde_assn_vars.
    unfold outArr, len, name_of_len.
    prove_low_expr; intros Hc; des_disj Hc; eauto; try congruence; substs.
    forwards* H': mpss_in; forwards* (? & ? & ?): (>>locals_pref H'); substs; inverts H.
    forwards* H': mpss_in; forwards* (? & ? & ?): (>>locals_pref H'); substs; inverts H.
    forwards*: aenv_ok_params; simpl in *; congruence.
    forwards*: aenv_ok_params; simpl in *; congruence.
  - intros; rewrite MyVector.init_spec.
    unfold E; prove_low_assn.
  - intros; rewrite MyVector.init_spec; unfold kernelInv. 
    apply has_no_vars_assn.
  - simpl; tauto.
  - simpl; tauto.
Qed.
End mkMap.
 
Lemma mkMap_ok M G GA dom cod arr_c (f_c : vars dom -> cmd * vars cod) pars tag avar_env arr (f : Skel.Func GA (Skel.Fun1 dom cod)) :
  aenv_ok avar_env -> ae_ok avar_env arr arr_c -> func_ok avar_env f f_c
  -> interp_kfun M G (mkMap GA dom cod arr_c f_c)
              (FS pars tag
                  (All ntrd nblk aptr_env aeval_env arr_res result outp outs,
                   FDbl (kernelInv avar_env aptr_env aeval_env (arrays (val2gl outp) outs 1)
                                   (ntrd <> 0 /\ nblk <> 0 /\ 
                                    Skel.aeDenote GA dom arr aeval_env = Some arr_res /\
                                    Monad.mapM (Skel.funcDenote GA (Skel.Fun1 dom cod) f aeval_env) arr_res = Some result /\
                                    Datatypes.length outs = Datatypes.length result)
                                   ("nblk" |-> Zn nblk :: "ntrd" |-> Zn ntrd ::
                                    inp_len_name |-> Zn (Datatypes.length arr_res) :: outArr cod |=> outp) 1)
                        (fun _ => kernelInv' aptr_env aeval_env (arrays (val2gl outp) (arr2CUDA result) 1) True 1)))%nat.
Proof.
  intros Havok ? ? n Hctx; unfold interp_kfun_n_simp; simpl.
  intros ntrd nblk aptr_env aeval_env result eval_map_ok outp outs.
  eapply (CSLkfun_threads_vars ntrd nblk (fun n m => _) (fun n m => _) (fun n m => _)).
  { unfold kernelInv; simpl.
    intros ? ?; prove_imp; try tauto.
    cbv; eauto. }
  introv.
  
  intros ? ?.
  apply CSLkfun_body; simpl.

  apply CSLg_float; intros Hprem; apply CSLg_weaken_pure.
  applys* mkMap_prog_ok.
Qed.