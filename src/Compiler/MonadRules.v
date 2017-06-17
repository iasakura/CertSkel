Require Import Monad DepList GPUCSL TypedTerm Compiler.
Require Import Program.Equality LibTactics String List.
Require Import CUDALib CodeGen CSLLemma CSLTactics Correctness mkMap.
Require Import SkelLib Psatz Host CodeGenM.

Record gassn : Type := Ga {gassn_a : assn; gassn_fc : FC}.

Definition gassnInv (P : gassn) : nat -> nat -> GModule -> Prop := fun n m M =>
  (exists xs, fv_assn (gassn_a P) xs /\ fvOk xs n) /\
  disjoint_list (map fst M) /\
  fc_ok M (gassn_fc P) /\ fnOk' (map fst M) m /\ sat_FC M (gassn_fc P) (gassn_fc P).

Definition gassnOk (P : gassn) (C : stmt) (M : GModule) (Q : gassn) := 
  CSLh M (gassn_fc Q) (gassn_a P) C (gassn_a Q).

Definition CMsat {T} (P : gassn) (gen : CUDAM T) (Q : T -> gassn) :=
  forall (n m n' m' : nat) st Mp M v,
    gassnInv P n m Mp 
    -> gen n m = (v, (n', m', st, M)) 
    -> gassnInv (Q v) n' m' (Mp ++ M) /\ gassnOk P (seqs st) (Mp ++ M) (Q v).

Lemma ST_ok_CMsat T P (gen : CUDAM T) (Q : T -> assn) G Gp :
  (ST_ok (preST nil nil P Gp) gen (fun x => postST nil nil P (Q x) Gp (G x))) 
  <-> CMsat (Ga P Gp) gen (fun x => Ga (Q x) (G x)).
Proof.
  unfold ST_ok, CMsat, preST, postST, gassnInv, gassnOk; simpl in *.
  split.
  - intros.
    destruct H0 as ((? & ? & ?) & ? & ?).
    forwards*(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?): H;
    [splits..|]; try first [now constructor|now jauto].
  - intros.
    destruct H0 as ((? & ? & ?) & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    forwards*((? & ? & ? & ? & ?) & ?): H.
    splits; try first [now constructor|now jauto].
    skip. skip.
    splits; jauto.
    Lemma Forall_app' T xs ys (P : T -> Prop) :
      Forall P (xs ++ ys) -> Forall P xs /\ Forall P ys.
    Proof.
      induction xs; simpl in *; intros; splits; try constructor; eauto.
      inverts H; eauto.
      all: forwards*: IHxs; inverts H; eauto.
    Qed.
    rewrite map_app in *.
    forwards*: (>>Forall_app' H15).
Qed.

Lemma rule_bind_s T U P (gen : CUDAM T) (gen' : T -> CUDAM U) Q R :
  CMsat P gen Q
  -> (forall v, CMsat (Q v) (gen' v) R)
  -> CMsat P (bind gen gen') R.
Proof.
  intros; apply ST_ok_CMsat; eapply rule_bind'.
  apply ST_ok_CMsat; apply H.
  intros; apply ST_ok_CMsat; apply H0.
Qed.

Lemma rule_backward_s T P (gen : CUDAM T) Q Q' :
  CMsat P gen Q
  -> (forall n' m' st Mp M v,
         gassnInv (Q v) n' m' (Mp ++ M) /\ gassnOk P (seqs st) (Mp ++ M) (Q v)
         -> gassnInv (Q' v) n' m' (Mp ++ M) /\ gassnOk P (seqs st) (Mp ++ M) (Q' v))
  -> CMsat P gen Q'.
Proof.
  unfold CMsat; intros; eauto.
Qed.  

Lemma postST_imp_s P Q Q' :
  (gassn_a Q |= gassn_a Q')
  -> incl (gassn_fc Q') (gassn_fc Q)
  -> (forall xs, fv_assn (gassn_a Q) xs -> fv_assn (gassn_a Q') xs)
  -> (forall n' m' st M,
      gassnInv Q n' m' M /\ gassnOk P (seqs st) M Q
      -> gassnInv Q' n' m' M /\ gassnOk P (seqs st) M Q').
Proof.
  unfold gassnInv, gassnOk; simpl.
  introv ? ? ? ((? & ? & ? & ? & ?) & ?); split; [splits|]; jauto.
  eapply incl_fc_ok; eauto.

  assert (sat_FC M nil (gassn_fc Q')).
  { apply rule_module_rec in H6; eauto.
    intros ? ?; eapply Forall_incl.
    apply H6; eauto.
    unfold incl; eauto. }
  apply sat_FC_strong; eauto.

  eapply rule_host_backward; [|eauto..].
  intros ? ?; forwards*: H7.
  apply rule_module_rec in H6; eauto.
  apply H6; constructor.
Qed.
  
Lemma gassnInv_imp_s Q Q' :
  incl (gassn_fc Q') (gassn_fc Q)
  -> (forall xs, fv_assn (gassn_a Q) xs -> fv_assn (gassn_a Q') xs)
  -> (forall n' m' M, gassnInv Q n' m' M -> gassnInv Q' n' m' M).
Proof.
  unfold gassnInv, gassnOk; simpl.
  introv ? ? ((? & ? & ?) & ? & ? & ? & ?); splits; jauto.
  eapply incl_fc_ok; eauto.
  
  assert (sat_FC M nil (gassn_fc Q')).
  { apply rule_module_rec in H6; eauto.
    intros ? ?; eapply Forall_incl.
    apply H6; eauto.
    unfold incl; eauto. }
  apply sat_FC_strong; eauto.
Qed.
    
Lemma rule_fLet_s Gp R P E e v :
  evalExp E e v
  -> CMsat (Ga (Assn R P E) Gp)
           (fLet e)
           (fun x => Ga ((Assn R P (x |-> v :: E))) (K Gp x)).
Proof.
  intros; apply ST_ok_CMsat; intros; applys* rule_fLet.
Qed.

Lemma rule_fAlloc_s Gp R P E len l :
  evalExp E len (Zn l)
  -> CMsat (Ga (Assn R P E) Gp)
           (fAlloc len)
           (fun x => Ga (Ex p vs, Assn (array (GLoc p) vs 1 *** R) (Datatypes.length vs = l /\ P) (x |-> p :: E)) (K Gp x)).
Proof.
  intros; apply ST_ok_CMsat; intros; applys* rule_fAlloc.
Qed.

Lemma rule_code_ex_s T A `{hd_A : hasDefval A} (gen : CUDAM T) Gp G P Q :
  (forall y, CMsat (Ga (P y) Gp) gen (fun x => Ga (Q x) (G x)))
  -> CMsat (Ga (Ex y : A, P y) Gp) gen (fun x => Ga (Q x) (G x)).
Proof.
  intros; apply ST_ok_CMsat, rule_code_ex; jauto.
  intros; apply ST_ok_CMsat; eauto.
Qed.

Lemma rule_ret_ignore_s (T : Type) P Q Gp (v : T) :
  P |= Q
  -> (forall xs, fv_assn P xs -> fv_assn Q xs)
  -> CMsat (Ga P Gp) (ret v) (fun _ => Ga Q Gp).
Proof.
  unfold ST_ok, preST, postST.
  intros; apply ST_ok_CMsat, rule_ret_ignore; eauto.
Qed.

Lemma rule_fAllocs_s typ Gp R P E size l :
  evalExp E size (Zn l)
  -> CMsat (Ga (Assn R P E) Gp)
           (fAllocs typ size)
           (fun x => Ga 
              (Ex ps vs, (Assn (arrays (val2gl ps) vs 1 *** R)) (Datatypes.length vs = l /\ P) (x |=> ps ++ E))
              (K Gp x)).
Proof.
  intros; apply ST_ok_CMsat, rule_fAllocs; eauto.
Qed.

Lemma rule_gen_kernel_s G P k fs:
  fs_tag fs = Kfun 
  -> fs_params fs = map fst (params_of k)
  -> (forall M, sat_FC M G G -> interp_kfun M G k fs)
  -> CMsat (Ga P G)
           (gen_kernel k)
           (fun fn => Ga (K P fn) (G ++ (fn, fs) :: nil)).
Proof.
  intros; apply ST_ok_CMsat, rule_gen_kernel; eauto.
Qed.

Lemma rule_ret_back_s (T T' : Type) (m : CUDAM T) (v : T') P Q Gp G :
  CMsat (Ga P Gp) (do! _ <- m in ret v) (fun x => Ga (Q v) (G v))
  -> CMsat (Ga P Gp) (do! _ <- m in ret v) (fun x => Ga (Q x) (G x)).
Proof.
  intros; apply ST_ok_CMsat, rule_ret_back, ST_ok_CMsat; eauto.
Qed.

Lemma rule_invokeKernel_s kerID fs ntrd nblk args G R (P : Prop) E Epre Rpre RF Ppre Q vs enb ent :
  In (kerID, fs) G
  -> fs_tag fs = Kfun
  -> length args = length (fs_params fs)
  -> (P -> inst_spec (fs_tri fs) (Assn Rpre Ppre Epre) Q)
  -> has_no_vars (Q 0%Z)
  -> evalExpseq E (enb :: ent :: args) (Zn nblk :: Zn ntrd :: vs)
  -> ntrd <> 0 -> nblk <> 0
  -> (P -> subst_env Epre (Var "nblk" :: Var "ntrd" :: fs_params fs) (Zn nblk :: Zn ntrd :: vs))
  -> (P -> Ppre)
  -> (P -> R |=R Rpre *** RF)
  -> CMsat (Ga (Assn R P E) G)
           (invokeKernel kerID ent enb args)
           (fun r => Ga (K (Assn RF P E ** Q 0%Z) r) (K G r)).
Proof.
  intros; eapply ST_ok_CMsat, rule_invokeKernel; eauto.
Qed.

Lemma rule_equiv_mono_pre_s T (P P' : assn) (Q : T -> assn) Gp G (m : CUDAM T) :
  P' |= P
  -> (forall xs, fv_assn P' xs -> fv_assn P xs)
  -> CMsat (Ga P Gp) m (fun x => Ga (Q x) (G x))
  -> CMsat (Ga P' Gp) m (fun x => Ga (Q x) (G x)).
Proof.
  intros; eapply ST_ok_CMsat, rule_equiv_mono_pre; eauto.
  apply ST_ok_CMsat; eauto.
Qed.

Lemma rule_ret_s T (v : T) P Q :
  (forall n m M, gassnInv P n m M -> gassnInv (Q v) n m M)
  -> (gassn_a P |= gassn_a (Q v))
  -> CMsat P (ret v) Q.
Proof.
  unfold CMsat, ret; simpl; intros.
  inverts H2; rewrite app_nil_r in *; simpl.
  splits.
  - forwards*: H.
  - eapply rule_host_forward.
    applys* rule_host_skip.
    apply H0.
Qed.

Lemma ST_ok_exec_s T P Q Gp G (gen : CUDAM T) res ss Mp M n m n' m' :
  (exists fvs, fv_assn P fvs /\ forall x m, In x fvs -> x <> hvar m)
  -> fnOk' (map fst Mp) m
  -> sat_FC Mp Gp Gp
  -> fc_ok Mp Gp
  -> disjoint_list (map fst Mp)
  -> CMsat (Ga P Gp) gen (fun x => Ga (Q x) (G x))
  -> (res, ((n', m'), ss, M)) = gen n m
  -> fc_ok (Mp ++ M) (G res) /\
     disjoint_list (map fst Mp ++ map fst M) /\
     fnOk' (map fst M) m' /\
     sat_FC (Mp ++ M) nil (G res) /\
     CSLh (Mp ++ M) (G res) P (seqs ss) (Q res).
Proof.
  intros. 
  rewrite <-ST_ok_CMsat in *.
  eapply ST_ok_exec; eauto.
  apply H4.
Qed.
