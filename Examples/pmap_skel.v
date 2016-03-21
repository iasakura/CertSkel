Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics.
Require Import Skel_lemma.
Require Import Psatz.

Close Scope Qc_scope.
Close Scope Q_scope.

Section Map.
(* variables *)
Local Notation TID := (Var "tid").
Local Notation BID := (Var "bid").
Local Notation ARR := (Var "arr").
Local Notation OUT := (Var "out").
Local Notation X := (Var "x").
Local Notation Y := (Var "y").
Local Notation I := (Var "i").

(* # of threads/blocks per block/grid *)
Variable ntrd : nat.
Variable nblk : nat.

(* Variable arr : val. *)
Variable len : nat.
(* Hypothesis len_neq_0 : len <> 0. *)
Variable out : list val.

(* free variable environment (de-bruijn indices, dimensions) *)
Variable env : list (nat * nat).

(* dimensions of input and output arrays *)
Variable inDim : nat.
Variable outDim : nat.

(* getter code of the input array *)
Variable get : var -> (cmd * list exp).
(* denotation of get *)
Variable get_den : val -> list val -> Prop.

(* compiled code of the mapping function *)
Variable func : list var -> (cmd * list exp).
(* code generators filling the function hole *)
(* func : the argument variable ->
    the command for getting the result and the return expression  *)
Variable f_den : list val -> list val -> Prop.

Hypothesis safety :
  forall i, i < len ->
    (exists gv, get_den (Zn i) gv) /\
    (forall gv, get_den (Zn i) gv -> exists fv, f_den gv fv).

Hypothesis ntrd_neq0 : ntrd <> 0.
Hypothesis nblk_neq0 : nblk <> 0.

(* Variable f_ini : nat -> val. *)
Variable fout : nat -> list val.

(* local variables used by the template *)
Definition xs := locals "x" inDim.

(* auxilirary definition for written array *)
Definition Outs := fst (fst (writeArray "Out" outDim Gl)).
Definition Len := snd (fst (writeArray "Out" outDim Gl)).
Definition setOut ix es := snd (writeArray "Out" outDim Gl) ix es.

(* map templates *)
Definition map_ker inv :=
  I ::= (TID +C BID *C Z.of_nat ntrd);;
  WhileI inv (I < Len) (
    (fst (get I)) ;;
    read_tup xs (snd (get I)) ;;
    (fst (func xs)) ;;
    catcmd (setOut I (snd (func xs))) ;;
    I ::= I +C Z.of_nat ntrd *C Z.of_nat nblk
  )%exp.

Local Close Scope exp_scope.

Local Notation nt_gr := (nblk * ntrd).

Import ListNotations.

(** runtime values *)
(* runtime value of the input arrays: length * elements *)
Variable env_den : list (list Z * nat * (nat -> list val)).

(* env is consistent with env_den *)
Hypothesis env_env_den_same_len : length env = length env_den.

Hypothesis get_local :
  forall v, forall u, In u (writes_var (fst (get v))) -> prefix "l" (var_of_str u) = true.
(* free variable conditions *)
Lemma get_fv :
  forall v, disjoint [I; BID] (writes_var (fst (get v))) .
Proof.
  simpl; repeat split; intros Hc; apply get_local in Hc; cbv in Hc; congruence.
Qed.

Lemma get_fv_sh :
  forall u v, List.In u (writes_var (fst (get v))) -> prefix "sh" (var_of_str u) = false.
Proof.
  intros u v H; apply get_local in H.
  apply prefix_ex in H as [s H]; rewrite H; cbv; eauto.
Qed.

Lemma get_fv_arr :
  forall u v, List.In u (writes_var (fst (get v))) -> prefix "arr" (var_of_str u) = false.
Proof.
  intros u v H; apply get_local in H.
  apply prefix_ex in H as [s H]; rewrite H; cbv; eauto.
Qed.

(* result expressions only contain "l"-prefixed variables or passed variables  *)
Hypothesis get_res_fv :
  forall v u e, In e (snd (get v)) -> In u (fv_E e) -> u = v \/ prefix "l" (var_of_str u) = true.
(* get has no barriers *)
Hypothesis get_no_bar :
  forall v, barriers (fst (get v)) = nil.

Lemma hback nt (R : Prop) C P Q BS tid:
  (R -> @CSL nt BS tid P C Q) <-> (@CSL nt BS tid (!(pure R) ** P) C Q).
Proof.
  split; intros H.
  intros s h H'; sep_split_in H'; simpl in *.
  apply H; eauto.
  intros Hr; eapply Hbackward; eauto.
  intros; sep_split; eauto.
Qed.

Hypothesis get_denote : forall (x : var) nt (tid : Fin.t nt) (v : val) gv,
  get_den v gv ->
  ~In x (writes_var (fst (get x))) ->
  CSL (fun _ => default nt) tid
    (!(x === v) ** input_spec env env_den (perm_n nt_gr))
    (fst (get x))
    (!((snd (get x)) ==t gv) ** input_spec env env_den (perm_n nt_gr)).

(* dimension *)
Hypothesis get_den_length :
  forall v gv, get_den v gv -> length gv = inDim.
Hypothesis get_length :
  forall v, length (snd (get v)) = inDim.

Hypothesis func_local :
  forall v, forall u, In u (writes_var (fst (func v))) -> prefix "l" (var_of_str u) = true.
Lemma func_fv :
  forall v, disjoint [I; BID] (writes_var (fst (func v))) .
Proof.
  simpl; repeat split; intros Hc; apply func_local in Hc; cbv in Hc; congruence.
Qed.
Hypothesis func_no_bar :
  forall v, barriers (fst (func v)) = nil.

Lemma func_fv_sh :
  forall u v, List.In u (writes_var (fst (func v))) -> prefix "sh" (var_of_str u) = false.
Proof.
  intros u v H; apply func_local in H.
  apply prefix_ex in H as [s H]; rewrite H; cbv; eauto.
Qed.

Lemma func_fv_arr :
  forall u v, List.In u (writes_var (fst (func v))) -> prefix "arr" (var_of_str u) = false.
Proof.
  intros u v H; apply func_local in H.
  apply prefix_ex in H as [s H]; rewrite H; cbv; eauto.
Qed.

Lemma func_fv_x :
  forall u v, List.In u (writes_var (fst (func v))) -> prefix "x" (var_of_str u) = false.
  intros u v H; apply func_local in H.
  apply prefix_ex in H as [s H]; rewrite H; cbv; eauto.
Qed.

Hypothesis func_res_fv :
  forall v u e, In e (snd (func v)) -> In u (fv_E e) -> In u v \/ prefix "l" (var_of_str u) = true.

(* {v == val} func {ret == f_den val} *)
Hypothesis func_denote : forall (x : list var) nt (tid : Fin.t nt) (vs fv : list val),
  f_den vs fv -> 
  length x = inDim ->
  disjoint x (writes_var (fst (func x))) ->
  CSL (fun _ => default nt) tid
    ( !(vars2es x ==t vs ) ** input_spec env env_den (perm_n nt_gr))
    (fst (func x))
    (!((snd (func x)) ==t fv) ** input_spec env env_den (perm_n nt_gr)).

Hypothesis fout_length :
  forall i, length (fout i) = outDim.
Hypothesis fden_length :
  forall v fv, f_den v fv -> length fv = outDim.
Hypothesis out_length :
  length out = outDim.
Hypothesis func_length :
  forall v, length (snd (func v)) = outDim.
Notation fg_den i v := (exists t, get_den i t /\ f_den t v).
Section block_verification.
Variable bid : Fin.t nblk.

Notation zf i := (Z_of_fin i).

Section thread_verification.
Variable tid : Fin.t ntrd.

Notation gtid := (nf tid + nf bid * ntrd).

Open Scope string.

Notation GOuts := (es2gls Outs).
Notation gl_out := (es2gls (vs2es out)).

Lemma ex_fgi :
  exists (fgi : nat -> list val),
    forall i, i < len ->
      fg_den (Zn i) (fgi i).
Proof.
  generalize len safety; intros l Hsf; induction l.
  - exists (fun _:nat => @nil Z); intros; try omega.
  - assert (exists f, forall i, i < l -> fg_den (Zn i) (f i)).
    { apply IHl.
      intros i Hi; apply Hsf; try omega. }
    destruct H as [f H].
    assert (exists v, fg_den (Zn l) v) as (v & H').
    { lets ((gv & Hg) & Hl): (>>Hsf l ___); try omega.
      lets (fv & Hg'): (>> Hl Hg).
      exists fv gv; split; eauto. }
    exists (fun i : nat => if Nat.eq_dec i l then v else f i).
    intros; destruct Nat.eq_dec; subst; eauto.
    apply H; omega.
Qed.

Definition inv fgi:=
  Ex ix,
    !(Outs ==t out) **
    !(Len === Zn len) **
    !(I === Enum' (ix * nt_gr + gtid)) **
    !(Apure (ix * nt_gr + gtid < len + nt_gr)%nat) **
    input_spec env env_den (perm_n nt_gr) **
    nth gtid (distribute_tup nt_gr gl_out len
       (fun i => if lt_dec i (ix * nt_gr + gtid)
                 then fgi i
                 else fout i)%Z (nt_step nt_gr) 0 1%Qc) emp.

Notation GTID := (TID +C BID *C Zn ntrd).

Hint Rewrite Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_succ div_Zdiv : sep.

Hint Unfold Len Outs writeArray name_of_len.

Open Scope string.

Arguments append _ _ : simpl never.

Lemma nt_gr_neq_0 : nt_gr <> 0.
nia.
Qed.

Hint Resolve nt_gr_neq_0.

Lemma map_correct : 
  forall fgi, (forall i, i < len -> fg_den (Zn i) (fgi i)) ->
  CSL (fun n => default ntrd) tid
   (!(Outs ==t out) **
   !(Len === Zn len) **
   (input_spec env env_den (perm_n nt_gr)) **
   List.nth gtid (distribute_tup nt_gr gl_out len fout (nt_step nt_gr) 0 1%Qc) emp **
   !(BID === zf bid) ** !(TID === zf tid))

  (map_ker (inv fgi))

   (input_spec' env_den (perm_n nt_gr) **
    List.nth gtid (distribute_tup nt_gr gl_out len (fun v=>(fgi v))%Z (nt_step nt_gr) 0 1%Qc) emp).
Proof.
  unfold map_ker; intros fgi Hfgi.
  eapply rule_seq.
  { hoare_forward; intros ? ? H'.
    destruct H' as [v H'].
    subA_normalize_in H' with ( fun H => first
      [ apply subA_distribute_tup in H | apply subA_eq_tup in H
        | apply subA_is_tuple_p in H | apply subA_input_spec in H; eauto ] ).
    repeat subE_simpl in *. simpl in H'. autounfold in H'. simpl in H'.
    rewrite subE_vars2es in H'; auto.
    exact H'. }
  hoare_forward.
  assert (mod_add : forall x y c, y <> 0 -> c < y -> (x * y + c) mod y = c).
  { intros; rewrite plus_comm; rewrite Nat.mod_add, Nat.mod_small; eauto. }
  { unfold inv; eapply Hbackward.
    Focus 2.
    { intros s h H; apply ex_lift_l_in in H as [x H].
      sep_split_in H.
      change_in H.
      { unfold_pures.
        lets Heq: (>> skip_arr_tup_forward (x * nt_gr + (nf tid + nf bid * ntrd))).
        sep_rewrite_in Heq H; simpl in *; [|try first [nia; omega | eauto]..].
        (* sep_rewrite_in (@is_array_unfold (Gl arr) (x * nt_gr + gtid)) H; [|try first [omega | eauto]..]. *)
        (* 2: nia. *)
        (* rewrite <-plus_n_O in H. *)
      apply H. } 
      sep_combine_in H. ex_intro x H. simpl in H. exact H. } Unfocus.
    
    hoare_forward.
    eapply Hbackward.
    (* Focus 2. { intros s h H; sep_lift_in H 2; exact H. } Unfocus. *)
    (* rewrite <-hback; intros Hfgi. *)
    (* eapply Hbackward. *)
    Focus 2.
    { intros s h H.
      assert (pure (fg_den (Zn (x * nt_gr + gtid)) (fgi (x * nt_gr + gtid))) s (emp_ph loc)).
      { lets (v & Hget & Hf): (Hfgi ((x * nt_gr + gtid))).
        sep_split_in H; unfold_pures; unfold_conn_all; simpl in *.
        rewrite HP2, HP1, <-Nat2Z.inj_lt in l; omega.
        (* destruct (Hf v) as [fv ?]; eauto. *)
        repeat eexists; eauto. }
      sep_combine_in H. sep_lift_in H 1. apply H. } Unfocus.
      rewrite <-hback; intros (gv & (Hgv & Hfv)).

    eapply rule_seq. 
    { autorewrite with sep. eapply Hbackward. 
      Focus 2.
      { intros s h H.
        sep_split_in H.
        change_in H.
        { assert (((Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))%Z === I)%exp
                      s (emp_ph loc)).
          { unfold_pures; unfold_conn; simpl; nia. }
          sep_rewrite_in (mps_eq1_tup') H; [|exact H0]. 
          sep_combine_in H; exact H. }
        evar (P : assn).
        assert (((!(I === (Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))%Z) **
                   (input_spec env env_den (1 / injZ (Zn nblk * Zn ntrd)))) ** P) s h).
        { sep_normal; repeat sep_cancel.
          (* sep_split; [sep_split_in H1; unfold_pures; unfold_conn; simpl in *; omega..|]. *)
          unfold P; eauto. }
        unfold P in *; apply H0. } Unfocus.
      apply rule_frame.
      { eapply Hbackward; [apply get_denote; lets: (>>get_fv I); simpl in *; jauto|].
        intros; autorewrite with sep; eauto. }
        (* intros s h Hg; sep_split_in Hg; sep_split; autorewrite with sep; eauto. *)
        (* lets ((v & Hsafe) & ?): (safety (Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))); eauto. *)
        (* intros. *)
        (* sep_split_in H; sep_split; eauto. *)
        (* unfold_pures; unfold_conn; simpl in *. *)
        (* autorewrite with sep; auto. } *)
      destructs (get_fv I).
      repeat prove_inde;
      try (first [apply disjoint_indeE | apply disjoint_indelE | apply disjoint_indeB]; simpl;
           repeat split; eauto );
      try (intros Hc; apply get_fv_sh in Hc; simpl in Hc; congruence);
      first [apply inde_distribute_tup | apply inde_is_tup |
             apply inde_eq_tup ]; apply Forall_forall;
      intros; first [apply indeE_fv|apply indelE_fv]; intros Hc;
      lazymatch goal with
        | [H : In _ (writes_var (fst (get _))) |- _] => lets: (>>get_fv_sh H); lets: (>>get_fv_arr H)
      end;  unfold tarr_idx, es2gls, vs2es in *.
      
      { eapply outs_prefix in H2; eauto; try congruence. 
        congruence. }
      { repeat apply in_map_iff in H2 as [? [? H2]]; subst; simpl in Hc; 
        destruct Hc. }
      { repeat apply in_map_iff in H2 as [? [? H2]]; subst;
        simpl in Hc; destruct Hc as [|[]]; subst; eauto. }
      { repeat apply in_map_iff in H2 as [? [? H2]]; subst; simpl in Hc; destruct Hc. }
      { repeat apply in_map_iff in H2 as [? [? H2]]; subst; simpl in Hc; destruct Hc. } }
      
      (* hoare_forward; try (apply inde_distribute; auto; repeat (constructor; prove_indeE)); simpl. *)
      (* apply inde_eq_tup. *)
      (* apply outs_inde; rewrite Forall_forall; simpl; intros ? [? | ?]; subst; simpl; tauto. *)
      (* apply inde_distribute_tup. *)
      (* apply inde_vals_l. *)
      (* apply inde_is_tup. *)
      
      (* Lemma inde_tarr_idx es ix vs : *)
      (*   Forall (fun e : loc_exp => forall v, In v vs -> indelE e v) es -> *)
      (*   (forall v, In v vs -> indeE ix v) -> *)
      (*   Forall (fun e : loc_exp => forall v : var, In v vs -> indelE e v) *)
      (*          (tarr_idx es ix). *)
      (* Proof. *)
      (*   unfold tarr_idx; rewrite !Forall_forall. *)
      (*   intros Hes Hix x Hx. *)
      (*   apply in_map_iff in Hx as [? [? Hx]]; subst. *)
      (*   intros. *)
      (*   forwards: (>> Hix H). *)
      (*   forwards: (>>Hes Hx H). *)
      (*   prove_indeE; rewrite <-H0, <-H1; auto. *)
      (* Qed. *)

      (* apply inde_tarr_idx. *)
      (* apply inde_vals_l. *)
      (* simpl; destruct 1; try tauto. *)
      (* subst; prove_inde. *)
      (* apply inde_vals. *)
      (* apply inde_distribute_tup. *)
      (* apply inde_vals_l. *)
      (* intros ? ? H; apply H. } *)

    eapply rule_seq.
    { eapply Hbackward; [|intros ? ? H; sep_normal_in H; eauto].
      apply rule_frame.
      apply read_tup_correct.
      intros; intros Hc.
      eapply get_res_fv in Hc as [Hc | Hc]; apply locals_pref in H; eauto.
      rewrite Hc in H; cbv in H; congruence.
      apply prefix_ex in Hc as [? Heq]; rewrite Heq in H; cbv in H; congruence.
      
      apply locals_disjoint_ls.
      erewrite get_den_length, get_length; eauto.
      unfold xs; erewrite locals_length, get_length; eauto.
      rewrite read_tup_writes; [|unfold xs; rewrite locals_length, get_length; auto].
      unfold xs.
      lets Hpref: (>>locals_pref "x" inDim).

      repeat prove_inde;
      try (first [apply disjoint_indeE | apply disjoint_indelE | apply disjoint_indeB]; simpl;
           repeat split; eauto );
      try (intros Hc; apply Hpref in Hc; simpl in Hc; congruence);
      first [apply inde_distribute_tup | apply inde_is_tup |
             apply inde_eq_tup | apply inde_input_spec]; try (apply Forall_forall;
      intros; first [apply indeE_fv|apply indelE_fv]; intros Hc;
      lazymatch goal with
        | [H : In _ (locals _ _) |- _] => lets: (>>Hpref H)
      end;  unfold tarr_idx, es2gls, vs2es in *).
      
      { intros; lets: (>>Hpref ___); eauto; apply prefix_ex in H0 as [? ?]; rewrite H0; simpl; auto. }
      { intros; lets: (>>Hpref ___); eauto; apply prefix_ex in H0 as [? ?]; rewrite H0; simpl; auto. }
      { eapply outs_prefix in H; eauto.
        apply prefix_ex in H1 as [? ?]; rewrite H1 in H; simpl in H; congruence. }
      { repeat apply in_map_iff in H as [? [? H]]; subst; simpl in Hc; destruct Hc. }
      { repeat apply in_map_iff in H as [? [? H]]; subst; simpl in Hc.
        destruct Hc as [Hc|[]]; subst; simpl in H1; congruence. }
      { repeat apply in_map_iff in H as [? [? H]]; subst; simpl in Hc; destruct Hc. }
      { repeat apply in_map_iff in H as [? [? H]]; subst; simpl in Hc; destruct Hc. } }
      
    eapply rule_seq.
    { (* executute the passed function *)
      eapply Hbackward.
      Focus 2.
      { intros s h H.
        evar (P : assn).
        assert (((!(vars2es xs ==t gv) **
                 input_spec env env_den (perm_n nt_gr)) ** P) s h).
        { unfold P; sep_normal; apply H. }
        apply H0. } Unfocus.
      apply rule_frame.
      { apply func_denote; eauto.
        unfold xs; rewrite locals_length; auto.
        apply disjoint_comm, not_in_disjoint; intros x0 H Hc.
        lets: (>>func_fv_x H).
        apply locals_pref in Hc; congruence. }
      lets: (func_fv xs); simpl in *.
      repeat prove_inde;
      try (first [apply disjoint_indeE | apply disjoint_indelE | apply disjoint_indeB]; simpl;
           repeat split; jauto );
      try (intros Hc; apply func_fv_sh in Hc; simpl in Hc; congruence);
      first [apply inde_distribute_tup | apply inde_is_tup |
             apply inde_eq_tup | apply inde_input_spec ]; try rewrite Forall_forall; eauto;
      intros; first [apply indeE_fv|apply indelE_fv]; intros Hc;
      lazymatch goal with
        | [H : In _ (writes_var (fst (func _))) |- _] => lets: (>>func_fv_sh H); lets: (>>func_fv_arr H)
      end;  unfold tarr_idx, es2gls, vs2es in *.
      { eapply outs_prefix in H0; eauto. congruence. }
      { repeat apply in_map_iff in H0 as [? [? H0]]; subst; simpl in Hc; destruct Hc.  }
      { repeat apply in_map_iff in H0 as [? [? H0]]; subst; simpl in Hc; destruct Hc as [|[]]; subst; jauto. }
      { repeat apply in_map_iff in H0 as [? [? H0]]; subst; simpl in Hc; destruct Hc. }
      { repeat apply in_map_iff in H0 as [? [? H0]]; subst; simpl in Hc; destruct Hc. } }

    eapply rule_seq.
    { (* set the results to output array *)
      eapply Hbackward.
      Focus 2. {
        intros s h H.
        sep_split_in H.
        sep_rewrite_in_r mps_eq1_tup H; [|eauto].
        sep_combine_in H.
        sep_lift_in H 7. exact H.
      } Unfocus.
      apply rule_frame.
      apply gen_write_correct; simpl.
      unfold vs2es; rewrite map_length.
      unfold Outs; destruct lt_dec; try omega;
      try rewrite fden_length; try rewrite get_den_length; eauto; try rewrite fout_length, outs_length; eauto.
      unfold Outs; rewrite outs_length; eauto.
      unfold catcmd, setOut; simpl; rewrite writes_var_gen_write.
      intros ?; destruct 1. }
    eapply Hforward.
    { eapply Hbackward; [|intros s h H; sep_normal_in H; exact H].
      hoare_forward.
      intros ? ? H; destruct H as [v H].
      sep_normal_in H.
      subA_normalize_in H with ( fun H => first
      [ apply subA_distribute_tup in H | apply subA_eq_tup in H
      | apply subA_is_tuple_p in H | apply subA_input_spec in H; eauto ] ). simpl in H.
      unfold Outs in *; simpl in H.
      repeat (rewrite !subE_vars2es in H; eauto).
      assert ((subEs I v (snd (func xs)) ==t fgi (x * nt_gr + gtid)) s (emp_ph loc)).
      { sep_split_in H; unfold_pures; eauto. }
      sep_rewrite_in mps_eq2_tup H; [|exact H0].
      subE_simpl in *.
      rewrite sublEs_tarr_idx in H.
      ex_intro v H. exact H. }
    
    unfold inv; intros s h H. destruct H as (v & H); simpl in H.
    sep_normal_in H; sep_split_in H.
    unfold_pures; subst.
    unfold Outs, writeArray, names_of_arg; simpl.
    exists (S x); autorewrite with sep.
    (* exists (fun i => if Nat.eq_dec i (x * nt_gr + gtid) then fv else fgi i). *)
    sep_split; try now (unfold_conn; simpl; auto; omega).
    (* { unfold_conn; intros i [Hilt Himod]; destruct Nat.eq_dec; [|apply Hfgi]. *)
    (*   subst; eauto. *)
    (*   split; eauto. *)
    (*   cut (~(x * nt_gr + gtid <= i)); [intros; omega| ]. *)
    (*   intros Hc. *)
    (*   lets H'': (>>mod_between i nt_gr x gtid ___); try omega; eauto. } *)
    { rewrite <-out_length; auto. }
    { unfold_conn; simpl. rewrite HP5. ring. }
    autorewrite with sep in H. sep_cancel.
    (* sep_rewrite (@is_array_unfold (Gl arr) (x * nt_gr + gtid)); try omega; eauto. *)
    lets Heq: (sublEs_es2gls); unfold es2gls in Heq; rewrite !Heq in H0.
    rewrite subE_vars2es in H0; auto.
    lets Heq': (>> skip_arr_tup_forward (x * nt_gr + (nf tid + nf bid * ntrd))).
    sep_rewrite Heq'; simpl in *; [|try first [ omega | eauto]..]; clear Heq'.
    (* sep_rewrite_r (@skip_arr_tup_fold (nf tid + nf bid * ntrd) gl_out); try omega; eauto. *)
    sep_normal; simpl.
    simpl; repeat sep_cancel.
    assert (0 < nt_gr) by (apply Nat.mul_pos_pos; omega).
    simpl in H0.
    destruct lt_dec; try omega; sep_lift 1; sep_cancel.
    
    (* cuts_rewrite (len - (nt_gr + x * nt_gr + gtid) = *)
    (*               len - (x * nt_gr + gtid) - nt_gr); [|nia]. *)
    sep_rewrite_r mps_eq1_tup; [|apply HP1].
    unfold es2gls. (* destruct Nat.eq_dec; try omega. *)

    repeat autorewrite with sep; sep_cancel.

    sep_rewrite nth_dist_tup_change; eauto.
    apply scC; sep_rewrite nth_dist_tup_change; eauto.
    apply scC; eauto.
    clear H1 Heq H0 H HP1.
    - intros; repeat destruct lt_dec; eauto; try omega. 
      assert (nt_gr - 1 <= j); [|omega].
      cutrewrite (j + (x * nt_gr + (nf tid + nf bid * ntrd) + 1) =
                  ((j + 1) + (nf tid + nf bid * ntrd)) + x * nt_gr) in H0; [|ring].
      Lemma mod_same: forall x y z, z <> 0 -> (x + y) mod z = y -> x mod z = 0.
      Proof.
        intros.
        lets: (>>Nat.div_mod (x + y) z ___); auto.
        assert (x = z * ((x + y) / z)) by omega.
        rewrite H2, mult_comm, Nat.mod_mul; eauto.
      Qed.
      unfold nt_step in H0; rewrite Nat.mod_add in H0; eauto.
      apply mod_same in H0; eauto.
      apply Nat.mod_divides in H0 as [[| c] ?]; subst; eauto; try omega.
      rewrite mult_succ_r in H0. generalize (nt_gr * c) H0; intros; omega.
      - intros; repeat destruct lt_dec; repeat destruct Nat.eq_dec; eauto; try omega. } 

  { unfold inv; intros s h H.
    apply ex_lift_l_in in H as (x & H).
    sep_split_in H. unfold_pures.
    revert H; apply scRw_stack; [intros; eapply input_spec_forget; eauto|].
    intros; sep_rewrite nth_dist_tup_change; eauto.
    (* sep_split; [intros i ? ?; apply HP0; split; nia|]. *)
    (* sep_rewrite nth_dist_tup_change; eauto. *)
    intros; destruct lt_dec; eauto; try (zify; omega); eauto. }

  { assert (Hlt : gtid < nt_gr) by auto.
    intros s h H; unfold inv; exists 0; simpl.
    sep_split_in H; unfold_pures; sep_split; auto.
    - unfold_conn; simpl; autorewrite with sep. unfold_conn_in HP; simpl in HP. 
      repeat match goal with [H : _ = _|- _] => first [rewrite <-H | rewrite H]; clear H end; auto.
    - unfold_conn. assert (nf tid + nf bid * ntrd < nt_gr) by auto. omega.
    - sep_cancel.
      sep_rewrite nth_dist_tup_change; eauto.
      intros; destruct lt_dec; try omega.
      unfold nt_step in H2; rewrite Nat.mod_small in H2; try omega.
      assert (nf tid + nf bid * ntrd < nt_gr); eauto; omega. }
Qed.
End thread_verification.
  
Require Import Bdiv.
Local Notation init := MyVector.init.
Definition bth_pre :=
  !(Outs ==t out) **
  !(Len === Zn len) **
  conj_xs (ls_init 0 ntrd (fun i => input_spec env env_den (perm_n nt_gr))) **
  conj_xs (ls_init 0 ntrd (fun i =>
    nth (i + nf bid * ntrd)
    (distribute_tup nt_gr (es2gls (vs2es out)) len fout (nt_step nt_gr) 0 1) emp)).

Definition tr_pres := init (fun i : Fin.t ntrd =>
  !(Outs ==t out) ** 
  !(Len === Zn len) **
  input_spec env env_den (perm_n nt_gr) **
  nth (nf i + nf bid * ntrd)
    (distribute_tup nt_gr (es2gls (vs2es out)) len fout (nt_step nt_gr) 0 1) emp **
  !(BID === zf bid)).

Definition bth_post fgi :=
  conj_xs (ls_init 0 ntrd (fun i => input_spec' env_den (perm_n nt_gr))) **
  conj_xs (ls_init 0 ntrd (fun tid =>
    nth (tid + nf bid * ntrd)
      (distribute_tup nt_gr (es2gls (vs2es out)) len
        (fun v : nat => fgi v) (nt_step nt_gr) 0 1) emp)).

Definition tr_posts fgi := (init (fun tid : Fin.t ntrd =>
  input_spec' env_den (perm_n nt_gr) **
  nth (nf tid + nf bid * ntrd)
    (distribute_tup nt_gr (es2gls (vs2es out)) len
      (fun v : nat => fgi v) (nt_step nt_gr) 0 1) emp)).

Definition out_vars := List.map Var (names_of_array "Out" outDim).

Definition E : Lang.env := fun v =>
  if var_eq_dec v BID then Lo
  else if prefix "sh" (var_of_str v) then Lo
  else if prefix "arr" (var_of_str v) then Lo
  else Hi.  
Close Scope Qc_scope.
Close Scope Q_scope.
(* delete arguments of map_ker *)
Definition tid0 : Fin.t ntrd.
destruct ntrd; try omega.
exact Fin.F1.
Qed.

Definition map' : cmd.
  pose (map_ker FalseP) as map'; unfold map_ker, WhileI in map'; exact map'.
Defined.

Definition bspec : (barrier_spec ntrd) := fun i => (default ntrd).

Lemma precise_false : precise (fun _ _ => False).
Proof.
  unfold precise; intros; tauto.
Qed.

Lemma map_correct_b fgi :
  (forall i, i < len -> fg_den (Zn i) (fgi i)) ->
  CSLp ntrd E (bth_pre ** !(BID === zf bid)) map' ((bth_post fgi)).
Proof.
  intros Hfgi.
  applys (>> rule_par bspec tr_pres (tr_posts fgi)).
  - destruct ntrd; eexists; try omega; eauto.
  - unfold bspec; split; intros; unfold default; simpl; rewrite MyVector.init_spec;
    unfold CSL.low_assn, low_assn, indeP; tauto.
  - eauto.
  - split; unfold bspec, default; simpl; rewrite MyVector.init_spec;
    apply precise_false.
  - unfold bth_pre, tr_pres; intros.
    sep_split_in H.
    istar_simplify.
    repeat sep_rewrite (@ls_star).
    repeat sep_rewrite (@ls_pure).
    sep_split.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    repeat sep_cancel.
  - unfold tr_posts, bth_post; intros s h H.
    istar_simplify_in H.
    sep_cancel.
  - intros; unfold tr_pres; rewrite MyVector.init_spec.
    unfold CSL.low_assn.
    repeat prove_low_assn; eauto.
    apply low_assn_eqt.
    apply Forall_forall; intros.
    
    unfold Outs, writeArray, names_of_arg, ss2es, names_of_array in H; simpl in H.
    rewrite in_map_iff in H; destruct H as [? [? ?]]; subst.

    rewrite In_ls_init in H0; destruct H0 as [z [? ?]]; subst.
    constructor; unfold E; simpl; auto.
    constructor; eauto.

    apply low_assn_input_spec.
    intros; unfold E; rewrite H; repeat destruct var_eq_dec; eauto.
    destruct (prefix "sh"); auto.
    intros; unfold E; rewrite H; repeat destruct var_eq_dec; eauto.
    apply low_assn_skip_arr_tup.
    rewrite Forall_forall; unfold es2gls, vs2es; intros.
    repeat (rewrite in_map_iff in H; destruct H as [? [? H]]; subst).
    repeat constructor.
  - intros; unfold CSL.low_assn, tr_posts; rewrite MyVector.init_spec.
    repeat prove_low_assn.

    apply low_assn_input_spec'.
    (* intros; unfold E; rewrite H; repeat destruct var_eq_dec; eauto. *)
    (* destruct (prefix "sh"); auto. *)
    (* intros; unfold E; rewrite H; repeat destruct var_eq_dec; eauto. *)
    apply low_assn_skip_arr_tup.
    apply Forall_forall; intros ? H. unfold es2gls, vs2es in H.
    repeat (rewrite in_map_iff in H; destruct H as [? [? H]]; subst).
    repeat constructor.
  - repeat (match goal with
            | [ |- typing_exp _ _ _ ] => eapply ty_var; apply le_type_refl
            | _ => econstructor
            end); try reflexivity.
    repeat instantiate (1 := Hi).
    apply typing_cmd_Hi; eauto.
    intros.
    unfold E; repeat destruct var_eq_dec; subst; lets: (get_fv I); simpl in *; try tauto.
    destruct (prefix "sh" (var_of_str v)) eqn:Heq.
    apply get_fv_sh in H; congruence.
    destruct (prefix "arr" (var_of_str v)) eqn:Heq'; auto.
    apply get_fv_arr in H; congruence.
    
    apply read_tup_hi.
    unfold xs; intros.
    apply locals_pref in H; unfold E.
    repeat (destruct (var_eq_dec); subst; simpl in H; try congruence).
    apply prefix_ex in H as [? ?]; rewrite H.
    simpl; eauto.

    apply typing_cmd_Hi; eauto.
    intros; unfold E.
    lets: (>>disjoint_not_in_r v (func_fv xs) H).
    lets: (>>func_fv_arr v xs H).
    lets: (>>func_fv_sh v xs H).
    destruct var_eq_dec; subst.
    elimtype False; apply H0; simpl; eauto.
    rewrite H1, H2; eauto.
    
    apply typing_cmd_Hi.
    apply gen_write_no_bars.
    unfold catcmd, setOut, writeArray; simpl; intros ?; rewrite writes_var_gen_write; simpl; try tauto.
  - unfold tr_pres, tr_posts; intros; rewrite !MyVector.init_spec.
    unfold bspec, skip_arr.
    eapply Hbackward.
    eapply Hforward.
    apply map_correct; eauto.
    intros s h H; sep_normal_in H; sep_normal; repeat sep_cancel.
    intros s h H; sep_normal_in H; sep_normal; repeat sep_cancel.
    (* hmm.. *)
    Grab Existential Variables.
    apply Lo.
    apply Lo.
    apply Lo.
    apply 0.
Qed.

End block_verification.

Definition bl_pres : Vector.t assn nblk :=
  MyVector.init (fun b : Fin.t nblk => (bth_pre b)).
Definition bl_posts fgi : Vector.t assn nblk :=
  MyVector.init (fun b : Fin.t nblk => (bth_post b fgi)).

Definition bid0 : Fin.t nblk.
  destruct nblk; try omega.
  exact Fin.F1.
Qed.

Theorem map_correct_g  :
  (exists fgi,
    (forall i, i < len -> fg_den (Zn i) (fgi i)) /\
    CSLg ntrd nblk 
         (!(Outs ==t out) ** !(Len === Zn len) **
     input_spec env env_den 1 ** is_tuple_array_p (es2gls (vs2es out)) len fout 0 1)

    (Pr nil map')

    (input_spec' env_den 1 **
     is_tuple_array_p (es2gls (vs2es out)) len (fun v => fgi v)%Z 0 1)).
Proof.
  lets (fgi & Hfgi) : ex_fgi.
  exists fgi; split; eauto.
  applys (>> rule_grid E bl_pres (bl_posts fgi)); eauto.
  - intros s h H.
    unfold bl_pres, bth_pre.
    sep_split_in H.
    istar_simplify.
    repeat sep_rewrite (@ls_star nblk).
    repeat sep_rewrite (@ls_pure nblk); sep_split.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    (* apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto. *)
    repeat (sep_rewrite_r is_array_skip_arr); sep_cancel; eauto.
    
    sep_rewrite conj_xs_init_flatten; simpl.
    
    sep_rewrite input_spec_p1; eauto; try nia.
    intros; simpl; unfold es2gls, vs2es; rewrite !map_length, fout_length.
    unfold val in *; rewrite out_length; auto.
  - unfold bl_pres, bl_posts; intros.
    rewrite !MyVector.init_spec.
    eapply CSLp_backward.
    eapply CSLp_forward.
    apply (map_correct_b bid); eauto.
    intros; simpl; sep_normal; eauto.
    intros; simpl in *; sep_normal_in H; eauto.
  - unfold bl_posts, bth_post in *.
    intros s h H.
    istar_simplify_in H.
    (* sep_rewrite_in (@ls_exists0 (list (nat -> list val)) nil) H; destruct H as [fs H]; sep_split_in H. *)
    (* repeat sep_rewrite_in (@ls_star) H. *)
    sep_rewrite_in conj_xs_init_flatten H; simpl in H.
    (* lets Heq: (>>is_array_is_array_p_1 __ __ nt_gr); sep_rewrite Heq; eauto; try nia. *)
    sep_rewrite_in input_spec'_p1 H; eauto; try nia.
    (* exists (fun i => let gid := i mod nt_gr in *)
    (*                  nth (gid mod ntrd) (nth (gid / nblk) fs nil) (fun _:nat => nil) i). *)
    sep_split.
    sep_rewrite is_array_skip_arr; eauto.
    intros.
    unfold es2gls, vs2es; rewrite !map_length.
    lets Heq: out_length; unfold val in Heq; rewrite Heq.
    destruct (Hfgi i H0) as (? & ? & ?); eauto. 
  - prove_inde.
  - intros; unfold bl_pres, bth_pre.
    rewrite MyVector.init_spec.
    prove_inde.
    apply inde_eq_tup, Forall_forall.
    intros.
    apply indeE_fv; intros Hc.
    eapply outs_prefix in H; eauto.
    simpl in H0; repeat destruct H0 as [|H0]; subst; simpl in H; congruence.
    (* apply inde_eq_tup, Forall_forall; unfold Outs, writeArray, names_of_arg; simpl; intros x H. *)
    (* unfold vars2es, names_of_array in H; *)
    (*   rewrite in_map_iff in H; destruct H as [? [? H]]; subst; rewrite In_ls_init in H; *)
    (*   destruct H as [? [? ?]]; subst. *)
    (* intros; destruct H as [? | [? | ?]]; try tauto; subst; *)
    (* prove_indeE. *)
    apply inde_conj_xs; rewrite init_length; intros;
    rewrite ls_init_spec; destruct lt_dec; prove_inde.
    apply inde_input_spec; intros v; destruct 1 as [|[|[]]]; subst; simpl; auto.
    apply inde_conj_xs; rewrite init_length; intros;
    rewrite ls_init_spec; destruct lt_dec; prove_inde; simpl.
    apply inde_distribute_tup; rewrite Forall_forall.
    intros; apply indelE_fv; intros Hc.
    unfold es2gls, vs2es in H0; repeat (apply in_map_iff in H0 as [? [? H0]]; subst).
    simpl in Hc; auto.
  - intros bid; unfold bl_pres, bth_pre; rewrite MyVector.init_spec.
    Hint Constructors typing_exp typing_lexp.
    repeat prove_low_assn; eauto.
    apply low_assn_eqt. unfold Outs.
    rewrite Forall_forall.
    intros x H; apply writeArray_vars in H.
    destruct H as [? [? H]]; subst.
    constructor; unfold E.
    unfold var_of_str. rewrite H.
    repeat lazymatch goal with [|- context [if ?X then _ else _]] => destruct X; auto end.
    jauto.
    constructor; eauto.
    apply low_assn_conj_xs; rewrite init_length; intros.
    rewrite ls_init_spec; destruct lt_dec; try repeat prove_low_assn.
    apply low_assn_input_spec.
    unfold E; intros ? ->; repeat (lazymatch goal with [|- context [if ?B then _ else  _]] => destruct B; eauto end).
    unfold E; intros ? ->; repeat (lazymatch goal with [|- context [if ?B then _ else  _]] => destruct B; eauto end).
    apply low_assn_conj_xs; rewrite init_length; intros.
    rewrite ls_init_spec; destruct lt_dec; try repeat prove_low_assn.
    apply low_assn_skip_arr_tup.
    rewrite Forall_forall; intros ? He.
    unfold es2gls, vs2es in He.
    repeat (rewrite in_map_iff in He; destruct He as [? [? He]]; subst).
    eauto.
  - intros.
    unfold bl_posts, bth_post.
    rewrite MyVector.init_spec.
    has_no_vars_assn; apply has_no_vars_conj_xs; rewrite init_length; intros; rewrite ls_init_spec;
    repeat has_no_vars_assn.
    
    apply has_no_vars_input_spec.
    apply has_no_vars_skip_arr_tup; repeat constructor.
    unfold es2gls, vs2es.
    rewrite Forall_forall; rewrite map_map; intros ? H'; rewrite in_map_iff in H';
    destruct H' as [? [? ?]]; subst; prove_inde.
  - simpl; tauto.
  - simpl; tauto.
Qed.
    
End Map.

