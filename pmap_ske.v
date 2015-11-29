Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics.
Require Import Skel_lemma.

Close Scope Qc_scope.
Close Scope Q_scope.
Section Map.
Local Notation TID := (Var "tid").
Local Notation BID := (Var "bid").
Local Notation ARR := (Var "arr").
Local Notation OUT := (Var "out").
Local Notation X := (Var "x").
Local Notation Y := (Var "y").
Local Notation I := (Var "i").

Variable ntrd : nat.
Variable nblk : nat.
Variable len : nat.
Hypothesis len_neq_0 : len <> 0.
Variable arr : val.
Variable out : list val.
Hypothesis ntrd_neq0 : ntrd <> 0.
Hypothesis nblk_neq0 : nblk <> 0.

Variable f_ini : nat -> val.
Variable fout : nat -> list val.
Local Close Scope exp_scope.

Local Notation nt_gr := (nblk * ntrd).

Ltac sep_rewrite lem :=
  match goal with
    | [|- ?X _ _] => pattern X
  end; erewrite lem; cbv beta. 
Ltac sep_rewrite_r lem :=
  match goal with
    | [|- ?X _ _] => pattern X
  end; erewrite <-lem; cbv beta. 

Variable aenv : assn.

Variable outDim : nat.
Variable inDim : nat.

Import ListNotations.

(* free variable environment: (de-bruijn idx, the dimension * length of the array * elems of the array) *)
Variable env : list (nat * nat).
Variable env_den : list (nat * (nat -> list val)).
Hypothesis env_env_den_same_len : length env = length env_den.
Definition vars2es := List.map Evar.
Definition grpOfInt n := ("In" ++ nat_to_string n)%string.

Lemma subEs_ss2es (ss : list string) (x : var) (e : exp) :
  (forall s, In s ss -> var_of_str x <> s) ->
  subEs x e (ss2es ss) = ss2es ss.
Proof.
  induction ss; simpl; eauto.
  intros H; destruct var_eq_dec; rewrite IHss; eauto.
  subst x; simpl in H.
  forwards: (>>H a ___); try congruence; eauto.
Qed.  

Fixpoint input_spec env env_den p :=
  match env, env_den with
  | (idx, d) :: env, (len, f) :: env_den =>
    let (Len, Arrs) := names_of_arg (grpOfInt idx) d in
    let Arrs' := es2gls (ss2es Arrs) in
    !(Evar (Var Len) === Zn len) **
     (is_tuple_array_p Arrs' len f 0 p) **
     input_spec env env_den p
  | _, _ => emp
  end.

Lemma subA_is_tup_arr var e Es l f s p :
  subA var e (is_tuple_array_p Es l f s p) |=
  is_tuple_array_p (sublEs var e Es) l f s p.
Proof.
  revert f; induction Es; simpl; intros; eauto.
  subA_norm_in H.
  sep_cancel; eauto.
Qed.  

Lemma In_ls_init (T : Type) s l f (x : T) : 
  In x (ls_init s l f) <-> exists y, x = f y /\ s <= y < s + l.
Proof.
  revert s; induction l; intros s; simpl; eauto.
  - split; [destruct 1| destruct 1; omega].
  - split; intros H.
    + destruct H as [|H]; [exists s; split; eauto; omega| ].
      rewrite IHl in H; destruct H as [y [? ?]]; exists y; split; eauto; omega.
    + destruct H as [y [Hh  Ht]].
      assert (y = s \/ S s <= y < (S s) + l) as [|] by omega; [subst; left; eauto|].
      right; rewrite IHl; exists y; split; eauto; omega.
Qed.

Lemma names_of_array_in grp n x :
  In x (names_of_array grp n) -> prefix "arr" x = true.
Proof.
  unfold names_of_array.
  rewrite In_ls_init; intros [? [? ?]]; subst; simpl.
  destruct (_ ++ _)%string; eauto.
Qed.

Lemma subA_input_spec var e E Ed p :
  prefix "arr" (var_of_str var) = false ->
  prefix "sh" (var_of_str var) = false ->
  subA var e (input_spec E Ed p) |=
  input_spec E Ed p.
Proof.
  revert Ed; induction E as [|[? ?] ?]; intros Ed; simpl.
  - intros ? ? ? H; eauto.
  - intros H H' s h Hsat.
    destruct Ed as [| [? ?] ?]; [apply Hsat|].
    subA_norm_in Hsat. simpl in Hsat.
    assert (var <> Var (name_of_len (grpOfInt n))).
    { intros Hc; unfold name_of_len in Hc; subst; simpl in H'; congruence. }
    destruct var_eq_dec; try congruence.
    sep_cancel.
    revert Hsat; apply scRw; intros ? ? Hsat'.
    apply subA_is_tup_arr in Hsat'.
    rewrite sublEs_es2gls, subEs_ss2es in Hsat'; eauto.
    intros s1 Hs1 Hc; apply names_of_array_in in Hs1; subst; congruence.
    apply IHE; eauto.
Qed.

Notation perm_n n := (1 / injZ (Zn n))%Qc.

Definition P p : assn := input_spec env env_den p.

Variable get : var -> (cmd * list exp).
Variable get_den : val -> list val. 
Hypothesis get_fv :
  forall v, disjoint [I; ARR; BID] (writes_var (fst (get v))) .
Hypothesis get_res_fv :
  forall v u e, In e (snd (get v)) -> In u (fv_E e) -> prefix "x" (var_of_str u) = false.
Hypothesis get_no_bar :
  forall v, barriers (fst (get v)) = nil.
Hypothesis get_fv_sh :
  forall u v, List.In u (writes_var (fst (get v))) -> prefix "sh" (var_of_str u) = false.
Hypothesis get_fv_arr :
  forall u v, List.In u (writes_var (fst (get v))) -> prefix "arr" (var_of_str u) = false.

Hypothesis get_denote : forall (var : var) nt (tid : Fin.t nt) (val : val),
  CSL (fun _ => default nt) tid
    (!(var === val) ** !(pure (0 <= val /\ val < Zn len))%Z ** P (perm_n nt_gr))
    (fst (get var))
    (!((snd (get var)) ==t (get_den val)) ** P (perm_n nt_gr)).

Hypothesis get_den_length :
  forall v, length (get_den v) = inDim.
Hypothesis get_length :
  forall v, length (snd (get v)) = inDim.

(* code generators filling the function hole *)
(* func : the argument variable ->
    the command for getting the result and the return expression  *)
Variable func : list var -> (cmd * list exp).
Variable f_den : list val -> list val.

Hypothesis func_fv :
  forall v, disjoint [I; ARR; BID] (writes_var (fst (func v))) .
Hypothesis func_no_bar :
  forall v, barriers (fst (func v)) = nil.
Hypothesis func_fv_sh :
  forall u v, List.In u (writes_var (fst (func v))) -> prefix "sh" (var_of_str u) = false.
Hypothesis func_fv_arr :
  forall u v, List.In u (writes_var (fst (func v))) -> prefix "arr" (var_of_str u) = false.



(* {v == val} func {ret == f_den val} *)
Hypothesis func_denote : forall (var : list var) nt (tid : Fin.t nt) (val : val),
  CSL (fun _ => default nt) tid
    (!(vars2es var ==t (get_den val)) ** P (perm_n nt_gr))
    (fst (func var))
    (!((snd (func var)) ==t (f_den (get_den val)))).

Hypothesis fout_length :
  forall i, length (fout i) = outDim.
Hypothesis fden_length :
  forall v, length (f_den v) = outDim.
Hypothesis out_length :
  length out = outDim.
Hypothesis func_length :
  forall v, length (snd (func v)) = outDim.

Section block_verification.
Variable bid : Fin.t nblk.

Notation zf i := (Z_of_fin i).

Section thread_verification.
Variable tid : Fin.t ntrd.

Notation gtid := (nf tid + nf bid * ntrd).

Open Scope string.

Definition Outs := fst (fst (writeArray "Out" outDim Gl)).
Definition Len := snd (fst (writeArray "Out" outDim Gl)).
Definition setOut ix es := snd (writeArray "Out" outDim Gl) ix es.

Notation GOuts := (es2gls Outs).
Notation gl_out := (es2gls (vs2es out)).

Definition inv :=
  Ex ix, 
    !(ARR === arr) **
    !(Outs ==t out) **
    !(Len === Zn len) **
    !(I === Enum' (ix * nt_gr + gtid)) **
    !(Apure (ix * nt_gr + gtid < len + nt_gr)%nat) **
    P (perm_n nt_gr) **
    nth gtid (distribute_tup nt_gr gl_out (ix * nt_gr) (fun i => (f_den (get_den (Zn i))))%Z (nt_step nt_gr) 0 1%Qc) emp **
    nth gtid (distribute_tup nt_gr gl_out (len - (ix * nt_gr)) (fun i => fout i) (nt_step nt_gr) (ix * nt_gr) 1%Qc) emp.

Notation GTID := (TID +C BID *C Zn ntrd).

Definition xs := locals "x" inDim.

Definition catcmd := fold_right Cseq Cskip. 

Fixpoint read_tup (vs : list var) (es : list exp) :=
  match vs, es with
  | v :: vs, e :: es => (v ::= e) ;; read_tup vs es
  | _, _  => Cskip
  end.

Lemma pure_pure P stk : stk ||= !(!(P)) <=> !(P).
Proof.
  split; intros.
  apply H. unfold_conn_all; simpl.
  repeat split; destructs H; eauto.
Qed.  
    
Lemma fv_subE' var v es :
  (forall e, In e es -> ~In var (fv_E e)) ->
  subEs var v es = es.
Proof.
  induction es; intros; simpl in *; eauto.
  rewrite fv_subE; eauto; rewrite IHes; eauto.
Qed.  

Lemma read_tup_writes vs es :
  length vs = length es ->
  writes_var (read_tup vs es) = vs.
Proof.
  revert vs; induction es; intros [|v vs]; simpl in *; try congruence.
  intros; f_equal; eauto.
Qed.

Lemma read_tup_correct nt i es vs vars :
  (forall v e, In v vars -> In e es -> ~In v (fv_E e)) ->
  disjoint_list vars ->
  length vs = length es -> length vars = length es ->
  CSL (fun _ => default nt) i
    ( !(es ==t vs) )
    (read_tup vars es)
    ( !(vars2es vars ==t vs) ).
Proof.
  revert vs vars; induction es; simpl in *; intros [|v vs] [|var vars]; simpl in *; try congruence;
  intros Hfv Hdisvars Hlen1 Hlen2.
  apply rule_skip.
  lets: (>> IHes vs vars ___); try omega; jauto.
  eapply rule_seq.
  - hoare_forward.
    intros s h [v' H'].
    subA_norm_in H'. simpl in H'.
    sep_rewrite_in pure_star H'; sep_rewrite_in pure_pure H'; sep_normal_in H'.
    rewrite fv_subE in H'; eauto.
    rewrite fv_subE' in H'; [|eauto].
    assert ((!(es ==t vs) ** !(var === v)) s h).
    { sep_split_in H'.
      sep_split.
      destruct H'.
      unfold_conn_all; auto.
      split; destruct H'; eauto.
      unfold_conn_all; simpl in *; congruence. }
    exact H0.
  - eapply Hforward.
    Focus 2. { intros. sep_rewrite pure_star; sep_rewrite pure_pure. apply scC; exact H0. } Unfocus.
    apply rule_frame; eauto.
    prove_inde; rewrite Forall_forall, read_tup_writes; auto.
    intros; apply indeE_fv; simpl; intros [|]; intros; subst; jauto.
Qed.    

Lemma prefix_cat s1 s2 : prefix s1 (s1 ++ s2) = true.
Proof.
  induction s1; destruct s2; simpl; auto;
  rewrite IHs1; destruct Ascii.ascii_dec; congruence.
Qed.  

Lemma locals_pref grp d x : List.In x (locals grp d) -> prefix grp (var_of_str x) = true.
Proof.
  induction d; simpl; [destruct 1|].
  intros [H|H]; subst; simpl; eauto.
  rewrite prefix_cat; auto.
Qed.

Definition map_ker :=
  I ::= (TID +C BID *C Z.of_nat ntrd);;
  WhileI inv (I < Len) (
    (fst (get I)) ;;
    read_tup xs (snd (get I)) ;;
    (fst (func xs)) ;;
    catcmd (setOut I (snd (func xs))) ;;
    I ::= I +C Z.of_nat ntrd *C Z.of_nat nblk
  )%exp.

Ltac unfold_pures :=
  repeat lazymatch goal with
   | [H : (bexp_to_assn _) ?s (emp_ph loc) |- _] => bexp H
   | [H : _ ?s (emp_ph loc) |- _ ] => unfold_conn_in H; simpl in H
end.

Hint Rewrite Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_succ div_Zdiv : sep.

Lemma nt_gr_neq_0 : nt_gr <> 0.
Proof.
  apply Nat.neq_mul_0; tauto.
Qed.

Require Import Psatz.

Lemma id_lt_nt_gr i j n m : i < n -> j < m -> i + j * n < m * n.
Proof.
  clears_all.
  intros.
  assert (i + j * n < n + j * n) by omega.
  assert (n + j * n <= m * n) by nia.
  omega.
Qed.

Lemma nf_lt : forall n (i : Fin.t n), nf i < n.
Proof.
  clears_all; introv; destruct Fin.to_nat; simpl; omega.
Qed.

Hint Resolve nt_gr_neq_0 id_lt_nt_gr nf_lt.

Lemma distribute_eq e e' stk i nt n f' dist:
  i < nt -> (forall i, dist i < nt) ->
  (e ===l e') stk (emp_ph loc) ->
  forall s, stk ||= nth i (distribute nt e n f' dist s) emp <=>
                    nth i (distribute nt e' n f' dist s) emp.
Proof.
  induction n; simpl; intros; [split; eauto|].
  rewrite !nth_add_nth; [|rewrite distribute_length; eauto..].
  destruct beq_nat; eauto.
  assert ((e +o Zn s ===l e' +o Zn s) stk (emp_ph loc)).
  { unfold_conn_all; simpl in *; rewrite H1; eauto. }
  rewrite mps_eq1; [|exact H2].
  split; intros; sep_cancel; apply IHn; auto.
Qed.

Hint Unfold Len Outs writeArray name_of_len.

Open Scope string.

Arguments append _ _ : simpl never.

Lemma inde_eq_tup E1 E2 vs:
  List.Forall (fun e => forall v, List.In v vs -> indeE e v) E1 -> inde (E1 ==t E2) vs.
Proof.
  revert E2; induction E1; intros [|e e2]; simpl; intros; prove_inde.
  inversion H; subst.
  rewrite Forall_forall; auto.
  inversion H; subst.
  rewrite Forall_forall; auto.
  apply IHE1; inversion H; subst; auto.
Qed.

Lemma outs_inde vs :
  List.Forall (fun e => prefix "arr" (var_of_str e) = false) vs ->
  List.Forall (fun e => forall v, List.In v vs -> indeE e v) Outs.
Proof.
  rewrite !Forall_forall.
  unfold Outs, writeArray, names_of_arg, names_of_array; simpl.
  unfold ss2es; intros H x Hx.
  apply in_map_iff in Hx as [? [? Hx]]; subst.
  apply In_ls_init in Hx as [? [? ?]]; subst.
  intros.
  unfold indeE; intros; simpl; unfold var_upd.
  destruct var_eq_dec; auto.
  subst; apply H in H0; cbv in H0; congruence.
Qed.

Lemma outs_length : length Outs = outDim.
Proof.
  unfold Outs, writeArray, names_of_arg, names_of_arg, ss2es, names_of_array; simpl.
  rewrite map_length, init_length; auto.
Qed.

Lemma inde_is_tup es1 es2 vs p :
  List.Forall (fun e => forall v, List.In v vs -> indelE e v) es1 ->
  List.Forall (fun e => forall v, List.In v vs -> indeE e v) es2 ->
  inde (is_tuple_p es1 es2 p) vs.
Proof.
  revert es2; induction es1; simpl; intros [| e es2 ]; simpl; intros; prove_inde.
  inversion H; subst; rewrite Forall_forall; auto.
  inversion H0; subst; rewrite Forall_forall; auto.
  apply IHes1; inverts H; inverts H0; auto.
Qed.

Lemma inde_distribute_tup nt es l f dist (i : nat) p vs : forall s,
    List.Forall (fun e => forall v, List.In v vs -> indelE e v) es ->
      inde (List.nth i (distribute_tup nt es l f dist s p) emp) vs.
Proof.
  induction l; [unfold subA'|]; intros s Hinde; simpl in *.
  - simpl_nth; destruct (Compare_dec.leb _ _); prove_inde.
  - assert (dist s < nt \/ nt <= dist s)%nat as [|] by omega.
    + assert (i < nt \/ nt <= i)%nat as [|] by omega.
      * rewrite nth_add_nth in *; [|rewrite distribute_tup_length; auto..].
        destruct (EqNat.beq_nat _ _); intuition.
        prove_inde.
        apply inde_is_tup; auto.
        rewrite Forall_forall; unfold tarr_idx; intros ? Htmp; rewrite in_map_iff in Htmp;
        destruct Htmp as [? [? ?]]; subst.
        rewrite Forall_forall in Hinde. specialize (Hinde x0 H3); intros;
        unfold indelE in *; simpl; intros; rewrite <-Hinde; auto.
        rewrite Forall_forall; intros ? Ht; unfold vs2es in Ht; rewrite in_map_iff in Ht.
        destruct Ht as [? [? ?]]; intros; subst.
        prove_inde.
        apply IHl; eauto.
      * rewrite List.nth_overflow in *; [|rewrite add_nth_length, distribute_tup_length..]; 
        prove_inde.
    + rewrite add_nth_overflow in *; (try rewrite distribute_tup_length); auto.
Qed.

Lemma inde_vals_l vs vals :
  List.Forall (fun e => forall v, List.In v vs -> indelE e v) (es2gls (vs2es vals)).
Proof.
  unfold es2gls, vs2es; rewrite map_map, Forall_forall.
  intros x Hx; rewrite in_map_iff in Hx; destruct Hx as [? [? Hx]]; subst.
  intros; auto.
Qed.

Lemma inde_vals vs vals :
  List.Forall (fun e => forall v, List.In v vs -> indeE e v) (vs2es vals).
Proof.
  unfold vs2es; rewrite Forall_forall.
  intros x Hx; rewrite in_map_iff in Hx; destruct Hx as [? [? Hx]]; subst.
  intros; auto.
Qed.

Lemma map_correct : 
  CSL (fun n => default ntrd) tid
  (!(ARR === arr) ** 
   !(Outs ==t out) **
   !(Len === Zn len) **
   (P (perm_n nt_gr)) **
   List.nth (nf tid + nf bid * ntrd) (distribute_tup nt_gr gl_out len fout (nt_step nt_gr) 0 1%Qc) emp **
   !(BID === zf bid) ** !(TID === zf tid))

  map_ker

  ( is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr) **
    List.nth gtid (distribute_tup nt_gr gl_out len (fun v=>(f_den (get_den (Zn v))))%Z (nt_step nt_gr) 0 1%Qc) emp).
Proof.
  unfold map_ker.
  eapply rule_seq.
  { hoare_forward; intros ? ? H'.
    destruct H' as [v H']; unfold P in H'.
    subA_normalize_in H' with ( fun H => first
      [ apply subA_distribute_tup in H | apply subA_eq_tup in H
      | apply subA_is_tuple_p in H | apply subA_input_spec in H; eauto ] ).
    repeat subE_simpl in *. simpl in H'. autounfold in H'. simpl in H'.
    rewrite subE_vars2es in H'; auto.
    exact H'. }
  hoare_forward.
  { unfold inv, P; eapply Hbackward.
    Focus 2.
    { intros s h H; apply ex_lift_l_in in H as [x H]; sep_split_in H.
      change_in H.
      { unfold_pures.
        sep_rewrite_in skip_arr_tup_unfold' H; [|try first [omega | eauto]..]. 
        2: nia.
        (* sep_rewrite_in (@is_array_unfold (Gl arr) (x * nt_gr + gtid)) H; [|try first [omega | eauto]..]. *)
        (* 2: nia. *)
        (* rewrite <-plus_n_O in H. *)
      apply H. } 
      sep_combine_in H. ex_intro x H. simpl in H. exact H. } Unfocus.
    
    hoare_forward.
    eapply rule_seq. 
    { autorewrite with sep. eapply Hbackward. 
      Focus 2.
      { intros s h H.
        sep_split_in H.
        change_in H.
        Lemma mps_eq1' (E : loc_exp) (E1 E1' E2 : exp) (p : Qc) (s : stack) :
          (E1 === E1') s (emp_ph loc) ->
          s ||= (E +o E1) -->p (p, E2) <=> (E +o E1') -->p (p, E2).
        Proof.
          unfold_conn; simpl; split; intros; destruct (ledenot E _);
          try rewrite H in *; eauto.
        Qed.

        { assert (((Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))%Z === I)%exp
                      s (emp_ph loc)).
          { unfold_pures; unfold_conn; simpl; nia. }
          (* sep_rewrite_in (mps_eq1') H; [|exact H0]. *)
          Lemma mps_eq1_tup' (Es : list loc_exp) (E1 E1' : exp) (E2 : list exp) (p : Qc) (s : stack) :
            (E1 === E1') s (emp_ph loc) ->
            s ||= is_tuple_p (tarr_idx Es E1) E2 p <=>
                  is_tuple_p (tarr_idx Es E1') E2 p.
          Proof.
            revert E2; induction Es; intros [|e E2] Heq; simpl; try reflexivity.
            lets H: (>> mps_eq1' Heq); rewrite H.
            rewrite IHEs; eauto; reflexivity.
          Qed.
          sep_rewrite_in (mps_eq1_tup') H; [|exact H0]. 
          sep_combine_in H; exact H. }
        evar (P : assn).
        assert (((input_spec env env_den (1 / injZ (Zn nblk * Zn ntrd)) **
                 !(pure (0 <= (Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd)) < Zn len))%Z **
                 !(I === (Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))%Z)) ** P) s h).
        { sep_normal; repeat sep_cancel.
          sep_split; [sep_split_in H1; unfold_pures; unfold_conn; simpl in *; nia|].
          unfold P; eauto. }
        unfold P in *; apply H0. } Unfocus.
      apply rule_frame.
      { eapply Hbackward; [apply get_denote|].
        intros.
        sep_split_in H; sep_split; eauto.
        unfold_pures; unfold_conn; simpl in *.
        autorewrite with sep; auto. }
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
      
      Lemma outs_prefix x v :
        In x Outs -> In v (fv_E x) -> prefix "arr" (var_of_str v) = true.
      Proof.
        unfold Outs, writeArray, names_of_arg, ss2es, names_of_array; simpl.
        intros H; apply in_map_iff in H as [? [? H]]; subst;
        apply In_ls_init in H as [? [? H]]; subst; simpl.
        intros [?|[]]; subst; simpl; auto.
      Qed.

      { eapply outs_prefix in H3; eauto; try congruence. 
        congruence. }
      { repeat apply in_map_iff in H3 as [? [? H3]]; subst; simpl in Hc; 
        destruct Hc. }
      { repeat apply in_map_iff in H3 as [? [? H3]]; subst;
        simpl in Hc; destruct Hc as [|[]]; subst; eauto. }
      { repeat apply in_map_iff in H3 as [? [? H3]]; subst; simpl in Hc; destruct Hc. }
      { repeat apply in_map_iff in H3 as [? [? H3]]; subst; simpl in Hc; destruct Hc. } }
      
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
      eapply get_res_fv in Hc; apply locals_pref in H; eauto; congruence.
      Lemma locals_disjoint_ls grp n : disjoint_list (locals grp n).
      Proof.
        induction n; simpl; auto; split; eauto; intros Hc.
      Admitted.
      Lemma locals_length grp n : length (locals grp n) = n.
      Proof. induction n; simpl; auto; rewrite IHn; auto. Qed.
      apply locals_disjoint_ls.
      rewrite get_den_length, get_length; auto.
      unfold xs; rewrite locals_length, get_length; auto.
      rewrite read_tup_writes; [|unfold xs; rewrite locals_length, get_length; auto].
      unfold xs.
      lets Hpref: (>>locals_pref "x" inDim).
      unfold P.

      Lemma inde_is_tup_arr Es l f s p vs :
        (forall e v, In e Es -> In v vs -> indelE e v) ->
        inde (is_tuple_array_p Es l f s p) vs.
      Proof.
        revert f; induction Es; simpl; intros; eauto.
        prove_inde.
        prove_inde.
        rewrite Forall_forall; intros; apply H; eauto.
        eauto.
      Qed.  

      Lemma inde_input_spec E Ed p vs :
        (forall v, In v vs -> prefix "arr" (var_of_str v) = false) ->
        (forall v, In v vs -> prefix "sh" (var_of_str v) = false) ->
        inde (input_spec E Ed p) vs.
      Proof.
        revert Ed; induction E as [|[? ?] ?]; intros Ed; simpl.
        - intros; prove_inde.
        - intros.
          destruct Ed as [| [? ?] ?]; [prove_inde|].
          prove_inde; try (rewrite Forall_forall; intros; apply indeE_fv; simpl; eauto).
          intros Hc; destruct Hc as [|[]]; subst.
          apply H0 in H1; simpl in H1; congruence.
          apply inde_is_tup_arr; intros.
          apply indelE_fv; intros Hc; simpl in Hc.
          unfold es2gls, ss2es in H1; repeat (apply in_map_iff in H1 as [? [? H1]]; subst).
          apply names_of_array_in in H1; simpl in Hc.
          destruct Hc as [|[]]; subst; eauto; apply H in H2; simpl in H2; congruence.
          apply IHE; eauto.
      Qed.

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
      
      Lemma prefix_ex s1 s2 : prefix s1 s2 = true <-> exists s, s2 = s1 ++ s.
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
            cutrewrite (String a0 s1 ++ s = String a0 (s1 ++ s)) in H; [|auto].
            inversion H; congruence.
      Qed.
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
      Focus 2. { 
        intros s h H.
        evar (Q : assn);
        assert (((!(vars2es xs ==t get_den
                    (Zn x * (Zn nblk * Zn ntrd) + (zf tid + zf bid * Zn ntrd))%Z) **
                 P (perm_n nt_gr)) **Q) s h).
        { sep_normal; repeat sep_cancel; unfold Q; apply H. }
        unfold Q in *; clear Q; exact H0. } Unfocus.
      apply rule_frame.
      { apply func_denote. }
      specialize (func_fv X); simpl in func_fv.
      repeat prove_inde;
      (try first [apply disjoint_indeE | apply disjoint_indelE | apply disjoint_indeB]; simpl; intuition);
      try lazymatch goal with
        | [H : In _ _ |- _] => first [apply func_fv_sh in H |
                                      apply func_fv_arr in H ]; simpl in H; try congruence
      end.
      apply inde_eq_tup, outs_inde.
      rewrite Forall_forall; intros; eapply func_fv_arr; eauto.

      apply inde_distribute_tup.
      apply inde_vals_l.

      apply inde_is_tup.
      apply inde_tarr_idx.
      apply inde_vals_l.
      intros; apply indeE_fv; simpl.
      intros [? | ?]; subst; auto.
      
      apply inde_vals.
      
      apply inde_distribute_tup.
      apply inde_vals_l. }

    eapply rule_seq.
    { (* set the results to output array *)
      eapply Hbackward.
      Focus 2. {
        intros s h H.
        sep_split_in H.
        Lemma mps_eq1_tup (E1 : list exp) (E1' : list val) (E : exp) (E2 : list exp) (p : Qc) (s : stack) :
          (E1 ==t E1') s (emp_ph loc) ->
          s ||= is_tuple_p (tarr_idx (es2gls E1) E) E2 p <=>
            is_tuple_p (tarr_idx (es2gls (vs2es E1')) E) E2 p.
        Proof.
          revert E1' E2; induction E1; intros [|e1' E1'] [|e2 E2] Heq; simpl in *; try reflexivity;
          try now destruct Heq.
          sep_split_in Heq.
          assert ((Gl a +o E ===l Gl e1' +o E) s (emp_ph loc)) by (unfold_conn_all; simpl in *; congruence).
          rewrite (mps_eq1); [|apply H].
          rewrite IHE1; eauto; reflexivity.
        Qed.
        sep_rewrite_in_r mps_eq1_tup H; [|eauto].
        sep_combine_in H.
        sep_lift_in H 12; exact H.
      } Unfocus.
      apply rule_frame.
      apply gen_write_correct; simpl.
      unfold vs2es; rewrite map_length.
      rewrite fout_length, outs_length; auto.
      rewrite func_length, outs_length; auto.
      
      unfold catcmd, setOut; simpl; rewrite writes_var_gen_write.
      intros ?; destruct 1. }
    eapply Hforward.
    { hoare_forward.
      intros ? ? H; destruct H as [v H].
      sep_normal_in H.
      subA_norm_in H. simpl in H.
      unfold Outs in *; simpl in H.
      rewrite !subE_vars2es in H.
      assert ((subEs I v (snd (func X)) ==t f_den (f_ini (x * nt_gr + gtid))) s (emp_ph loc)).
      { sep_split_in H; unfold_pures; eauto. }
      Lemma mps_eq2_tup (Es : list loc_exp) E2 E2' (p : Qc) (s : stack) :
        (E2 ==t E2') s (emp_ph loc) ->
        s ||= is_tuple_p Es E2 p <=> is_tuple_p Es (vs2es E2') p.
      Proof.
        revert E2 E2'; induction Es; intros [|e E2] [|e' E2'] Heq; simpl in *;
          try first [now destruct Heq | reflexivity | congruence].
        sep_split_in Heq.
        lets H: (>> mps_eq2 HP); rewrite H.
        rewrite IHEs; eauto; reflexivity.
      Qed.

      sep_rewrite_in mps_eq2_tup H; [|exact H0].
      subE_simpl in *.
      rewrite sublEs_tarr_idx in H.
      ex_intro v H. exact H. auto. }
    
    unfold inv; intros s h H. destruct H as (v & H); simpl in H.
    sep_normal_in H; sep_split_in H.
    unfold_pures; subst.
    unfold Outs, writeArray, names_of_arg; simpl.
    exists (S x); autorewrite with sep.
    sep_split; try now (unfold_conn; simpl; auto; omega).
    { rewrite <-out_length; auto. }
    { unfold_conn; simpl. rewrite HP7. ring. }
    sep_rewrite (@is_array_unfold (Gl arr) (x * nt_gr + gtid)); try omega; eauto.
    lets Heq: (sublEs_es2gls); unfold es2gls in Heq; rewrite !Heq in H.
    rewrite subE_vars2es in H; auto.
    sep_rewrite_r (@skip_arr_tup_fold' (nf tid + nf bid * ntrd) gl_out); try omega; eauto.
    sep_normal; simpl.
    simpl; repeat sep_cancel.
    cuts_rewrite (len - (nt_gr + x * nt_gr) = len - x * nt_gr - nt_gr); [|nia].
    sep_rewrite_r mps_eq1_tup; [|apply HP2].
    unfold Outs, es2gls in *; simpl. 
    repeat autorewrite with sep. repeat sep_cancel. }
  { unfold inv; intros s h H. apply ex_lift_l_in in H as [x H]. sep_split_in H. unfold_pures.
    rewrite HP2, HP3 in n; rewrite <-Nat2Z.inj_lt in n.
    assert (len - x * nt_gr <= nf tid + nf bid * ntrd) by (zify; omega).
    assert (nf tid + nf bid * ntrd < nt_gr) by auto.
    sep_cancel.
    (* apply scC in H; sep_rewrite_in nth_dist_nil H; try omega; eauto. *)
    (* 2: instantiate (1 :=len - x * nt_gr); intros j Hj; unfold nt_step. *)
    (* 2: rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try (zify; omega). *)
    sep_lift_in H2 1; sep_rewrite_in nth_dist_nil_tup H2; try omega; eauto.
    2: instantiate (1 :=len - x * nt_gr); intros j Hj; unfold nt_step.
    2: rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try (zify; omega).
    rewrite minus_diag in H2; simpl in H2.
    rewrite nth_nseq in H2.
    assert (x * nt_gr <= len \/ len < x * nt_gr) as [|] by omega.
    - apply scC in H2; sep_rewrite_in nth_dist_tup_ext H2; try omega; auto.
      2: instantiate (1 :=len - x * nt_gr); intros j Hj; simpl; unfold nt_step;
         rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try omega.
      sep_normal_in H2.
      (* sep_rewrite_in nth_dist_ext H2; try omega; auto. *)
      (* 2: instantiate (1 :=len - x * nt_gr); intros j Hj; simpl; unfold nt_step. *)
      (* 2: rewrite plus_comm, Nat.mod_add; auto; rewrite Nat.mod_small; auto; try omega. *)
      cutrewrite (x * nt_gr + (len - x * nt_gr) = len) in H2; [|omega].
      destruct Compare_dec.leb; sep_normal_in H2; sep_split; try now (unfold_conn; simpl; auto); sep_cancel.
    - (* apply scC in H2; sep_rewrite nth_dist_ext; try omega; auto. *)
      (* cutrewrite (len - x * ntrd = 0) in H2; [|omega]. *)
      cutrewrite (x * nt_gr = len + (x * nt_gr - len)) in H2; [|omega].
      assert (forall j, j < x * nt_gr - len -> nt_step nt_gr (0 + len + j) <> nf tid + nf bid * ntrd).
      { unfold nt_step; simpl; intros j Hj Hc.
        assert (len + j + nt_gr < (S x) * nt_gr) by (simpl; omega).
        assert (x * nt_gr + j + (nf tid + nf bid * ntrd) < len + j + nt_gr) by omega.
        let t := (eval simpl in (Nat.mod_add (len + j) 1 nt_gr)) in pose proof t.
        rewrite mult_1_l in H6.
        rewrite (Nat.div_mod (len + j + nt_gr) nt_gr), H6 in H4, H5; auto.
        assert (x * nt_gr  < nt_gr * ((len + j + nt_gr) / nt_gr)) by omega.
        assert (nt_gr * ((len + j + nt_gr) / nt_gr) < S x * nt_gr) by omega.
        rewrite mult_comm in H7; apply Nat.mul_lt_mono_pos_l in H7; try omega.
        rewrite mult_comm in H8; apply Nat.mul_lt_mono_pos_r in H8; omega. } 
      sep_rewrite_in_r nth_dist_tup_ext H2; try omega; eauto.
      sep_split; auto.
      destruct Compare_dec.leb; sep_normal_in H2; repeat sep_cancel. }

  {  intros s h H; unfold inv; exists 0; simpl.
     sep_split_in H; unfold_pures; sep_split; auto.
     - unfold_conn; simpl; autorewrite with sep. unfold_conn_in HP; simpl in HP. 
       repeat match goal with [H : _ = _|- _] => first [rewrite <-H | rewrite H]; clear H end; auto.
     - unfold_conn. assert (nf tid + nf bid * ntrd < nt_gr) by auto. omega.
     - rewrite <-minus_n_O, nth_nseq; destruct Compare_dec.leb; sep_normal; sep_cancel. }
Qed.
End thread_verification.

Require Import Bdiv.
Local Notation init := MyVector.init.
Definition bth_pre :=
  !(ARR === arr) **
  !(Outs ==t out) **
  !(Len === Zn len) **
  conj_xs (ls_init 0 ntrd (fun i =>
    is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr))) **
  conj_xs (ls_init 0 ntrd (fun i =>
    nth (i + nf bid * ntrd)
    (distribute_tup nt_gr (es2gls (vs2es out)) len fout (nt_step nt_gr) 0 1) emp)).

Definition tr_pres := init (fun i : Fin.t ntrd =>
  !(ARR === arr) ** 
  !(Outs ==t out) ** 
  !(Len === Zn len) ** 
  is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr) **
  nth (nf i + nf bid * ntrd)
    (distribute_tup nt_gr (es2gls (vs2es out)) len fout (nt_step nt_gr) 0 1) emp **
  !(BID === zf bid)).

Definition bth_post  :=
  conj_xs (ls_init 0 ntrd (fun i =>
    is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr))) **
  conj_xs (ls_init 0 ntrd (fun i =>
    nth (i + nf bid * ntrd)
      (distribute_tup nt_gr (es2gls (vs2es out)) len
        (fun v : nat => f_den (f_ini v)) (nt_step nt_gr) 0 1) emp)).

Definition tr_posts := (init (fun i : Fin.t ntrd =>
  is_array_p (Gl arr) len f_ini 0 (perm_n nt_gr) **
  nth (nf i + nf bid * ntrd)
    (distribute_tup nt_gr (es2gls (vs2es out)) len
      (fun v : nat => f_den (f_ini v)) (nt_step nt_gr) 0 1) emp)).

Definition out_vars := List.map Var (names_of_array "Out" outDim).

Definition E : env := fun v =>
  if var_eq_dec v BID then Lo
  else if var_eq_dec v ARR then Lo
  else if var_eq_dec v (Var "shOut") then Lo
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
  pose (map_ker tid0) as map'; unfold map_ker, WhileI in map'; exact map'.
Defined.

Definition bspec : (barrier_spec ntrd) := fun i => (default ntrd).

Lemma precise_false : precise (fun _ _ => False).
Proof.
  unfold precise; intros; tauto.
Qed.

Lemma map_correct_b :
  CSLp ntrd E (bth_pre ** !(BID === zf bid)) map' (bth_post).
Proof.
  applys (>> rule_par bspec tr_pres tr_posts);
  try first [omega | nia | eauto].
  - destruct ntrd; eexists; try omega; eauto.
  - unfold bspec; split; intros; unfold default; simpl; rewrite MyVector.init_spec;
    unfold CSL.low_assn, low_assn, indeP; tauto.
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
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    repeat sep_cancel.
  - unfold tr_posts, bth_post; intros s h H.
    istar_simplify_in H.
    sep_cancel.
  - intros; unfold tr_pres; rewrite MyVector.init_spec.
    unfold CSL.low_assn.
    repeat prove_low_assn; eauto.
    Lemma low_assn_eqt E1 E2 G :
      List.Forall (fun e => typing_exp G e Lo) E1 -> low_assn G (E1 ==t E2).
    Proof.
      revert E2; induction E1; simpl; intros [|e2 E2]; simpl; repeat prove_low_assn.
      intros; inversion H; subst.
      repeat prove_low_assn; eauto.
    Qed.
    apply low_assn_eqt.
    unfold Outs, writeArray, names_of_arg, vars2es, names_of_array; simpl.
    rewrite Forall_forall.
    intros x H; rewrite in_map_iff in H; destruct H as [? [? ?]]; subst.

    rewrite In_ls_init in H0; destruct H0 as [z [? ?]]; subst.
    constructor; unfold E; simpl; auto.
    constructor; eauto.

    Lemma low_assn_is_tuple G E1 E2 q :
      List.Forall (fun e => typing_lexp G e Lo) E1 ->
      List.Forall (fun e => typing_exp G e Lo) E2 ->
      low_assn G (is_tuple_p E1 E2 q).
    Proof.
      revert E2; induction E1; intros [|e2 E2]; simpl; rewrite !Forall_forall; intros;
      repeat prove_low_assn.
      apply H; simpl; eauto.
      apply H0; simpl; eauto.
      apply IHE1; rewrite !Forall_forall; intros; [apply H | apply H0]; simpl; eauto.
    Qed.

    Lemma low_assn_skip_arr_tup G Es n skip f dist i p : forall st,
        Forall (fun e => typing_lexp G e Lo) Es ->
        low_assn G (nth i(distribute_tup skip Es n f dist st p) emp).
    Proof.
      assert (skip = 0 \/ skip <> 0) as [|] by omega.
      - subst; induction n; simpl in *; intros s He.
        destruct i; apply low_assn_emp.
        unfold nt_step; simpl.
        rewrite nth_overflow; [apply low_assn_emp|].
        rewrite add_nth_length, distribute_tup_length; omega.
      - unfold skip_arr; induction n; simpl in *; intros s He.
        + rewrite nth_nseq; destruct leb; apply low_assn_emp.
        + assert (i < skip \/ skip <= i) as [|] by omega.
          assert(dist s < skip \/ skip <= dist s) as [|] by omega.
          rewrite nth_add_nth; [|try rewrite distribute_tup_length; unfold nt_step; eauto..].
          destruct (beq_nat i (dist s)) eqn:Heq.
          apply low_assn_star; eauto.
          apply low_assn_is_tuple.
          rewrite Forall_forall in *; intros x H'.
          unfold tarr_idx in H'; rewrite in_map_iff in H'; destruct H' as [y [? ?]]; subst.
          cutrewrite (Lo = join Lo Lo); [|eauto].
          repeat constructor; eauto.
          unfold vs2es; rewrite Forall_forall; intros ? H'; apply in_map_iff in H' as [? [? ?]]; subst; constructor.
          eauto.
          rewrite add_nth_overflow; [|rewrite distribute_tup_length; eauto].
          apply IHn; auto.
          rewrite nth_overflow.
          apply low_assn_emp.
          rewrite add_nth_length, distribute_tup_length; eauto.
    Qed.

    apply low_assn_skip_arr_tup.
    apply Forall_forall; intros ? H. unfold es2gls, vs2es in H.
    repeat (rewrite in_map_iff in H; destruct H as [? [? H]]; subst).
    repeat constructor.
  - intros; unfold CSL.low_assn, tr_posts; rewrite MyVector.init_spec.
    repeat prove_low_assn. 
    constructor; eauto.
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
    lets: (>>disjoint_not_in_r v (func_fv X) H).
    lets: (>>func_fv_arr v X H).
    lets: (>>func_fv_sh v X H).
    unfold E, var_of_str in *; simpl in *.
    repeat lazymatch goal with
      | [|- (if ?B then _ else _) = _] => destruct B eqn:?; first [intuition | congruence]
    end.
    subst v; simpl in H2; simpl in H2; congruence.
    apply typing_cmd_Hi.
    apply gen_write_no_bars.
    unfold catcmd, setOut, writeArray; simpl; intros ?; rewrite writes_var_gen_write; simpl; try tauto.
  - unfold tr_pres, tr_posts; intros; rewrite !MyVector.init_spec.
    unfold bspec, skip_arr.
    eapply Hbackward.
    eapply Hforward.
    apply map_correct.
    intros.
    
    apply H.
    intros; sep_normal_in H; sep_normal; repeat sep_cancel.
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
Definition bl_posts : Vector.t assn nblk :=
  MyVector.init (fun b : Fin.t nblk => (bth_post b)).

Definition bid0 : Fin.t nblk.
  destruct nblk; try omega.
  exact Fin.F1.
Qed.

Theorem map_correct_g  :
  CSLg ntrd nblk ntrd_neq0 nblk_neq0
    (!(ARR === arr) ** !(Outs ==t out) ** !(Len === Zn len) **
     is_array (Gl arr) len f_ini 0 **
     is_tuple_array_p (es2gls (vs2es out)) len fout 0 1)
    (Pr nil (map' bid0))
    (is_array (Gl arr) len f_ini 0 **
     is_tuple_array_p (es2gls (vs2es out)) len (fun v => f_den (f_ini v))%Z 0 1).
Proof.
  applys (>> rule_grid E bl_pres bl_posts).
  - intros s h H.
    unfold bl_pres, bth_pre.
    sep_split_in H.
    istar_simplify.
    repeat sep_rewrite (@ls_star nblk).
    repeat sep_rewrite (@ls_pure nblk); sep_split.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
    repeat (sep_rewrite_r is_array_skip_arr); sep_cancel; eauto.
    Lemma conj_xs_init_flatten (l1 l2 : nat) (a : assn) :
      forall (s : nat) (stk : stack),
        stk
          ||= conj_xs
          (ls_init s l1
             (fun i : nat =>
                conj_xs (ls_init 0 l2 (fun j : nat => a)))) <=>
          conj_xs (ls_init (s * l2) (l1 * l2) (fun i : nat => a)).
    Proof.          
      induction l1; simpl.
      - intros; reflexivity.
      - intros; rewrite IHl1.
        rewrite ls_init_app, conj_xs_app; simpl.
        erewrite ls_init_eq.
        cutrewrite (l2 + s * l2 = s * l2 + l2); [|ring].
        rewrite <-plus_n_O.
        reflexivity.
        intros; simpl; auto.
    Qed.
    Lemma is_array_skip_arr Es n m len' f p :
      n <> 0 -> m <> 0 ->
      (forall i : nat, i < len' -> length (f i) = length Es) ->
      forall stk, stk ||= 
        is_tuple_array_p Es len' f 0 p <=>
        conj_xs (ls_init 0 n (fun i =>
        conj_xs (ls_init 0 m (fun j =>
        nth (j + i * m) (distribute_tup (n * m) Es len' f (nt_step (n * m)) 0 p) emp)))).
    Proof.
      intros.
      lets flat: (>>conj_xs_init_flatten0 n m 
         (fun x => nth x (distribute_tup (n * m) Es len' f (nt_step (n * m)) 0 p) emp)).
      simpl in flat. rewrite flat.
      lets Heq: (>>distribute_correct (n * m) (nt_step (n * m))); rewrite Heq; clear Heq.
      2: unfold nt_step; intros; apply Nat.mod_upper_bound; nia.
      eapply (@equiv_from_nth emp).
      rewrite init_length, distribute_tup_length; ring. 
      rewrite distribute_tup_length; intros i Hi stk'.
      rewrite ls_init_spec; destruct lt_dec; try omega.
      reflexivity.
      auto.
    Qed.
    
    sep_rewrite conj_xs_init_flatten; simpl.
    lets Heq: (>>is_array_is_array_p_1 __ __ nt_gr 0); try nia. sep_rewrite_in Heq H.
    sep_cancel.
    sep_rewrite_r is_array_skip_arr; auto.
    intros; simpl; unfold es2gls, vs2es; rewrite !map_length.
    unfold val in *; rewrite out_length, fout_length; auto.
  - unfold bl_pres, bl_posts; intros.
    rewrite !MyVector.init_spec.
    eapply CSLp_backward.
    eapply CSLp_forward.
    apply (map_correct_b bid).
    intros; simpl; sep_normal; eauto.
    intros; simpl in *; sep_normal_in H; eauto.
  - unfold bl_posts, bth_post.
    intros s h H.
    istar_simplify_in H.
    sep_rewrite_in conj_xs_init_flatten H; simpl in H.
    lets Heq: (>>is_array_is_array_p_1 __ __ nt_gr); sep_rewrite Heq; eauto; try nia.
    sep_rewrite is_array_skip_arr; eauto.
    unfold es2gls, vs2es, val in *; rewrite !map_length; intros.
    rewrite out_length, fden_length; auto.
  - prove_inde.
  - intros; unfold bl_pres, bth_pre.
    rewrite MyVector.init_spec.
    prove_inde.
    apply inde_eq_tup, Forall_forall; unfold Outs, writeArray, names_of_arg; simpl; intros x H.
    unfold vars2es, names_of_array in H;
      rewrite in_map_iff in H; destruct H as [? [? H]]; subst; rewrite In_ls_init in H;
      destruct H as [? [? ?]]; subst.
    intros; destruct H as [? | [? | ?]]; try tauto; subst;
    prove_indeE.
    apply inde_conj_xs; rewrite init_length; intros;
    rewrite ls_init_spec; destruct lt_dec; prove_inde;
    apply inde_distribute; prove_indeE.
    apply inde_conj_xs; rewrite init_length; intros;
    rewrite ls_init_spec; destruct lt_dec; prove_inde.

    
    apply inde_distribute_tup; prove_indeE.
    unfold es2gls, vs2es; rewrite Forall_forall; intros ? Ht;
    repeat (rewrite in_map_iff in Ht;  destruct Ht as [? [? Ht]]; subst).
    simpl; intros; auto.
  - intros bid; unfold bl_pres, bth_pre; rewrite MyVector.init_spec.
    Hint Constructors typing_exp typing_lexp.
    repeat prove_low_assn; eauto.
    apply low_assn_eqt. unfold Outs.
    rewrite Forall_forall.
    Lemma writeArray_vars grp dim pl x: 
      pl = Gl \/ pl = Sh ->
      In x (fst (fst (writeArray grp dim pl))) ->
      exists st, (Evar (Var st)) = x /\ prefix "arr" st = true.
    Proof.
      unfold writeArray, names_of_arg, names_of_array, vars2es; simpl.
      intros H; rewrite in_map_iff; intros [? [? H']]; rewrite In_ls_init in H';
      destruct H' as [? [? H']]; subst; simpl.
      eexists; split; [reflexivity|].
      simpl; destruct (_ ++ _)%string; eauto.
    Qed.
    intros x H; apply writeArray_vars in H.
    destruct H as [? [? H]]; subst.
    constructor; unfold E.
    unfold var_of_str. rewrite H.
    repeat lazymatch goal with [|- context [if ?X then _ else _]] => destruct X; auto end.
    jauto.
    constructor; eauto.
    apply low_assn_conj_xs; rewrite init_length; intros.
    rewrite ls_init_spec; destruct lt_dec; try repeat prove_low_assn.
    repeat constructor; eauto.
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
    apply has_no_vars_is_array_p; repeat constructor.
    Lemma has_no_vars_is_tup es1 es2 p :
      List.Forall (fun e => has_no_vars_lE e) es1 ->
      List.Forall (fun e => has_no_vars_E e) es2 ->
      has_no_vars (is_tuple_p es1 es2 p).
    Proof.
      revert es2; induction es1; simpl; intros [| e es2 ]; simpl; intros; try apply has_no_vars_emp.
      inverts H; inverts H0.
      has_no_vars_assn.
      apply has_no_vars_mp; eauto.
      apply IHes1; eauto.
    Qed.

    Lemma has_no_vars_skip_arr_tup (Es : list loc_exp) (n skip : nat) (f : nat -> list Z) (i st : nat) dist p :
      forall s, 
        Forall (fun e => has_no_vars_lE e) Es ->
        has_no_vars (nth i (distribute_tup skip Es n f dist s p) emp).
    Proof.
      induction n; intros s Hinde; simpl in *.
      - simpl_nth; destruct (Compare_dec.leb _ _); prove_inde.
      - assert ( dist s < skip \/ skip <= dist s)%nat as [|] by omega.
        + assert (i < skip \/ skip <= i)%nat as [|] by omega.
          * rewrite nth_add_nth in *; [|rewrite distribute_tup_length; auto..].
            destruct (EqNat.beq_nat _ _); intuition.
            has_no_vars_assn.
            apply has_no_vars_is_tup; auto.
            rewrite Forall_forall; unfold tarr_idx; intros ? Htmp; rewrite in_map_iff in Htmp;
            destruct Htmp as [? [? ?]]; subst.
            rewrite Forall_forall in Hinde; specialize (Hinde x0 H3); intros;
            unfold has_no_vars in *; simpl; intros; split; eauto.
            unfold vs2es; rewrite Forall_forall; unfold tarr_idx; intros ? Htmp; rewrite in_map_iff in Htmp.
            destruct Htmp as [? [? ?]]; subst.
            unfold has_no_vars_E; auto.
            eauto.
          * rewrite List.nth_overflow in *; [|rewrite add_nth_length, distribute_tup_length..]; 
            prove_inde.
        + rewrite add_nth_overflow in *; (try rewrite distribute_tup_length); auto.
    Qed.
    apply has_no_vars_skip_arr_tup; repeat constructor.
    unfold es2gls, vs2es.
    rewrite Forall_forall; rewrite map_map; intros ? H'; rewrite in_map_iff in H';
    destruct H' as [? [? ?]]; subst; prove_inde.
  - simpl; tauto.
  - unfold E; eauto.
  - unfold E; eauto.
  - eauto.
  - eauto.
  - simpl; eauto.
Qed.
    
End Map.