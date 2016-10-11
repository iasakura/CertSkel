Require Import LibTactics Psatz.
Require Import GPUCSL SkelLib scan_lib CSLTactics.
Require Import CUDALib TypedTerm.
Require Import Host.
Require Import Skel_lemma CodeGen CUDALib Correctness Grid CSLTactics CSLLemma.

Notation fin_star n f :=
  (istar (ls_init 0 n f)).

Section mkReduce.

Variable typ : Skel.Typ.

Variable ntrd nblk : nat.
Variable e_b : nat.

Hypothesis ntrd_neq_0: ntrd <> 0.
Hypothesis nblk_neq_0: nblk <> 0.

Hypothesis max_th_size : ntrd <= 2 ^ e_b.
Hypothesis eb_neq_0 : e_b <> 0.

Variable GA : list Skel.Typ.
Variable avar_env : AVarEnv GA.
Variable aptr_env : APtrEnv GA.
Variable aeval_env : AEvalEnv GA.
Notation kinv R P E p := (kernelInv avar_env aptr_env aeval_env R P E p).
Hypothesis Haok : aenv_ok avar_env.
Notation p := (RP (ntrd * nblk)).

Variable arr : Skel.AE GA typ.
Variable arr_c : var -> (cmd * vars typ).
Hypothesis arr_ok : ae_ok avar_env arr arr_c.

Variable func : Skel.Func GA (Skel.Fun2 typ typ typ).
Variable func_c : vars typ -> vars typ -> (cmd * vars typ).
Hypothesis f_ok : func_ok avar_env func func_c.

Variable f_tot : Skel.typDenote typ -> Skel.typDenote typ -> Skel.typDenote typ.
Infix "\op" := f_tot (at level 50, left associativity).

Hypothesis f_total :
  forall x y, Skel.funcDenote _ _ func aeval_env x y = Some (x \op y).

Hypothesis f_comm : 
  forall x y, x \op y = y \op x.
Hypothesis f_assoc :
  forall x y z, x \op y \op z = x \op (y \op z).

Variable result : Skel.aTypDenote typ.
Hypothesis eval_reduce_ok :
  Skel.skelDenote _ _ (Skel.Reduce _ _ func arr) aeval_env = Some result.

Variable outp : vals typ.
Variable outs : list (vals typ).
Hypothesis outs_length : length (outs) = nblk + 0.
Notation sarr := (locals "_sarr" typ 0).

Definition outArr ty := locals "_arrOut" ty 0.
Notation out := (outArr typ).
Notation len := inp_len_name.
Definition dist_outs i := i * ntrd.

Lemma eval_arr_ok :
  { arr_res | Skel.aeDenote _ _ arr aeval_env = Some arr_res}.
Proof.
  simpl in *; unfold Monad.bind_opt in *.
  destruct Skel.aeDenote; simpl in *; inverts eval_reduce_ok; eexists; eauto.
Qed.

Definition arr_res : Skel.aTypDenote typ := let (a, _) := eval_arr_ok in a.

Definition eval_arr_ok' : Skel.aeDenote _ _ arr aeval_env = Some arr_res.
Proof.
  unfold arr_res; destruct eval_arr_ok; eauto.
Qed.

Hint Resolve eval_arr_ok' : pure_lemma.

Notation xs := (locals "xs" typ 0).
Notation ys := (locals "ys" typ 0).
Notation zs := (locals "zs" typ 0).
Notation t := (locals "t" typ 0).

Notation g := (fun x => gets' arr_res x).

Definition reduce_body n s :=
  (Cbarrier (n - 1) ;;
   Cif (Band ("tid" +C Zn s <C "slen") ("tid" <C Zn s)) (
     reads xs (ty2ctys typ) (v2sh sarr +os ("tid" +C Zn s)) ;;
     assigns_call2 zs func_c ys xs ;;
     assigns ys (ty2ctys typ) (v2e zs) ;;
     writes (v2sh sarr +os "tid") (v2e ys)
   ) Cskip
  )%exp.

Definition st n := 2 ^ (e_b - n).

Fixpoint reduce_aux t m :=
  match m with
  | O => Cskip    
  | S m =>
    reduce_body t (st t) ;; reduce_aux (S t) m 
  end.

Definition reduceBlock := reduce_aux 1 e_b.

Definition seq_reduce inv :=
  assigns ys (ty2ctys typ) (vals2es defval) ;;
  writes (v2sh sarr +os "tid") (vals2es defval) ;;
  "ix" :T Int ::= ("tid" +C "bid" *C Zn ntrd) ;;
  Cif ("ix" <C len) (
    assigns_get ys arr_c "ix" ;;
    "ix" ::= "ix" +C Zn ntrd *C Zn nblk ;;
    WhileI inv ("ix" < len) (
      assigns_get xs arr_c "ix" ;;
      assigns_call2 zs func_c ys xs ;;
      assigns ys (ty2ctys typ) (v2e zs) ;;
      "ix" ::= "ix" +C Zn ntrd *C Zn nblk
    );;
    writes (v2sh sarr +os "tid") (v2e ys)
  ) Cskip.

Definition setToLen :=
  Cif (len <C "bid" *C Zn ntrd) (
    "slen" :T Int ::= 0%Z 
  ) (Cif (len <C ("bid" +C 1%Z) *C Zn ntrd) (
    "slen" :T Int ::= len -C "bid" *C Zn ntrd 
  ) (
    "slen" :T Int ::= Zn ntrd
  )).

Definition mkReduce_cmd :=
  seq_reduce FalseP ;;
  setToLen ;;
  reduceBlock ;;
  Cif ("tid" == 0%Z) (
    writes (v2gl out +os "bid") (v2e ys) 
  ) Cskip.

Section Sum_of.
  Variable T : Type.
  Variable op : T -> T -> T.
  Hypothesis op_assoc : forall x y z, op (op x y) z = op x (op y z).
  Hypothesis op_comm : forall x y, op x y = op y x.
  Variable u : T.
  Definition op' x y : option T :=
    match x, y with
    | None, _ => y
    | _, None => x
    | Some x, Some y => Some (op x y)
    end.
  Notation "a '+++' b" := (op' a b) (at level 40, left associativity).
  
  Lemma opopt_assoc x y z : op' (op' x y) z = op' x (op' y z).
  Proof.
    destruct x, y, z; simpl; eauto.
    rewrite op_assoc; eauto.
  Qed.
  
  Lemma opopt_comm x y : op' x y = op' y x.
  Proof.
    destruct x, y; simpl; eauto.
    rewrite op_comm; eauto.
  Qed.
  
  Arguments op' _ _ : simpl never.
  
  Fixpoint sum_of_f_opt (s len : nat) f : option T :=
    match len with
    | 0 => None
    | S l => Some (f s) +++ sum_of_f_opt (S s) l f
    end.

  Fixpoint skip_sum_of_opt skip (s len : nat) f i : option T :=
    match len with
    | 0 => None
    | S l =>
      if Nat.eq_dec (s mod skip) i 
      then (skip_sum_of_opt skip (S s) l f i +++ Some (f s))%Z
      else skip_sum_of_opt skip (S s) l f i
    end.
  
  Lemma sum_of_eq s len f1 f2: 
    (forall i, s <= i < s + len -> f1 i = f2 i) ->
    sum_of_f_opt s len f1 = sum_of_f_opt s len f2.
  Proof.
    revert s; induction len; simpl; intros s H; eauto. 
    rewrite IHlen; eauto; intros; try omega.
    rewrite H; eauto; omega.
    rewrite H; eauto; try omega.
  Qed.

  Lemma sum_of_f_split s n m f g :
    s <= m -> m < s + n ->
    sum_of_f_opt s n (fun i => if lt_dec i m then f i else g i) = 
    (sum_of_f_opt s (m - s) f +++ sum_of_f_opt m (n - (m - s)) g)%Z.
  Proof.
    revert s m; induction n.
    - intros s m Hsm Hmn; assert (Heq : (m - s) = 0) by omega; rewrite Heq in *; simpl; eauto.
    - intros s m Hsm Hmn; remember (S n - (m - s)); simpl in *.
      assert (s = m \/ s < m) as [Hsm' | Hsm'] by omega; subst.
      + destruct lt_dec; try omega.
        rewrite minus_diag; simpl.
        (* rewrite minus_diag, <-minus_n_O in *; simpl. *)
        erewrite sum_of_eq; unfold op'; simpl; eauto.
        intros i Hi; destruct lt_dec; eauto; try omega.
      + destruct lt_dec; try omega.
        assert (exists ms, m - s = S ms) as [ms Hms]
                                           by (exists (m - s - 1); omega); rewrite Hms.
        simpl.
        rewrite IHn; try omega.
        rewrite opopt_assoc; repeat f_equal; omega.
  Qed.

  Lemma shift_values :
    forall (l1 : nat) (fc : nat -> T) (s sft : nat),
      (sum_of_f_opt s l1 fc +++ sum_of_f_opt (s + sft) l1 fc)%Z =
      sum_of_f_opt s l1 (fun i : nat => (op (fc i) (fc (i + sft)%nat))%Z).
  Proof.
    induction l1; intros fc s sft; simpl; auto.
    cutrewrite (S (s + sft) = S s + sft); [|omega].
    rewrite <-IHl1; simpl.
    rewrite <-!opopt_assoc.
    cutrewrite (Some (op (fc s) (fc (s + sft))) = Some (fc s) +++ Some (fc (s + sft)));
      [|reflexivity].
    f_equal; rewrite !opopt_assoc; f_equal; rewrite opopt_comm; eauto.
  Qed.

  Lemma sum_of_concat :
    forall (l1 : nat) (fc : nat -> T) (s l2 : nat),
      sum_of_f_opt s (l1 + l2) fc = (sum_of_f_opt s l1 fc +++ sum_of_f_opt (l1 + s) l2 fc)%Z.
  Proof.
    induction l1; intros fc s l2; simpl; auto.
    rewrite IHl1, opopt_assoc; do 3 f_equal; omega.
  Qed.

  Lemma skip_sum_opt_nil skip i next fc : forall s (len : nat),
      (forall j, j < next -> (s + j) mod skip <> i) ->
      skip_sum_of_opt skip s len fc i =
      skip_sum_of_opt skip (s + next) (len - next) fc i.
  Proof.
    induction next; intros s len Hj; simpl.
    - rewrite <-plus_n_O, <-minus_n_O; auto.
    - destruct len; auto.
      cutrewrite (s + S next = S s + next); [|omega].
      cutrewrite (S len - S next = len - next); [|omega].
      rewrite <-IHnext.
      + simpl; destruct Nat.eq_dec; auto.
        specialize (Hj 0); rewrite <-plus_n_O in Hj; apply Hj in e; [tauto|omega].
      + intros j Hjn; cutrewrite (S s + j = s + S j); [|omega]; apply Hj; omega.
  Qed.
  
  Lemma skip_sum_opt_unfold skip i (len : nat) fc : forall s,
      skip <> 0 ->
      (i < len)%nat -> (i < skip)%nat ->
      skip_sum_of_opt skip (s * skip) len fc i =
      (op' (skip_sum_of_opt skip (S s * skip)%nat (len - skip)%nat fc i)%Z
                  (Some (fc (i + s * skip)%nat))).
  Proof.
    intros s Hskip Hil His.
    rewrite skip_sum_opt_nil with (next:=i). 
    2: intros; rewrite plus_comm, Nat.add_mod; auto.
    2: rewrite Nat.mod_mul; auto; rewrite <-plus_n_O, Nat.mod_mod; auto; rewrite Nat.mod_small; omega.
    assert (exists li, len - i = S li) as [li Hli] by (exists (len - i - 1); omega).
    rewrite (plus_comm (s * skip));
      rewrite Hli; simpl; destruct Nat.eq_dec as [He | He].
    2 : rewrite Nat.mod_add in He; auto; rewrite Nat.mod_small in He; omega.
    f_equal.
    rewrite skip_sum_opt_nil with (next:= skip - S i).
    lazymatch goal with [|- context [skip_sum_of_opt _ ?X _ _ _]] => cutrewrite (X = skip + s * skip); [|omega] end.
    cutrewrite (li - (skip - S i) = len - skip); [|omega]; auto.
    intros j Hj. 
    lazymatch goal with [|- context [?X mod _]] => cutrewrite (X = (S i + j) + s * skip); [|omega] end.
    rewrite Nat.mod_add; auto; rewrite Nat.mod_small; omega.
  Qed.

  Lemma skip_sum_opt_sum f skip i s n m :
    i < skip ->
    skip * n + i < m + skip <= skip * S n + i ->
    skip_sum_of_opt skip (s * skip) m f i =
    sum_of_f_opt s n (fun j => f (i + j * skip)).
  Proof.
    revert s m; induction n; simpl; intros s m His Hmi.
    - assert (m <= i) by omega.
      rewrites* (>>skip_sum_opt_nil m).
      { intros; rewrite plus_comm; rewrite Nat.mod_add; try omega;
        rewrite Nat.mod_small; try omega. }
      rewrite minus_diag; simpl; eauto.
    - rewrites* skip_sum_opt_unfold; [|nia..].
      destruct n; simpl.
      + rewrites (>>skip_sum_opt_nil (m - skip)); try rewrite minus_diag; simpl; eauto.
        intros; cutrewrite (skip + s * skip + j = j + (S s) * skip); [|ring];
          rewrite Nat.mod_add; try omega; rewrite Nat.mod_small; try omega.
      + cutrewrite (skip + s * skip = S s * skip); [|ring].
        rewrite IHn; [|try omega..].
        2: nia.
        repeat (unfold op'; simpl).
        repeat lazymatch goal with
        | [|- context [match ?X with Some _ => _ | None => _ end]] => destruct X
        end; eauto.
        rewrite op_comm; auto.
  Qed.
  
  Lemma skip_sum_sum0 f skip i n m :
    i < skip ->
    skip * n + i < m + skip <= skip * S n + i ->
    skip_sum_of_opt skip 0 m f i =
    sum_of_f_opt 0 n (fun j => f (i + j * skip)).
  Proof.
    cutrewrite (0 = 0 * skip); [|omega]; apply skip_sum_opt_sum.
  Qed.
End Sum_of.

Section blockReduce.
Variable tid : Fin.t ntrd.
Variable bid : Fin.t nblk.
Variable inp : list (Skel.typDenote typ).
Hypothesis inp_length : length inp = ntrd.
Variable l : nat.
Hypothesis l_le_ntrd : l <= ntrd.
Variable inpp : vals typ.

Arguments Sumbool.sumbool_and {A B C D} _ _.

(* the elements of sarr after the n-th iteration *)
Fixpoint f_sim n i :=
  match n with
  | O => gets' inp i
  | S m => 
    if Sumbool.sumbool_and (lt_dec (i + st n) l) (lt_dec i (st n)) then
      f_sim m i \op f_sim m (i + st n)
    else 
      f_sim m i
  end.

Definition dist n i :=
  if Sumbool.sumbool_and (lt_dec (i + st (S n)) l) (lt_dec i (st (S n))) then i
  else i - st (S n).

Definition dist_pre (i : nat) := i.

Notation cvals f := (arr2CUDA (ls_init 0 ntrd f)).

Definition Binv f n i := (arrays' (val2sh inpp) (ith_vals (dist n) (cvals f) i 0) 1).

Definition BSpre n i :=
  match n with
  | O => (arrays' (val2sh inpp) (ith_vals dist_pre (arr2CUDA inp) i 0 ) 1)
  | S n => Binv (f_sim (S n)) n i
  end.

Definition BSpost n i := Binv (f_sim n) n i.

Definition BS n := (MyVector.init (fun i : Fin.t ntrd => Assn (BSpre n (nf i)) True nil),
                    MyVector.init (fun i : Fin.t ntrd => Assn (BSpost n (nf i)) True nil)).

Lemma st_lt n : st (S n) <= st n.
Proof.
  unfold st.
  apply Nat.pow_le_mono_r; lia.
Qed.

Hint Rewrite map_length : pure.
Notation gid := (nf tid + nf bid * ntrd).

Lemma reduce_body_ok n :
  CSL BS tid
      (kernelInv avar_env aptr_env aeval_env
         (BSpre n (nf tid) *** arrays' (val2gl outp) (ith_vals dist_outs outs gid 0) 1)
         True
         ("tid" |-> Zn (nf tid) ::
          "bid" |-> Zn (nf bid) ::
          "slen" |-> Zn l :: 
          len |-> Zn (length arr_res) ::
          out |=> outp ++
          sarr |=> inpp ++
          ys |=> sc2CUDA (f_sim n (nf tid))) p)
      (reduce_body (S n) (st (S n)))
      (kernelInv avar_env aptr_env aeval_env
        (BSpre (S n) (nf tid) *** arrays' (val2gl outp) (ith_vals dist_outs outs gid 0) 1)
        True
        ("tid" |-> Zn (nf tid) ::
         "bid" |-> Zn (nf bid) ::
         "slen" |-> Zn l :: 
         len |-> Zn (length arr_res) ::
         out |=> outp ++
         sarr |=> inpp ++
         ys |=> sc2CUDA (f_sim (S n) (nf tid))) p).
Proof.
  unfold reduce_body, BS.
  cutrewrite (S n - 1 = n); [|omega].

  hoare_forward.
  hoare_forward.
  - unfold BSpost, Binv.
    hoare_forward.
    { unfold arr2CUDA; rewrite map_length, init_length; lia. }
    { unfold dist; destruct Sumbool.sumbool_and; try lia. }
    simpl; simplify_remove_var.
    apply CSL_prop_prem; intros.
    asserts_rewrite (gets (cvals (f_sim n)) (nf tid + st (S n)) = sc2CUDA (f_sim n (nf tid + st (S n)))).
    { unfold arr2CUDA; rewrite (nth_map defval').
      2: autorewrite with pure; lia.
      rewrite ls_init_spec; destruct lt_dec; simpl; eauto; lia. }
    (* TODO: implement as VCG *)
    eapply rule_seq.
    applys* (>>assigns_call2_ok Haok f_ok); [prove_not_local| evalExps |evalExps ].
    simplify_remove_var.
    (* END TODO *)
    hoare_forward; simplify_remove_var.
    hoare_forward; simplify_remove_var.
    { unfold arr2CUDA; rewrite map_length, init_length; lia. }
    { unfold dist; destruct Sumbool.sumbool_and; try lia. }
    intros; eauto.
  - hoare_forward; eauto.
  - unfold kernelDisj, kernelInv.
    rewrite app_nil_r.
    intros s h Hsat; destruct Hsat as [Hsat | Hsat]; fold_sat_in Hsat; revert s h Hsat; unfold BSpre, BSpost, Binv; prove_imp.
    { destruct Sumbool.sumbool_and; try lia; eauto. }
    { applys (>>(@eq_from_nth) (@None (vals typ))); unfold arr2CUDA.
      repeat autorewrite with pure; eauto.
      introv; repeat autorewrite with pure; intros.
      repeat rewrite (nth_map defval'); repeat autorewrite with pure; try lia.
      repeat autorewrite with pure; simpl.
      unfold dist in *.
      clear H.
      Time (repeat match goal with
       | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
       | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
      end). }
    { destruct Sumbool.sumbool_and; try lia; eauto 10. }
    { applys (>>(@eq_from_nth) (@None (vals typ))); unfold arr2CUDA.
      repeat autorewrite with pure; eauto.
      introv; repeat autorewrite with pure; intros.
      repeat rewrite (nth_map defval'); repeat autorewrite with pure; try lia.
      repeat autorewrite with pure; simpl.
      unfold dist in *.
      clear H.
      Time (repeat match goal with
       | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
       | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
      end). }
Qed.

Lemma reduce_aux_ok n m :
  CSL BS tid
      (kernelInv avar_env aptr_env aeval_env
         (BSpre n (nf tid) *** arrays' (val2gl outp) (ith_vals dist_outs outs gid 0) 1)
         True
         ("tid" |-> Zn (nf tid) ::
          "bid" |-> Zn (nf bid) ::
          "slen" |-> Zn l :: 
          len |-> Zn (length arr_res) ::
          out |=> outp ++
          sarr |=> inpp ++
          ys |=> sc2CUDA (f_sim n (nf tid))) p)
      (reduce_aux (S n) m)
      (kernelInv avar_env aptr_env aeval_env
        (BSpre (n + m) (nf tid) *** arrays' (val2gl outp) (ith_vals dist_outs outs gid 0) 1)
        True
        ("tid" |-> Zn (nf tid) ::
        "bid" |-> Zn (nf bid) ::
        "slen" |-> Zn l :: 
        len |-> Zn (length arr_res) ::
        out |=> outp ++
        sarr |=> inpp ++
        ys |=> sc2CUDA (f_sim (n + m) (nf tid))) p).
Proof.
  revert n; induction m; simpl; introv.
  - rewrite <-plus_n_O; hoare_forward; eauto.
  - eapply rule_seq; eauto.
    apply reduce_body_ok.
    cutrewrite (n + S m = S n + m); try lia; eauto.
Qed.    

Lemma reduceBlock_ok :
  CSL BS tid
      (kernelInv avar_env aptr_env aeval_env
         (arrays' (val2sh inpp) (ith_vals dist_pre (arr2CUDA inp) (nf tid) 0) 1 ***
          arrays' (val2gl outp) (ith_vals dist_outs outs gid 0) 1)
         True
         ("tid" |-> Zn (nf tid) ::
          "bid" |-> Zn (nf bid) ::
          "slen" |-> Zn l :: 
          len |-> Zn (length arr_res) ::
          out |=> outp ++
          sarr |=> inpp ++
          ys |=> sc2CUDA (gets' inp (nf tid))) p)
      reduceBlock
      (kernelInv avar_env aptr_env aeval_env
        (BSpre (e_b) (nf tid) *** arrays' (val2gl outp) (ith_vals dist_outs outs gid 0) 1)
        True
        ("tid" |-> Zn (nf tid) ::
         "bid" |-> Zn (nf bid) ::
         "slen" |-> Zn l :: 
         len |-> Zn (length arr_res) ::
         out |=> outp ++
         sarr |=> inpp ++
         ys |=> sc2CUDA (f_sim e_b (nf tid))) p).
Proof.
  forwards*: (>>reduce_aux_ok 0 e_b).
Qed.

Lemma sn_double n : S n <= e_b -> st (S n) + st (S n) = st n.
Proof.
  intros Hsneb. unfold st.
  assert (Heq : e_b - n = S (e_b - S n)) by omega; rewrite Heq; simpl; eauto.
Qed.

Notation sum_of_vs := (sum_of_f_opt (Skel.typDenote typ) f_tot).  

Notation "a '+++' b" := (op' _ f_tot a b) (at level 40, left associativity).
Lemma f_inv n :
  S n <= e_b ->
  sum_of_vs 0 (min l (st (S n))) (f_sim (S n)) = sum_of_vs 0 (min l (st n)) (f_sim n).
Proof.
  intros Hsneb.
  simpl.
  lets Hsn : (>>sn_double n ___); try omega.
  assert (l <= st (S n) \/ st (S n) < l < st n \/ st n <= l) as [HsSnl | [HsSnl | HsSnl] ] by omega.
  - erewrite sum_of_eq.
    Focus 2.
    { simpl; intros i Hi.
      assert (i <= l) by nia.
      destruct Sumbool.sumbool_and; try omega.
      reflexivity. } Unfocus.
    rewrite !min_l; try omega; eauto.
  - erewrite sum_of_eq.
    Focus 2.
    { simpl; intros i Hi.
      instantiate (1 := fun i => if lt_dec i (min (l - st (S n)) (st (S n)))
                                 then (f_sim n i \op f_sim n (i + st (S n))%nat)%Z
                                 else f_sim n i); simpl.
      destruct Sumbool.sumbool_and, lt_dec; rewrite Nat.min_glb_lt_iff in *; try omega; eauto.
    } Unfocus.
    rewrite sum_of_f_split; try omega.
    2: now intros; rewrite f_assoc; eauto.
    2: now simpl; rewrite Nat.min_glb_lt_iff; repeat rewrite Nat.min_lt_iff; split; try omega. 
    rewrite <-minus_n_O.
    rewrite (min_l _ (st n)); try omega.
    rewrite min_l; try omega.
    rewrite min_r; try omega.
    cutrewrite (st (S n) - (l - st (S n)) = st n - l); [|omega].
    rewrite <-shift_values; simpl; eauto.
    assert (Heq : l = (l - st (S n)) + st (S n)) by omega; rewrite Heq at 5.
    Lemma shuffle a b c: a +++ b +++ c = a +++ c +++ b.
    Proof.
      destruct a, b, c; simpl; eauto.
      rewrite f_assoc, (f_comm t0 t1), <-f_assoc; eauto.
      rewrite f_comm; eauto.
    Qed.
    rewrite shuffle.
    rewrite opopt_assoc; eauto.
    rewrite sum_of_concat; f_equal; clear Heq; eauto.
    assert (Heq : st (S n) = st n - l + (l - st (S n))) by omega; rewrite Heq.
    rewrite <-plus_n_O.
    rewrite sum_of_concat; f_equal; eauto.
    rewrite <-Heq; f_equal; omega; eauto.
  - repeat rewrite min_r; try omega.
    erewrite sum_of_eq.
    Focus 2.
    { simpl; intros i Hi.
      destruct Sumbool.sumbool_and; try omega.
      reflexivity.
    } Unfocus.
    rewrite <-Hsn; rewrite sum_of_concat; eauto.
    rewrite <-shift_values; f_equal; eauto.
    f_equal; omega.
Qed.

Lemma fn_ok n :
  n <= e_b ->
  sum_of_vs 0 (min l (st n)) (f_sim n) = sum_of_vs 0 l (fun x => gets' inp x).
Proof.
  induction n; simpl.
  - unfold st; rewrite <-minus_n_O, min_l; try omega.
    intros; apply sum_of_eq; intros; eauto.
  - intros; rewrite f_inv; eauto.
    apply IHn; omega.
Qed.

Lemma feb_ok : match sum_of_vs 0 l (fun x => gets' inp x) with None => l = 0 | Some v => v = f_sim e_b 0 end.
Proof.
  rewrite <-(fn_ok e_b); eauto.
  unfold st; rewrite minus_diag; simpl.
  assert (l = 0 \/ l > 0) as [|] by omega; subst; simpl; eauto.
  rewrite min_r; try omega; simpl; auto.
Qed.

End blockReduce.

Section seqReduce.

Variable tid : Fin.t ntrd.
Variable bid : Fin.t nblk.

Variable svs : list (vals typ).
Variable sps : (vals typ).

Notation gid := (nf tid + nf bid * ntrd).

Notation skip_sum_of_vs := (skip_sum_of_opt (Skel.typDenote typ) f_tot).
Notation xix x := (x * (ntrd * nblk) + gid).

Definition maybe {T : Type} (x : option T) y := match x with Some z => z | None => y end.

Definition seqInv (inpp : vals typ) :=
  Ex nl i, 
    kinv (arrays' (val2sh inpp) (ith_vals dist_pre (nseq ntrd defval) (nf tid) 0) 1 ***
          arrays' (val2gl outp) (ith_vals dist_outs outs gid 0) 1)
         (0 < nl /\
          i = nl * (ntrd * nblk) + (nf tid + nf bid * ntrd))
         ("tid" |-> Zn (nf tid) ::
          "bid" |-> Zn (nf bid) ::
          len |-> Zn (length arr_res) ::
          "ix" |-> Zn i ::
          out |=> outp ++
          sarr |=> inpp ++
          ys |=> sc2CUDA (maybe (skip_sum_of_vs (ntrd * nblk) 0 (min (xix nl) (length arr_res)) g gid) defval')) p.

Definition vi g j i := 
  maybe (skip_sum_of_vs (ntrd * nblk) 0 (length arr_res) g (i + j * ntrd)) defval'.

Ltac clear_assn :=
  match goal with
  | [H : context [Assn _ _ _] |- _] => clear H 
  | [H : context [kernelInv _ _ _ _ _ _ _] |- _] => clear H
  end.

Lemma seq_reduce_ok BS inpp inp : 
  length inp = ntrd ->
  CSL BS tid
      (kinv
         (arrays' (val2sh inpp) (ith_vals dist_pre inp (nf tid) 0) 1 ***
          arrays' (val2gl outp) (ith_vals dist_outs outs gid 0) 1)
         True
         ("tid" |-> Zn (nf tid) ::
          "bid" |-> Zn (nf bid) ::
          len |-> Zn (length arr_res) ::
          out |=> outp ++
          sarr |=> inpp) p)
      (seq_reduce (seqInv inpp))
      (kinv
         (arrays' (val2sh inpp) (ith_vals dist_pre (arr2CUDA (ls_init 0 ntrd (vi g (nf bid)))) (nf tid) 0) 1 ***
          arrays' (val2gl outp) (ith_vals dist_outs outs gid 0) 1)
         True
         ("tid" |-> Zn (nf tid) ::
          "bid" |-> Zn (nf bid) ::
          len |-> Zn (length arr_res) ::
          out |=> outp ++
          sarr |=> inpp ++ 
          ys |=> sc2CUDA (vi g (nf bid) (nf tid))) p).
Proof.
  intros.
  forwards*: (>>nf_lt tid).
  unfold seq_reduce.
  hoare_forward; simplify_remove_var.
  hoare_forward.
  hoare_forward; simplify_remove_var.
  hoare_forward.
  3: introv; destruct 1; eauto.
  - hoare_forward; simplify_remove_var.
    hoare_forward; simplify_remove_var.
    unfold seqInv; hoare_forward.
    hoare_forward; simplify_remove_var.
    (* TODO: implement as VCG *)
    eapply rule_seq.
    applys* (>>assigns_call2_ok Haok f_ok); [prove_not_local| evalExps |evalExps ].
    simplify_remove_var.
    (* TODO: End TODO *)
    hoare_forward; simplify_remove_var.
    hoare_forward; simplify_remove_var.
    intros s h Hsat; exists (S nl) (S nl * (ntrd * nblk) + gid).
    revert s h Hsat; prove_imp. 
    { clear H1; nia. }
    {  rewrites (>>mult_comm (length inp)); eauto.
       rewrites (>>skip_sum_sum0 nl); eauto.
      { clear_assn; nia. }
      rewrites (>>skip_sum_sum0 (S nl)); eauto.
      { clear_assn; nia. }
      cutrewrite (S nl = nl + 1); [|clear_assn; lia]; rewrite sum_of_concat; eauto.
      simpl; f_equal; unfold maybe, op'; destruct (sum_of_f_opt _ _ _ _ _) eqn:Heq.
      - des_conj H2; substs; do 2 f_equal; clear_assn; nia.
      - destruct nl; simpl in *; try (destruct sum_of_f_opt; congruence).
        omega. }
    intros s h Hsat; exists 1 (1 * (ntrd * nblk) + gid).
    revert s h Hsat; prove_imp. 
    { nia. }
    { rewrites (>>mult_comm (length inp)); eauto.
      rewrites (>>skip_sum_sum0 1); eauto. 
      clear_assn; nia.
      simpl; do 2 f_equal; ring. }
    { unfold arr2CUDA.
      applys (>>(@eq_from_nth) (@None (vals typ))).
      { repeat autorewrite with pure; rewrite length_nseq; eauto. }
      { introv; repeat autorewrite with pure; rewrite length_nseq; intros.
        unfold dist_pre; simpl; rewrite nth_nseq.
        Time (repeat match goal with
         | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
         | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
        end). } }
    hoare_forward; eauto.
    { rewrite length_nseq; lia. }
    prove_imp.
    repeat clear_assn.
    { unfold vi; rewrite Nat.min_r; substs; eauto; lia. }
    { rewrite Nat.min_r; try (clear_assn; lia).
      applys (>>(@eq_from_nth) (@None (vals typ))).
      { unfold arr2CUDA; repeat autorewrite with pure; rewrite length_nseq, map_length, init_length; eauto. }
      { unfold arr2CUDA; introv; repeat autorewrite with pure; rewrite length_nseq, map_length, init_length; intros.
        unfold dist_pre; simpl; rewrite nth_nseq, (nth_map defval'); [|autorewrite with pure; clear_assn; lia].
        repeat autorewrite with pure.
        clear_assn.
        Time (repeat match goal with
         | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
         | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
        end). 
        unfold vi; substs; eauto. } }
  - hoare_forward.
    prove_imp.
    { unfold vi; substs; rewrites (>>mult_comm (length inp)).
      rewrites* (>>skip_sum_sum0 0).
      forwards*: (>>id_lt_nt_gr (nf tid) (nf bid)); nia.
      simpl; rewrites* defval_sc2CUDA. }
    { applys (>>(@eq_from_nth) (@None (vals typ))).
      { unfold arr2CUDA; repeat autorewrite with pure; rewrite !map_length, init_length; eauto. }
      { unfold arr2CUDA; introv; repeat autorewrite with pure; rewrite !map_length, init_length; intros.
        unfold dist_pre; simpl; rewrite ! (nth_map defval'), ls_init_spec; [|try rewrite init_length; lia..].
        repeat autorewrite with pure.
        clear_assn.
        Time (repeat match goal with
         | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
         | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
        end). 
        unfold vi; substs.
        rewrites (>>mult_comm (length inp)).
        rewrites* (>>skip_sum_sum0 0).
        forwards*: (>>id_lt_nt_gr (nf tid) (nf bid)); nia.
        simpl; rewrites* defval_sc2CUDA. } }
Qed.    

End seqReduce.

Lemma setToLen_ok BS R (tid : Fin.t ntrd) (bid : Fin.t nblk) inpp y:
  CSL BS tid
      (kinv
         R True
         ("tid" |-> Zn (nf tid) ::
          "bid" |-> Zn (nf bid) ::
          len |-> Zn (length arr_res) ::
          out |=> outp ++
          sarr |=> inpp ++ ys |=> y) p)
      setToLen
      (kinv
         R True
         ("tid" |-> Zn (nf tid) ::
          "bid" |-> Zn (nf bid) ::
          len |-> Zn (length arr_res) ::
          "slen" |-> Zn (min (length arr_res - nf bid * ntrd) ntrd) ::
          out |=> outp ++
          sarr |=> inpp ++ ys |=> y) p).
Proof.
  unfold setToLen.
  hoare_forward; [| |introv; destruct 1; eauto].
  hoare_forward; simplify_remove_var.
  prove_imp; nia.
  hoare_forward; [| |introv; destruct 1; eauto].
  hoare_forward; simplify_remove_var.
  prove_imp. 
  left. f_equal. nia.
  hoare_forward; simplify_remove_var.
  prove_imp.
  nia.
Qed.

Section mkReduce_block.

Variable bid : Fin.t nblk.


Variable inp : list (vals typ). 
Hypothesis inp_length : length inp = ntrd.
Variable inpp : vals typ.

Section mkReduce_thread.
Variable tid : Fin.t ntrd.

Definition BSpre' :=
  (BSpre (ls_init 0 ntrd (fun i => vi g (nf bid) i))
          (min (length arr_res - nf bid * ntrd) ntrd)
          inpp e_b (nf tid)).

Definition BS' :=
  (BS (ls_init 0 ntrd (fun i => vi g (nf bid) i))
      (min (length arr_res - nf bid * ntrd) ntrd)
      inpp).

Ltac clear_assn :=
  match goal with
  | [H : context [Assn _ _ _] |- _] => clear H 
  | [H : context [kernelInv _ _ _ _ _ _ _] |- _] => clear H
  end.

Lemma mkReduce_cmd_ok :
  CSL BS' tid
    (kinv
       (arrays' (val2sh inpp) (ith_vals dist_pre inp (nf tid) 0) 1 ***
        arrays' (val2gl outp) (ith_vals dist_outs outs (nf tid + nf bid * ntrd) 0) 1)
       True
       ("tid" |-> Zn (nf tid) ::
        "bid" |-> Zn (nf bid) ::
        len |-> Zn (length arr_res) ::
        out |=> outp ++
        sarr |=> inpp) p)  
    mkReduce_cmd
    (kernelInv' aptr_env aeval_env
       (BSpre'  ***
        arrays' (val2gl outp)
          (ith_vals dist_outs (arr2CUDA (ls_init 0 nblk (fun j => (f_sim
                                                                     (ls_init 0 ntrd (fun i : nat => vi g j i))
                                                                     (min (Datatypes.length arr_res - j * ntrd) ntrd) (e_b) 0))))
                    (nf tid + nf bid * ntrd) 0) 1)
       True p).
Proof.
  intros; 
  unfold mkReduce_cmd.
  eapply rule_seq; [apply* seq_reduce_ok|].
  eapply rule_seq.
  { eapply backwardR; [applys* (>>setToLen_ok bid inpp)|]; eauto. }
  eapply rule_seq.
  { eapply backwardR; [applys* (>>reduceBlock_ok bid inpp)|].
    rewrite init_length; auto.
    nia.
    prove_imp.
    rewrite ls_init_spec; destruct lt_dec; eauto.
    false; eauto. }
  hoare_forward.
  hoare_forward; eauto; try lia.
  forwards*: (>>nf_lt bid); lia.
  unfold dist_outs; nia.
  hoare_forward; eauto.
  intros s h; destruct 1 as [Hsat | Hsat]; fold_sat_in Hsat; revert s h Hsat; unfold kernelInv', kernelInv;
  unfold BSpre', BSpre, BSpost, Binv.
  { prove_imp; try tauto.
    destruct e_b; [false; lia|].
    applys (>> (@eq_from_nth) (@None (vals typ))).
    unfold arr2CUDA; repeat autorewrite with pure; rewrite map_length; autorewrite with pure; eauto.
    lia.
    introv; repeat autorewrite with pure; intros.
    unfold dist_outs.
    unfold arr2CUDA; repeat rewrite map_length; autorewrite with pure.
    rewrite (nth_map defval'); autorewrite with pure; [|clear_assn; lia].
    clear_assn.
    Time (repeat match goal with
       | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
       | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
    end).
    intros; do 3 f_equal; try lia.
    nia. }
  { prove_imp; try tauto.
    destruct e_b; [false; lia|].
    applys (>> (@eq_from_nth) (@None (vals typ))).
    unfold arr2CUDA; repeat autorewrite with pure; rewrite map_length; autorewrite with pure; eauto.
    introv; repeat autorewrite with pure; intros.
    lia.
    unfold arr2CUDA; repeat autorewrite with pure; eauto.
    introv; repeat autorewrite with pure; try rewrite map_length; autorewrite with pure; intros.
    unfold dist_outs.
    rewrite (nth_map defval'); autorewrite with pure; [|clear_assn; lia].
    clear_assn.
    Time (repeat match goal with
       | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
       | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
    end).
    false.
    assert ((nf tid + nf bid * length inp) mod length inp = 0).
    { rewrite <-e; simpl; rewrite Nat.mod_mul; eauto. }
    rewrite Nat.mod_add in *; eauto; rewrite Nat.mod_small in *; eauto; try lia. }
Qed.

End mkReduce_thread.

Definition ith_pre (tid : Fin.t ntrd) := 
  (kinv
       (arrays' (val2sh inpp) (ith_vals dist_pre inp (nf tid) 0) 1 ***
        arrays' (val2gl outp) (ith_vals dist_outs outs (nf tid + nf bid * ntrd) 0) 1)
       True
       ("bid" |-> Zn (nf bid) ::
        len |-> Zn (length arr_res) ::
        out |=> outp ++
        sarr |=> inpp) p).

Definition ith_post (tid : Fin.t ntrd) :=
  kernelInv' aptr_env aeval_env
       (BSpre' tid ***
        arrays' (val2gl outp)
          (ith_vals dist_outs (arr2CUDA (ls_init 0 nblk (fun j => (f_sim
             (ls_init 0 ntrd (fun i : nat => vi g j i))
             (min (Datatypes.length arr_res - j * ntrd) ntrd) (e_b) 0))))
                    (nf tid + nf bid * ntrd) 0) 1)
       True p.

Notation fin_star n f :=
  (istar (ls_init 0 n f)).

Definition E (x : var) :=
  if prefix "_" (str_of_var x) then Lo
  else if var_eq_dec "bid" x then Lo
  else Hi.

Definition shvals_last : list (Skel.typDenote typ) :=
   (ls_init 0 ntrd
      (f_sim
         (ls_init 0 ntrd (fun i : nat => vi g (nf bid) i))
         (min (Datatypes.length arr_res - (nf bid) * ntrd) ntrd) (e_b))).

Lemma reduce_aux_Lo n m : typing_cmd E (reduce_aux n m) Lo.
Proof.
  revert n; induction m; simpl; eauto.
  intros; constructor; eauto.
  unfold reduce_body, assigns_call2.
  unfold E; repeat prove_typing_cmd.
  econstructor.
  constructor.
  constructor.
  prove_typing_exp.
  prove_typing_exp.
  prove_typing_bexp.
  repeat prove_typing_cmd; eauto.
  prove_typing_cmd.
Qed.

Lemma reduceBlock_Lo : typing_cmd E reduceBlock Lo.
Proof.
  apply reduce_aux_Lo.
Qed.

Lemma mkReduce_cmd_ok_b :
  CSLp ntrd E
    (kinv
       (arrays (val2sh inpp) inp 1 ***
        fin_star ntrd (fun i => arrays' (val2gl outp) (ith_vals dist_outs outs (i + nf bid * ntrd) 0) 1))
       True
       ("bid" |-> Zn (nf bid) ::
        len |-> Zn (length arr_res) ::
        out |=> outp ++
        sarr |=> inpp) (p * injZ (Zn ntrd)))
    mkReduce_cmd
    (kernelInv' aptr_env aeval_env
       (arrays (val2sh inpp) (arr2CUDA shvals_last) 1  ***
        fin_star ntrd (fun i =>
        arrays' (val2gl outp)
          (ith_vals dist_outs (arr2CUDA (ls_init 0 nblk (fun j => (f_sim
             (ls_init 0 ntrd (fun i : nat => vi g j i))
             (min (Datatypes.length arr_res - j * ntrd) ntrd) (e_b) 0))))
                    (i + nf bid * ntrd) 0) 1))
       True (p * injZ (Zn ntrd))).
Proof.
  applys* (>>rule_block BS' E (MyVector.init ith_pre) (MyVector.init ith_post)); eauto;
  unfold BS', BS, BSpre, BSpost.
  - split; intros; simpl; rewrite MyVector.init_spec; prove_low_assn.
  - intros [|i]; simpl.
    { unfold Binv; prove_istar_imp.
      clear H0.
      rewrite CodeGen.array'_ok in *; try (introv; unfold arr2CUDA, dist_pre, dist; rewrite map_length, init_length; intros; lia).
      2: introv; unfold arr2CUDA, dist; rewrite map_length, init_length; destruct Sumbool.sumbool_and; try lia.
      erewrite ls_init_eq0; [eauto|].
      intros; rewrite ls_init_spec; destruct lt_dec; eauto; lia. }
    { prove_istar_imp.
      unfold Binv in *; simpl in *.
      clear H0.
      rewrite CodeGen.array'_ok in *;
        try (introv; unfold arr2CUDA, dist; rewrite map_length, init_length; destruct Sumbool.sumbool_and; clear H; intros; lia).
      eauto. }
  - Hint Resolve precise_arrays'.
    unfold Binv; intros [|i] ?; simpl; split; rewrite !MyVector.init_spec; prove_precise.
  - unfold ith_pre.
    prove_istar_imp.
    rewrite ls_star_res, CodeGen.array'_ok.
    repeat sep_cancel'.
    unfold arr2CUDA, dist_pre; introv; intros; lia.
  - unfold ith_post.
    unfold BSpre', BSpre, Binv, shvals_last.
    prove_istar_imp.
    destruct e_b; try lia.
    repeat rewrite ls_star_res in H.
    rewrite CodeGen.array'_ok in H.
    repeat sep_cancel'; eauto.
    introv; unfold arr2CUDA, dist; rewrite map_length, init_length; destruct Sumbool.sumbool_and; clear H; intros; lia. 
  - unfold E, ith_pre; introv; rewrite MyVector.init_spec; prove_low_assn.
  - unfold E, ith_post; introv; rewrite MyVector.init_spec; prove_low_assn.
  - unfold E, mkReduce_cmd, seq_reduce, setToLen, assigns_get, assigns_call2.
    instantiate (1 := Lo).
    repeat apply ty_seq; try apply reduceBlock_Lo; repeat prove_typing_cmd.
    applys (>>weaken_type Hi); eauto; prove_typing_cmd.
    applys (>>weaken_type Hi); eauto; prove_typing_cmd.
  - intros; rewrite !MyVector.init_spec.
    unfold ith_pre, ith_post; eapply rule_conseq; eauto using mkReduce_cmd_ok.
    unfold kernelInv; introv; rewrite assn_var_in; revert s h; prove_imp.
Qed.
End mkReduce_block.

Fixpoint addTyp {ty} :=
  match ty return vars ty -> vartys ty with 
  | Skel.TBool => fun x => (x, Bool)
  | Skel.TZ => fun x => (x, Int)
  | Skel.TTup t1 t2 => fun xs => (addTyp (fst xs), addTyp (snd xs))
  end.

Definition sh_decl len typ pref st :=
  flatTup (maptys (fun sv => Grid.SD (fst sv) (snd sv) len) (addTyp (locals pref typ st))).

Definition mkReduce_prog :=
  Pr (sh_decl ntrd typ "_sarr" 0) (mkReduce_cmd).

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

Definition jth_pre (bid : Fin.t nblk) :=
  (kinv
       (fin_star ntrd (fun i => arrays' (val2gl outp) (ith_vals dist_outs outs (i + nf bid * ntrd) 0) 1))
       True
       (len |-> Zn (length arr_res) ::
        out |=> outp) (p * injZ (Zn ntrd))).

Definition jth_post (bid : Fin.t nblk) :=
  (kernelInv' aptr_env aeval_env
       (fin_star ntrd 
                 (fun i =>
                    arrays' (val2gl outp)
                            (ith_vals dist_outs (arr2CUDA (ls_init 0 nblk (fun j => (f_sim
                            (ls_init 0 ntrd (fun i : nat => vi g j i))
                            (min (Datatypes.length arr_res - j * ntrd) ntrd) (e_b) 0))))
                                      (i + nf bid * ntrd) 0) 1))
       True (p * injZ (Zn ntrd))).

Lemma length_app_split T n m (l : list T) : 
  length l = n + m 
  -> exists l1 l2, length l1 = n /\ length l2 = m /\ l = l1 ++ l2.
Proof.
  revert l m; induction n; simpl; eauto.
  intros; exists (@nil T) l; simpl; split; eauto.
  intros ? ? Hlen.
  destruct l as [|x l]; simpl in *; try lia; inverts Hlen.
  forwards* (l1 & l2 & ? & ? & ?): (>>IHn l m).
  exists (x :: l1) l2; splits; simpl; eauto.
  substs; simpl; eauto.
Qed.

Lemma flatTup_length ty T (xs : typ2Coq T ty):
  length (flatTup xs) = nleaf ty.
Proof.
  induction ty; simpl; try autorewrite with pure; eauto.
Qed.
Hint Rewrite flatTup_length : pure.

Lemma sdecl_len_vals n ty T locs pref st :
  length (sh_decl n ty pref st) = length locs 
  -> exists (locs' : typ2Coq T ty), locs = flatTup locs'.
Proof.
  revert locs; induction ty; simpl.
  - destruct locs as [| ? [| ? ?]]; simpl; intros; try omega; eexists; eauto.
  - destruct locs as [| ? [| ? ?]]; simpl; intros; try omega; eexists; eauto.
  - unfold sh_decl; simpl.
    intros; autorewrite with pure in *.
    forwards* (? & ? & ? & ? & ?): (>>length_app_split (nleaf ty1) (nleaf ty2)).
    forwards* (? & ?): (IHty1); unfold sh_decl; autorewrite with pure; eauto.
    forwards* (? & ?): (IHty2); unfold sh_decl; autorewrite with pure; eauto.
    exists (x1, x2); simpl; congruence.
Qed.

Lemma ls_init_nth_aux' T (xs : list T) d n s :
  length xs = n 
  -> ls_init s n (fun i => nth (i - s) xs d) = xs.
Proof.
  intros.
  applys (>>eq_from_nth d); autorewrite with pure; eauto.
  intros.
  autorewrite with pure; destruct lt_dec; f_equal; lia.
Qed.
Lemma ls_init_nth' T (xs : list T) d n :
  length xs = n 
  -> ls_init 0 n (fun i => nth i xs d) = xs.
Proof.
  intros; forwards*: (>>ls_init_nth_aux' d n 0); eauto.
  erewrite ls_init_eq0; eauto.
  intros; simpl; rewrite* <-minus_n_O.
Qed.

Require Import SetoidClass.
Lemma arrays_TZ (l : locs Skel.TZ) (v : list (vals Skel.TZ)) p :
  arrays l v p == array l v p.
Proof.
  revert l; induction v; simpl; try reflexivity.
  intros; rewrite IHv; reflexivity.
Qed.
Lemma arrays_TB (l : locs Skel.TBool) (v : list (vals Skel.TBool)) p :
  arrays l v p == array l v p.
Proof.
  revert l; induction v; simpl; try reflexivity.
  intros; rewrite IHv; reflexivity.
Qed.
Notation convertSvals n vals := (ls_init 0 n (fun i => maptys (fun xs => get xs i) vals)).

Lemma sh_spec_res_tup st n ty (locs : vals ty) vals pref : 
  sh_spec_pure (sh_decl n ty pref st) (flatTup vals) 
  ->(sh_spec_res (sh_decl n ty pref st) (flatTup locs) (flatTup vals) ==
     arrays (val2sh locs) (convertSvals n vals) 1).
Proof.
  revert st; induction ty; unfold val2sh; simpl; 
  try (rewrite emp_unit_r_res).
  intros; rewrite ls_init_nth'; try lia.
  rewrite <-arrays_TB, emp_unit_r_res; reflexivity. 
  intros; rewrite ls_init_nth'; try lia.
  rewrite <-arrays_TZ, emp_unit_r_res; reflexivity.
  simpl.
  
  Lemma sh_spec_pure_app sd1 sd2 vs1 vs2 :
    length sd1 = length vs1 
    -> (sh_spec_pure (sd1 ++ sd2) (vs1 ++ vs2)
    <-> sh_spec_pure sd1 vs1 /\ sh_spec_pure sd2 vs2).
  Proof.
    split.
    - revert vs1 H; induction sd1 as [|[? ? ?] ?]; intros [|? vs1]; simpl; intros; try lia; eauto.
      forwards*: IHsd1.
    - revert vs1 H; induction sd1 as [|[? ? ?] ?]; intros [|? vs1]; simpl; intros; try lia; jauto.
  Qed.
  
  Lemma sh_spec_res_app sd1 sd2 ls1 ls2 vs1 vs2 :
    length sd1 = length vs1 
    -> length sd1 = length ls1
    -> (sh_spec_res (sd1 ++ sd2) (ls1 ++ ls2) (vs1 ++ vs2) ==
        (sh_spec_res sd1 ls1 vs1 *** sh_spec_res sd2 ls2 vs2)).
  Proof.
    revert vs1 ls1; induction sd1 as [|[? ? ?] ?]; intros [|? vs1] [|? ls1]; simpl; intros; try lia; eauto;
    try (rewrite emp_unit_l_res; reflexivity).
    rewrite IHsd1; [|lia..].
    rewrite res_assoc; reflexivity.
  Qed.

  intros ? Hpure.
  unfold sh_decl in *; simpl in *.
  apply sh_spec_pure_app in Hpure as [Hpure1 Hpure2]; [|autorewrite with pure; eauto].
  rewrite sh_spec_res_app; [|autorewrite with pure; eauto..].
  rewrites* IHty1; rewrites* IHty2.
  
  Lemma arrays_TTup t1 t2 (ls : locs (Skel.TTup t1 t2)) (vs : list (vals (Skel.TTup t1 t2))) p :
    (arrays ls vs p == (arrays (fst ls) (map fst vs) p *** arrays (snd ls) (map snd vs) p)).
  Proof.
    revert ls; induction vs; introv; simpl.
    rewrite emp_unit_l_res; reflexivity.
    rewrite <-!res_assoc.
    apply res_star_proper; [reflexivity|].
    rewrite <-res_CA, IHvs; reflexivity.
  Qed.

  Lemma map_ls_init T1 T2 s t (f : nat -> T1) (g : T1 -> T2) :
    map g (ls_init s t f) = ls_init s t (fun x => g (f x)).
  Proof.
    revert s; induction t; simpl; eauto.
    introv; congruence.
  Qed.
  rewrite arrays_TTup, !map_ls_init; simpl; reflexivity.
Qed.

Lemma sh_spec_env_tup st n ty (locs : vals ty) pref :
  sh_spec_env (sh_decl n ty pref st) (flatTup locs) = 
  locals pref ty st |=> locs.
Proof.
  revert st; induction ty; simpl; eauto.
  Lemma sh_spec_env_app sd1 sd2 vs1 vs2 :
    length sd1 = length vs1 
    -> sh_spec_env (sd1 ++ sd2) (vs1 ++ vs2) = sh_spec_env sd1 vs1 ++ sh_spec_env sd2 vs2.
  Proof.
    revert vs1 vs2; induction sd1 as [|[? ? ?] ?]; simpl; intros [|? vs1] vs2;
    simpl in *; intros; try lia; eauto.
    rewrite IHsd1; eauto.
  Qed.
  introv; unfold sh_decl in *; simpl in *; rewrite sh_spec_env_app; try congruence.
  autorewrite with pure; eauto.
Qed.

Lemma sh_decl_length_aux st n ty pref:
  length (sh_decl n ty pref st) = nleaf ty.
Proof.
  revert st; induction ty; simpl; eauto.
  intros; unfold sh_decl in *; simpl in *; rewrite app_length; congruence.
Qed.

Lemma sh_decl_length n ty pref st:
  length (sh_decl n ty pref st) = nleaf ty.
Proof. unfold sh_decl; apply sh_decl_length_aux. Qed.

Theorem mkReduce_ok :
  CSLg ntrd nblk
    (kinv
       (arrays (val2gl outp) outs 1)
       True
       (len |-> Zn (length arr_res) ::
        out |=> outp) 1)
    mkReduce_prog
    (kernelInv' aptr_env aeval_env
       (arrays (val2gl outp)
              (arr2CUDA (ls_init 0 nblk (fun j => (f_sim
                (ls_init 0 ntrd (fun i : nat => vi g j i))
                (min (Datatypes.length arr_res - j * ntrd) ntrd) (e_b) 0)))) 1)
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
    intros; unfold dist_outs; nia.
  - unfold kernelInv; introv; rewrite !MyVector.init_spec.
    apply CSLp_preprocess; simpl.
    intros; unfold sh_spec_assn, sh_spec_assn'.
    forwards* (locs' & ?): (>>sdecl_len_vals H).
    forwards* (vals' & ?): (>>sdecl_len_vals H0); substs.
    eapply rule_p_backward; [|intros ? ? Hsat; rewrite Assn_combine in Hsat; eauto].
    apply rule_p_assn; intros (_ & Hprem).
    eapply rule_p_conseq.
    applys (>>mkReduce_cmd_ok_b bid (convertSvals ntrd vals')); try (intros s h; rewrite Assn_combine in *; eauto).
    { autorewrite with pure; eauto. }
    + unfold kernelInv; prove_istar_imp; substs; eauto.
      rewrite sh_spec_env_tup; eauto.
      rewrite Heq; repeat rewrite <-res_assoc in *.
      sep_cancel'.
      rewrites* sh_spec_res_tup in H4.
      repeat sep_cancel'.
    + Fixpoint to_shvals {ty} :=
        match ty return list (vals ty) -> list (list val) with
        | Skel.TZ | Skel.TBool => fun vals => vals :: nil
        | Skel.TTup t1 t2 => fun vals => to_shvals (map fst vals) ++ to_shvals (map snd vals)
        end.
      exists (to_shvals (arr2CUDA (shvals_last bid))).
      Lemma to_shvals_length ty (vs : list (vals ty)) :
        length (to_shvals vs) = nleaf ty.
      Proof.
        induction ty; simpl; eauto.
        rewrite app_length; congruence.
      Qed.
      
      split; [unfold arr2CUDA, shvals_last; rewrite !to_shvals_length; autorewrite with pure|].
      rewrite sh_decl_length; unfold Apure; eauto.
      fold_sat; revert s h H1; prove_imp.
      rewrite Heq in *; repeat rewrite <-res_assoc in *.
      repeat sep_cancel'.
      
      Lemma sh_spec_res_tup' n ty pref st (locs : vals ty) (vals : list (vals ty)):
        sh_spec_res (sh_decl n ty pref st) (flatTup locs) (to_shvals vals) ==
        arrays (val2sh locs) vals 1.
      Proof.
        unfold sh_decl; revert st; induction ty; simpl; intros.
        - rewrite arrays_TB, emp_unit_r_res; reflexivity.
        - rewrite arrays_TZ, emp_unit_r_res; reflexivity.
        - rewrite sh_spec_res_app.
          rewrite IHty1.
          rewrite IHty2.
          rewrite arrays_TTup; reflexivity.
          autorewrite with pure; rewrite to_shvals_length; eauto.
          autorewrite with pure; eauto.
      Qed.
      
      rewrite sh_spec_res_tup'; eauto.
      
      Lemma sh_spec_pure_tup' n ty pref st (vs : list (vals ty)) :
        length vs = n
        -> sh_spec_pure (sh_decl n ty pref st) (to_shvals vs).
      Proof.
        revert st; unfold sh_decl; induction ty; simpl; eauto.
        intros.
        rewrite sh_spec_pure_app.
        2: autorewrite with pure; rewrite to_shvals_length; eauto.
        split; [apply IHty1|apply IHty2]; rewrite map_length; eauto.
      Qed.
      apply sh_spec_pure_tup'.
      unfold arr2CUDA, shvals_last; rewrite map_length; autorewrite with pure; eauto.
  - intros s h H; rewrite Heq'; revert s h H.
    prove_istar_imp.
    simpl_nested_istar.
    rewrite CodeGen.array'_ok in H.
    rewrite <-Heq' in *; eauto.
    unfold dist_outs, arr2CUDA; rewrite map_length; autorewrite with pure; intros; nia.
  - intros; rewrite MyVector.init_spec.
    apply inde_assn_vars.
    unfold outArr, len, name_of_len.
    prove_low_expr; intros Hc; des_disj Hc; eauto; try congruence; substs.
    forwards* H': mpss_in; forwards* (H'' & ? & ?): (>>locals_pref H'); substs; inverts H.
    forwards* H': mpss_in; forwards* (H'' & ? & ?): (>>locals_pref H'); substs; inverts H.
    forwards*: aenv_ok_params; simpl in *; congruence.
    forwards*: aenv_ok_params; simpl in *; congruence.
  - intros; rewrite MyVector.init_spec.
    unfold E; prove_low_assn.
  - intros; rewrite MyVector.init_spec; unfold kernelInv. 
    apply has_no_vars_assn.
  - unfold E.
    Lemma sh_decl_map n ty pref st:
      map SD_var (sh_decl n ty pref st) = flatTup (locals pref ty st).
    Proof.
      revert st; unfold sh_decl; induction ty; simpl; eauto.
      introv; rewrite map_app; congruence.
    Qed.      
    intros ? Hin; rewrite sh_decl_map in Hin; apply locals_pref in Hin as (? & ? & ?);
    substs; simpl; eauto.
  - rewrite sh_decl_map; apply locals_disjoint_ls.
Qed.    
End mkReduce.
