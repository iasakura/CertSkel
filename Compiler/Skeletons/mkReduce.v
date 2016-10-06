Require Import LibTactics Psatz.
Require Import GPUCSL SkelLib scan_lib CSLTactics.
Require Import CUDALib TypedTerm.
Require Import Host.
Require Import Skel_lemma CodeGen CUDALib Correctness Grid CSLTactics CSLLemma.

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
Notation sarr := (locals "sarr" typ 0).
Definition outArr ty := locals "_arrOut" ty 0.
Notation out := (outArr typ).
Notation len := out_len_name.

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

Fixpoint vals2es {ty} (v : val) :=
  match ty return exps ty with
  | Skel.TBool | Skel.TZ => Enum v
  | Skel.TTup t1 t2 => (@vals2es t1 v, @vals2es t2 v)
  end.

Definition seq_reduce inv :=
  assigns ys (ty2ctys typ) (vals2es 0%Z) ;;
  writes (v2sh sarr +os "tid") (vals2es 0%Z) ;;
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

Notation p := (RP (ntrd * nblk)).

Definition BS n := (MyVector.init (fun i : Fin.t ntrd => Assn (BSpre n (nf i)) True nil),
                    MyVector.init (fun i : Fin.t ntrd => Assn (BSpost n (nf i)) True nil)).

Lemma st_lt n : st (S n) <= st n.
Proof.
  unfold st.
  apply Nat.pow_le_mono_r; lia.
Qed.

Hint Rewrite map_length : pure.

Lemma reduce_body_ok n :
  CSL BS tid
      (kernelInv avar_env aptr_env aeval_env
         (BSpre n (nf tid)) True
            ("tid" |-> Zn (nf tid) ::
             "bid" |-> Zn (nf bid) ::
             "slen" |-> Zn l :: 
             sarr |=> inpp ++
             ys |=> sc2CUDA (f_sim n (nf tid))) p)
      (reduce_body (S n) (st (S n)))
      (kernelInv avar_env aptr_env aeval_env
        (BSpre (S n) (nf tid)) True
            ("tid" |-> Zn (nf tid) ::
             "bid" |-> Zn (nf bid) ::
             "slen" |-> Zn l :: 
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
         (BSpre n (nf tid)) True
            ("tid" |-> Zn (nf tid) ::
             "bid" |-> Zn (nf bid) ::
             "slen" |-> Zn l :: 
             sarr |=> inpp ++
             ys |=> sc2CUDA (f_sim n (nf tid))) p)
      (reduce_aux (S n) m)
      (kernelInv avar_env aptr_env aeval_env
        (BSpre (n + m) (nf tid)) True
            ("tid" |-> Zn (nf tid) ::
             "bid" |-> Zn (nf bid) ::
             "slen" |-> Zn l :: 
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
         (arrays' (val2sh inpp) (ith_vals dist_pre (arr2CUDA inp) (nf tid) 0) 1) True
            ("tid" |-> Zn (nf tid) ::
             "bid" |-> Zn (nf bid) ::
             "slen" |-> Zn l :: 
             sarr |=> inpp ++
             ys |=> sc2CUDA (gets' inp (nf tid))) p)
      reduceBlock
      (kernelInv avar_env aptr_env aeval_env
        (BSpre (e_b) (nf tid)) True
            ("tid" |-> Zn (nf tid) ::
             "bid" |-> Zn (nf bid) ::
             "slen" |-> Zn l :: 
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
End Sum_of.

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

End mkReduce.
