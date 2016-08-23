Require Import GPUCSL scan_lib LibTactics Psatz CSLLemma SetoidClass.
Require Import CSLLemma CSLTactics.

Section reduce.
Variable ntrd nblk : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis nblk_neq_0 : nblk <> 0.
Hint Resolve ntrd_neq_0 nblk_neq_0.
Variable tid : Fin.t ntrd.
Variable bid : Fin.t nblk.

Coercion Var : string >-> var.
Open Scope string_scope.
Open Scope list_scope.

Arguments div _ _ : simpl never.
Arguments modulo _ _ : simpl never.

Definition next (x : nat * list val):=
  let (l, ls) := x in
  let d := ((l + 1) / 2) in
  (d, zipWith Z.add (firstn (l - d) ls) (firstn (l - d) (skipn d ls)) ++ skipn (l - d) ls).

Fixpoint iter {T : Type} n f (x : T) := 
  match n with
  | 0 => x
  | S n => f (iter n f x)
  end.

Variable init_vals out_vals sh_vals : list val.
Variable arr inp out : val.

Hypothesis inp_len : length init_vals = nblk * ntrd.
Hypothesis out_len : length out_vals = nblk + 0.

Definition reg_b' j := (firstn ntrd (skipn (ntrd * j) init_vals)).
Notation reg_b := (reg_b' (nf bid)).

Lemma reg_b_length:
  length reg_b = ntrd.
Proof.
  unfold reg_b'; autorewrite with pure.
  rewrite inp_len in *.
  assert (nf bid < nblk) by eauto.
  destruct lt_dec; nia.
Qed.  

Local Notation c_state c := (iter c next (length reg_b, reg_b)).

Definition reduce inv := 
  "t" ::= [Gl "inp" +o ("tid" +C "bid" *C Zn ntrd)] ;;
  [Sh "arr" +o "tid"] ::= "t" ;;
  Cbarrier 0 ;;
  "c" ::= 0%Z ;;
  "st" ::= Zn ntrd ;;
  WhileI inv (1%Z <C "st") (
    "d" ::= ("st" +C 1%Z)>>1 ;;
    Cif ("tid" +C "d" <C "st") (
      "t1" ::= [ Sh "arr" +o "tid" ] ;;
      "t2" ::= [ Sh "arr" +o ("tid" +C "d") ] ;;
      [ Sh "arr" +o "tid" ] ::= "t1" +C "t2"
    ) Cskip ;;
    Cbarrier 1 ;;
    "st" ::= "d" ;;
    "c" ::= "c" +C 1%Z
  ) ;;
  Cif ("tid" == 0%Z) (
    "t" ::= [ Sh "arr" +o 0%Z] ;;
    [Gl "out" +o "bid"] ::= "t"
  ) Cskip.

Definition dist st i :=
  let d := (st + 1) / 2 in
  if lt_dec (i + d) st then i
  else if lt_dec i st then (i - d)
  else 0.

Notation p := (1 / injZ (Zn (nblk * ntrd)))%Qc.

Definition inv :=
  Ex st c,
  let vals := snd (c_state c) in
  Assn (array' (SLoc arr) (ith_vals (dist st) vals (nf tid) 0) 1 ***
        array (GLoc inp) init_vals p ***
        array' (GLoc out) (ith_vals (fun i => i * ntrd) out_vals (nf tid + nf bid * ntrd) 0) 1)
       (st = fst (c_state c))
       ("tid" |-> Zn (nf tid) ::
        "bid" |-> Zn (nf bid) ::
        "st" |-> Zn st ::
        "arr" |-> arr ::
        "out" |-> out ::
        "c" |-> Zn c ::
        nil).

Definition BS0 :=
  (MyVector.init (fun i : Fin.t ntrd =>
     Assn (array' (SLoc arr) (ith_vals (fun i => i) reg_b (nf i) 0) 1)
          True
          nil),
   MyVector.init (fun i : Fin.t ntrd =>
     Assn (array' (SLoc arr) (ith_vals (dist (length reg_b)) reg_b (nf tid) 0) 1)
          True
          nil)).

Definition BS1 :=
  (MyVector.init (fun i : Fin.t ntrd =>
     Ex c,
     Assn (array' (SLoc arr) (ith_vals (dist (fst (c_state c))) (snd (c_state (c + 1))) (nf i) 0) 1)
          True
          ("c" |-> Zn c :: nil)),
   MyVector.init (fun i : Fin.t ntrd =>
     Ex c,
     Assn (array' (SLoc arr) (ith_vals (dist (fst (c_state (c + 1)))) (snd (c_state (c + 1))) (nf i) 0) 1)
          True
          ("c" |-> Zn c :: nil))).

Definition BS := (fun i => if Nat.eq_dec i 0 then BS0
                           else if Nat.eq_dec i 1 then BS1
                           else default ntrd).

Lemma st_decrease c :
  fst (c_state (S c)) <= fst (c_state c).
Proof.
  induction c; simpl; try div_lia.
  unfold next; destruct (iter c _ _); simpl.
  div_lia.
Qed.

Lemma st_length c :
  fst (c_state c) <= length reg_b.
Proof.
  induction c.
  - simpl; eauto.
  - forwards*: (st_decrease c); simpl in *; lia.
Qed.  

Lemma stS c :
  fst (c_state (S c)) = (fst (c_state c) + 1) / 2.
Proof.
  simpl; unfold next; destruct (iter c _ _); simpl; eauto.
Qed.

Lemma st_inv1 c :
  (fst (c_state c) - (fst (c_state (S c)))) <= length reg_b.
Proof.
  intros; induction c. simpl in *. div_lia.
  simpl in *.
  unfold next in *; destruct (iter c _ _); simpl in *.
  div_lia.
Qed.  
  
Lemma st_inv2 c :
  length (snd (c_state c)) = length reg_b.
Proof.
  intros; induction c; simpl; eauto.
  lets: (st_decrease c).
  lets: (st_length c).
  unfold next in *; simpl in *; destruct (iter c _ _) eqn:Heq; simpl in *.
  autorewrite with pure.
  repeat destruct lt_dec; try div_lia.
Qed.  

Definition sum_of := fold_right Z.add 0%Z.

Lemma firstn_app {A : Type} n (xs ys : list A) :
  firstn n (xs ++ ys) = firstn n xs ++ firstn (n - length xs) ys.
Proof.
  revert xs ys; induction n; intros [|x xs] [|y ys]; simpl; eauto;
  rewrite IHn; eauto.
Qed.

Lemma sum_of_app xs ys :
  (sum_of (xs ++ ys) = sum_of xs + sum_of ys)%Z.
Proof.
  unfold sum_of; induction xs; simpl; try lia.
Qed.

Lemma firstn_zipWith (A B C : Type) (f : A -> B -> C) xs ys n :
  firstn n (zipWith f xs ys) = zipWith f (firstn n xs) (firstn n ys).
Proof.
  revert xs ys; induction n; intros [|x xs] [|y ys]; simpl; eauto.
  rewrite IHn; eauto.
Qed.

Lemma zipWith_sum_of xs ys:
  length xs = length ys ->
  sum_of (zipWith Z.add xs ys) = (sum_of xs + sum_of ys)%Z.
Proof.
  revert ys; induction xs; intros [|y ys]; simpl; try lia.
  intros; rewrite IHxs; try ring; omega.
Qed.

Lemma firstn_firstn (A : Type) n m (xs : list A) :
  firstn n (firstn m xs) = if lt_dec n m then firstn n xs else firstn m xs.
Proof.
  revert m xs; induction n; intros [|m] [|x xs]; simpl; eauto.
  destruct lt_dec; eauto.
  rewrite IHn; do 2 destruct lt_dec; simpl; eauto; lia.
Qed.

Lemma skipn_skipn (A : Type) n m (xs : list A) :
  skipn n (skipn m xs) = skipn (n + m) xs.
Proof.
  revert n xs; induction m; intros [|n] [|x xs]; try now (simpl; eauto).
  simpl; f_equal; lia.
  repeat rewrite <- plus_n_Sm.
  forwards*: (IHm n xs).
Qed.

Lemma st_inv c :
  sum_of (firstn (fst (c_state (S c))) (snd (c_state (S c)))) = 
  sum_of (firstn (fst (c_state c)) (snd (c_state c))).
Proof.
  forwards*: (st_length c).
  forwards*: (st_inv1 c).
  forwards*: (st_inv2 c).
  simpl; destruct (c_state c) eqn:Heq; simpl in *.
  rewrite firstn_app.
  rewrite sum_of_app.
  autorewrite with pure.
  rewrite firstn_zipWith.
  rewrites zipWith_sum_of; [|autorewrite with pure ].
  2: repeat destruct lt_dec; try div_lia.
  rewrite firstn_firstn; destruct lt_dec; try (false; div_lia).
  rewrite firstn_firstn; destruct lt_dec; try (false; div_lia).
  rewrite <-(firstn_skipn (n - (n + 1) / 2) l) at 6; rewrite firstn_app.
  rewrite firstn_firstn; destruct (lt_dec n _); try (false; div_lia).
  autorewrite with pure; rewrite sum_of_app.
  rewrite <-(firstn_skipn ((n + 1) / 2 - (n - (n + 1) / 2)) (skipn (n - (n + 1) / 2) l)); repeat rewrite firstn_app, sum_of_app.
  rewrite !firstn_firstn.
  rewrite !skipn_skipn.
  autorewrite with pure.
  elim_div.
  repeat (destruct lt_dec; try (false; lia)).

  cutrewrite (x - (n - x) - (x - (n - x)) = 0); [| lia]; simpl.
  cutrewrite (n - (n - x) - (x - (n - x)) = n - x); [|lia].
  cutrewrite (x - (n - x) + (n - x) = x); [|lia].
  lia.

  cutrewrite (length l = n);[| lia].
  cutrewrite (x - (n - x) - (x - (n - x)) = 0); [| lia]; simpl.
  cutrewrite (n - (n - x) - (x - (n - x)) = n - x); [|lia].
  cutrewrite (x - (n - x) + (n - x) = x); [|lia].
  lia.

  cutrewrite (length l = n);[| lia].
  cutrewrite (x = n); [|lia].
  rewrite !minus_diag; simpl. lia.

  cutrewrite (x = n); [|lia].
  cutrewrite (length l = n);[| lia].
  rewrite !minus_diag; simpl. lia.
Qed.

Lemma firstn_length_self (A : Type) (xs : list A) :
  firstn (length xs) xs = xs.
Proof.  
  induction xs; simpl; eauto; rewrite IHxs; eauto.
Qed.

Lemma before_loop :
  sum_of (firstn (fst (c_state 0)) (snd (c_state 0))) = 
  sum_of reg_b.
Proof.
  simpl; rewrite firstn_length_self; eauto.
Qed.

Lemma sum_of_inv c:
  sum_of (firstn (fst (c_state c)) (snd (c_state c))) =
  sum_of reg_b.
Proof.
  induction c; eauto using before_loop.
  rewrite st_inv; eauto.
Qed.

Lemma st0 c :
  fst (c_state c) = 0 -> reg_b = nil.
Proof.
  induction c; simpl.
  - destruct reg_b; simpl; inversion 1; eauto.
  - destruct (c_state c); simpl in *.
    intros; apply IHc.
    div_lia.
Qed.

Lemma init_vals0 c:
  reg_b = nil -> snd (c_state c) = nil.
Proof.
  induction c; simpl; eauto.
  intros; destruct (c_state c); simpl in *.
  rewrite* IHc; simpl.
  destruct (n - (n + 1) / 2); simpl; eauto.
Qed.

Lemma after_loop c :
  fst (c_state c) <= 1 ->
  nth 0 (snd (c_state c)) 0%Z = sum_of reg_b.
Proof.
  intros; rewrites<- (sum_of_inv c).
  lets: (st0 c).
  lets: (init_vals0 c).
  destruct (c_state c); simpl in *.
  assert (n = 0 \/ n = 1) as [|] by omega; substs; simpl.
  rewrite H1; eauto.
  destruct l; simpl; eauto.
  lia.
Qed.  

Lemma barrier_sync_then vals st c :
      st = fst (c_state c) ->
      vals = snd (c_state c) ->
      (1 < Zn st)%Z -> 
      (Zn (nf tid) + (Zn st + 1) / 2 < Zn st)%Z ->
      ith_vals (dist st)
               (set_nth (nf tid) vals
                        (get vals (nf tid) + get vals (nf tid + (st + 1) / 2))%Z) 
               (nf tid) 0 =
      ith_vals (dist (fst (c_state c))) (snd (c_state (c + 1))) (nf tid) 0.
Proof.
  intros.
  subst st vals.
  rewrite (Nat.add_1_r c).
  applys (>>(@eq_from_nth) (@None Z)).
  autorewrite with pure.
  rewrites (st_inv2); rewrites (st_inv2); lia.
  autorewrite with pure.
  intros.
  autorewrite with pure.
  repeat rewrites (st_inv2) in *.
  unfold dist; simpl in *.
  forwards*: (st_inv1 c). 
  forwards*: (st_inv2 c).
  forwards*: (st_length c).
  destruct (c_state c); simpl in *; autorewrite with pure.
  rewrites* (>> nth_zipWith 0 0 0)%Z.
  autorewrite with pure.
  elim_div.
  Time (repeat match goal with
     | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
     | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
   end);
    first [do 3 f_equal; ring | do 2 f_equal; lia].
Qed.

Lemma barrier_sync_else vals st c :
  st = fst (c_state c) ->
  vals = snd (c_state c) ->
  (1 < Zn st)%Z -> 
  ~(Zn (nf tid) + (Zn st + 1) / 2 < Zn st)%Z ->
  ith_vals (dist st) vals (nf tid) 0 =
  ith_vals (dist (fst (c_state c))) (snd (c_state (c + 1))) (nf tid) 0.
Proof.
  intros.
  subst st vals.
  rewrite (Nat.add_1_r c).
  applys (>>(@eq_from_nth) (@None Z)).
  autorewrite with pure; repeat rewrites (st_inv2); lia.
  introv; autorewrite with pure; intros.
  repeat rewrites (st_inv2) in *.
  unfold dist; simpl in *.
  forwards*: (st_inv1 c).
  forwards*: (st_inv2 c).
  forwards*: (st_length c).
  destruct (c_state c); simpl in *; autorewrite with pure.
  rewrites* (>> nth_zipWith 0 0 0)%Z.
  autorewrite with pure.
  elim_div.
  Time (repeat match goal with
     | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
     | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
  end).
Qed.

Hint Resolve barrier_sync_then barrier_sync_else : pure_lemma.

Hypothesis sh_vals_len : length sh_vals = ntrd + 0.

Lemma reduce_ok :
  CSL BS tid 
      (Assn (array' (SLoc arr) (ith_vals (fun i => i) sh_vals (nf tid) 0) 1 ***
             array (GLoc inp) init_vals p ***
             array' (GLoc out) (ith_vals (fun i => i * ntrd) out_vals (nf tid + nf bid * ntrd) 0) 1)
            True
            ("arr" |-> arr ::
             "inp" |-> inp ::
             "out" |-> out :: 
             "l" |-> Zn (length init_vals) ::
             "tid" |-> Zn (nf tid) ::
             "bid" |-> Zn (nf bid) :: nil))
      (reduce inv)
      (Ex c,
       Assn (array' (SLoc arr) (ith_vals (dist (fst (c_state c))) (snd (c_state c)) (nf tid) 0) 1 ***
             array (GLoc inp) init_vals p ***
             array' (GLoc out) (ith_vals (fun i => i * ntrd) (ls_init 0 nblk (fun i => sum_of (reg_b' i))) (nf tid + nf bid * ntrd) 0) 1)
            True
            ("c" |-> Zn c :: nil)).
Proof.
  intros; unfold reduce, inv, BS.
  assert (nf tid < ntrd) by eauto.
  assert (nf bid < nblk) by eauto.
  pose proof reg_b_length.
  
  hoare_forward.
  rewrite inp_len; eauto.

  hoare_forward.

  hoare_forward; eauto.
  { applys (>>(@eq_from_nth) (@None Z)).
    autorewrite with pure; rewrite* reg_b_length.
    lia.
    clear H2.
    unfold reg_b'; intros i Hi; autorewrite with pure in *.
    repeat match goal with
     | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; nia)
     | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; nia)
    end; do 2 f_equal; nia. }

  do 4 hoare_forward.
  hoare_forward.
  lets: (st_decrease c); rewrite stS in *.

  hoare_forward.
  hoare_forward.
  rewrite st_inv2; lia.
  unfold dist; repeat (destruct lt_dec; eauto); div_lia.
  
  hoare_forward.
  forwards*: (st_length c).
  forwards*: (st_inv2 c); try div_lia.
  unfold dist; repeat (destruct lt_dec; eauto); div_lia.

  hoare_forward; eauto.
  rewrite st_inv2; lia.
  unfold dist; repeat (destruct lt_dec; eauto); div_lia.

  hoare_forward; eauto.

  do 2 hoare_forward; eauto with pure_lemma.

  do 3 hoare_forward.
  prove_imp.
  clear H3.
  repeat f_equal; subst st.
  rewrite Nat.add_1_r, stS; repeat f_equal; lia.
  lia.
  rewrite (Nat.add_1_r c), stS; repeat f_equal; lia.

  hoare_forward; eauto with pure_lemma.
  do 2 hoare_forward; prove_imp; substs.
  
  clear H3.
  repeat f_equal. 
  rewrite Nat.add_1_r, stS; repeat f_equal; lia.
  lia.
  rewrite (Nat.add_1_r c), stS; repeat f_equal; lia.
  
  prove_imp.
  
  hoare_forward.
  hoare_forward.
  rewrite st_inv2, reg_b_length; lia.
  cutrewrite (nf tid = 0); [|lia].
  unfold dist; simpl; repeat destruct lt_dec; eauto.
  
  repeat hoare_forward; eauto.
  hoare_forward; eauto.

  Hint Rewrite @init_length @ls_init_spec : pure.
  prove_imp; subst st; eauto; clear H2; applys (>>eq_from_nth (@None Z));
  autorewrite with pure; try lia; intros i; autorewrite with pure; intros Hi;
  rewrite out_len in *.
  - cutrewrite (nf tid = 0); [|lia]; simpl.
    assert (i * ntrd = nf bid * ntrd -> i = nf bid) by nia.
    repeat match goal with
     | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; nia)
     | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; nia)
    end.
    f_equal.
    apply after_loop; lia.
  - simpl.
    assert (nf tid <> 0) by lia.
    assert (i * ntrd <> nf tid + nf bid * ntrd).
    { intros Hc.
      apply (f_equal (fun x => x mod ntrd)) in Hc.
      rewrite Nat.mod_add, Nat.mod_mul, Nat.mod_small in Hc; eauto. }
    repeat match goal with
     | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; nia)
     | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; nia)
    end.
Qed.
    
End reduce.

Section reduce_b.
  Variable ntrd nblk : nat.
  Hypothesis ntrd_neq_0 : ntrd <> 0.
  Hypothesis nblk_neq_0 : nblk <> 0.
  Hint Resolve ntrd_neq_0 nblk_neq_0.
  Variable bid : Fin.t nblk.

  Open Scope string_scope.
  Open Scope list_scope.
  
  Arguments div _ _ : simpl never.
  Arguments modulo _ _ : simpl never.
  Variable init_vals : list val.
  Variable arr : val.

  Definition E := fun x =>
    if var_eq_dec x "arr" then Lo
    else if var_eq_dec x "l" then Lo
    else if var_eq_dec x "bid" then Lo
    else Hi.



  Lemma reduce_ok_b :
    CSLp nblk E
         (Assn (array (SLoc arr) init_vals 1)
               True
               ("arr" |-> arr :: "l" |-> Zn (length init_vals) :: nil))
         (reduce TrueP)
         (Ex (vals : list val) (st c : nat),
            Assn (array (SLoc arr) vals 1)
                 (vals = snd (iter c next (length init_vals, init_vals)) /\
                  fst (iter c next (length init_vals, init_vals)) <= st)
                 nil).
  Proof.
    eapply rule_par.
    