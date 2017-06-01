Require Import Default GPUCSL LibTactics Psatz CSLLemma SetoidClass Utils CUDALib.
Require Import Grid CSLLemma CSLTactics.
Require Import PeanoNat.
Arguments Nat.div _ _ : simpl never.
Arguments Nat.modulo _ _ : simpl never.

Section reduce.
Variable ntrd nblk : nat.
Notation p := (1 / injZ (Zn (nblk * ntrd)))%Qc.

Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis nblk_neq_0 : nblk <> 0.
Hint Resolve ntrd_neq_0 nblk_neq_0.

Variable init_vals out_vals : list Z.
Variable inp out : Z.

Hypothesis inp_len : length init_vals = nblk * ntrd.
Hypothesis out_len : length out_vals = nblk + 0.

Definition next (x : nat * list Z):=
  let (l, ls) := x in
  let d := ((l + 1) / 2) in
  (d, zipWith Z.add (firstn (l - d) ls) (firstn (l - d) (skipn d ls)) ++ skipn (l - d) ls).

Fixpoint iter {T : Type} n f (x : T) := 
  match n with
  | 0 => x
  | S n => f (iter n f x)
  end.

Section block.
Variable arr : Z.
Variable sh_vals : list val.
Hypothesis sh_vals_len : length sh_vals = ntrd + 0.
Variable bid : Fin.t nblk.

Definition reg_b' j := (firstn ntrd (skipn (ntrd * j) init_vals)).
Notation reg_b := (reg_b' (nf bid)).

Notation c_state c := (iter c next (length reg_b, reg_b)).

Section thread.

Variable tid : Fin.t ntrd.

Lemma reg_b_length:
  length reg_b = ntrd + 0.
Proof.
  unfold reg_b'; autorewrite with pure.
  rewrite inp_len in *.
  assert (nf bid < nblk) by eauto.
  destruct lt_dec; nia.
Qed.

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

Lemma sum_of_app xs ys :
  (sum_of (xs ++ ys) = sum_of xs + sum_of ys)%Z.
Proof.
  unfold sum_of; induction xs; simpl; try lia.
Qed.

Lemma zipWith_sum_of xs ys:
  length xs = length ys ->
  sum_of (zipWith Z.add xs ys) = (sum_of xs + sum_of ys)%Z.
Proof.
  revert ys; induction xs; intros [|y ys]; simpl; try lia.
  intros; rewrite IHxs; try ring; omega.
Qed.

Lemma firstn_plus A n m (l : list A) :
  firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  revert l; induction n; intros [|? ?]; simpl; eauto.
  destruct m; eauto.
  congruence.
Qed.

Lemma st_inv c :
  sum_of (firstn (fst (c_state (S c))) (snd (c_state (S c)))) = 
  sum_of (firstn (fst (c_state c)) (snd (c_state c))).
Proof.
  forwards*: (st_length c).
  forwards*: (st_inv1 c).
  forwards*: (st_inv2 c).
  simpl; destruct (c_state c) eqn:Heq; simpl in *.
  rewrite firstn_app, firstn_zipWith, sum_of_app.
  rewrite zipWith_sum_of;
    [|repeat (autorewrite with pure; destruct lt_dec); div_lia].
  repeat (rewrite firstn_firstn; destruct lt_dec; try div_lia).
  lazymatch goal with
  | [|- context [?X - length ?Y]] =>
    cutrewrite (X - length Y = (n + 1) / 2 - (n - (n + 1) / 2));
      [|autorewrite with pure; repeat destruct lt_dec; div_lia]
  end.
  assert (Heq_n : n = (n - (n + 1) / 2) + ((n + 1) / 2 - (n - (n + 1) / 2)) + (n - (n + 1) / 2))
         by div_lia.
  rewrite Heq_n at 11.
  repeat rewrite firstn_plus, sum_of_app.
  repeat rewrite <-Zplus_assoc; f_equal.
  rewrite le_plus_minus_r; [|div_lia].
  lia.
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

Definition reduce inv := 
  "t" ::= ["inp" +o ("tid" +C "bid" *C Zn ntrd)] ;;
  ["arr" +o "tid"] ::= "t" ;;
  Cbarrier 0 ;;
  "c" ::= 0%Z ;;
  "st" ::= Zn ntrd ;;
  WhileI inv (1%Z <C "st") (
    "d" ::= ("st" +C 1%Z) /C 2%Z ;;
    Cif ("tid" +C "d" <C "st") (
      "t1" ::= [ "arr" +o "tid" ] ;;
      "t2" ::= [ "arr" +o ("tid" +C "d") ] ;;
      [ "arr" +o "tid" ] ::= "t1" +C "t2"
    ) Cskip ;;
    Cbarrier 1 ;;
    "st" ::= "d" ;;
    "c" ::= "c" +C 1%Z
  ) ;;
  Cif ("tid" ==C 0%Z) (
    "t" ::= [ "arr" +o 0%Z] ;;
    ["out" +o "bid"] ::= "t"
  ) Cskip.

Definition dist st i :=
  let d := (st + 1) / 2 in
  if lt_dec (i + d) st then i
  else if lt_dec i st then (i - d)
  else 0.

Definition inv :=
  Ex st c,
  let vals := map VZ (snd (c_state c)) in
  Assn (array' (SLoc arr) (ith_vals (dist st) vals (nf tid) 0) 1 ***
        array (GLoc inp) (map VZ init_vals) p ***
        array' (GLoc out) (ith_vals (fun i => i * ntrd) (map VZ out_vals) (nf tid + nf bid * ntrd) 0) 1)
       (st = fst (c_state c))
       ("tid" |-> Zn (nf tid) ::
        "bid" |-> Zn (nf bid) ::
        "st" |-> Zn st ::
        "arr" |-> SLoc arr ::
        "out" |-> GLoc out ::
        "c" |-> Zn c ::
        nil).

Definition BS0 :=
  (MyVector.init (fun i : Fin.t ntrd =>
     Assn (array' (SLoc arr) (ith_vals (fun i => i) (map VZ reg_b) (nf i) 0) 1)
          True
          nil),
   MyVector.init (fun i : Fin.t ntrd =>
     Assn (array' (SLoc arr) (ith_vals (dist (length reg_b)) (map VZ reg_b) (nf i) 0) 1)
          True
          nil)).

Definition BS1 :=
  (MyVector.init (fun i : Fin.t ntrd =>
     Ex c,
     Assn (array' (SLoc arr) (ith_vals (dist (fst (c_state c))) (map VZ (snd (c_state (c + 1)))) (nf i) 0) 1)
          True
          ("c" |-> Zn c :: nil)),
   MyVector.init (fun i : Fin.t ntrd =>
     Ex c,
     Assn (array' (SLoc arr) (ith_vals (dist (fst (c_state (c + 1)))) (map VZ (snd (c_state (c + 1)))) (nf i) 0) 1)
          True
          ("c" |-> Zn c :: nil))).

Definition BS := (fun i => if Nat.eq_dec i 0 then BS0
                           else if Nat.eq_dec i 1 then BS1
                           else defaultSpec ntrd).

Lemma barrier_sync_then vals st c :
      st = fst (c_state c) ->
      vals = snd (c_state c) ->
      (1 < Zn st)%Z -> 
      (Zn (nf tid) + (Zn st + 1) / 2 < Zn st)%Z ->
      ith_vals (dist st)
               (set_nth (nf tid) (z2v vals)
                        (get vals (nf tid) + get vals (nf tid + (st + 1) / 2))%Z) 
               (nf tid) 0 =
      ith_vals (dist (fst (c_state c))) (z2v (snd (c_state (c + 1)))) (nf tid) 0.
Proof.
  intros.
  subst st vals.
  rewrite (Nat.add_1_r c).
  applys (>>(@eq_from_nth) (@None val)).
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
  repeat rewrites* (>> map_nth).
  autorewrite with pure.
  rewrites (>>nth_zipWith 0 0 0)%Z.
  autorewrite with pure.
  elim_div.
  Time (repeat match goal with
     | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
     | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
   end).
  all: first [do 4 f_equal; ring | do 3 f_equal; lia].
Qed.

Lemma barrier_sync_else vals st c :
  st = fst (c_state c) ->
  vals = z2v (snd (c_state c)) ->
  (1 < Zn st)%Z ->
  ~(Zn (nf tid) + (Zn st + 1) / 2 < Zn st)%Z ->
  ith_vals (dist st) vals (nf tid) 0 =
  ith_vals (dist (fst (c_state c))) (z2v (snd (c_state (c + 1)))) (nf tid) 0.
Proof.
  intros.
  subst st vals.
  rewrite (Nat.add_1_r c).
  applys (>>(@eq_from_nth) (@None val)).
  autorewrite with pure; repeat rewrites (st_inv2); lia.
  introv; autorewrite with pure; intros.
  repeat rewrites (st_inv2) in *.
  unfold dist; simpl in *.
  forwards*: (st_inv1 c).
  forwards*: (st_inv2 c).
  forwards*: (st_length c).
  destruct (c_state c); simpl in *; autorewrite with pure.
  repeat rewrites* (>> map_nth).
  autorewrite with pure.
  rewrites* (>> nth_zipWith 0 0 0)%Z.
  autorewrite with pure.
  elim_div.
  Time (repeat match goal with
     | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
     | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
  end).
Qed.

Hint Resolve barrier_sync_then barrier_sync_else : pure_lemma.

Lemma reduce_ok :
  CSL BS tid 
      (Assn (array' (SLoc arr) (ith_vals (fun i => i) sh_vals (nf tid) 0) 1 ***
             array (GLoc inp) (z2v init_vals) p ***
             array' (GLoc out) (ith_vals (fun i => i * ntrd) (z2v out_vals) (nf tid + nf bid * ntrd) 0) 1)
            True
            ("arr" |-> SLoc arr ::
             "inp" |-> GLoc inp ::
             "out" |-> GLoc out :: 
             "l" |-> Zn (length init_vals) ::
             "tid" |-> Zn (nf tid) ::
             "bid" |-> Zn (nf bid) :: nil))
      (reduce inv)
      (Ex c,
       Assn (array' (SLoc arr) (ith_vals (dist (fst (c_state c))) (z2v (snd (c_state c))) (nf tid) 0) 1 ***
             array (GLoc inp) (z2v init_vals) p ***
             array' (GLoc out) (ith_vals (fun i => i * ntrd) (z2v (ls_init 0 nblk (fun i => sum_of (reg_b' i)))) (nf tid + nf bid * ntrd) 0) 1)
            True
            ("c" |-> Zn c :: "arr" |-> SLoc arr :: nil)).
Proof.
  intros; unfold reduce, inv, BS.
  assert (nf tid < ntrd) by eauto.
  assert (nf bid < nblk) by eauto.
  forwards*: (>>id_lt_nt_gr (nf tid) (nf bid)).
  pose proof reg_b_length.
  hoare_forward.
  rewrite inp_len; eauto.

  hoare_forward.
  hoare_forward; eauto.
  { applys (>>(@eq_from_nth) (default : option val)).
    autorewrite with pure; rewrite* reg_b_length.
    clear H2 H3.
    unfold reg_b'; intros i Hi; autorewrite with pure in *.
    rewrites (>> nth_map 0%Z); [repeat autorewrite with pure; try lia|].
    rewrites (>> nth_map 0%Z); [repeat autorewrite with pure; try lia|].
    destruct lt_dec; try nia.
    repeat autorewrite with pure.
    repeat lazymatch goal with
     | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia)
     | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia)
    end; do 3 f_equal; nia. }

  do 4 hoare_forward.
  hoare_forward.
  lets: (st_decrease c); rewrite stS in *.
  forwards*: (st_length c).
  forwards*: (st_inv2 c).

  hoare_forward.
  hoare_forward.
  unfold dist; repeat (destruct lt_dec; eauto); div_lia.
  
  hoare_forward.
  unfold dist; repeat (destruct lt_dec; eauto); div_lia.

  (* Because t1 |-> nth (z2v ...) 0%Z, we need to expose VZ at the top of value *)
  apply CSL_prop_prem; intros Hp.
  repeat (rewrites (>>nth_map 0%Z); [div_lia|]).

  hoare_forward; eauto.
  unfold dist; repeat (destruct lt_dec; eauto); div_lia.

  hoare_forward; eauto.

  do 2 hoare_forward; eauto with pure_lemma.  

  do 3 hoare_forward.
  prove_imp.
  assert (Zn c0 = Zn c) by congruence.
  clear H6.
  repeat f_equal; subst st; try lia.
  rewrite Nat.add_1_r, stS; repeat f_equal; lia.
  rewrite (Nat.add_1_r c), stS; repeat f_equal; lia.
  substs; eauto.
    
  hoare_forward; eauto with pure_lemma.
  do 2 hoare_forward; prove_imp; substs.
  
  clear H6.
  assert (Zn c0 = Zn c) by congruence.
  assert (c0 = c) by lia; substs.
  repeat f_equal. 
  rewrite Nat.add_1_r, stS; eauto.
  rewrite (Nat.add_1_r c), stS; eauto.
  
  prove_imp.
  { do 3 f_equal; omega. }
  simpl; omega.
  hoare_forward.
  hoare_forward.
  rewrite st_inv2, reg_b_length; lia.
  cutrewrite (nf tid = 0); [|lia].
  unfold dist; simpl; repeat destruct lt_dec; eauto.
  
  repeat hoare_forward; eauto.
  hoare_forward; eauto.

  prove_imp; eauto; try subst st; clear H3; applys (>>eq_from_nth (@None val));
  autorewrite with pure; try lia; intros i; autorewrite with pure; intros Hi;
  eauto; rewrite out_len.
  - cutrewrite (nf tid = 0); [|lia]; simpl.
    assert (i * ntrd = nf bid * ntrd -> i = nf bid) by nia.
    repeat match goal with
     | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; nia)
     | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; nia)
    end.
    f_equal.
    rewrite !map_nth; autorewrite with pure; f_equal.
    destruct lt_dec; try lia.
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

End thread.

Definition ith_pre (tid : Fin.t ntrd) :=
  (Assn
     (array' (SLoc arr) (ith_vals (fun i : nat => i) sh_vals (nf tid) 0) 1 ***
      array (GLoc inp) (z2v init_vals) (1 / injZ (Zn (nblk * ntrd))) ***
      array' (GLoc out)
        (ith_vals (fun i : nat => i * ntrd) (z2v out_vals)
           (nf tid + nf bid * ntrd) 0) 1) True
     ("arr" |-> SLoc arr ::
      "inp" |-> GLoc inp ::
      "out" |-> GLoc out ::
      "l" |-> Zn (Datatypes.length init_vals) ::
      "bid" |-> Zn (nf bid) :: nil)).

Definition ith_post (tid : Fin.t ntrd) :=
  (Ex c : nat,
   Assn
     (array' (SLoc arr)
        (ith_vals
           (dist
              (fst
                 (iter c next
                    (Datatypes.length (reg_b' (nf bid)), (reg_b' (nf bid))))))
           (snd
              (iter c next
                 (Datatypes.length (reg_b' (nf bid)), reg_b' (nf bid))))
           (nf tid) 0) 1 ***
      array (GLoc inp) init_vals (1 / injZ (Zn (nblk * ntrd))) ***
      array' (GLoc out)
        (ith_vals (fun i : nat => i * ntrd)
           (ls_init 0 nblk (fun i : nat => sum_of (reg_b' i)))
           (nf tid + nf bid * ntrd) 0) 1) True ("c" |-> Zn c :: "arr" |-> arr :: nil)).

Definition jth_pre :=
  (Assn
     (array (SLoc arr) sh_vals 1 ***
      fin_star ntrd (fun _  => array (GLoc inp) init_vals (1 / injZ (Zn (nblk * ntrd)))) ***
      fin_star ntrd (fun tid =>
        array' (GLoc out)
        (ith_vals (fun i  => i * ntrd) out_vals
           (tid + nf bid * ntrd) 0) 1))
     True
     ("arr" |-> arr ::
      "inp" |-> inp ::
      "out" |-> out ::
      "l" |-> Zn (Datatypes.length init_vals) ::
      nil)).

Definition jth_post :=
  Ex sh_vals,
  (Assn
     (array (SLoc arr) sh_vals 1 ***
      fin_star ntrd (fun _  => array (GLoc inp) init_vals (1 / injZ (Zn (nblk * ntrd)))) ***
      fin_star ntrd (fun tid =>
        array' (GLoc out)
        (ith_vals (fun i => i * ntrd) (ls_init 0 nblk (fun i : nat => sum_of (reg_b' i)))
           (tid + nf bid * ntrd) 0) 1))
     (length sh_vals = ntrd)
     ("arr" |-> arr :: nil)).

Definition E := fun x =>
  if var_eq_dec x "arr" then Lo
  else if var_eq_dec x "inp" then Lo
  else if var_eq_dec x "out" then Lo
  else if var_eq_dec x "l" then Lo
  else if var_eq_dec x "bid" then Lo
  else if var_eq_dec x "c" then Lo
  else if var_eq_dec x "st" then Lo
  else if var_eq_dec x "d" then Lo
  else Hi.

Lemma reduce_ok_b :
  CSLp ntrd E
       (jth_pre ** Assn Emp True ("bid" |-> Zn (nf bid) :: nil))
       (reduce Emp_assn)
       jth_post.
Proof.
  applys (>>rule_block BS E (MyVector.init ith_pre) (MyVector.init ith_post)).
    unfold BS, ith_pre, ith_post; eauto.
  - unfold E; intros [|[|i]]; simpl; split; intros; rewrite MyVector.init_spec; simpl;
    try prove_low_assn.
  - intros [|[|i]]; eauto; simpl.
    prove_istar_imp.
    unfold dist; repeat destruct lt_dec; try omega.
    rewrite array'_ok in * |- *; eauto; rewrite reg_b_length; intros; try omega.
    repeat destruct lt_dec; try omega.
    prove_istar_imp.
    rewrite array'_ok in * |- *; eauto; intros; try omega;
    rewrite st_inv2, reg_b_length in *;
    unfold dist; repeat destruct lt_dec; try omega.
  - unfold BS; intros [|[|i]] ?; simpl; rewrite !MyVector.init_spec; split; prove_precise.
  - unfold jth_pre, ith_pre.
    intros s h H; rewrite assn_var_in in H; revert s h H.
    prove_istar_imp.
    repeat rewrite ls_star_res.
    rewrite array'_ok; [|intros; lia]; auto.
  - lets st2: st_inv2.
    lets reg_b_len: reg_b_length.
    unfold jth_post, ith_post.
    prove_istar_imp.
    repeat rewrite ls_star_res in *.
    rewrite array'_ok in *; eauto.
    intros i; rewrite st_inv2, reg_b_length; intros ?; unfold dist.
    repeat destruct lt_dec; try lia.
    rewrite st2, reg_b_len; eauto.
  - unfold ith_pre; intros; rewrite MyVector.init_spec; prove_low_assn.
  - unfold ith_post; intros; rewrite MyVector.init_spec; prove_low_assn.
  - unfold reduce.
    unfold E.
    instantiate (1 := Lo).
    repeat prove_typing_cmd.
  - intros; rewrite !MyVector.init_spec.
    eapply rule_conseq; eauto using reduce_ok.
    unfold ith_pre; intros s h H; rewrite assn_var_in in H; revert s h H; prove_imp.
Qed.
   
End block.

Definition reduce_prog := Pr ((SD "arr" Int ntrd) :: nil) (reduce Emp_assn).

Definition jth_pre' (bid : Fin.t nblk) :=
  (Assn
      (fin_star ntrd (fun _  => array (GLoc inp) init_vals (1 / injZ (Zn (nblk * ntrd)))) ***
       fin_star ntrd (fun tid =>
         array' (GLoc out)
         (ith_vals (fun i  => i * ntrd) out_vals
            (tid + nf bid * ntrd) 0) 1))
     True
     ("inp" |-> inp ::
      "out" |-> out ::
      "l" |-> Zn (Datatypes.length init_vals) ::
      nil)).

Definition jth_post' (bid : Fin.t nblk) :=
  (Assn
      (fin_star ntrd (fun _  => array (GLoc inp) init_vals (1 / injZ (Zn (nblk * ntrd)))) ***
       fin_star ntrd (fun tid =>
         array' (GLoc out)
         (ith_vals (fun i => i * ntrd) (ls_init 0 nblk (fun i : nat => sum_of (reg_b' i)))
            (tid + nf bid * ntrd) 0) 1))
     True
     nil).

Lemma reduce_ok_g :
  CSLg ntrd nblk
       (Assn (array (GLoc inp) init_vals 1 ***
              array (GLoc out) out_vals 1)
             True
             ("inp" |-> inp ::
              "out" |-> out ::
              "l" |-> Zn (length init_vals) :: nil))
       reduce_prog
       (Assn (array (GLoc inp) init_vals 1 ***
              array (GLoc out) (ls_init 0 nblk (fun i => reduce.sum_of (reg_b' i))) 1)
             True
             nil).
Proof.
  applys (>> rule_grid E (MyVector.init jth_pre') (MyVector.init jth_post'));
  unfold jth_pre', jth_post'; eauto.
  - prove_istar_imp.
    rewrite ls_star_res.
    repeat simpl_nested_istar.
    rewrite array'_ok. 
    2: intros; nia.
    rewrite <-is_array_is_array_p_1; eauto.
    nia.
  - introv; rewrite !MyVector.init_spec.

    apply CSLp_preprocess; simpl.
    intros [|vs [|? ?]] ? ?; simpl in *; try lia.
    destruct locs as [|l [|? ?]]; simpl in *; try lia.
    unfold sh_spec_assn; simpl.

    eapply rule_p_backward; [|intros; rewrite Assn_combine in *; eauto].
    apply rule_p_assn; intros.    
    eapply rule_p_conseq; try applys (>>reduce_ok_b l vs bid); try lia.

    + unfold jth_pre.
      intros s h Hsat; rewrite assn_var_in; revert s h Hsat; prove_imp.
      rewrite <-!res_assoc in H4.
      repeat sep_cancel'.
    + unfold jth_post.
      intros s h [sh_vals Hsat].
      exists (sh_vals :: nil); fold_sat; rewrite sat_pure_l; splits; simpl; eauto.
      fold_sat; fold_sat_in Hsat; unfold sh_spec_assn'.
      revert s h Hsat; prove_imp.
      rewrite <-!res_assoc; simpl.
      repeat sep_cancel'.
  - prove_istar_imp.
    rewrite !ls_star_res in *.
    repeat simpl_nested_istar.
    rewrite array'_ok in *.
    2: intros; rewrite @init_length in *; nia.
    rewrite <-is_array_is_array_p_1 in *; eauto.
    nia.
  - intros; rewrite MyVector.init_spec.
    apply inde_assn_vars.
    prove_low_expr; intros Hc; des_disj Hc; congruence.
  - intros; rewrite MyVector.init_spec.
    prove_low_assn.
  - intros; rewrite MyVector.init_spec.
    apply has_no_vars_assn.
  - unfold E; simpl.
    intros ? [? | []]; substs; eauto.
  - simpl; tauto.
Qed.

End reduce.