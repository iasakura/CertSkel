Require Import GPUCSL scan_lib LibTactics Psatz CSLLemma SetoidClass.
Require Import CSLLemma CSLTactics.

Coercion Var : string >-> var.
Open Scope string_scope.
Open Scope list_scope.

Arguments div _ _ : simpl never.
Arguments modulo _ _ : simpl never.

Section reduce.
Variable ntrd nblk : nat.
Notation p := (1 / injZ (Zn (nblk * ntrd)))%Qc.

Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis nblk_neq_0 : nblk <> 0.
Hint Resolve ntrd_neq_0 nblk_neq_0.

Variable init_vals out_vals sh_vals : list val.
Variable arr inp out : val.

Hypothesis inp_len : length init_vals = nblk * ntrd.
Hypothesis out_len : length out_vals = nblk + 0.
Hypothesis sh_vals_len : length sh_vals = ntrd + 0.

Definition next (x : nat * list val):=
  let (l, ls) := x in
  let d := ((l + 1) / 2) in
  (d, zipWith Z.add (firstn (l - d) ls) (firstn (l - d) (skipn d ls)) ++ skipn (l - d) ls).

Fixpoint iter {T : Type} n f (x : T) := 
  match n with
  | 0 => x
  | S n => f (iter n f x)
  end.

Section block.

Variable bid : Fin.t nblk.

Definition reg_b' j := (firstn ntrd (skipn (ntrd * j) init_vals)).
Notation reg_b := (reg_b' (nf bid)).

Notation c_state c := (iter c next (length reg_b, reg_b)).

Section thread.

Variable tid : Fin.t ntrd.

Lemma reg_b_length:
  length reg_b = ntrd.
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
     Assn (array' (SLoc arr) (ith_vals (dist (length reg_b)) reg_b (nf i) 0) 1)
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
            ("c" |-> Zn c :: "arr" |-> arr :: nil)).
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

End thread.

Definition ith_pre (tid : Fin.t ntrd) :=
  (Assn
     (array' (SLoc arr) (ith_vals (fun i : nat => i) sh_vals (nf tid) 0) 1 ***
      array (GLoc inp) init_vals (1 / injZ (Zn (nblk * ntrd))) ***
      array' (GLoc out)
        (ith_vals (fun i : nat => i * ntrd) out_vals
           (nf tid + nf bid * ntrd) 0) 1) True
     ("arr" |-> arr ::
      "inp" |-> inp ::
      "out" |-> out ::
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
                    (Datatypes.length (reg_b' (nf bid)), reg_b' (nf bid)))))
           (snd
              (iter c next
                 (Datatypes.length (reg_b' (nf bid)), reg_b' (nf bid))))
           (nf tid) 0) 1 ***
      array (GLoc inp) init_vals (1 / injZ (Zn (nblk * ntrd))) ***
      array' (GLoc out)
        (ith_vals (fun i : nat => i * ntrd)
           (ls_init 0 nblk (fun i : nat => sum_of (reg_b' i)))
           (nf tid + nf bid * ntrd) 0) 1) True ("c" |-> Zn c :: "arr" |-> arr :: nil)).

Definition fin_star n (f : nat -> res) :=
  List.fold_right Star Emp (ls_init 0 n f).

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
      "bid" |-> Zn (nf bid) :: nil)).

Definition jth_post :=
  Ex sh_vals,
  (Assn
     (array (SLoc arr) sh_vals 1 ***
      fin_star ntrd (fun _  => array (GLoc inp) init_vals (1 / injZ (Zn (nblk * ntrd)))) ***
      fin_star ntrd (fun tid =>
        array' (GLoc out)
        (ith_vals (fun i => i * ntrd) (ls_init 0 nblk (fun i : nat => sum_of (reg_b' i)))
           (tid + nf bid * ntrd) 0) 1))
     True
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

Require Import Skel_lemma scan_lib.

Ltac no_side_cond tac :=
  (now tac) || (tac; [now auto_star..|idtac]).

Lemma fv_edenot e s s' :
  (forall x, In x (fv_E e) -> s x = s' x)
  -> edenot e s = edenot e s'.
Proof.
  intros Heq.
  Ltac tac Heq H := rewrites* H; try now (intros; applys* Heq; repeat rewrite in_app_iff; eauto).
  induction e; simpl in *; 
  (try no_side_cond ltac:(tac Heq IHe));
  (try no_side_cond ltac:(tac Heq IHe1));
  (try no_side_cond ltac:(tac Heq IHe2)); try congruence.
  rewrites* Heq.
Qed.

Lemma low_assn_vars R P Env E :
  (forall e x v, In (e |-> v) Env -> In x (fv_E e) -> E x = Lo) ->
  low_assn E (Assn R P Env).
Proof.
  intros HEnv.
  unfold low_assn, Bdiv.low_assn, Bdiv.indeP; simpl.
  unfold low_eq.
  unfold Assn; split; intros Hsat; sep_split_in Hsat; sep_split; eauto;
  induction Env as [|[? ?] ?]; simpl in *; eauto; destruct HP0; split;
  unfold_conn_all; simpl in *; eauto;
  [rewrites (>>fv_edenot s1); [|eauto];
   intros; rewrites* H..].
Qed.

Lemma low_assn_ex {T : Type} G (P : T -> assn) :
  (forall x, low_assn G (P x)) ->
  low_assn G (Ex x, P x).
Proof.
  unfold low_assn, Bdiv.low_assn, Bdiv.indeP.
  intros Hl s1 s2 h Hlow; simpl.
  split; intros [x H]; exists x; simpl in *.
  rewrite Hl.
  exact H.
  apply Bdiv.low_eq_sym; eauto.
  rewrite Hl.
  exact H.
  eauto.
Qed.

Lemma low_assn_FalseP E : low_assn E FalseP.
Proof.
  intros s1 s2 h H; tauto.
Qed.
Ltac des H :=
  let t := type of H in idtac "H : " t;
  match type of H with
  | _ \/ _ =>
    let H' := fresh "H" in
    destruct H as [H | H']; [des H | des H']
  | (_ |-> _ = _ |-> _) => inverts H; substs
  | False => destruct H
  | _ => substs
  end.
Ltac prove_low_expr :=
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  simpl in *; 
  intros ? ? ? H1 H2;
  des H1; simpl in *; des H2; simpl; eauto.

Ltac prove_low_assn :=
  lazymatch goal with
  | [|- low_assn _ (Ex _ : _, _) ] =>
    apply low_assn_ex; intros ?; prove_low_assn
  | [|- low_assn _ (Assn _ _ _)] =>
    apply low_assn_vars; prove_low_expr
  | [|- low_assn _ FalseP] =>
    apply low_assn_FalseP
  end.

Lemma rule_block n BS E (Ps Qs : Vector.t assn n) (P : assn) c (Q : assn) ty:
  n <> 0 ->
  (forall i : nat,
      (forall tid : Fin.t n, low_assn E (Vector.nth (fst (BS i)) tid)) /\
      (forall tid : Fin.t n, low_assn E (Vector.nth (snd (BS i)) tid))) ->
  (forall (i : nat),
      Bdiv.Aistar_v (fst (BS i)) |= Bdiv.Aistar_v (snd (BS i))) ->
  (forall (i : nat) (tid : Fin.t n),
      precise (Vector.nth (fst (BS i)) tid) /\
      precise (Vector.nth (snd (BS i)) tid)) ->
  P |= Bdiv.Aistar_v Ps ->
  Bdiv.Aistar_v Qs |= Q ->
  (forall tid : Fin.t n, low_assn E (Vector.nth Ps tid)) ->
  (forall tid : Fin.t n, low_assn E (Vector.nth Qs tid)) ->
  typing_cmd E c ty ->
  (forall tid : Fin.t n,
      CSL BS tid (Vector.nth Ps tid ** !("tid" === Zn (nf tid))) c
          (Vector.nth Qs tid)) -> CSLp n E P c Q.
Proof.
  intros; eapply rule_par; eauto.
  destruct n; try omega; eauto.
  intros ? [? ?] ?; simpl in *; unfold sat in *; eauto.
Qed.

Lemma rule_conseq (n : nat)
  (bspec : nat -> Vector.t assn n * Vector.t assn n)
  (tid : Fin.t n) (P : assn) (C : cmd) (Q P' Q' : assn) :
  CSL bspec tid P C Q -> P' |= P -> Q |= Q' -> CSL bspec tid P' C Q'.
Proof.
  intros; eapply rule_conseq; eauto.
Qed.

Lemma assn_var_in Res P Env x (v : val) :
  (Assn Res P Env ** !(x === v)) == (Assn Res P (x |-> v :: Env)).
Proof.
  unfold Assn; split; simpl; intros H; sep_split_in H; sep_split; eauto.
  split; eauto.
  destruct HP0; eauto.
  destruct HP0; eauto.
Qed.

Definition istar ls := List.fold_right Star Emp ls.

Lemma conj_xs_assn st n Res P Env :
  n <> 0 ->
  conj_xs (ls_init st n (fun i => Assn (Res i) P Env)) ==
  Assn (istar (ls_init st n (fun i => Res i))) P Env.
Proof.
  unfold Assn, sat; intros Hn0 s h.
  split; intros.
  - repeat sep_rewrite_in @ls_star H.
    repeat sep_rewrite_in @ls_pure H; sep_split_in H.
    apply (ls_emp _ _ 0) in HP; rewrite ls_init_spec in HP.
    destruct lt_dec; try omega.
    apply (ls_emp _ _ 0) in HP0; rewrite ls_init_spec in HP0.
    destruct lt_dec; try omega.
    sep_split; eauto.
    Lemma conj_xs_istar s n f :
      res_denote (istar (ls_init s n f)) == conj_xs (ls_init s n (fun i => res_denote (f i))).
    Proof.
      revert s; induction n; simpl.
      - reflexivity.
      - intros; rewrite IHn; reflexivity.
    Qed.
    fold_sat; rewrite conj_xs_istar; apply H.
  - sep_split_in H.
    repeat sep_rewrite @ls_star.
    repeat sep_rewrite @ls_pure; sep_split.
    + apply ls_emp'; intros i; rewrite init_length, ls_init_spec; intros;
      destruct lt_dec; try omega; eauto.
    + apply ls_emp'; intros i; rewrite init_length, ls_init_spec; intros;
      destruct lt_dec; try omega; eauto.
    + fold_sat; rewrite <-conj_xs_istar; apply H.
Qed.

Lemma sc_v2l n (assns : Vector.t assn n) :
  Bdiv.Aistar_v assns == conj_xs (Vector.to_list assns).
Proof.
  simpl; introv; apply sc_v2l.
Qed.

Lemma emp_unit_l P: 
  (Emp *** P) == P.
Proof.
  intros s h; unfold sat_res; simpl.
  apply emp_unit_l.
Qed.

Lemma emp_unit_r P: 
  (P *** Emp) == P.
Proof.
  intros s h; unfold sat_res; simpl.
  apply emp_unit_r.
Qed.

Lemma init_emp_emp b n :
  istar (ls_init b n (fun _ => Emp)) == Emp.
Proof.
  revert b; induction n; simpl; [reflexivity|]; intros.
  rewrite IHn.
  rewrite emp_unit_l; reflexivity.
Qed.

Lemma ls_star b n P Q :
  istar (ls_init b n (fun i => P i *** Q i)) ==
  (istar (ls_init b n (fun i => P i)) *** istar (ls_init b n (fun i => Q i))).
Proof.
   revert b; induction n; simpl; eauto.
   - intros; rewrite emp_unit_l; reflexivity.
   - intros; rewrite IHn; rewrite <-!res_assoc.
     apply res_star_proper; [reflexivity|].
     rewrite res_CA; reflexivity.
Qed.

Lemma istar_app Ps Qs: 
  istar (Ps ++ Qs) == (istar Ps *** istar Qs).
Proof.
  induction Ps; simpl; eauto.
  rewrite emp_unit_l; reflexivity.
  rewrite IHPs, <-res_assoc; reflexivity.
Qed.  
                       
Lemma array'_ok n ptr dist vals s p :
  (forall i, s <= i < length vals + s -> dist i < n) ->
  istar (ls_init 0 n (fun i => array' ptr (ith_vals dist vals i s) p)) ==
  array ptr vals p.
Proof.
  revert s ptr; induction vals; intros; simpl.
  - intros s' h.
    rewrite init_emp_emp; reflexivity.
  - rewrite ls_star.
    rewrite IHvals.
    apply res_star_proper; try reflexivity.
    lazymatch goal with
    | [|- context [ls_init 0 n ?f]] =>
      cutrewrite (ls_init 0 n f =
                  (ls_init 0 (dist s) (fun _ => Emp) ++
                  (ptr |->p (p, a)) ::
                  ls_init ((dist s) + 1) (n - dist s - 1) (fun _ => Emp)))
    end.
    rewrite istar_app, init_emp_emp; simpl; rewrite init_emp_emp.
    rewrite emp_unit_l, emp_unit_r; reflexivity.
    specialize (H s).
    simpl in *.
    cutrewrite (n = (dist s) + 1 + (n - dist s - 1)); [|omega].
    repeat rewrite ls_init_app; simpl.
    rewrite <-app_assoc; simpl.
    f_equal; [apply ls_init_eq'|f_equal]; eauto.
    intros; simpl; destruct Nat.eq_dec; try omega; eauto.
    intros; simpl; destruct Nat.eq_dec; try omega; eauto.
    lazymatch goal with
    | [|- _ _ ?p _ = _ _ ?q _] =>
      cutrewrite (q = p); [|lia];
      apply ls_init_eq';
      intros; simpl; destruct Nat.eq_dec; try omega; eauto
    end.
    intros; apply H; simpl; omega.
Qed.

Lemma nseq_nth_same T i n (x : T) :
  nth i (nseq n x) x = x.
Proof.
  rewrite nth_nseq; destruct leb; auto.
Qed.

Lemma ex_assn_in_env (x : var) v Res P Env s h n :
  sat s h (conj_xs (ls_init 0 n (fun i => Assn (Res i) (P i) (Env i)))) ->
  (forall i, i < n -> evalExp (Env i) x (Zn (v i))) -> 
  exists c, forall i, i < n -> v i = c.
Proof.
  unfold sat, Assn; intros H Hin.
  repeat sep_rewrite_in @scan_lib.ls_star H;
  repeat sep_rewrite_in @ls_pure H; sep_split_in H.
  exists (Z.to_nat (s x)).
  intros i Hi.
  eapply (ls_emp _ _ i) in HP0; rewrite ls_init_spec in HP0.
  destruct lt_dec; try omega.
  simpl in HP0.
  forwards*: (>>evalExp_ok (Env i)).
  unfold_conn_in H0; simpl in *.
  rewrite H0, Nat2Z.id; auto.
Qed.

Ltac find_const fs H :=
  let find v :=
    match goal with _ => idtac end; 
    lazymatch type of H with
    | sat ?s ?h (conj_xs (ls_init 0 ?n (fun i => Assn (@?Res i) (@?P i) (@?Env i)))) =>
      idtac Res P Env;
        let x := fresh "x" in
        let Heq := fresh "Heq" in
        evar (x : var);
        forwards [? Heq]: (ex_assn_in_env x (fun i => nth i v 0) Res P Env s h n H);
        unfold x in *;
        [now (intros; evalExp) |
         repeat (erewrite ls_init_eq0 in H; [|intros; rewrite Heq; eauto; reflexivity])]
  end in
  let rec iter fs :=
      lazymatch fs with
      | (?x, ?y) =>
        find x;
        iter y
      | ?x => idtac 
      end in
  iter fs.

Ltac dest_ex_in acc H :=
  match goal with _ => idtac end;
  lazymatch type of H with
  | sat _ _ (conj_xs (ls_init 0 ?n (fun i => Ex t : ?T, @?P i t))) =>
    let d := default T in
    rewrite (ls_exists0 d) in H; destruct H as [t H];
    sep_split_in H; unfold_pures; fold_sat_in H; dest_ex_in (t, acc) H
  | sat _ _ (conj_xs (ls_init 0 ?n (fun i => Assn (@?Res i) (@?P i) (@?Env i)))) =>
    find_const acc H
  end.

Ltac dest_ex :=
  repeat (lazymatch goal with
  | [|- sat _ _ (conj_xs (ls_init 0 ?n (fun i => Ex x : ?T, @?P i x)))] =>
    let x := fresh "x" in
    evar (x : T);
    rewrite (ls_exists0 x);
    eexists (nseq n x); unfold x; sep_split;
    [rewrite length_nseq; reflexivity|]; fold_sat;
    erewrite @ls_init_eq0; [|intros; rewrite nseq_nth_same; reflexivity]
  end).

Ltac prove_istar_imp :=
  let s := fresh "s" in
  let h := fresh "h" in
  let H := fresh "H" in
  let simplify :=
      let i := fresh "i" in
      let Hi := fresh in
      let Hex := fresh in
      let Heq := fresh in
      intros i Hi;
        lazymatch goal with
          [|- match ?X with inleft _ => _ | inright _ => _ end = _] =>
          destruct X as [|Hex] eqn:Heq; [|destruct Hex; omega]
        end;
        rewrite (Fin_nat_inv Heq); reflexivity in
  intros s h H;
  match goal with _ => idtac end;
  try lazymatch type of H with
  | sat _ _ (Bdiv.Aistar_v (MyVector.init _))  =>
    rewrite sc_v2l, (vec_to_list_init0 _ emp) in H;
    erewrite ls_init_eq0 in H; [|simplify];
    dest_ex_in tt H;
    rewrite conj_xs_assn in H; auto
  end;
  try lazymatch goal with
  | [|- sat _ _ (Bdiv.Aistar_v (MyVector.init _)) ] =>
    rewrite sc_v2l, (vec_to_list_init0 _ emp);
    erewrite ls_init_eq0; [|simplify];
    dest_ex;
    rewrite conj_xs_assn; auto
  end;
  revert s h H; prove_imp.


Ltac ls_rewrite_in Heq H :=
  erewrite ls_init_eq0 in H; [|intros; rewrite Heq; reflexivity].

Lemma precise_false : precise (fun _ _ => False).
Proof.
  unfold precise; intros; tauto.
Qed.

Lemma precise_sat (P Q : assn) :
  (Q |= P) -> precise P -> precise Q.
Proof.
  unfold precise; simpl; intros Hsat HprecP; introv.
  intros HsatQ HsatQ' ? ? ?.
  eapply HprecP; eauto; apply Hsat; eauto.
Qed.

Definition precise_res P :=
  forall (h1 h2 h1' h2' : pheap) s,
    sat_res s h1 P ->
    sat_res s h2 P ->
    pdisj h1 h1' ->
    pdisj h2 h2' ->
    phplus h1 h1' = phplus h2 h2' -> h1 = h2. 

Lemma precise_assn Res P Env :
  precise_res Res
  -> precise (Assn Res P Env).
Proof.
  unfold Assn; intros.
  eapply precise_sat; unfold sat; intros s h Hsat; sep_split_in Hsat; eauto.
Qed.

Lemma precise_star (P Q : res) : precise_res P -> precise_res Q -> precise_res (P *** Q).
Proof.
  unfold_conn; intros pp pq h1 h2 h1' h2' s hsat hsat' hdis hdis' heq; simpl in *.
  destruct hsat as [ph1 [ph1' [satp1 [satq1 [Hdis1 Heq1]]]]], 
                   hsat' as [ph2 [ph2' [satp2 [satq2 [Hdis2 Heq2]]]]].
  destruct h1 as [h1 ?], h2 as [h2 ?]; apply pheap_eq; simpl in *; rewrite <-Heq1, <-Heq2 in *.
  apply pdisj_padd_expand in hdis; apply pdisj_padd_expand in hdis'; eauto.
  rewrite !padd_assoc in heq; try tauto. 
  f_equal; destruct hdis as [hdis1 hdis2], hdis' as [hdis1' hdis2'].
  - rewrite (pp ph1 ph2 (phplus_pheap hdis2) (phplus_pheap hdis2') s); eauto.
  - rewrite padd_left_comm in heq at 1; try tauto.
    rewrite (@padd_left_comm _ ph2 ph2' h2') in heq; try tauto.
    pose proof (pdisjE2 hdis1 hdis2) as dis12; pose proof (pdisjE2 hdis1' hdis2') as dis12'.
    rewrite (pq ph1' ph2' (phplus_pheap dis12) (phplus_pheap dis12') s); simpl in *; eauto; 
    apply pdisj_padd_comm; eauto.
Qed.

Lemma precise_mps l v p :
  precise_res (l |->p (p, v)).
Proof.
  unfold precise_res, precise; intros; simpl in *.
  unfold sat_res in *; simpl in *; unfold_conn_all; simpl in *.
  destruct h1 as [h1 ?], h2 as [h2 ?]; apply pheap_eq.
  extensionality x; simpl in *; rewrite H, H0; auto.
Qed.

Lemma precise_emp :
  precise_res Emp.
Proof.
  unfold precise_res, sat_res, sat; simpl.
  intros; applys precise_emp; simpl; eauto.
Qed.

Hint Resolve precise_star precise_mps precise_emp precise_false precise_assn.

Lemma precise_array l vs p: 
  precise_res (array l vs p).
Proof.
  revert l; induction vs; simpl; eauto.
Qed.

Lemma precise_array' l vs q :
  precise_res (array' l vs q).
Proof.
  revert l; induction vs as [|[?|] ?]; simpl; eauto.
Qed.              

Hint Resolve precise_star precise_array precise_array'.

Lemma ty_var' g v ty :
  g v = ty -> typing_exp g v ty.
Proof.
  intros; constructor; rewrite H; destruct ty; eauto.
Qed.
Ltac prove_typing_exp :=
  lazymatch goal with
  | |- typing_exp ?E (Evar ?v) _ => apply ty_var'; simpl; eauto
  | |- typing_exp ?E (Enum _) _ => apply (ty_num _ _ Lo)
  | |- typing_exp ?E (_ ?e1 ?e2) _ => constructor; prove_typing_exp
  | |- typing_exp ?E (_ ?e) _ => constructor; prove_typing_exp
  end.
Ltac prove_typing_lexp :=
  match goal with |- ?g => idtac g end;
  lazymatch goal with
  | |- typing_lexp _ (Sh ?e) _ =>
    idtac "A";
    constructor; prove_typing_exp
  | |- typing_lexp _ (Gl ?e) _ =>
    idtac "A";
    constructor; prove_typing_exp
  | |- typing_lexp _ (_ +o _) _ =>
    idtac "B";
    constructor; [prove_typing_lexp | prove_typing_exp]; simpl
  end.
Ltac prove_typing_bexp :=
  match goal with |- ?g => idtac g end;
  lazymatch goal with
  | |- typing_bexp _ (Beq _ _) _ =>
    constructor; prove_typing_exp; simpl
  | |- typing_bexp _ (_ <C _) _ =>
    constructor; prove_typing_exp; simpl
  | |- typing_bexp _ (Bnot _) _ =>
    idtac "A";
    constructor; prove_typing_bexp
  | |- typing_lexp _ (Band _ _) _ =>
    idtac "B";
    constructor; [prove_typing_bexp | prove_typing_bexp]; simpl
  end.

Lemma le_type_hi ty : 
  le_type ty Hi = true.
Proof.
  destruct ty; auto.
Qed.

Ltac prove_le_type :=
  eauto;
  lazymatch goal with
  | [|- le_type Lo _ = true] => eauto
  | [|- le_type _ Hi = true] => apply le_type_hi
  | _ => idtac
  end.

Ltac prove_typing_cmd :=
  lazymatch goal with
  | [|- typing_cmd _ (_ ::T _ ::= [_]) _] =>
    eapply ty_read; simpl; [prove_typing_lexp | prove_le_type]
  | [|- typing_cmd _ (_ ::T _ ::= _) _] =>
    eapply ty_assign; simpl; [prove_typing_exp | prove_le_type]
  | [|- typing_cmd _ ([_] ::= _) _] => constructor
  | [|- typing_cmd _ (_ ;; _) _] => constructor
  | [|- typing_cmd _ (BARRIER (_) ) _] => constructor
  | [|- typing_cmd _ (Cwhile _ _) _ ] => econstructor; [prove_typing_bexp| ]
  | [|- typing_cmd _ (WhileI _ _ _) _ ] => econstructor; [prove_typing_bexp| ]
  | [|- typing_cmd _ (Cif _ _ _) _ ] => econstructor; [prove_typing_bexp|..]
  | [|- typing_cmd _ Cskip _ ] => constructor
  | _ => idtac
  end.

Lemma precise_ex T (P : T -> assn) :
  (forall x, precise (P x)) ->
  (forall x1 x2 s h1 h2, sat s h1 (P x1) -> sat s h2 (P x2) -> x1 = x2) ->
  precise (Ex x, (P x)).
Proof.
  unfold precise; simpl; intros Hprec Heqx; introv [x Hsat] [x' Hsat'] Hdisj Hdisj' Heqh.
  rewrites (Heqx x x' s h1 h1') in Hsat; auto.
  eapply Hprec; eauto.
Qed.

Lemma eval_to_Zn_unique s h Res P Env (x : exp) v :
  sat s h (Assn Res P Env) -> 
  evalExp Env x (Zn v) -> 
  v = Z.to_nat (edenot x s).
Proof.
  intros.
  unfold Assn, sat in *; sep_split_in H.
  forwards*: (>>evalExp_ok); unfold_pures.
  rewrite H1, Nat2Z.id; auto.
Qed.

Ltac prove_uniq := match goal with
| [H : context [?x |-> Zn ?v1], H' : context [?y |-> Zn ?v2] |- ?v1 = ?v2] =>
  forwards*: (>>eval_to_Zn_unique x v1 H); [evalExp|];
  forwards*: (>>eval_to_Zn_unique y v2 H'); [evalExp|];
  congruence
end.

Ltac prove_precise :=
  match goal with
  | [|- precise (Ex _, _)] =>
    apply precise_ex; [intros; eauto| intros; prove_uniq]
  | [|- _] => eauto
  end.

Lemma reduce_ok_b :
  CSLp ntrd E
       jth_pre
       (reduce TrueP)
       jth_post.
Proof.
  applys (>>rule_block BS E (MyVector.init ith_pre) (MyVector.init ith_post)).
    unfold BS, ith_pre, ith_post; eauto.
  - unfold E; intros [|[|i]]; simpl; split; intros; rewrite MyVector.init_spec; simpl;
    try prove_low_assn.
  - intros [|[|i]]; eauto; simpl.
    prove_istar_imp.
    rewrite array'_ok in H |- *; eauto; rewrite reg_b_length; intros; try omega.
    unfold dist; repeat destruct lt_dec; try omega.
    prove_istar_imp.
    rewrite array'_ok in H |- *; eauto; intros; try omega;
    rewrite st_inv2, reg_b_length in H1;
    unfold dist; repeat destruct lt_dec; try omega.
  - unfold BS; intros [|[|i]] ?; simpl; rewrite !MyVector.init_spec; split; prove_precise.
  - unfold jth_pre, ith_pre.
    prove_istar_imp.
    repeat rewrite ls_star.
    rewrite array'_ok; [|intros; lia]; auto.
  - unfold jth_post, ith_post.
    prove_istar_imp.
    repeat rewrite ls_star in H.
    rewrite array'_ok in H; eauto.
    intros i; rewrite st_inv2, reg_b_length; intros ?; unfold dist;
    repeat destruct lt_dec; lia.
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