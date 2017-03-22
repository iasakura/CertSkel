Require Import TypedTerm SkelLib GPUCSL LibTactics Psatz SetoidClass CodeGen Correctness CUDALib Grid CSLLemma Host.
Import String List Program DepList.

Lemma ex_lift_r T P Q :
  ((Ex x : T, P x) ** Q) == (Ex x : T, P x ** Q).
Proof.
  intros s h; split; intros H.
  - destruct H as (? & ? & ? & ? & ? & ?).
    destruct H as (? & ?).
    do 3 eexists; repeat split; eauto.
  - destruct H as (? & ? & ? & ? & ? & ? & ?).
    do 2 eexists; repeat split; eauto.
    eexists; eauto.
Qed.

Lemma cond_prop_in Res P P' Env cond b :
  evalBExp Env cond P' ->
  (Assn Res P Env ** (BEval_assn cond b)) ==
  (Assn Res (P /\ if b then P' else ~P') Env).
Proof.
  intros Heval s h; split; intros Hsat.
  - unfold sat in *; simpl in *; splits; destruct Hsat as (? & ? & ? & ? & ? & ?); jauto.
    + cutrewrite (h = x); jauto.
      cutrewrite (x0 = emp_ph loc) in H2; [rewrite phplus_emp2 in H2; destruct h, x; apply pheap_eq; simpl in *; congruence |].
      applys* emp_is_emp.
    + splits; jauto.
      forwards*: (>>evalBExp_ok Heval).
      destruct b; try tauto.
      rewrite <-H3; destruct bdenot; destruct H0; congruence.
  - unfold sat in *; simpl in *.
    exists h (emp_ph loc); splits; jauto.
    forwards*: evalBExp_ok.
    destruct b.
    + rewrite H; jauto.
    + rewrite <-H in Hsat.
      destruct Hsat as (? & (? & ?) & ?).
      splits; jauto.
      destruct bdenot; congruence.
    + apply disj_emp1.
    + apply phplus_emp2.
Qed.

Lemma cond_prop ntrd BS (tid : Fin.t ntrd) Res P P' Env C Q cond (b : bool) :
  evalBExp Env cond  P' ->
  CSL BS tid (Assn Res (P /\ if b then P' else ~P') Env) C Q ->
  CSL BS tid (Assn Res P Env ** (BEval_assn cond b)) C Q.
Proof.
  intros Heval Hc; eapply backward; [|apply Hc].
  intros s h H; rewrite cond_prop_in in H; eauto.
Qed.

Ltac lift_ex :=
  let H := fresh in
  lazymatch goal with
  | [|- CSL _ _ ((Ex j, @?P j) ** _) _ _] =>
    let j := fresh j in
    eapply backward; [intros ? ? H; rewrite ex_lift_r in H; exact H|];
    apply rule_ex; intros j
  end.

Ltac evalExp' := 
  repeat match goal with
  | [|- evalExp _ _ _] => constructor
  end;
  simpl; repeat rewrite in_app_iff; simpl; repeat rewrite <-app_assoc; eauto 20.

Ltac evalExp :=
  let t := fresh "tmp" in
  evar (t : val);
    lazymatch goal with
    | [|- evalExp _ _ ?x] => cutrewrite (x = t); [unfold t; evalExp'|unfold t; simpl; eauto]
    end.

Ltac evalBExp' := 
  repeat match goal with
         | [|- evalBExp _ _ _] => constructor
         | [|- _] => evalExp'
  end;
  simpl; eauto 20.

Ltac evalBExp :=
  let t := fresh "tmp" in
  evar (t : Prop);
    lazymatch goal with
    | [|- evalBExp _ _ ?x] => cutrewrite (x = t); [unfold t; evalBExp'|unfold t; simpl; eauto]
    end.

Ltac evalLExp' := 
  repeat match goal with
         | [|- evalLExp _ _ _] => constructor
         | [|- _] => evalExp'
  end;
  simpl; eauto 20.

Ltac evalLExp :=
  let t := fresh "tmp" in
  evar (t : loc);
    lazymatch goal with
    | [|- evalLExp _ _ ?x] => cutrewrite (x = t); [unfold t; evalLExp'|unfold t; simpl; eauto]
    end.

Ltac elim_remove env x := simpl.

Ltac simpl_env := 
  lazymatch goal with
  | [|- context [remove_var ?env ?x]] => elim_remove env x
  | _ => idtac
  end.

Create HintDb pure_lemma.

Ltac prove_mod_eq :=
  match goal with
  | [|- ?x mod ?n = ?m] =>
    let rec iter t :=
      match t with
      | ?t + ?u =>
        (* t = t + t' * n *)
        match iter t with (?t, ?t') =>
        match iter u with (?u, ?u') =>
        constr:(t + u, t' + u') end end
      | ?t * n => constr:(0, t)
      | n * ?t => constr:(0, t)
      | _ => constr:(t, 0)
      end in
    match iter x with
    | (?t, ?u) => cutrewrite (x = t + u * n);
      [rewrite Nat.mod_add; [|eauto with pure_lemma] | ring];
      apply Nat.mod_small; first [now eauto with pure_lemma | nia]
    end
  end.

Create HintDb pure.

Lemma firstn_length T i (arr : list T) :
  length (firstn i arr) = if lt_dec i (length arr) then i else length arr.
Proof.
  revert arr; induction i; intros [|? ?]; destruct lt_dec; simpl in *; try omega;
  rewrite IHi; destruct lt_dec; simpl in *; try omega.
Qed.

Lemma skipn_length T i (arr : list T) :
  length (skipn i arr) = length arr - i.
Proof.
  revert arr; induction i; intros [|? ?]; simpl in *; try omega.
  rewrite IHi; simpl in *; try omega.
Qed.

Lemma firstn_app (A : Type) n (xs ys : list A) :
  firstn n (xs ++ ys) = firstn n xs ++ firstn (n - length xs) ys.
Proof.
  revert xs ys; induction n; intros [|x xs] [|y ys]; simpl; eauto;
  rewrite IHn; eauto.
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

Fixpoint zipWith {A B C : Type} (f : A -> B -> C) xs ys :=
  match xs, ys with
  | x :: xs, y :: ys => f x y :: zipWith f xs ys
  | _, _ => nil
  end.

Lemma firstn_zipWith (A B C : Type) (f : A -> B -> C) xs ys n :
  firstn n (zipWith f xs ys) = zipWith f (firstn n xs) (firstn n ys).
Proof.
  revert xs ys; induction n; intros [|x xs] [|y ys]; simpl; eauto.
  rewrite IHn; eauto.
Qed.

Lemma firstn_length_self (A : Type) (xs : list A) :
  firstn (length xs) xs = xs.
Proof.  
  induction xs; simpl; eauto; rewrite IHxs; eauto.
Qed.


Lemma nth_app (T : Type) i ls1 ls2 (v : T) :
  nth i (ls1 ++ ls2) v = if lt_dec i (length ls1) then nth i ls1 v else nth (i - length ls1) ls2 v.
Proof.
  revert i; induction ls1; simpl; eauto.
  intros [|i]; simpl; eauto.
  intros [|i]; simpl; eauto.
  rewrite IHls1; repeat match goal with
                | [|- context [if ?b then _ else _]] => destruct b
                end; try omega; eauto.
Qed.

Lemma nth_firstn (T : Type) n i ls1 (v : T) :
  nth i (firstn n ls1) v = if lt_dec i n then nth i ls1 v else v.
Proof.
  revert i n; induction ls1; simpl; eauto.
  - intros [|i] [|n]; simpl; eauto.
    destruct lt_dec; eauto.
  - intros [|i] [|n]; simpl; eauto.
    rewrite IHls1; repeat destruct lt_dec; try omega; eauto.
Qed.

Lemma nth_skipn (T : Type) n i ls1 (v : T) :
  nth i (skipn n ls1) v = nth (n + i) ls1 v.
Proof.
  revert i n; induction ls1; eauto.
  - intros [|i] [|n]; simpl; eauto.
  - intros i [|n]; eauto; simpl.
    eauto.
Qed.        

Lemma set_nth_app (T : Type) i xs ys (v : T) :
  set_nth i (xs ++ ys) v =
  if lt_dec i (length xs) then set_nth i xs v ++ ys
  else xs ++ set_nth (i - length xs) ys v.
Proof.
  revert i; induction xs; simpl; eauto.
  intros [|i]; simpl; eauto.
  intros [|i]; simpl; eauto.
  rewrite IHxs; repeat match goal with
                | [|- context [if ?b then _ else _]] => destruct b
                end; try omega; eauto.
Qed.

Lemma zipWith_length (A B C : Type) (f : A -> B -> C) xs ys :
  length (zipWith f xs ys) = if lt_dec (length xs) (length ys) then length xs else length ys.
Proof.
  revert ys; induction xs; intros [|? ?]; simpl; eauto.
  destruct lt_dec; rewrite IHxs; destruct lt_dec; omega.
Qed.

Lemma nth_zipWith (A B C : Type) (f : A -> B -> C) xs ys d i d1 d2:
  nth i (zipWith f xs ys) d =
  if Sumbool.sumbool_and _ _ _ _ (lt_dec i (length xs)) (lt_dec i (length ys)) then
    f (nth i xs d1) (nth i ys d2) else d.
Proof.
  revert i ys; induction xs; intros [|i] [|? ?]; destruct Sumbool.sumbool_and; simpl in *; eauto; try lia;
  rewrite IHxs; do 2 destruct lt_dec; simpl; eauto; omega.
Qed.

Lemma nth_skip_Z i arr dist j s :
  nth i (ith_vals dist arr j s) None =
  (if Nat.eq_dec (dist (s + i)) j
   then if lt_dec i (Datatypes.length arr) then Some (nth i arr 0%Z) else None
   else None).
Proof.
  apply nth_skip.
Qed.

Lemma nth_skip_ls ty i (arr : list (vals ty)) dist j s :
  nth i (ith_vals dist arr j s) None =
  (if Nat.eq_dec (dist (s + i)) j
   then if lt_dec i (Datatypes.length arr) then Some (nth i arr defval) else None
   else None).
Proof.
  apply nth_skip.
Qed.

Hint Rewrite length_set_nth ith_vals_length app_length zipWith_length : pure.
Hint Rewrite nth_app nth_skip_Z nth_skip_ls nth_set_nth nth_firstn nth_skipn : pure.

Lemma ls_init_spec {T : Type} (n : nat) (fc : nat -> T) d: forall i,
  forall b, nth i (ls_init b n fc) d = if lt_dec i n then fc (b + i) else d.
Proof.
  induction n; simpl; intros [|i] b; auto.
  destruct (lt_dec 0 (S n)); f_equal; try omega.
  rewrite IHn; destruct (lt_dec i n), (lt_dec (S i) (S n)); try omega; auto.
  f_equal; omega.
Qed.

Hint Rewrite
     app_length
     firstn_length
     skipn_length
     firstn_app
     firstn_firstn
     skipn_skipn
     firstn_zipWith
     firstn_length_self
     @init_length
     @ls_init_spec : pure.

Ltac prove_pure :=
  intros; 
  repeat match goal with
  | [H : _ /\ _ |- _] => destruct H as [H ?]
  end; substs; repeat split;
  repeat match goal with
  | [H : context [Assn _ _ _]|- _] => clear H
  | [H : context [kernelInv _ _ _ _ _ _ _]|- _] => clear H
  | [H : evalExp _ _ _ |- _] => clear H
  | [H : evalLExp _ _ _ |- _] => clear H
  | [H : _ |=R _ |- _] => clear H
  end;
  repeat autorewrite with pure in *;
  try now
      repeat (match goal with
       | [|- context [if ?b then _ else _]] => destruct b
       | [H : context [if ?b then _ else _] |- _] => destruct b
       | [|- context [match ?b with _ => _ end]] => destruct b
       | [H : context [if ?b then _ else _] |- _] => destruct b
       end);
  first [prove_mod_eq |now (eauto with pure_lemma) | lia].

Ltac is_const v :=
  match v with
  | Z0 => constr:true
  | Zpos ?v => is_const v
  | Zneg ?v => is_const v
  | xI ?v => is_const v
  | xO ?v => is_const v
  | xH => constr:true
  end.

Ltac simpl_to_zn v :=
  match v with
  | (?v1 + ?v2)%Z =>
    let v1 := simpl_to_zn v1 in
    let v2 := simpl_to_zn v2 in
    constr:(v1 + v2)
  | (?v1 * ?v2)%Z =>
    let v1 := simpl_to_zn v1 in
    let v2 := simpl_to_zn v2 in
    constr:(v1 * v2)
  | (Z.div2 ?v1)%Z =>
    let v1 := simpl_to_zn v1 in
    constr:(v1 / 2)
  | (?v1 / ?v2)%Z =>
    let v1 := simpl_to_zn v1 in
    let v2 := simpl_to_zn v2 in
    constr:(v1 / v2)
  | Zn ?v => v
  | ?v =>
    match is_const v with
    | true => let t := eval compute in (Z.to_nat v) in t
    end
  end.

Create HintDb zn.
Hint Rewrite
     Zdiv2_div
     div_Zdiv
     Nat2Z.inj_0 
     Nat2Z.inj_succ 
     Nat2Z.is_nonneg 
     Nat2Z.id 
     Nat2Z.inj 
     Nat2Z.inj_iff 
     Nat2Z.inj_compare 
     Nat2Z.inj_le 
     Nat2Z.inj_lt 
     Nat2Z.inj_ge 
     Nat2Z.inj_gt 
     Nat2Z.inj_abs_nat 
     Nat2Z.inj_add 
     Nat2Z.inj_mul 
     Nat2Z.inj_sub_max 
     Nat2Z.inj_sub 
     Nat2Z.inj_pred_max 
     Nat2Z.inj_pred 
     Nat2Z.inj_min 
     Nat2Z.inj_max : zn.

Ltac solve_zn :=
  match goal with
  | |- ?v = Zn ?rhs =>
    let v' := simpl_to_zn v in
    cutrewrite (v = Zn v'); [|autorewrite with zn]; eauto
  end.

Lemma scC2 P Q R :
  Q |=R R -> (P *** Q) |=R (P *** R).
Proof.
  unfold sat_res; simpl; intros ? ? (? & ? & ? & ? & ? & ?); do 2 eexists; splits; jauto.
Qed.
  
Ltac same_res P Q := unify P Q.

Ltac append_assn P Q :=
  match P with
  | Emp => Q
  | (?P1 *** ?P2) => 
    let t := append_assn P2 Q in
    constr:(P1 *** t)
  | _ => constr:(P *** Q)
  end.

Ltac remove_last_emp P :=
  match P with
  | (?P1 *** Emp) => P1
  | (?P1 *** ?P2) => 
    let t := remove_last_emp P2 in
    constr:(P1 *** t)
  | Emp => Emp
  end.

Lemma mps_eq (l : loc) (v v' : val) p : 
  v = v' ->
  (l |->p (p, v)) == (l |->p (p, v')).
Proof.
  intros->; reflexivity.
Qed.

Lemma array_eq l vs vs' p :
  vs = vs' ->
  array l vs p == array l vs' p.
Proof.
  intros ->; reflexivity.
Qed.

Lemma res_mono P Q R1 R2 :
  P |=R Q ->
  R1 |=R R2 ->
  (P *** R1) |=R (Q *** R2).
Proof.
  unfold sat_res; simpl; intros ? ? ? (? & ? & ? & ? & ? & ?); do 2 eexists; splits; jauto.
Qed.

Lemma array'_eq ls ls' ptr p: 
  ls = ls' -> array' ptr ls p |=R array' ptr ls' p.
Proof.
  intros; substs; eauto.
Qed.

Lemma arrays_eq ty (ls : list (vals ty)) ls' ptr p: 
  ls = ls' -> arrays ptr ls p |=R arrays ptr ls' p.
Proof.
  intros ->; eauto.
Qed.

Lemma arrays'_eq ty (ls : list (option (vals ty))) ls' ptr p: 
  ls = ls' -> arrays' ptr ls p |=R arrays' ptr ls' p.
Proof.
  intros ->; eauto.
Qed.

Ltac matches P Q :=
  match constr:(P, Q) with
  | (?P, ?P) => constr:(Some true)
  | ((?l |->p (_, _)), (?l |->p (_, _))) => constr:(Some mps_eq)
  | ((array ?l _ _), (array ?l _ _)) => constr:(Some array_eq)
  | ((array' ?l _ _), (array' ?l _ _)) => constr:(Some array'_eq)
  | ((arrays ?l _ _), (arrays ?l _ _)) => constr:(Some arrays_eq)
  | ((arrays' ?l _ _), (arrays' ?l _ _)) => constr:(Some arrays'_eq)
  | _ => constr:false
  end.

Ltac find_idx P Q :=
  lazymatch Q with
  | ?Q1 *** ?Q2 =>
    lazymatch matches P Q1 with
    | Some _ => constr:0 
    | false => let idx' := find_idx P Q2 in constr:(S idx') end
  | ?Q1 =>
    lazymatch matches P Q1 with
    | Some _ => constr:0
    end
  end.

Ltac lift_in idx H :=
  lazymatch idx with
  | 0 => idtac
  | S ?idx =>
    lazymatch type of H with
    | sat_res _ (?P *** ?Q) =>
      eapply res_mono in H; [| clear H; intros ? H; apply H |
                             clear H; intros ? H; lift_in idx H; apply H];
      first [rewrite res_CA in H | rewrite res_comm in H]
    end
  end.

Goal forall h P Q R S T U, sat_res h (P *** Q *** R *** S *** T *** U) -> False.
Proof.
  intros.
  Time lift_in 4 H.
  Time lift_in 5 H.
Abort.

Ltac prove_prim :=
  lazymatch goal with
  | [|- ?P |=R ?Q] => 
    lazymatch matches P Q with
    | Some true => let H := fresh "H" in intros ? H; apply H
    | Some ?lem => apply lem; eauto
    end
  end.

Lemma emp_unit_r_res R :
  (R *** Emp) == R.
Proof.
  apply res_emp_r_unit.
Qed.

Lemma emp_unit_l_res R :
  (Emp *** R) == R.
Proof.
  apply res_emp_l_unit.
Qed.

Create HintDb sep_eq.
Hint Rewrite emp_unit_l_res emp_unit_r_res res_assoc : sep_eq.

Ltac sep_cancel' :=
  lazymatch goal with
  | [H : sat_res ?h (?P1 *** ?P2) |- sat_res ?h (?Q1 *** ?Q2) ] =>
    idtac "sep_cancel': match star case";
    let idx := find_idx Q1 (P1 *** P2) in
    lift_in idx H; revert h H; apply res_mono; [
      prove_prim
    |intros h H]
  | [H : sat_res ?h (?P1 *** ?P2) |- sat_res ?h ?Q ] =>
    idtac "sep_cancel': match goal is atom case";
    rewrite <-emp_unit_r_res; sep_cancel'
  | [H : sat_res ?h ?P |- sat_res ?h (?Q1 *** ?Q2) ] =>
    idtac "sep_cancel': match hypo is atom case ";
    rewrite <-emp_unit_r_res in H; sep_cancel'
  | [H : sat_res ?h ?P |- sat_res ?h ?Q ] =>
    idtac "sep_cancel': match both is atom case ";
    revert h H; prove_prim
  end.

Goal forall (l1 l2 l3 : loc) v1 vs2 vs3 vs4, 
  ((l1 |->p (1, v1)) *** (array l2 vs2 1) *** (array' l3 vs3 1)) |=R
  ((array' l3 vs4 1) *** (l1 |->p (1, v1)) *** (array l2 vs2 1)).
Proof.
  intros.
  let t := matches (array' l3 vs4 1) (array' l1 vs3 1) in pose t.
  let idx := find_idx (array' l3 vs4 1) ((l1 |->p (1, v1)) *** (array l2 vs2 1) *** (array' l3 vs3 1)) in pose idx.
  sep_cancel'.
  admit.
  sep_cancel'.
  sep_cancel'.
Abort.

Ltac sep_auto' := 
  intros ? ?;
  repeat autorewrite with sep_eq in *;
  repeat sep_cancel'.

(*
  prove P |= Q ** ?R
  where 
    Q contains evars (index, contents)
    R is an evar.
*)
Ltac find_res' acc :=
  let H := fresh "H" in
  let H' := fresh "H'" in
  let s := fresh "s" in
  let h := fresh "h" in
  match goal with
  | [|- ?P |=R ?Q *** ?R] =>
    idtac "find_res': P = " P;
    idtac "find_res': P = " Q;
    is_evar R; intros h H;
    match P with
    | ?P1 *** ?P2 =>
      idtac "find_res': match sep conj case";
      same_res P1 Q;
      let P' := append_assn acc P2 in
      assert (H' : sat_res h (P1 *** P')) by (unfold sat in *; sep_cancel');
      clear H; revert H'; apply scC2; eauto
    | _ =>
      idtac "find_res': match atom case";
      same_res P Q;
      idtac "succeed to unify";
      assert (H' : sat_res h (P ** Emp));
      [  rewrite res_emp_r_unit; apply H | apply H']
    | _ => 
      find_res' (P ** acc)
    end
  end.

Ltac find_res := find_res' Emp.

(* Ltac sep_auto :=  *)
(*   intros ? ? ?; *)
(*   repeat autorewrite with sep_eq in *; *)
(*   unfold sat in *;  *)
(*   repeat sep_cancel. *)

Ltac lift_ex_in H :=
  repeat match type of H with
         | sat _ _ ((Ex i, @?f i) ** ?P) =>
           let i := fresh i in
           rewrite ex_lift_r in H; destruct H as (i & H); fold_sat_in H
         end.

Ltac des_disj H :=
  repeat match type of H with
  | _ \/ _ => 
    destruct H as [H | H]; 
      des_disj H; des_disj H
  end.

Ltac des_conj H :=
  repeat match type of H with
  | _ /\ _ => 
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    destruct H as [H1 H2]; 
      des_conj H1; des_conj H2
  end.

Ltac choose_var_vals :=
  let H := fresh in
  let e := fresh in
  unfold incl; simpl; intros e H;
  repeat (rewrite in_app_iff in *; simpl); des_disj H; substs; simpl; eauto 20;
  let rec tac :=
      match goal with
      | [H : In ?e (?xs |=> ?vs) |- context [?xs |=> ?vs']] => 
        cutrewrite (vs' = vs); eauto 20
      | [|- ?x |-> ?v = ?x |-> ?v' \/ ?H] =>
        left; cutrewrite (v = v'); eauto;
        solve_zn
      | [|- _ \/ ?H] => right; tac
      end in try tac.

Ltac prove_imp :=
  let s := fresh "s" in
  let h := fresh "h" in
  let H := fresh "H" in
  intros s h H; 
    try match type of H with
        | sat _ _ (_ ** _) =>
          lift_ex_in H;
            rewrites cond_prop_in in H; [|evalBExp]
        | sat _ _ (Disj_assn _ _) =>
          destruct H as [H|H]; revert s h H; prove_imp
        end;
    repeat
      match goal with
      | [|- sat _ _ (Ex _, _)] => eexists; fold_sat
      | [|- sat _ _ ((Ex _, _) ** _)] => rewrite ex_lift_r
      | [|- sat _ _ (Assn _ _ _ ** Assn _ _ _)] => rewrite Assn_combine
      end;
    repeat autorewrite with sep_eq in *;
    [ applys (>>Assn_imply s h H);
      [ (* proof impl. on environment *)
        intros ?; choose_var_vals |
        (* proof impl. on resource assertion *)
        intros Hp; des_conj Hp; sep_auto' |
        (* proof impl. on pure assertion *)
        let H' := fresh "H" in
        intros H'; des_conj H'; repeat split; substs; try prove_pure]..].

(*
  find an R in Res that contains le in its arguments, 
  and prove resource and bound check condution, then apply appropriate rule
 *)
Ltac apply_read_rule Hle Hv Hn P Res le i :=
  let checkR Res' R :=
    idtac "checkR: Res', R, le = " Res' "," R ", " le;
    let Hres := fresh "Hres" in
    let Hbnd := fresh "Hbnd" in
    match R with
    | array le ?arr _ =>
      idtac "apply read rule: match array case.";
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr); [prove_pure|
      applys (>> rule_read_array Hle Hv Hres Hn Hbnd); eauto with pure_lemma]]
    | array' le (ith_vals ?dist ?arr ?j ?s_) _ =>
      idtac "apply read rule: match sarray case.";
      idtac dist i;
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr /\ dist (s_ + i) = j); [simpl; prove_pure|
      applys (>> rule_read_array' Hle Hv Hres Hn Hbnd); eauto with pure_lemma]]
    end in
  let rec iter acc Res :=
    match Res with
    | ?R *** ?Res =>
      first [let Res' := append_assn acc Res in checkR Res' R |
             iter (R *** acc) Res]
    | ?R => checkR acc R
    end in
  iter Emp Res.

(*
  find an R in Res that contains le in its arguments, 
  and prove resource and bound check condution, then apply appropriate rule
 *)
Ltac apply_write_rule Hle Hix He Hn P Res le i :=
  let checkR Res' R :=
    idtac "checkR: Res', R, le = " Res' "," R ", " le;
    let Hres := fresh "Hres" in
    let Hbnd := fresh "Hbnd" in
    lazymatch R with
    | array le ?arr _ =>
      idtac "apply read rule: match array case.";
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr); [prove_pure|
      applys (>> rule_write_array Hle Hix Hn Hbnd He Hres); eauto with pure_lemma]]
    | array' le (ith_vals ?dist ?arr ?j ?s_) _ =>
      idtac "apply read rule: match sarray case.";
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr /\ dist (s_ + i) = j); [prove_pure|
      applys (>> rule_write_array' Hle Hix Hres He Hn Hbnd); eauto with pure_lemma]]
    end in
  let rec iter acc Res :=
    lazymatch Res with
    | ?R *** ?Res =>
      first [let Res' := append_assn acc Res in 
             idtac "append_assn: P, Q = " acc Res;
               checkR Res' R |
             iter (R *** acc) Res]
    | ?R => let Res' := remove_last_emp acc in checkR Res' R
    end in
  iter Emp Res.

Lemma rule_barrier n bs (i : Fin.t n) b A_pre Res_F A_post Res P Env:
  (Vector.nth (fst (bs b)) i) = A_pre ->
  (Vector.nth (snd (bs b)) i) = A_post ->
  Assn Res P Env |= A_pre ** Assn Res_F P Env ->
  CSL bs i (Assn Res P Env) (Cbarrier b) (A_post ** Assn Res_F P Env).
Proof.
  intros Hpre Hpost Himp.
  eapply backward.
  { intros ? ? H; apply Himp in H; eauto. }
  eapply forward.
  { intros ? ? H; rewrite sep_comm; eauto. }
  eapply forward; [intros s h H; rewrite sep_comm; apply H|].
  apply rule_frame; try rewrite <-Hpre, <-Hpost; eauto using rule_barrier0.
  simpl; intros ? ? ? ?; simpl; destruct 1.
Qed.

Lemma evalExp_app1 E1 E2 e v:
  evalExp E1 e v
  -> evalExp (E1 ++ E2) e v.
Proof.
  induction 1; simpl; constructor; eauto.
  rewrites* in_app_iff.
Qed.

Lemma evalBExp_app1 E1 E2 be v :
  evalBExp E1 be v
  -> evalBExp (E1 ++ E2) be v.
Proof.
  induction 1; constructor; eauto; apply evalExp_app1; eauto.
Qed.

Definition kernelDisj {GA} (avenv : AVarEnv GA) apenv aeenv R1 P1 E1 R2 P2 E2 p :=
  kernelInv avenv apenv aeenv R1 P1 E1 p \\//
  kernelInv avenv apenv aeenv R2 P2 E2 p.

Lemma rule_if_disj_kinv GA n (avenv : AVarEnv GA)
      apenv aeenv BS (tid : Fin.t n) R R1 R2 P P1 P2 E E1 E2 p cond b C1 C2:

  evalBExp E b cond

  -> CSL BS tid
         (kernelInv avenv apenv aeenv R (P /\ cond) E p)
         C1 
         (kernelInv avenv apenv aeenv R1 P1 E1 p)
  
  -> CSL BS tid
         (kernelInv avenv apenv aeenv R (P /\ ~ cond) E p)
         C2
         (kernelInv avenv apenv aeenv R2 P2 E2 p)

  -> CSL BS tid
         (kernelInv avenv apenv aeenv R P E p)
         (Cif b C1 C2)
         (kernelDisj avenv apenv aeenv R1 P1 E1 R2 P2 E2 p).
Proof.
  intros.
  unfold kernelDisj, kernelInv in *.
  eapply rule_if_disj; eauto using evalBExp_app1.
Qed.

(* TODO: Move SeqRules.v *)
Lemma rule_skip ntrd BS (tid : Fin.t ntrd) (Q : assn) : CSL BS tid Q Cskip Q.
Proof.
  unfold CSL; intros st ph H n; induction n; simpl; eauto; repeat split; simpl; eauto.
  - intros; inversion 1.
  - intros ? ? ? ? ? ? hred; inversion hred.
  - intros ? ? heq; inversion heq.
Qed.

Ltac hoare_forward_prim :=
  lazymatch goal with
  | [|- CSL _ _ (Assn ?Res ?P ?Env) (?x ::T _ ::= [?le +o ?ix]) ?Q] =>
    let Hle := fresh "Hle" in let l := fresh "l" in
    evar (l : loc); assert (Hle : evalLExp Env le l) by (unfold l; evalLExp); unfold l in *;
    let Hv := fresh "Hv" in let v := fresh "v" in
    evar (v : val); assert (Hv : evalExp Env ix v) by (unfold v; evalLExp); unfold v in *;
    let Hn := fresh "Hn" in let n := fresh "n" in
    evar (n : nat); assert (Hn : v = Zn n) by (unfold v, n; solve_zn); unfold n in *;
    let le := eval unfold l in l in
    let i := eval unfold n in n in
    unfold l, v, n in *; clear l v n;
    apply_read_rule Hle Hv Hn P Res le i

  | [|- CSL _ _ ?P (?x ::T _ ::= [?e]) ?Q] =>
    idtac "hoare_forward_prim: match read case";
    eapply rule_read; [evalExp | find_res | ]

  | [|- CSL _ _ (Assn ?Res ?P ?Env) ([?le +o ?ix] ::= ?e) ?Q] =>
    idtac "hoare_forward_prim: match write array case";
    let Hle := fresh "Hle" in let l := fresh "l" in
    evar (l : loc); assert (Hle : evalLExp Env le l) by (unfold l; evalLExp); unfold l in *;

    let Hix := fresh "Hix" in let i := fresh "i" in
    evar (i : val); assert (Hix : evalExp Env ix i) by (unfold i; evalExp); unfold i in *;

    let He := fresh "He" in let v := fresh "v" in
    evar (v : val); assert (He : evalExp Env e v) by (unfold v; evalExp); unfold v in *;

    let Hn := fresh "Hn" in let n := fresh "n" in
    evar (n : nat); assert (Hn : i = Zn n) by (unfold i, n; solve_zn); unfold n in *;
    
    let l' := eval unfold l in l in
    let n' := eval unfold n in n in
    unfold l, i, v, n in *; clear l i v n;
      
    apply_write_rule Hle Hix He Hn P Res l' n'
  | [|- CSL _ _ ?P (assigns ?xs _ ?es) ?Q] =>
    apply rule_assigns; eauto

  | [|- CSL _ _ ?P (?x ::T _ ::= ?e) ?Q] =>
    idtac "hoare_forward_prim: match assign case";
    eapply rule_assign; evalExp

  | [|- CSL _ _ _ (WhileI ?inv _ _) _ ] =>
    idtac "hoare_forward_prim: match while case";
    eapply backwardR; [applys (>>rule_while inv)|]

  | [|- CSL _ _ (Assn _ _ _) (Cif _ _ _) _] =>
    eapply rule_if_disj; [evalBExp|..]

  | [|- CSL _ _ (kernelInv _ _ _ _ _ _ _) (Cif _ _ _) _] =>
    eapply rule_if_disj_kinv; [evalBExp|..]

  | [|- CSL _ _ _ Cskip _] =>
    apply rule_skip

  | [|- CSL _ _ ?P (Cbarrier ?i) ?Q] =>
    idtac "hoare_forward_prim: match barrier case";
    idtac "P, Q = " P Q;
    let unify_bspec := rewrite MyVector.init_spec; reflexivity in
    let tac :=
        eapply rule_barrier; simpl; [unify_bspec | unify_bspec | prove_imp | ..] in
    ((is_evar Q; tac) || (eapply forward; [|tac]; try (introv; rewrite Assn_combine); eauto))
  | _ => idtac
  end.

Definition assigns_get {ty} (xs : vars ty) (arr : var -> cmd * vars ty) (i : var) :=
  (fst (arr i)) ;;
  assigns xs (ty2ctys ty) (v2e (snd (arr i))).

Definition writes_get {ty} (les : lexps ty) (arr : var -> cmd * vars ty) (i : var) :=
  (fst (arr i)) ;;
  writes les (v2e (snd (arr i))).

Definition assigns_call1 {cod dom} (xs : vars cod) (func : vars dom -> cmd * vars cod) (args : vars dom) :=
  (fst (func args)) ;;
  assigns xs (ty2ctys cod) (v2e (snd (func args))).

Definition writes_call1 {cod dom} (les : lexps cod) (func : vars dom -> cmd * vars cod) (args : vars dom) :=
  (fst (func args)) ;;
  writes les (v2e (snd (func args))).

Definition assigns_call2 {dom1 dom2 cod}
           (xs : vars cod)
           (func : vars dom1 -> vars dom2 -> cmd * vars cod)
           (args1 : vars dom1) (args2 : vars dom2) :=
  (fst (func args1 args2)) ;;
  assigns xs (ty2ctys cod) (v2e (snd (func args1 args2))).

Definition is_param v := String.prefix "_" (str_of_var v) = true.

Lemma mpss_in ty x v (xs : vars ty) vs :
  In (x |-> v) (xs |=> vs) -> In x (flatTup xs).
Proof.
  induction ty; simpl; eauto; try tauto.
  intros [H | []]; inverts H; substs; eauto.
  intros [H | []]; inverts H; substs; eauto.
  rewrite !in_app_iff; intros [H | H]; eauto.
Qed.

Lemma arrInvVar_in GA (avar_env : AVarEnv GA) aptr_env aeval_env x v :
  In (x |-> v) (arrInvVar avar_env aptr_env aeval_env) ->
  exists ty, exists (m : member ty GA), x = fst (hget avar_env m) \/
                                        In x (flatTup (snd (hget avar_env m))).
Proof.
  induction GA;
  dependent destruction avar_env;
  dependent destruction aptr_env;
  dependent destruction aeval_env;
  simpl in *; try tauto.
  unfold arrInvVar in *; simpl.
  destruct p eqn:Heq; simpl.
  intros [Hin | Hin].
  - inverts Hin.
    exists a (@HFirst _ a GA); simpl; eauto.
  - rewrite in_app_iff in Hin; destruct Hin as [Hin | Hin].
    + exists a (@HFirst _ a GA); simpl; eauto.
      forwards*: mpss_in.
    + forwards*(ty & m & IH): IHGA.
      exists* ty (@HNext _ ty a GA m).
Qed.

Lemma kernelInv_assn GA (avar_env : AVarEnv GA) aptr_env aeval_env R P Env p :
  kernelInv avar_env aptr_env aeval_env R P Env p ==
  (Assn R P Env ** kernelInv avar_env aptr_env aeval_env Emp True nil p).
Proof.
  unfold kernelInv; rewrite Assn_combine; simpl.
  intros s h; split; revert s h; prove_imp.
Qed.

Lemma inde_assn_vars:
  forall (R : res) (P : Prop) (Env : list entry) (E : list var),
    (forall (x : var) (v : val),
        In (x |-> v) Env -> ~In x E) ->
    inde (Assn R P Env) E.
Proof.
  intros HEnv.
  intros; apply inde_equiv; intros.
  unfold sat in *; simpl in *; splits; jauto.
  applys* (>>disjoint_inde_env (x :: nil)); simpl; eauto.
  unfold inde_env; apply disjoint_comm; simpl; splits; eauto.
  intros Hc; rewrite in_map_iff in Hc; destruct Hc as ((? & ?) & ?); simpl in *.
  forwards*: H.
  destruct H2; substs; tauto.
Qed.

Lemma kernelInv_inner n BS (tid : Fin.t n) GA (avar_env : AVarEnv GA)
      aptr_env aeval_env R P Env R' P' Env' C p:
  aenv_ok avar_env 
  -> (forall x, In x (writes_var C) -> ~is_param x)
  -> CSL BS tid
         (Assn R P Env)
         C
         (Assn R' P' Env')
  -> CSL BS tid
         (kernelInv avar_env aptr_env aeval_env R P Env p)
         C
         (kernelInv avar_env aptr_env aeval_env R' P' Env' p).
Proof.
  intros Hok Hwr Htri.
  eapply backward; [intros s h Hsat; rewrite kernelInv_assn in Hsat; eauto|].
  eapply forward; [intros s h Hsat; rewrite kernelInv_assn; eauto|].
  eapply rule_frame; eauto.
  apply inde_assn_vars; simpl.
  introv Hin Hc; substs.
  unfold aenv_ok in *.
  destruct Hok as [Hok1 Hok2].
  assert (String.prefix "_" (str_of_var x) = false).
  { forwards*: Hwr; unfold is_param in *.
    destruct String.prefix; congruence. }
  forwards* (ty & m & [? | ?]): arrInvVar_in.
  forwards*: (>>Hok1 m); congruence.
  forwards*: (>>Hok2 m); congruence.
Qed.
  
Lemma cond_prop_kerInv ntrd BS (tid : Fin.t ntrd)
      GA (avenv : AVarEnv GA) apenv aeenv p
      Res P P' Env C Q cond (b : bool) :
  evalBExp Env cond  P'
  -> CSL BS tid (kernelInv avenv apenv aeenv Res (P /\ if b then P' else ~P') Env p) C Q
  -> CSL BS tid (kernelInv avenv apenv aeenv Res P Env p ** (BEval_assn cond b)) C Q.
Proof.
  intros.
  eapply cond_prop.
  apply evalBExp_app1; eauto.
  eauto.
Qed.

Ltac prove_not_local :=
  introv;
  lazymatch goal with
  | [|- In (_ |-> _) _ -> _] =>
    let H := fresh "H" in
    intros H; simpl in H; repeat (rewrite in_app_iff in H; simpl in H); des_disj H;
    try lazymatch type of H with
      | In (_ |-> _) (_ |=> _) => apply mpss_in, locals_pref in H as (? & ? & H); substs
      | _ |-> _ = _ |-> _ => inverts H
      end
  | [|- In _ _ -> _] =>
    try rewrite assigns_writes;
    try rewrite reads_writes;
    try rewrite writes_writes; 
    let H := fresh "H" in
    simpl; intros H;
    (repeat rewrite in_app_iff in H);
    des_disj H; 
    try lazymatch type of H with
      | In _ _ => apply locals_pref in H as (? & ? & H); substs
      | _ = _ => substs
      end
  | [|- is_param _ -> False] => idtac
  | [|- is_local _ -> False] => idtac
  end;
  unfold is_param, is_local; simpl; try congruence.

Lemma prefix_leq x y p :
  String.length p <= String.length x 
  -> String.prefix p (x ++ y) = true
  -> String.prefix p x = true.
Proof.
  revert y p; induction x; intros y [|? p] ?; simpl in *; eauto; try omega.
  destruct Ascii.ascii_dec; eauto; substs.
  intros; applys* IHx; lia.
Qed.

Lemma prefix_leq_false x y p :
  String.length p <= String.length x 
  -> prefix p x = false 
  -> prefix p (x ++ y) = false.
Proof.
  intros.
  destruct (prefix p (x ++ y)) eqn:Heq; eauto.
  forwards*: (prefix_leq x y p); congruence.
Qed.

Lemma locals_prefix_neq ty x p n :
  String.length p <= String.length x ->
  prefix p x = false ->
  forall y, In y (flatTup (locals x ty n)) -> prefix p (str_of_var y) = false.
Proof.
  revert n; induction ty; simpl; intros ? ? ? ? Hin; des_disj Hin; try tauto; substs;
  eauto using prefix_leq_false.
  rewrite in_app_iff in Hin; des_disj Hin; eauto.
Qed.

Lemma fvEs_v2e ty (xs : vars ty) : fv_Es (v2e xs) = flatTup xs.
Proof.
  unfold v2e; induction ty; simpl; eauto; congruence.
Qed.

Notation char_ := (Ascii.Ascii true true true true true false true false).
Notation charl := (Ascii.Ascii false false true true false true true false).

Lemma prefix_nil s : prefix "" s = true. destruct s; eauto. Qed.
Lemma ae_assigns GA ty (avenv : AVarEnv GA) apenv aeenv (ae : Skel.AE GA ty) arr_c (res0 : Skel.aTypDenote ty) ix i'
      (ntrd : nat) (tid : Fin.t ntrd)
          (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd) 
          (i : nat) 
          (R : res) (P : Prop) (resEnv : list entry) (p : Qc) n (x : string) :
  aenv_ok avenv
  -> Skel.aeDenote GA ty ae aeenv = Some res0
  -> ae_ok avenv ae arr_c
  -> ~ is_local x -> ~ is_param x
  -> ~ is_local ix 
  -> (forall (l : var) (v : val), In (l |-> v) resEnv -> ~ is_local l)
  -> evalExp resEnv ix i'
  -> i' = Zn i
  -> (P -> i < Datatypes.length res0)
  -> CSL BS tid (kernelInv avenv apenv aeenv R P resEnv p)
         (assigns_get (locals x ty n) arr_c ix)
         (kernelInv avenv apenv aeenv R P
                    ((locals x ty n) |=> sc2CUDA (gets' res0 i) ++ remove_vars resEnv (flatTup (locals x ty n))) p).
Proof.
  intros ? ? (? & ? & Htri & ?) ? ? ?; intros; substs; eauto.
  eapply rule_seq.
  forwards*: Htri.
  eapply kernelInv_inner; eauto.
  rewrite assigns_writes.
  Lemma not_is_local_locals x ty n y:
    prefix "l" x = false
    -> In y (flatTup (locals x ty n))
    -> ~is_local y.
  Proof.
    intros; unfold is_local.
    forwards* (? & ? & ?): locals_pref; substs.
    destruct x.
    - destruct x0; simpl; eauto.
    - Opaque Ascii.ascii_dec.
      simpl.
      destruct Ascii.ascii_dec; eauto.
      rewrites* prefix_nil; substs; simpl in *.
      destruct Ascii.ascii_dec; try congruence.
      rewrite prefix_nil in H; congruence.
      Transparent Ascii.ascii_dec.
  Qed.

  Lemma not_is_param_locals x ty n y:
    prefix "_" x = false
    -> In y (flatTup (locals x ty n))
    -> ~is_param y.
  Proof.
    intros; unfold is_param.
    forwards* (? & ? & ?): locals_pref; substs.
    destruct x.
    - destruct x0; simpl; eauto.
    - Opaque Ascii.ascii_dec.
      simpl.
      destruct Ascii.ascii_dec; eauto.
      rewrites* prefix_nil; substs; simpl in *.
      destruct Ascii.ascii_dec; try congruence.
      rewrite prefix_nil in H; congruence.
  Qed.
  
  intros; forwards*: not_is_param_locals.
  unfold is_param in *; simpl in *.
  destruct (prefix "_" x); congruence.

  unfold is_param in *; eauto.
  eapply forward; try apply rule_assigns; eauto using locals_disjoint_ls.
  repeat rewrite remove_vars_app; prove_imp.
  apply not_in_disjoint; intros.
  rewrite fvEs_v2e.
  forwards*: not_is_local_locals.
  unfold is_local in *; simpl in *.
  destruct (prefix "l" x); congruence.
  apply evalExps_vars.
  apply incl_appl.
  eauto.
Qed.

Lemma assigns_call2_ok GA dom1 dom2 cod (avenv : AVarEnv GA) apenv aeenv
      (func : Skel.Func GA (Skel.Fun2 dom1 dom2 cod)) func_c  vs1 vs2 r
      (ntrd : nat) (tid : Fin.t ntrd)
      (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd) 
      (R : res) (P : Prop) (resEnv : list entry) (p : Qc) n (x : string) arg1 arg2 :
  aenv_ok avenv
  -> (P -> Skel.funcDenote GA _ func aeenv vs1 vs2 = Some r)
  -> func_ok avenv func func_c
  -> prefix "l" arg1 = false
  -> prefix "l" arg2 = false
  -> prefix "l" x = false
  -> prefix "_" x = false
  -> (forall (l : var) (v : val), In (l |-> v) resEnv -> ~ is_local l)
  -> evalExps resEnv (v2e (locals arg1 dom1 0)) (sc2CUDA vs1)
  -> evalExps resEnv (v2e (locals arg2 dom2 0)) (sc2CUDA vs2)
  -> CSL BS tid
         (kernelInv avenv apenv aeenv R P resEnv p)
         (assigns_call2 (locals x cod n) func_c (locals arg1 dom1 0) (locals arg2 dom2 0))
         (kernelInv avenv apenv aeenv R P
                    ((locals x cod n) |=> sc2CUDA r ++
                     remove_vars resEnv (flatTup (locals x cod n))) p).
Proof.
  intros ? ? (? & ? & Htri & ?); intros; substs; eauto.
  eapply rule_seq.
  forwards*: Htri.
  intros? Hin; forwards*: (>>not_is_local_locals Hin).
  intros? Hin; forwards*: (>>not_is_local_locals Hin).
  
  eapply kernelInv_inner; eauto.
  rewrite assigns_writes.
  
  intros; forwards*: not_is_param_locals.

  eapply forward; try apply rule_assigns; eauto using locals_disjoint_ls.
  repeat rewrite remove_vars_app; prove_imp.
  apply not_in_disjoint; intros.
  rewrite fvEs_v2e.
  intros Hc; forwards*: H2.
  forwards*: not_is_local_locals.
  apply evalExps_vars.
  apply incl_appl.
  eauto.
Qed.

Lemma ae_ok_tri GA ty (avenv : AVarEnv GA) apenv aeenv (ae : Skel.AE GA ty) arr_c (res0 : Skel.aTypDenote ty) ix 
      (ntrd : nat) (tid : Fin.t ntrd)
          (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd) 
          (i : nat) 
          (R : res) (P : Prop) (resEnv : list entry) (p : Qc) :
  ~ is_local ix 
  -> aenv_ok avenv
  -> Skel.aeDenote GA ty ae aeenv = Some res0
  -> ae_ok avenv ae arr_c
  -> (forall (l : var) (v : val), In (l |-> v) resEnv -> ~ is_local l)
  -> evalExp resEnv ix (Zn i)
  -> (P -> i < Datatypes.length res0)
  -> CSL BS tid (kernelInv avenv apenv aeenv R P resEnv p)
         (fst (arr_c ix))
         (kernelInv avenv apenv aeenv R P
                    (snd (arr_c ix) |=> sc2CUDA (gets' res0 i) ++ resEnv) p).
Proof.
  intros ? ? ? (? & ? & ? & ?); eauto.
Qed.

Lemma func_ok_tri GA dom cod (avenv : AVarEnv GA) apenv aeenv (f : Skel.Func GA (Skel.Fun1 dom cod))
      (f_c : vars dom -> cmd * vars cod) 
      (ntrd : nat) (tid : Fin.t ntrd)
      (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd)
      (xs : typ2Coq var dom) (vs : Skel.typDenote dom)
      (res0 : Skel.typDenote cod) (R : res) (P : Prop) (resEnv : list entry)
      (p : Qc) :
  aenv_ok avenv ->
  func_ok avenv f f_c ->
  (forall l : var, In l (flatTup xs) -> ~ is_local l) ->
  (forall (l : var) (v : val), In (l |-> v) resEnv -> ~ is_local l) ->
  evalExps resEnv (v2e xs) (sc2CUDA vs) ->
  (P -> Skel.funcDenote GA (Skel.Fun1 dom cod) f aeenv vs = Some res0) ->
  CSL BS tid (kernelInv avenv apenv aeenv R P resEnv p)
      (fst (f_c xs))
      (kernelInv avenv apenv aeenv R P
                 (snd (f_c xs) |=> sc2CUDA res0 ++ resEnv) p).
Proof.
  intros ? (? & ? & ? & ?); eauto.
Qed.      

Lemma disjoint_user_local_vars_ae GA ty (avenv : AVarEnv GA) (arr : Skel.AE GA ty) arr_c t n i:
  aenv_ok avenv 
  -> prefix "l" t = false
  -> ae_ok avenv arr arr_c
  -> disjoint (flatTup (locals t ty n)) (flatTup (snd (arr_c i))).
Proof.
  intros.
  apply not_in_disjoint; introv Hin Hc.
  destruct H1 as (? & ? & ? & ?); eauto.
  forwards*: H2; unfold is_local in *.
  forwards* (? & ? & ?): locals_pref; substs; simpl in *.
  destruct t; simpl in *.
  destruct x0; simpl in *; destruct Ascii.ascii_dec; try congruence.
  destruct Ascii.ascii_dec; simpl in *.
  rewrite prefix_nil in *; congruence.
  congruence.
Qed.

Lemma disjoint_user_local_ae GA ty (avenv : AVarEnv GA) (arr : Skel.AE GA ty) arr_c t n i :
  aenv_ok avenv 
  -> prefix "l" t = false
  -> ae_ok avenv arr arr_c
  -> disjoint (flatTup (locals t ty n)) (fv_Es (v2e (snd (arr_c i)))).
Proof.
  rewrite fvEs_v2e; apply disjoint_user_local_vars_ae.
Qed.

Lemma disjoint_user_local_vars_func1 GA dom cod (avenv : AVarEnv GA) (f : Skel.Func GA (Skel.Fun1 dom cod)) func_c t n i:
  aenv_ok avenv 
  -> prefix "l" t = false
  -> func_ok avenv f func_c
  -> disjoint (flatTup (locals t cod n)) (flatTup (snd (func_c i))).
Proof.
  intros.
  apply not_in_disjoint; introv Hin Hc.
  destruct H1 as (? & ? & ? & ?); eauto.
  forwards*: H2; unfold is_local in *.
  forwards* (? & ? & ?): locals_pref; substs; simpl in *.
  destruct t; simpl in *.
  destruct x0; simpl in *; destruct Ascii.ascii_dec; try congruence.
  destruct Ascii.ascii_dec; simpl in *.
  rewrite prefix_nil in *; congruence.
  congruence.
Qed.

Lemma disjoint_user_local_func1 GA dom cod (avenv : AVarEnv GA) (f : Skel.Func GA (Skel.Fun1 dom cod)) func_c t n i:
  aenv_ok avenv 
  -> prefix "l" t = false
  -> func_ok avenv f func_c
  -> disjoint (flatTup (locals t cod n)) (fv_Es (v2e (snd (func_c i)))).
Proof.
  rewrite fvEs_v2e; apply disjoint_user_local_vars_func1.
Qed.

Lemma disjoint_user_local_vars_func2 GA dom1 dom2 cod (avenv : AVarEnv GA)
      (f : Skel.Func GA (Skel.Fun2 dom1 dom2 cod)) func_c t n x y:
  aenv_ok avenv 
  -> prefix "l" t = false
  -> func_ok avenv f func_c
  -> disjoint (flatTup (locals t cod n)) (flatTup (snd (func_c x y))).
Proof.
  intros.
  apply not_in_disjoint; introv Hin Hc.
  destruct H1 as (? & ? & ? & ?); eauto.
  forwards*: H2; unfold is_local in *.
  forwards* (? & ? & ?): locals_pref; substs; simpl in *.
  destruct t; simpl in *.
  destruct x1; simpl in *; destruct Ascii.ascii_dec; try congruence.
  destruct Ascii.ascii_dec; simpl in *.
  rewrite prefix_nil in *; congruence.
  congruence.
Qed.

Lemma disjoint_user_local_func2 GA dom1 dom2 cod (avenv : AVarEnv GA) (f : Skel.Func GA (Skel.Fun2 dom1 dom2 cod)) func_c t n x y:
  aenv_ok avenv 
  -> prefix "l" t = false
  -> func_ok avenv f func_c
  -> disjoint (flatTup (locals t cod n)) (fv_Es (v2e (snd (func_c x y)))).
Proof.
  rewrite fvEs_v2e; apply disjoint_user_local_vars_func2.
Qed.

Lemma not_in_user_local_vars_ae GA ty (avenv : AVarEnv GA) (arr : Skel.AE GA ty) arr_c (t : var) i:
  aenv_ok avenv 
  -> prefix "l" (str_of_var t) = false
  -> ae_ok avenv arr arr_c
  -> ~ In t (flatTup (snd (arr_c i))).
Proof.
  intros.
  destruct H1 as (? & ? & ? & ?); eauto.
  intros Hc; forwards*: H2; unfold is_local in *; congruence.
Qed.

Lemma not_in_user_local_ae GA ty (avenv : AVarEnv GA) (arr : Skel.AE GA ty) arr_c (t : var) i :
  aenv_ok avenv 
  -> prefix "l" (str_of_var t) = false
  -> ae_ok avenv arr arr_c
  -> ~ In t (fv_Es (v2e (snd (arr_c i)))).
Proof.
  rewrite fvEs_v2e; apply not_in_user_local_vars_ae.
Qed.

Lemma not_in_user_local_vars_func1 GA dom cod (avenv : AVarEnv GA) (f : Skel.Func GA (Skel.Fun1 dom cod)) func_c t i:
  aenv_ok avenv 
  -> prefix "l" (str_of_var t) = false
  -> func_ok avenv f func_c
  -> ~In t (flatTup (snd (func_c i))).
Proof.
  intros.
  destruct H1 as (? & ? & ? & ?); eauto.
  intros Hc; forwards*: H2; unfold is_local in *; congruence.
Qed.

Lemma not_in_user_local_func1 GA dom cod (avenv : AVarEnv GA) (f : Skel.Func GA (Skel.Fun1 dom cod)) func_c t i:
  aenv_ok avenv 
  -> prefix "l" (str_of_var t) = false
  -> func_ok avenv f func_c
  -> ~ In t (fv_Es (v2e (snd (func_c i)))).
Proof.
  rewrite fvEs_v2e; apply not_in_user_local_vars_func1.
Qed.

Lemma not_in_user_local_vars_func2 GA dom1 dom2 cod (avenv : AVarEnv GA)
      (f : Skel.Func GA (Skel.Fun2 dom1 dom2 cod)) func_c t x y:
  aenv_ok avenv 
  -> prefix "l" (str_of_var t) = false
  -> func_ok avenv f func_c
  -> ~ In t (flatTup (snd (func_c x y))).
Proof.
  intros.
  destruct H1 as (? & ? & ? & ?); eauto.
  intros Hc; forwards*: H2; unfold is_local in *; congruence.
Qed.

Lemma not_in_user_local_func2 GA dom1 dom2 cod (avenv : AVarEnv GA) (f : Skel.Func GA (Skel.Fun2 dom1 dom2 cod)) func_c t x y:
  aenv_ok avenv 
  -> prefix "l" (str_of_var t) = false
  -> func_ok avenv f func_c
  -> ~In t (fv_Es (v2e (snd (func_c x y)))).
Proof.
  rewrite fvEs_v2e; apply not_in_user_local_vars_func2.
Qed.


Lemma locals_disj x y :
  prefix x y = false ->
  prefix y x = false ->
  forall (z w : string), (x ++ z <> y ++ w)%string.
Proof.
  revert y; induction x; simpl in *; intros y Hxy Hyx z w Hc.
  rewrite prefix_nil in *; congruence.
  destruct y; simpl in *; try congruence.
  inverts Hc.
  destruct Ascii.ascii_dec; try congruence.
  forwards*: IHx.
Qed.

Lemma locals_disjoint ty1 ty2 x y n m :
  prefix x y = false ->
  prefix y x = false ->
  disjoint (flatTup (locals x ty1 n)) (flatTup (locals y ty2 m)).
Proof.
  intros; apply not_in_disjoint; intros ? Hin1 Hin2.
  forwards* (? & ? & ?): (>>locals_pref Hin1); substs.
  forwards* (? & ? & ?): (>>locals_pref Hin2).
  inverts H1.
  applys* (>>locals_disj H H0).
Qed.

Lemma str_app_nil_r s :
  (s ++ "" = s)%string.
Proof.
  induction s; simpl; congruence.
Qed.

Lemma locals_not_in ty1 x n (y : string) :
  prefix x y = false 
  -> prefix y x = false
  -> ~In (Var y) (flatTup (locals x ty1 n)).
Proof.
  intros Hxy Hyx Hin.
  forwards* (? & ? & ?): (>>locals_pref Hin); substs.
  forwards*: (>>locals_disj Hxy Hyx (nat2str x0) ""); substs.
  rewrite str_app_nil_r in *; congruence.
Qed.

Lemma mpss_remove_vars ty (xs : vars ty) vs ys :
  disjoint (flatTup xs) ys
  -> remove_vars (xs |=> vs) ys = xs |=> vs.
Proof.
  cutrewrite (xs |=> vs = xs |=> vs ++ nil); [|rewrites* app_nil_r].
  intros; rewrite env_assns_remove_app; eauto using disjoint_comm.
  rewrite remove_vars_nil; eauto.
Qed.

(* Lemma remove_var_out ty ps x : *)
(*   prefix "_" x = false *)
(*   -> remove_var (outArr ty |=> ps) x = outArr ty |=> ps. *)
(* Proof. *)
(*   intros Hpref. *)
(*   apply remove_var_disjoint; simpl. *)
(*   unfold outArr; intros Hc. *)
(*   apply in_map_iff in Hc as (? & ? & ?); substs. *)
(*   destruct x0; simpl in *. *)
(*   apply mpss_in in H0. *)
(*   forwards* (j & Heq & ?): locals_pref; substs. *)

(*   inverts Heq; simpl in *; congruence. *)
(* Qed. *)

Lemma remove_var_cons x e Env :
  remove_var (e :: Env) x = (if var_eq_dec x (ent_e e) then remove_var Env x else e :: remove_var Env x).
Proof.
  simpl; destruct var_eq_dec; eauto.
Qed.

Lemma remove_vars_comm (xs ys : list var) Env :
  remove_vars Env (xs ++ ys) = remove_vars Env (ys ++ xs).
Proof.
  revert ys; induction xs; introv; simpl; eauto.
  rewrite app_nil_r; eauto.
  rewrite IHxs.
  rewrite !remove_vars_nest.
  rewrite <-remove_removes; simpl.
  rewrite remove_removes; eauto.
Qed.  

Lemma remove_vars_same ty (xs : vars ty) vs Env :
  remove_vars (xs |=> vs ++ Env) (flatTup xs) = remove_vars Env (flatTup xs).
Proof.
  revert Env; induction ty; simpl; eauto;
  try (destruct var_eq_dec; try congruence).
  introv; rewrite remove_vars_nest.
  rewrite <-app_assoc, IHty1.
  rewrite <-remove_vars_nest.
  rewrite remove_vars_comm.
  rewrite remove_vars_nest.
  rewrite IHty2.
  rewrite <-remove_vars_nest.
  rewrite remove_vars_comm.
  eauto.
Qed.

Lemma remove_vars_same' ty (xs : vars ty) vs  :
  remove_vars (xs |=> vs) (flatTup xs) = nil.
Proof.
  forwards*: (>>remove_vars_same (@nil entry)); simpl in *; eauto.
  rewrite app_nil_r in *.
  rewrite remove_vars_nil in *.
  eauto.
Qed.

Lemma remove_remove_vars Env x :
  remove_var Env x = remove_vars Env (x :: nil).
Proof. eauto. Qed.

Lemma remove_var_app_r ty Env (xs : vars ty) vs x :
  ~ In x (flatTup xs) ->
  remove_var (xs |=> vs ++ Env) x = xs |=> vs ++ remove_var Env x.
Proof.
  rewrite remove_remove_vars.
  intros.
  apply env_assns_remove_app; simpl; eauto.
Qed.

Lemma remove_var_ignore ty (xs : vars ty) vs x :
  ~ In x (flatTup xs) ->
  remove_var (xs |=> vs) x = xs |=> vs.
Proof.
  rewrite remove_remove_vars.
  intros.
  apply mpss_remove_vars; simpl; eauto.
Qed.

Ltac simplify_remove_var :=
  let tac := now first [applys* disjoint_user_local_vars_ae |
                        applys* disjoint_user_local_vars_func1 |
                        applys* disjoint_user_local_vars_func2 |
                        applys* not_in_user_local_vars_ae |
                        applys* not_in_user_local_vars_func1 |
                        applys* not_in_user_local_vars_func2 |
                        simpl; applys* locals_not_in |
                        applys* locals_disjoint] in
  repeat (first [
           rewrite remove_vars_same |
           rewrite remove_vars_same' |
           rewrite remove_var_app_r; [|tac] |
           rewrite remove_var_ignore; [|tac] |
           rewrite env_assns_remove_app; [|tac] |
           rewrite env_assns_removes_cons; [|tac] |
           rewrite mpss_remove_vars; [|tac] ]; simpl).

Ltac prove_incl :=
  lazymatch goal with
  | |- incl (?X |=> _) (?X |=> _) => apply incl_refl
  | |- incl (?X |=> _) (?X |=> _ ++ _) => apply incl_appl, incl_refl
  | |- incl (?X |=> _) (_ |=> _ ++ _) => apply incl_appr; prove_incl
  | |- incl (_ |=> _) (_ :: _) => apply incl_tl; prove_incl
  end.

Fixpoint vals2es {ty} :=
  match ty return vals ty -> exps ty with
  | Skel.TBool | Skel.TZ => fun v => Enum v
  | Skel.TTup t1 t2 => fun v => (vals2es (fst v), vals2es (snd v))
  end.

Lemma vals2es_eval ty E (vs : vals ty) :
  evalExps E (vals2es vs) vs.
Proof.
  induction ty; try do 2 constructor; simpl; jauto.
Qed.

Ltac evalExps :=
  match goal with
  | [|- evalExps _ (vals2es _) _] => apply vals2es_eval
  | [|- evalExps _ (v2e _) _] => apply evalExps_vars; repeat rewrite <-app_assoc; simpl; prove_incl
  end.

Ltac is_IO_cmd c :=
  lazymatch c with
  | (_ ::T _ ::= _) => constr:true
  | (_ ::T _ ::= [_]) => constr:true
  | ([_] ::= _) => constr:true
  | assigns _ _ _ => constr:true
  | reads _ _ _ => constr:true
  | writes _ _ => constr:true
  | Cbarrier _ => constr:true
  | _ => constr:false
  end.

Ltac evalLExps := 
  lazymatch goal with
  | [|- evalLExps _ (e2gl _) _] => 
    apply evalLExps_gl; evalExps
  | [|- evalLExps _ (e2sh _) _] =>
    apply evalLExps_sh; evalExps
  | [|- evalLExps _ (v2gl _) _] => 
    apply evalLExps_gl; evalExps
  | [|- evalLExps _ (v2sh _) _] =>
    apply evalLExps_sh; evalExps
  end.

Ltac apply_write_rule' Hle Hix He Hn P Res le i :=
  let checkR Res' R :=
    idtac "checkR: Res', R, le = " Res' "," R ", " le;
    let Hres := fresh "Hres" in
    let Hbnd := fresh "Hbnd" in
    lazymatch R with
    | arrays le ?arr _ =>
      idtac "apply read rule: match array case.";
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr); [prove_pure|
      applys (>> rule_writes_arrays Hle Hix Hn Hbnd He Hres); eauto with pure_lemma]]
    | arrays' le (ith_vals ?dist ?arr ?j ?s_) _ =>
      idtac "apply read rule: match sarray case.";
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr /\ dist (s_ + i) = j); [prove_pure|
      applys (>> rule_writes_arrays' Hle Hix He Hn); eauto with pure_lemma]]
    end in
  let rec iter acc Res :=
    lazymatch Res with
    | ?R *** ?Res =>
      first [let Res' := append_assn acc Res in 
             idtac "append_assn: P, Q = " acc Res;
               checkR Res' R |
             iter (R *** acc) Res]
    | ?R => let Res' := remove_last_emp acc in checkR Res' R
    end in
  iter Emp Res.

Lemma fvlEs_v2sh ty (xs : vars ty) : fv_lEs (v2sh xs) = flatTup xs.
Proof.
  unfold v2sh, e2sh, v2e; induction ty; simpl; try congruence.
Qed.

Lemma fvEs_vals2es ty (vs : vals ty) : fv_Es (vals2es vs) = nil.
Proof.
  induction ty; simpl; eauto.
  rewrite IHty1, IHty2; simpl; eauto.
Qed.

Ltac prove_disj :=
  repeat first [rewrite fvlEs_v2sh | rewrite fvEs_v2e | rewrite fvEs_vals2es ];
  lazymatch goal with
  | [|- disjoint _ nil] => apply disjoint_nil_r
  | [|- disjoint (flatTup (locals _ _ _)) (flatTup (locals _ _ _)) ] =>
    applys* locals_disjoint
  | [|- disjoint (flatTup (locals _ _ _)) _] =>
    apply disjoint_comm; simpl;
    repeat (rewrite disjoint_app; simpl);
    split; eauto;
    lazymatch goal with
    | [|- ~In _ _] => 
      applys* locals_not_in
    end
  end.

Ltac apply_read_rule' Hle Hv Hn P Res le i :=
  let checkR Res' R :=
    idtac "checkR: Res', R, le = " Res' "," R ", " le;
    let Hres := fresh "Hres" in
    let Hbnd := fresh "Hbnd" in
    let Hp := fresh "Hp" in
    match R with
    | arrays le ?arr _ =>
      idtac "apply read rule: match array case.";
      assert (Hres : P -> Res |=R R *** Res'); [intros Hp; sep_auto'|
      assert (Hbnd : P -> i < length arr); [prove_pure|
      applys (>> rule_reads_arrays Hle Hv Hres Hn Hbnd);
        (try (now prove_disj)); (try apply locals_disjoint_ls); eauto with pure_lemma]]
    | arrays' le (ith_vals ?dist ?arr ?j ?s_) _ =>
      idtac "apply read rule: match sarray case.";
      idtac dist i;
      assert (Hres : P -> Res |=R R *** Res'); [intros Hp; sep_auto'|
      assert (Hbnd : P -> i < length arr /\ dist (s_ + i) = j); [simpl; prove_pure|
      applys (>> rule_reads_arrays' Hle Hv Hres Hn Hbnd); 
        (try (now prove_disj)); (try apply locals_disjoint_ls); eauto with pure_lemma]]
    end in
  let rec iter acc Res :=
    match Res with
    | ?R *** ?Res =>
      first [let Res' := append_assn acc Res in checkR Res' R |
             iter (R *** acc) Res]
    | ?R => checkR acc R
    end in
  iter Emp Res.

Ltac hoare_forward_prim' :=
  lazymatch goal with
  | [|- CSL _ _ ?P ?c ?Q] =>
    lazymatch is_IO_cmd c with
    | true => 
      try match goal with 
      | [|- CSL _ _ (kernelInv _ _ _ _ _ _ _) _ _ ] => 
        idtac "hoare_forward_prim': apply kernelInv_inner";
        applys* kernelInv_inner; try prove_not_local;
        try match goal with
        | [|- CSL _ _ ?P _ ?Q ] =>
          idtac "after kernelInv_inner" P Q
        end
      end;
      lazymatch goal with
      | |- CSL _ _ _ (assigns _ _ _) _ => 
        eapply rule_assigns; [try prove_disj| eauto using locals_disjoint_ls|evalExps ]

      | [|- CSL _ _ (Assn ?Res ?P ?Env) (reads ?xs _ (?le +os ?ix)) _] =>
        let ty := match type of le with 
                  | lexps ?ty => ty
                  end in
        let Hle := fresh "Hle" in let l := fresh "l" in
        evar (l : locs ty); assert (Hle : evalLExps Env le l) by (unfold l; evalLExps); unfold l in *;

        let Hv := fresh "Hv" in let v := fresh "v" in
        evar (v : val); assert (Hv : evalExp Env ix v) by (unfold v; evalExp); unfold v in *;

        let Hn := fresh "Hn" in let n := fresh "n" in
        evar (n : nat); assert (Hn : v = Zn n) by (unfold v, n; solve_zn); unfold n in *;

        let le := eval unfold l in l in
        let i := eval unfold n in n in
        unfold l, v, n in *; clear l v n;
        apply_read_rule' Hle Hv Hn P Res le i

      | [|- CSL _ _ (Assn ?Res ?P ?Env) (writes (?le +os ?ix) ?e) ?Q] =>
        idtac "hoare_forward_prim: match write array case";
          let ty := match type of le with 
                    | lexps ?ty => ty
                    end in
          let Hle := fresh "Hle" in let l := fresh "l" in
          evar (l : locs ty); assert (Hle : evalLExps Env le l) by (unfold l; evalLExps); unfold l in *;
          
          let Hix := fresh "Hix" in let i := fresh "i" in
          evar (i : val); assert (Hix : evalExp Env ix i) by (unfold i; evalExp); unfold i in *;

          let He := fresh "He" in let v := fresh "v" in
          evar (v : vals ty); assert (He : evalExps Env e v) by (unfold v; evalExps); unfold v in *;

          let Hn := fresh "Hn" in let n := fresh "n" in
          evar (n : nat); assert (Hn : i = Zn n) by (unfold i, n; solve_zn); unfold n in *;
  
          let l' := eval unfold l in l in
          let n' := eval unfold n in n in
          unfold l, i, v, n in *; clear l i v n;
          apply_write_rule' Hle Hix He Hn P Res l' n'
      | _ =>
        idtac "hoare_forward_prim': calling hoare_forward_prim";
        hoare_forward_prim
      end
    | false => 
      match goal with _ => idtac end;
      lazymatch goal with
      | [Haok : aenv_ok ?avar_env, Hok : ae_ok _ ?arr ?arr_c |- CSL _ _ ?P (fst (?arr_c _)) ?Q] =>
        applys (>>ae_ok_tri Haok Hok);
          [prove_not_local| eauto with pure_lemma |prove_not_local | evalExp| prove_pure|..]
      | [Haok : aenv_ok ?avar_env, Hok : ae_ok _ ?arr ?arr_c |- CSL _ _ ?P (assigns_get ?xs ?arr_c _) ?Q] =>
        applys (>>ae_assigns Haok Hok); try (now (prove_not_local)); 
        [eauto with pure_lemma | evalExp | solve_zn | prove_pure|..]
      | [Haok : aenv_ok ?avar_env, Hfok : func_ok _ ?f ?f_c |- CSL _ _ ?P (fst (?f_c _)) ?Q] =>
        idtac "ok";
        applys (>>func_ok_tri Haok Hfok); [prove_not_local | prove_not_local | evalExps | eauto with pure_lemma..]
      | _ => hoare_forward_prim
      end
    end
  end.

Lemma merge_var_val R1 R2 P1 P2 E1 E2 x v v' s h:
  sat s h (Assn R1 P1 (x |-> v :: E1) ** Assn R2 P2 E2) ->
  evalExp E2 x v' ->
  sat s h (Assn R1 (v = v' /\ P1) E1 ** Assn R2 P2 E2).
Proof.
  rewrite !Assn_combine.
  intros Hsat ?.
  applys (>>Assn_imply Hsat); jauto.
  intros ?; choose_var_vals.
  intros H'; des_conj H'; repeat split; substs; try now prove_pure.
  unfold sat in Hsat; simpl in Hsat.
  apply (evalExp_app_ig E1) in H.
  forwards*: evalExp_ok; simpl in *.
  destruct Hsat as (? & ? & ? & ?); congruence.
Qed.

Ltac merge_pre H :=
  lazymatch type of H with
  | sat _ _ (Assn _ _ (_ :: _) ** Assn _ _ _) =>
    eapply merge_var_val in H; [|evalExp]; merge_pre H
  | sat _ _ (Assn _ _ nil ** Assn _ _ _) =>
    rewrite Assn_combine in H; simpl in H
  end.

Lemma rule_disj_kinv GA n (avenv : AVarEnv GA ) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA)
      R1 P1 E1 R2 P2 E2 p BS (tid : Fin.t n) C Q :
  CSL BS tid (kernelInv avenv apenv aeenv R1 P1 E1 p) C Q
  -> CSL BS tid (kernelInv avenv apenv aeenv R2 P2 E2 p) C Q
  -> CSL BS tid (kernelDisj avenv apenv aeenv R1 P1 E1 R2 P2 E2 p) C Q.
Proof. apply rule_disj. Qed.

Ltac hoare_forward :=
  lazymatch goal with
  | [|- CSL _ _ (Assn _ _ _ ** Assn _ _ _) _ _] =>
    let H := fresh "H" in
    eapply backward; [intros ? ? H; merge_pre H; apply H|]
  | [|- CSL _ _ ((Ex _, _) ** _) _ _] =>
    idtac "hoare_forward: match ex case";
    lift_ex; hoare_forward
  | [|- CSL _ _ (Disj_assn _ _) _ _] =>
    idtac "hoare_forward: match disj case";
    apply rule_disj
  | [|- CSL _ _ (kernelDisj _ _ _ _ _ _ _ _ _ _) _ _] =>
    idtac "hoare_forward: match disj case";
    apply rule_disj_kinv
  | [|- CSL _ _ (kernelInv _ _ _ _ _ _ _ ** !(_)) _ _] =>
    idtac "hoare_forward: match conditional case";
    eapply cond_prop_kerInv; [evalBExp|]; hoare_forward
  | [|- CSL _ _ (Assn _ _ _ ** !(_)) _ _] =>
    idtac "hoare_forward: match conditional case";
    eapply cond_prop; [evalBExp|]; hoare_forward
  | [|- CSL _ _ ?P (_ ;; _) ?Q ] =>
    idtac "hoare_forward: match seq case";
    eapply rule_seq; [hoare_forward |]; simpl_env
  | [|- CSL _ _ _ _ ?Q] =>
    idtac "hoare_forward: match prim case";
    first [is_evar Q; hoare_forward_prim'; idtac "ok" |
           idtac "hoare_forward: match back case";
           eapply forwardR; [hoare_forward_prim'|]];
    simpl_env
end.

Transparent Ascii.ascii_dec.

Lemma div_spec x y :
  y <> 0 ->
  exists q r,  x / y = q /\ x = y * q + r /\ r < y.
Proof.
  intros; exists (x / y) (x mod y); repeat split; eauto.
  applys* Nat.div_mod.
  eauto using Nat.mod_upper_bound.
Qed.

Lemma Zdiv_spec x y :
  (0%Z < y ->
   exists q r,  (x / y = q /\ x = y * q + r /\ 0 <= r < y))%Z.
Proof.
  intros; exists (x / y)%Z (x mod y)%Z; repeat split; eauto.
  applys* Z.div_mod; lia.
  apply Z_mod_lt; lia.
  apply Z_mod_lt; lia.
Qed.

Ltac elim_div :=
  (repeat rewrite Z.div2_div in *);
  repeat
    (let Heq := fresh in
     match goal with
     | [|- context [?x / ?y]] =>
       forwards*(? & ? & Heq & ? & ?): (>> div_spec x y); rewrite Heq in *; clear Heq
     | [H : context [?x / ?y] |- _] =>
       forwards*(? & ? & Heq & ? & ?): (>> div_spec x y); rewrite Heq in *; clear Heq
     | [|- context [(?x / ?y)%Z]] =>
       forwards*(? & ? & Heq & ? & ?): (>> Zdiv_spec x y); [cbv; auto|rewrite Heq in *; clear Heq]
     | [H : context [(?x / ?y)%Z] |- _] =>
       forwards*(? & ? & Heq & ? & ?): (>> Zdiv_spec x y); [cbv; auto |rewrite Heq in *; clear Heq]
     end).

Ltac div_lia :=
  elim_div; lia.

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
  (forall x v, In (x |-> v) Env -> E x = Lo) ->
  low_assn E (Assn R P Env).
Proof.
  intros HEnv.
  unfold low_assn, Bdiv.low_assn, Bdiv.indeP; simpl.
  unfold low_eq.
  unfold sat in *; simpl; intros; splits; intros; splits; jauto;
  destruct H0 as (_ & _ & HP0);
  induction Env as [|[? ?] ?]; simpl in *; eauto; destruct HP0; split;
  simpl in *; eauto;
  try rewrite <-H; eauto;
  rewrite H; eauto.
Qed.

Lemma low_assn_ex {T : Type} G (P : T -> assn) :
  (forall x, low_assn G (P x)) ->
  low_assn G (Ex x, P x).
Proof.
  unfold sat, low_assn, Bdiv.low_assn, Bdiv.indeP.
  intros Hl s1 s2 h Hlow; simpl.
  split; intros [x H]; exists x; simpl in *.
  - unfold sat in *; rewrite Hl.
    exact H.
    apply Bdiv.low_eq_sym; eauto.
  - unfold sat in *; rewrite Hl.
    exact H.
    eauto.
Qed.

Lemma low_assn_Emp E : low_assn E Emp_assn.
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
  simpl in *; 
  intros ? ? H1;
  repeat rewrite in_app_iff in *;
  des H1; simpl in *; simpl; eauto;
  try now (forwards*: mpss_in; forwards* (? & ? & ?): locals_pref; substs; eauto).

Lemma low_assn_kernelInv E GA (avar_env : AVarEnv GA) aptr_env aeval_env Res P Env p: 
  aenv_ok avar_env
  -> (forall x, prefix "_" (str_of_var x) = true -> E x = Lo)
  -> (forall x v, In (x |-> v) Env -> E x = Lo) 
  -> low_assn E (kernelInv avar_env aptr_env aeval_env Res P Env p).
Proof.
  intros.
  apply low_assn_vars; introv.
  rewrite in_app_iff; destruct 1 as [Hin | Hin]; eauto.
  destruct H.
  forwards* (? & ? & [? | ?]): arrInvVar_in; substs.
  forwards*: H.
  Grab Existential Variables.
  eauto.
Qed.

Ltac prove_is_param :=
  introv;
  match goal with
  | [|- prefix "_" ?X = true -> _ ] =>
    destruct (prefix "_" X); congruence
  end.

Ltac prove_low_assn :=
  lazymatch goal with
  | [|- low_assn _ (Ex _ : _, _) ] =>
    apply low_assn_ex; intros ?; prove_low_assn
  | [|- low_assn _ (Assn _ _ _)] =>
    apply low_assn_vars; prove_low_expr
  | [|- low_assn _ (kernelInv _ _ _ _ _ _ _) ] =>
    applys* low_assn_kernelInv; [try prove_is_param | prove_low_expr]
  | [|- low_assn _ (kernelInv' _ _ _ _ _) ] =>
    applys* low_assn_vars; simpl in *; tauto
  | [|- low_assn _ Emp_assn] =>
    apply low_assn_Emp
  end.

Notation nf tid := (nat_of_fin tid).

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
      CSL BS tid (Vector.nth Ps tid ** Assn Emp True ("tid" |-> Zn (nf tid) :: nil)) c
          (Vector.nth Qs tid)) -> CSLp n E P c Q.
Proof.
  intros; eapply rule_par; eauto.
  destruct n; try omega; eauto.
Qed.

Lemma rule_conseq (n : nat)
  (bspec : nat -> Vector.t assn n * Vector.t assn n)
  (tid : Fin.t n) (P : assn) (C : cmd) (Q P' Q' : assn) :
  CSL bspec tid P C Q -> P' |= P -> Q |= Q' -> CSL bspec tid P' C Q'.
Proof.
  intros; eapply rule_conseq; eauto.
Qed.

Lemma assn_var_in Res P Env (x : var) (v : val) :
  (Assn Res P Env ** Assn Emp True (x |-> v :: nil)) == (Assn Res P (x |-> v :: Env)).
Proof.
  rewrite Assn_combine; split; revert s h; prove_imp.
  simpl in *; tauto.
Qed.

Lemma kernelInv_var_in GA (avE : AVarEnv GA) apE aeE Res P Env (x : var) (v : val) p:
  (kernelInv avE apE aeE Res P Env p ** (Assn Emp True (x |-> v :: nil))) ==
  (kernelInv avE apE aeE Res P (x |-> v :: Env) p).
Proof.
  unfold kernelInv.
  apply assn_var_in.
Qed.

Lemma conj_xs_assn st n Res P Env :
  n <> 0 ->
  conj_xs (ls_init st n (fun i => Assn (Res i) P Env)) ==
  Assn (istar (ls_init st n (fun i => Res i))) P Env.
Proof.
  intros Hn0.
  revert st; induction n; simpl; try (intros; omega).
  intros st; destruct n.
  - simpl in *. 
    rewrite sep_emp_r_unit.
    split; intros Hsat; clear IHn; revert s h Hsat; prove_imp.
  - rewrite IHn; try omega.
    rewrite Assn_combine.
    intros s h; split; clear IHn; revert s h; prove_imp.
Qed.

Lemma sc_v2l n (assns : Vector.t assn n) :
  Bdiv.Aistar_v assns == conj_xs (Vector.to_list assns).
Proof.
  dependent induction assns; intros s; simpl; [reflexivity|].
  fold (Vector.to_list assns).
  introv; rewrite IHassns; reflexivity.
Qed.

Lemma nth_nseq :
  forall (T : Type) (x0 : T) (m : nat) (x : T) (n : nat),
    nth n (nseq m x) x0 = (if leb m n then x0 else x).
Proof.
  induction m; intros; simpl; eauto.
  - destruct n; simpl; eauto.
  - destruct n; eauto.
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
  Lemma conj_xs_assn_env Res P Env s h n :
    forall st, sat s h (conj_xs (ls_init st n (fun i => Assn (Res i) (P i) (Env i)))) ->
    forall i, st <= i < st + n -> env_assns_denote (Env i) s.
  Proof.
    revert h; induction n; simpl; [intros; omega|].
    introv (? & ? & ? & ? & ? & ?).
    intros.
    assert (i = st \/ S st <= i < S st + n) as [|] by omega; [substs; simpl in H; jauto|]. 
    forwards*: IHn.
  Qed.
  intros; lets*: (>>conj_xs_assn_env __ __ __ __ __ __ __ __).
  assert (forall i, i < n -> Zn (v i) = s x).
  { intros; forwards*: (H0 i); forwards*: (H1 i); try omega.
    forwards*: evalExp_ok. }
  exists (Z.to_nat (s x)); intros.
  rewrite <-(H2 i); try omega.
  rewrite* Nat2Z.id.
Qed.

Lemma ls_init_eq (T : Type) (fc fc' : nat -> T) n: forall s s',
  (forall i, i < n -> fc (s + i) = fc' (s' + s + i)) -> 
  ls_init s n fc = ls_init (s' + s) n fc'.
Proof.
  induction n; simpl; intros s s' H; auto.
  cutrewrite (s' + s = s' + s + 0); [|omega].
  rewrite <-H; f_equal; (omega || auto).
  cutrewrite (S (s' + s + 0) = s' + S s); [apply IHn|omega].
  intros i Hi.
  cutrewrite (S s + i = s + S i); [|omega].
  cutrewrite (s' + S s + i = s' + s + S i); [|omega].
  apply H; omega.
Qed.

Lemma ls_init_eq0 (T : Type) (n : nat) (fc fc' : nat -> T) :
  (forall i, i < n -> fc i = fc' i) ->
  ls_init 0 n fc = ls_init 0 n fc'.
Proof.
  intros; rewrite (@ls_init_eq _ _ fc' n 0 0); auto.
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

Lemma ls_exists (T : Type) (d : T) (n : nat) (P : T -> nat -> assn) : 
  forall b,
    conj_xs (ls_init b n (fun i => Ex x : T, P x i)) ==
    Ex vs : list T, (Assn Emp (length vs = n) nil) ** conj_xs (ls_init b n (fun i => P (nth (i - b) vs d) i)).
Proof.
  induction n as [|n]; simpl; intros b s h; try omega.
  - rewrite ex_sat.
    split.
    + intros; exists (@nil T); rewrite sat_pure_l; splits; simpl; jauto.
    + intros [? Hsat]; rewrite sat_pure_l in Hsat; jauto.
  - rewrite !ex_sat.
    split; intros Hsat.
    + rewrite ex_lift_r, ex_sat in Hsat; destruct Hsat as [x Hsat].
      rewrite IHn in Hsat.
      rewrite sep_comm, ex_lift_r, ex_sat in Hsat; destruct Hsat as [vs Hsat].
      rewrite <-sep_assoc, sat_pure_l in Hsat; destruct Hsat as [Hsat ?].
      exists (x :: vs); rewrite sat_pure_l in *; split; [|simpl; jauto].
      rewrite minus_diag.
      erewrite ls_init_eq'; [rewrite sep_comm; apply Hsat|].
      intros.
      cutrewrite (S b + i - b = S i); [|omega].
      cutrewrite (S b + i - S b = i); [|omega].
      eauto.
    + destruct Hsat as [vs Hsat].
      rewrite sat_pure_l in Hsat; destruct Hsat as [Hsat ?].
      rewrite minus_diag in Hsat.
      destruct vs as [| v vs]; [simpl in *; try omega|].
      rewrite ex_lift_r, ex_sat.
      exists v.
      rewrite IHn, sep_comm, ex_lift_r, ex_sat.
      exists vs.
      rewrite <-sep_assoc, sat_pure_l; splits; jauto.
      erewrite ls_init_eq'; [rewrite sep_comm; apply Hsat|].
      intros.
      cutrewrite (S b + i - S b = i); [|omega].
      cutrewrite (S b + i - b = S i); [|omega].
      eauto.
Qed.

Lemma ex_eq T P Q :
  (forall x, P x == Q x)
  -> (Ex x : T, P x) == (Ex x, Q x).
Proof.
  intros Heq; split; rewrite !ex_sat; intros [x ?]; exists x; rewrites* Heq in *.
Qed.

Lemma ls_exists0 {T : Type} (d : T) {n : nat} (P : T -> nat -> assn) : 
  conj_xs (ls_init 0 n (fun i => Ex x : T, P x i)) ==
  Ex vs : list T, (Assn Emp (length vs = n) nil) ** conj_xs (ls_init 0 n (fun i => P (nth i vs d) i)).
Proof.
  intros.
  rewrite ls_exists.
  apply ex_eq; introv.
  erewrite (ls_init_eq0 _ n (fun i => P (nth i x d) i)); [reflexivity|].
  intros; simpl; rewrite Nat.sub_0_r; eauto.
Qed.

Ltac default T :=
  lazymatch T with
    | nat => constr:(0)
    | Z => constr:(0%Z)
    | ?T1 -> ?T2 => let t := default T2 in constr:(fun _ : T1 => t)
  end.

Ltac dest_ex_in acc H :=
  match goal with _ => idtac end;
  lazymatch type of H with
  | sat _ _ (conj_xs (ls_init 0 ?n (fun i => Ex t : ?T, @?P i t))) =>
    let d := default T in
    rewrite (ls_exists0 d), ex_sat in H; destruct H as [t H];
    rewrite sat_pure_l in H; destruct H as [H ?];
    fold_sat_in H; dest_ex_in (t, acc) H
  | sat _ _ (conj_xs (ls_init 0 ?n (fun i => Assn (@?Res i) (@?P i) (@?Env i)))) =>
    find_const acc H
  | sat _ _ (conj_xs (ls_init 0 ?n (fun i => kernelInv _ _ _ (@?Res i) (@?P i) (@?Env i) _))) =>
    find_const acc H
  | sat _ _ (conj_xs (ls_init 0 ?n (fun i => kernelInv' _ _ (@?Res i) (@?P i)  _))) =>
    find_const acc H
  end.

Lemma length_nseq : forall (T : Type) (n : nat) (x : T), length (nseq n x) = n.
Proof.
  intros; induction n; simpl; omega.
Qed.

Ltac dest_ex :=
  repeat (lazymatch goal with
  | [|- sat _ _ (conj_xs (ls_init 0 ?n (fun i => Ex x : ?T, @?P i x)))] =>
    let x := fresh "x" in
    evar (x : T);
    rewrite (ls_exists0 x), ex_sat; 
    eexists (nseq n x); unfold x;
    rewrite sat_pure_l; split;
    [|rewrite length_nseq; reflexivity]; fold_sat;
    erewrite @ls_init_eq0; [|intros; rewrite nseq_nth_same; reflexivity]
  end).

Lemma arrInvRes_star GA (apenv : APtrEnv GA) aeenv p st n :
  (0 < p)%Qc ->
  (injZ (Zn n) * p <= 1)%Qc ->
  (p <= 1)%Qc ->
  n <> 0 ->
  istar (ls_init st n (fun _ => arrInvRes apenv aeenv p)) ==
  arrInvRes apenv aeenv (p * injZ (Zn n)).
Proof.
  unfold arrInvRes; intros.
  induction GA; dependent destruction apenv; dependent destruction aeenv; simpl.
  rewrite init_emp_emp_res; reflexivity.
  rewrite ls_star_res, IHGA.
  rewrite <-arrays_p_n; eauto.
  rewrite Qcmult_comm in *; reflexivity.
Qed.

Notation RP n := (1 / injZ (Zn n))%Qc.

Lemma conj_xs_kernelInv st n GA (avenv : AVarEnv GA) apenv aeenv Res P Env m:
  n <> 0 ->
  m <> 0 ->
  n <= m ->
  conj_xs (ls_init st n (fun i => kernelInv avenv apenv aeenv (Res i) P Env (RP m))) ==
  kernelInv avenv apenv aeenv (istar (ls_init st n Res)) P Env (RP m * injZ (Zn n)).
Proof.
  intros.
  assert (0 < injZ (Zn m))%Qc. 
  { injZ_simplify. Qc_to_Q.
    destruct m; try lia.
    forwards*: (>>inject_Z_Sn_gt0 m); simpl in *; lra. }
  assert (0 < RP m)%Qc.
  { Qc_to_Q.
    Require Import QArith.
    apply Qlt_shift_div_l; lra. }
  assert (injZ (Zn n) * RP m <= 1)%Qc.
  { assert (injZ (Zn n) <= injZ (Zn m))%Qc.
    { unfold injZ; Qc_to_Q.
      rewrite <-Zle_Qle; lia. }
    Qc_to_Q.
    rewrite Qmult_assoc.
    apply Qle_shift_div_r. eauto.
    lra. }
  assert (RP m <= 1).
  { unfold injZ in *; Qc_to_Q.
    apply Qle_shift_div_r.
    lra.
    destruct m; try lia.
    lets: (>>inject_Z_Sn_gt0 m).
    lra. }
  intros; unfold kernelInv; rewrites* conj_xs_assn.
  split; revert s h; prove_imp; rewrite ls_star_res, arrInvRes_star in *; eauto.
Qed.

Close Scope Q_scope.

Lemma conj_xs_kernelInv' st n GA (apenv : APtrEnv GA) aeenv Res P m:
  n <> 0 ->
  m <> 0 ->
  n <= m ->
  conj_xs (ls_init st n (fun i => kernelInv' apenv aeenv (Res i) P (RP m))) ==
  kernelInv' apenv aeenv (istar (ls_init st n Res)) P (RP m * injZ (Zn n)).
Proof.
  intros.
  assert (0 < injZ (Zn m))%Qc. 
  { injZ_simplify. Qc_to_Q.
    destruct m; try lia.
    forwards*: (>>inject_Z_Sn_gt0 m); simpl in *; lra. }
  assert (0 < RP m)%Qc.
  { Qc_to_Q.
    Require Import QArith.
    apply Qlt_shift_div_l; lra. }
  assert (injZ (Zn n) * RP m <= 1)%Qc.
  { assert (injZ (Zn n) <= injZ (Zn m))%Qc.
    { unfold injZ; Qc_to_Q.
      rewrite <-Zle_Qle; lia. }
    Qc_to_Q.
    rewrite Qmult_assoc.
    apply Qle_shift_div_r. eauto.
    lra. }
  assert (RP m <= 1)%Qc.
  { unfold injZ in *; Qc_to_Q.
    apply Qle_shift_div_r.
    lra.
    destruct m; try lia.
    lets: (>>inject_Z_Sn_gt0 m).
    lra. }
  intros; unfold kernelInv'; rewrites* conj_xs_assn.
  split; revert s h; prove_imp; rewrite ls_star_res, arrInvRes_star in *; eauto.
Qed.

Lemma Fin_nat_inv (n : nat) (t : Fin.t n) : forall i,
  Fin.of_nat i n = inleft t -> ` (Fin.to_nat t) = i.
Proof.
  induction n; [inversion t|].
  destruct i; simpl; [inversion 1; reflexivity|].
  destruct (Fin.of_nat i n) eqn:Heq.
  apply IHn in Heq.
  inversion 1; subst; simpl; destruct (Fin.to_nat); auto.
  inversion 1.
Qed.

Lemma vec_to_list_init {T : Type} (n : nat) (fc : Fin.t n -> T) (d : T) : forall s,
  Vector.to_list (MyVector.init fc) = 
  ls_init s n (fun i => match Fin.of_nat (i - s) n with
                          | inleft idx => fc idx
                          | _ => d
                        end).
Proof.
  induction n; [reflexivity|].
  simpl; unfold ls_init, Vector.to_list; simpl; intros s.
  f_equal; [rewrite minus_diag; reflexivity|].
  
  fold (Vector.to_list (MyVector.init (fun i => fc (Fin.FS i)))); rewrite (IHn _ s).
  fold (@ls_init T (S s) n).
  cutrewrite (S s = 1 + s); [apply ls_init_eq|]; auto; intros i.
  cutrewrite (s + i - s = i); [|omega].
  cutrewrite (1 + s + i - s = S i); [|omega].
  intros H.
  simpl; destruct Fin.of_nat; reflexivity.
Qed.

Lemma vec_to_list_init0 {T : Type} (n : nat) (fc : Fin.t n -> T) (d : T) :
  Vector.to_list (MyVector.init fc) = 
  ls_init 0 n (fun i => match Fin.of_nat i n with
                          | inleft idx => fc idx
                          | _ => d
                        end).
Proof.
  rewrite (@vec_to_list_init _ _ _ d 0); f_equal; extensionality x.
  destruct (minus_n_O x); (omega || auto).
Qed.  

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
    rewrite sc_v2l, (vec_to_list_init0 _ Emp_assn) in H;
    erewrite ls_init_eq0 in H; [|simplify];
    dest_ex_in tt H;
    try rewrite conj_xs_assn in H;
    try (rewrite conj_xs_kernelInv in H; intros; try nia);
    try (rewrite conj_xs_kernelInv' in H; intros; try nia); auto
  end;
  try lazymatch goal with
  | [|- sat _ _ (Bdiv.Aistar_v (MyVector.init _)) ] =>
    rewrite sc_v2l, (vec_to_list_init0 _ Emp_assn);
    erewrite ls_init_eq0; [|simplify];
    dest_ex;
    try rewrite conj_xs_assn;
    try (rewrite conj_xs_kernelInv; intros; try nia);
    try (rewrite conj_xs_kernelInv'; intros; try nia);
    auto
  end;
  revert s h H; unfold kernelInv; try prove_imp.

Ltac ls_rewrite_in Heq H :=
  erewrite ls_init_eq0 in H; [|intros; rewrite Heq; reflexivity].

Lemma ty_var' g v ty :
  g v = ty -> typing_exp g v ty.
Proof.
  intros; constructor; rewrite H; destruct ty; eauto.
Qed.

Ltac prove_typing_exp :=
  lazymatch goal with
  | |- typing_exp ?E (Evar ?v) _ => apply ty_var'; simpl; eauto
  | |- typing_exp ?E (Enum _) _ => apply (ty_num _ _ Lo)
  | |- typing_exp ?E (Ebinop _ ?e1 ?e2) _ => constructor; prove_typing_exp
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
  | |- typing_bexp _ (Bcomp _ _ _) _ =>
    constructor; prove_typing_exp; simpl
  | |- typing_bexp _ (Bunary _ _) _ =>
    idtac "A";
    constructor; prove_typing_bexp
  | |- typing_lexp _ (Bbool _ _ _) _ =>
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

Lemma prefix_not_eq x y s :
  prefix x s = true -> prefix x y = false -> prefix y x = false -> prefix y s = false.
Proof.
  revert y s; induction x; introv.
  rewrite !prefix_nil; simpl; congruence.
  destruct s; simpl; try congruence.
  destruct Ascii.ascii_dec; try congruence.
  destruct y; simpl; try congruence.
  repeat lazymatch goal with |- context [if ?b then _ else _] => destruct b end; try congruence.
  eauto.
Qed.

Lemma arr_ok_no_barrier ty GA (avar_env : AVarEnv GA) (arr : Skel.AE GA ty) arr_c :
  aenv_ok avar_env
  -> ae_ok avar_env arr arr_c
  -> forall x, barriers (fst (arr_c x)) = nil.
Proof.
  unfold ae_ok; intros ? H; destruct H as (? & ? & ? & ?); eauto.
Qed.

Lemma func_ok_no_barrier1 dom cod GA (avar_env : AVarEnv GA) (func : Skel.Func GA (Skel.Fun1 dom cod)) func_c :
  aenv_ok avar_env
  -> func_ok avar_env func func_c
  -> forall x, barriers (fst (func_c x)) = nil.
Proof.
  unfold func_ok; intros ? H; destruct H as (? & ? & ? & ?); eauto.
Qed.

Lemma func_ok_no_barrier2 dom1 dom2 cod GA (avar_env : AVarEnv GA) (func : Skel.Func GA (Skel.Fun2 dom1 dom2 cod)) func_c :
  aenv_ok avar_env
  -> func_ok avar_env func func_c
  -> forall x y, barriers (fst (func_c x y)) = nil.
Proof.
  unfold func_ok; intros ? H; destruct H as (? & ? & ? & ?); eauto.
Qed.

Create HintDb typing.

Hint Resolve arr_ok_no_barrier func_ok_no_barrier1 func_ok_no_barrier2 : typing.

Lemma assigns_no_barriers ty (xs : vars ty) (ts : ctys ty) (es : exps ty) :
  barriers (assigns xs ts es) = nil.
Proof. induction ty; simpl; eauto; rewrite IHty1, IHty2; simpl; eauto. Qed.

Lemma assigns_get_no_barriers GA ty (avar_env : AVarEnv GA) (arr : Skel.AE GA ty)
      arr_c (xs : vars ty) :
  aenv_ok avar_env
  -> ae_ok avar_env arr arr_c
  -> forall x, barriers (assigns_get xs arr_c x) = nil.
Proof. 
  unfold assigns_get; intros; simpl; erewrite assigns_no_barriers, arr_ok_no_barrier; eauto.
Qed.

Lemma reads_no_barriers ty (xs : vars ty) (ts : ctys ty) (es : lexps ty) :
  barriers (reads xs ts es) = nil.
Proof. induction ty; simpl; eauto; rewrite IHty1, IHty2; simpl; eauto. Qed.

Lemma writes_no_barriers ty (les : lexps ty) (es : exps ty) :
  barriers (writes les es) = nil.
Proof. induction ty; simpl; eauto; rewrite IHty1, IHty2; simpl; eauto. Qed.

Hint Resolve
     assigns_no_barriers
     assigns_get_no_barriers
     reads_no_barriers
     writes_no_barriers : typing.

Lemma arr_ok_writes_var ty GA (avar_env : AVarEnv GA) (arr : Skel.AE GA ty) arr_c :
  aenv_ok avar_env
  -> ae_ok avar_env arr arr_c
  -> forall x y, In y (writes_var (fst (arr_c x))) -> is_local y.
Proof.
  unfold ae_ok; intros ? H; destruct H as (? & ? & ? & ?); intros; eauto.
Qed.

Lemma func_ok_writes_var1 dom cod GA (avar_env : AVarEnv GA) (func : Skel.Func GA (Skel.Fun1 dom cod)) func_c :
  aenv_ok avar_env
  -> func_ok avar_env func func_c
  -> forall x y, In y (writes_var (fst (func_c x))) -> is_local y.
Proof.
  unfold func_ok; intros ? H; destruct H as (? & ? & ? & ?); eauto.
Qed.

Lemma func_ok_writes_var2 dom1 dom2 cod GA (avar_env : AVarEnv GA) (func : Skel.Func GA (Skel.Fun2 dom1 dom2 cod)) func_c :
  aenv_ok avar_env
  -> func_ok avar_env func func_c
  -> forall x y z, In z (writes_var (fst (func_c x y))) -> is_local z.
Proof.
  unfold func_ok; intros ? H; destruct H as (? & ? & ? & ?); eauto.
Qed.

Hint Rewrite arr_ok_writes_var func_ok_writes_var1 func_ok_writes_var2 reads_writes assigns_writes writes_writes : typing.

Ltac prove_has_Hi :=
  introv; 
  let Hf := fresh "H" in
  let Hx := fresh "H" in
  lazymatch goal with
  | [H : ae_ok _ _ ?f |- In _ (writes_var (fst (?f _))) -> _ ] =>
    intros Hf; forwards*Hx: arr_ok_writes_var; unfold is_local in *
  | [H : func_ok _ _ ?f |- In _ (writes_var (fst (?f _))) -> _ ] =>
    intros Hf; forwards*Hx: func_ok_writes_var1; unfold is_local in *
  | [H : func_ok _ _ ?f |- In _ (writes_var (fst (?f _ _))) -> _ ] =>
    intros Hf; forwards*Hx: func_ok_writes_var2; unfold is_local in *
  | [|- In _ (flatTup (locals _ _ _)) -> _] => 
    intros Hf; forwards* (? & ? & ?): (>>locals_pref Hf); substs; eauto
  end;
   repeat lazymatch goal with
  | [|- (if prefix ?X ?Y then _ else _) = Hi] =>
    cutrewrite (prefix X Y = false); [|(applys* (>>prefix_not_eq Hx))]
  | [|- (if var_eq_dec ?X ?Y then _ else _) = Hi] => 
    destruct var_eq_dec; [substs; simpl in *; congruence|]
  end; eauto.

Hint Constructors typing_exp typing_lexp typing_bexp typing_cmd.

Lemma typing_exp_Hi E (e : exp) : typing_exp E e Hi.
Proof.
  induction e; eauto; equates 1; eauto.
  apply ty_var; destruct (E x); eauto.
Qed.

Hint Resolve typing_exp_Hi.

Lemma typing_bexp_Hi E (e : bexp) : typing_bexp E e Hi.
Proof.
  induction e; eauto; equates 1; eauto.
Qed.  

Lemma typing_lexp_Hi E (e : loc_exp) : typing_lexp E e Hi.
Proof.
  induction e; try destruct p; eauto; equates 1; eauto.
Qed.  

Hint Resolve typing_bexp_Hi typing_lexp_Hi.

Lemma typing_cmd_Hi E (c : cmd) :
  barriers c = nil ->
  (forall v, List.In v (writes_var c) -> E v = Hi) ->
  typing_cmd E c Hi.
Proof.
  induction c; intros; eauto; equates 1; eauto.
  - equates 1; [econstructor; eauto|].
    rewrite H0; simpl; eauto.
    eauto.
  - equates 1; [econstructor; eauto|].
    rewrite H0; simpl; eauto.
    reflexivity.
  - simpl in H.
    assert (barriers c1 = nil).
    { destruct (barriers c1); simpl in *;  congruence. }
    assert (barriers c2 = nil).
    { rewrite H1 in H; eauto. }
    assert (forall v, In v (writes_var c1) -> E v = Hi).
    { intros; apply H0; simpl; rewrite in_app_iff; eauto. }
    assert (forall v, In v (writes_var c2) -> E v = Hi).
    { intros; apply H0; simpl; rewrite in_app_iff; eauto. }
    equates 1; [econstructor; eauto|eauto].
  - simpl in *; econstructor; eauto.
    apply IHc1.
    destruct barriers; simpl in *; congruence.
    intros; apply H0; rewrite in_app_iff; eauto.
    apply IHc2.
    destruct barriers; simpl in *; congruence.
    intros; apply H0; rewrite in_app_iff; eauto.
  - simpl in H; congruence.
Qed.

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
  | _ => try (apply typing_cmd_Hi; [eauto with typing| repeat autorewrite with typing; try (simpl; tauto); try prove_has_Hi ])
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
  unfold sat in H; simpl in H.
  forwards*: (>>evalExp_ok).
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

Lemma CSLp_backward (P' P : assn) n E C Q : 
  CSLp n E P C Q -> (P' |= P) -> CSLp n E P' C Q.
Proof.
  unfold CSLp; intros Hcsl Hp; intros.
  forwards: (Hcsl ks h leqks); eauto. 
  unfold sat_k in *.
  destruct low_eq_repr; eauto.
Qed.  

Lemma safe_gl_forward n m E ks h (Q Q' : assn) : 
  @safe_nk n E m ks h Q -> 
  (Q |= Q') ->
  @safe_nk n E m ks h Q'.
Proof.
  revert h ks; induction m; simpl; intros h ks Hsafe Hq; eauto.
  simpl in Hsafe; destructs Hsafe.
  repeat split; auto.
  - intros; unfold sat_k in *.
    forwards [x ?]: H; eauto.
    exists x.
    destruct low_eq_repr; apply Hq; eauto.
  - forwards: H2; jauto.
  - forwards: H2; jauto.
  - intros; forwards: H3; eauto.
    destruct H7 as (ph'' & ? & ? & ?); exists ph''; repeat split; eauto.
Qed.  

Lemma CSLp_forward P n E C (Q Q' : assn) : 
  CSLp n E P C Q -> (Q |= Q') -> CSLp n E P C Q'.
Proof.
  unfold CSLp; intros; applys safe_gl_forward; eauto.
Qed.

Lemma rule_p_conseq (P P' : assn) (n : nat) (E : env) (C : cmd) (Q Q' : assn) :
  CSLp n E P C Q -> P' |= P -> Q |= Q' -> CSLp n E P' C Q'.
Proof.
  intros.
  eapply CSLp_backward; [eapply CSLp_forward|]; eauto.
Qed.

Lemma rule_p_backward (P P' : assn) (n : nat) (E : env) (C : cmd) (Q : assn) :
  CSLp n E P C Q -> P' |= P -> CSLp n E P' C Q.
Proof.
  intros.
  eapply CSLp_backward; [eapply CSLp_forward|]; eauto.
Qed.

Lemma rule_p_forward (P : assn) (n : nat) (E : env) (C : cmd) (Q Q' : assn) :
  CSLp n E P C Q -> Q |= Q' -> CSLp n E P C Q'.
Proof.
  intros.
  eapply CSLp_backward; [eapply CSLp_forward|]; eauto.
Qed.

Fixpoint sh_spec_env sdecs locs :=
  match sdecs, locs with
  | SD x _ len :: sdecs, l :: locs =>
    x |-> l :: sh_spec_env sdecs locs
  | _, _ => nil
  end.

Fixpoint sh_spec_res sdecs locs vals :=
  match sdecs, locs, vals with
  | SD x _ len :: sdecs, l :: locs, vs :: vals =>
    array (SLoc l) vs 1 *** sh_spec_res sdecs locs vals
  | _, _, _ => Emp
  end.

Fixpoint sh_spec_pure sdecs (vals : list (list val)) :=
  match sdecs, vals with
  | SD x _ len :: sdecs, vs :: vals =>
    length vs = len /\ sh_spec_pure sdecs vals
  | _, _ => True
  end.

Definition sh_spec_assn sdecs locs vals :=
  Assn (sh_spec_res sdecs locs vals)
       (sh_spec_pure sdecs vals)
       (sh_spec_env sdecs locs).

Definition sh_spec_assn' sdecs locs vals :=
  Assn (sh_spec_res sdecs locs vals)
       (sh_spec_pure sdecs vals)
       (nil).

Definition sh_ok (sdecs : list Sdecl) (locs : list Z) (vals : list (list val)) :=
  Assn Emp (length sdecs = length locs /\ length sdecs = length vals) nil.

Lemma array_is_array' loc len vs f s :
  length vs = len ->
  (forall i, i < len -> nth i vs 0%Z = f (s + i)) ->
  (array (SLoc loc) vs 1) == (array (SLoc loc) (ls_init s len f) 1).
Proof.
  revert loc len s; induction vs; intros loc [|len] s Hlen Heq; simpl in *; try omega.
  reflexivity.
  cutrewrite (loc + Zn s + 1 = loc + Zn (s + 1))%Z; [|rewrite Nat2Z.inj_add; lia].
  rewrites* (>>IHvs len (s + 1)); try lia.
  intros; forwards*Heq': (Heq (S i)); [lia|].
  rewrite Heq'; f_equal; lia.
  cutrewrite (S s = s +1); [apply* res_star_proper; [|reflexivity]|lia].
  assert (Heq' : a = f s); [|rewrite Heq'; clear Heq'].
  { forwards*: (Heq 0); [lia|].
    rewrite H; f_equal; lia. }
  reflexivity.
Qed.

Lemma array_is_array loc len vs f :
  length vs = len ->
  (forall i, i < len -> nth i vs 0%Z = f i) ->
  (array (SLoc loc) vs 1) == (array (SLoc loc) (ls_init 0 len f) 1).
Proof.
  intros; 
  forwards*: (>>array_is_array' loc len vs f 0); eauto.
Qed.

Lemma sh_spec_assn_ok sdecs locs :
  (Ex vals, (sh_ok sdecs locs vals) ** sh_spec_assn sdecs locs vals) == sh_inv sdecs locs.
Proof.
  unfold sh_spec_assn, sh_inv, sh_ok, Grid.sh_ok; revert locs; induction sdecs as [|[? ? ?] ?].
  - introv; simpl; unfold equiv_sep; introv.
    rewrite !ex_sat; split; intros [[|vs vals] Hsat];
    rewrite sat_pure_l in Hsat; unfold sat in Hsat; simpl in *; try omega;
    try exists (@nil (list val)); try exists (@nil sh_val); rewrite sat_pure_l; splits; jauto.
    unfold sat; simpl; splits; jauto.
  - introv; simpl; unfold equiv_sep; introv.
    rewrite !ex_sat; split; intros [[|vs vals] Hsat];
    destruct locs as [|l locs];
    rewrite sat_pure_l in Hsat; try now (unfold sat in Hsat; simpl in *; try omega);
    try exists (@nil (list val)); try exists (@nil sh_val); rewrite sat_pure_l; splits; jauto.
                                             simpl in *.
    destruct Hsat as (Hsat & ? & ? & ?).
    apply Assn_split in Hsat.
    destruct Hsat as (h1 & h2 & Hsat1 & Hsat2 & ?); eauto; fold_sat_in Hsat1; fold_sat_in Hsat2.
    forwards* [IH1 _]: (IHsdecs locs s h1).
    forwards* [sh_vals' [Hlen' IH1']]: IH1.
    { exists vals; unfold Apure; split; [omega|].
      unfold Apure in *; sep_split; try tauto; destruct HP0; eauto. }
    exists ((fun i => nth i vs 0%Z) :: sh_vals').
    destruct HP0.
    split; simpl; [unfold Apure in *; lia| sep_split; eauto].
    exists h1 h2; repeat split; try tauto.

    fold_sat.
    rewrite <-array_is_array; destruct HP; eauto.
  - destruct Hsat as (h1 & h2 & ? & ? & ?); eauto.
    forwards* [IH1 IH2]: (IHsdecs locs).
    forwards* [vss' [Hlen' IH2']]: IH2.
    { exists vals; unfold Apure; split; [omega|]; eauto. }
    exists ((ls_init 0 SD_len vs) :: vss').
    sep_split_in IH2'.
    split; simpl; [unfold Apure in *; lia..| sep_split; eauto].
    unfold Apure in *; rewrite init_length; try tauto.
    split; eauto.
    exists h1 h2; repeat split; try tauto.
    fold_sat.
    rewrite array_is_array; destruct HP; eauto.
    rewrite init_length; omega.
    intros; rewrite ls_init_spec; destruct lt_dec; eauto; omega.
Qed.

Lemma sh_spec_assn'_ok sdecs locs :
  (Ex vals, sh_ok sdecs locs vals //\\ sh_spec_assn' sdecs locs vals) == sh_inv' sdecs locs.
Proof.
  unfold sh_spec_assn', sh_inv', sh_ok, Grid.sh_ok; revert locs; induction sdecs as [|[? ? ?] ?];
  intros [|l locs]; split; intros [[|vs vals] [Hlen Hsat]]; unfold Apure in Hlen; simpl in *;
  try omega; unfold Assn in *; simpl in *; sep_split_in Hsat.
  - exists (@nil sh_val); split; eauto.
  - exists (@nil (list val)); split; sep_split; eauto using emp_emp_ph.
    unfold Apure; eauto.
  - destruct Hsat as (h1 & h2 & ? & ? & ?); eauto.
    forwards* [IH1 IH2]: (IHsdecs locs).
    forwards* [sh_vals' [Hlen' IH1']]: IH1.
    { exists vals; unfold Apure; split; [omega|].
      unfold Apure in *; sep_split; try tauto; eauto. }
    exists ((fun i => nth i vs 0%Z) :: sh_vals').
    split; simpl; [unfold Apure in *; lia| sep_split; eauto].
    exists h1 h2; repeat split; try tauto.

    fold_sat.
    rewrite <-array_is_array; destruct HP; eauto.
  - destruct Hsat as (h1 & h2 & ? & ? & ?); eauto.
    forwards* [IH1 IH2]: (IHsdecs locs).
    forwards* [vss' [Hlen' IH2']]: IH2.
    { exists vals; unfold Apure; split; [omega|]; eauto. }
    exists ((ls_init 0 SD_len vs) :: vss').
    sep_split_in IH2'.
    split; simpl; [unfold Apure in *; lia..| sep_split; eauto].
    unfold Apure in *; rewrite init_length; try tauto.
    exists h1 h2; repeat split; try tauto.
    fold_sat.
    rewrite array_is_array; eauto.
    rewrite init_length; omega.
    intros; rewrite ls_init_spec; destruct lt_dec; eauto; omega.
Qed.

Lemma ex_lift_l T P Q :
  (P ** (Ex x : T, Q x)) == (Ex x : T, P ** Q x).
Proof.
  intros s h; split; intros H.
  - destruct H as (? & ? & ? & [? ?] & ? & ?).
    do 3 eexists; repeat split; eauto.
  - destruct H as (? & ? & ? & ? & ? & ? & ?).
    do 2 eexists; repeat split; eauto.
    eexists; eauto.
Qed.

Lemma CSLp_preprocess n E Res Res' P P' Env Env' C sdecs locs bid :
  (forall vss,
      length sdecs = length locs ->
      length sdecs = length vss ->
      CSLp n E 
       ((Assn Res P ("bid" |-> bid :: Env)) ** sh_spec_assn sdecs locs vss)
       C
       (Ex vss, pure (length vss = length sdecs) //\\ (Assn Res' P' Env') ** sh_spec_assn' sdecs locs vss))
  -> CSLp n E 
       ((Assn Res P Env) ** sh_inv sdecs locs ** !("bid" === bid))
       C
       ((Assn Res' P' Env') ** sh_inv' sdecs locs).
Proof.
  intros.
  applys (>>rule_p_backward (Ex vss, sh_ok sdecs locs vss //\\ (Assn Res P ("bid" |-> bid :: Env) ** sh_spec_assn sdecs locs vss))).
  Focus 2.
  { unfold sat; intros ? ? Hsat; sep_split_in Hsat.
    fold_sat_in Hsat.
    rewrite <-sh_spec_assn_ok in Hsat.
    apply ex_lift_r_in in Hsat as [vss Hsat].
    destruct Hsat as (h1 & h2  & ? & (? & ?) & ? & ?); unfold sh_ok in *; eauto.
    exists vss; split; eauto.
    apply scC; sep_cancel.
    fold_sat; rewrite <-assn_var_in.
    exists h2 h1; repeat split; eauto; sep_split; eauto.
    rewrite phplus_comm; eauto. } Unfocus.
  applys (>>rule_p_forward (Ex vss, sh_ok sdecs locs vss //\\ (Assn Res' P' Env' ** sh_spec_assn' sdecs locs vss))). 
  Focus 2. {
    unfold sat; intros s h [vss Hsat].
    fold_sat; rewrite <-sh_spec_assn'_ok.
    rewrite ex_lift_l; exists vss; eauto.
    destruct Hsat as (? & h1 & h2 & ? & ? & ? & ?).
    unfold sh_ok, Apure in *; exists h1 h2; repeat split; try tauto. } Unfocus.
  Lemma rule_p_ex_pre n E T P C Q :
    (forall x, CSLp n E (P x) C Q)
    -> CSLp n E (Ex x : T, P x) C Q.
  Proof.
    intros H; simpl.
    unfold CSLp, sat_k in *.
    introv.
    intros ? ?.
    destruct (low_eq_repr _) eqn:Heq; simpl; intros [e Hsat] m.
    forwards*: (>>H); simpl.
    instantiate (2 := leqks); rewrite Heq; eauto.
  Qed.
  apply rule_p_ex_pre; intros.
  Lemma rule_p_conj_pure n E(P : Prop) P' C Q :
    (P -> CSLp n E (P') C Q)
    -> CSLp n E (pure P //\\ P') C Q.
  Proof.
    intros H; simpl.
    unfold CSLp, sat_k in *.
    introv.
    intros ? ?.
    destruct (low_eq_repr _) eqn:Heq; simpl; intros [? ?] m.
    forwards*: (>>H); simpl.
    instantiate (1 := leqks); rewrite Heq; eauto.
  Qed.
  apply rule_p_conj_pure; intros [? ?].
  applys* rule_p_forward.
  intros ? ? [vss [? ?]]; exists vss; split; eauto.
  unfold sh_ok; split; eauto.
Qed.


Lemma rule_p_assn n E Res (P : Prop) Env C Q :
  (P -> CSLp n E (Assn Res P Env) C Q)
  -> CSLp n E (Assn Res P Env) C Q.
Proof.
  intros H; simpl.
  unfold CSLp, sat_k in *.
  introv.
  intros ? ?.
  destruct (low_eq_repr _) eqn:Heq; simpl; intros ? m.
  forwards*: (>>H); simpl.
  unfold Assn, Apure in H2; sep_split_in H2; eauto.
  instantiate (1 := leqks); rewrite Heq; eauto.
Qed.


Lemma rule_grid :
  forall (ntrd nblk : nat) (E : env),
    ntrd <> 0 ->
    nblk <> 0 ->
    forall (P : assn) (Ps : Vector.t assn nblk) (C : cmd)
           (Qs : Vector.t assn nblk) (Q : assn) (sh_decl : list Sdecl),
      P |= Bdiv.Aistar_v Ps ->
      (forall (bid : Fin.t nblk) (locs : list val),
          let sinv := sh_inv sh_decl locs in
          let sinv' := sh_inv' sh_decl locs in
          CSLp ntrd E (Vector.nth Ps bid ** sinv ** !("bid" === Zn (nf bid))) C
               (Vector.nth Qs bid ** sinv')) ->
      Bdiv.Aistar_v Qs |= Q ->
      (forall bid : Fin.t nblk, inde (Vector.nth Ps bid) (Var "bid" :: Var "tid" :: nil)) ->
      (forall bid : Fin.t nblk, low_assn E (Vector.nth Ps bid)) ->
      (forall bid : Fin.t nblk, has_no_vars (Vector.nth Qs bid)) ->
      (forall v : var, In v (map SD_var sh_decl) -> E v = Lo) ->
      E "tid" = Hi ->
      E "bid" = Lo ->
      disjoint_list (map SD_var sh_decl) ->
      CSLg ntrd nblk P {| get_sh_decl := sh_decl; get_cmd := C |} Q.
Proof. eauto using rule_grid. Qed.

Lemma has_no_vars_assn R P : 
  has_no_vars (Assn R P nil).
Proof.
  unfold has_no_vars, Bdiv.indeP; simpl.
  unfold Assn; split; intros Hsat; sep_split_in Hsat; sep_split; eauto.
Qed.

    
Lemma conj_xs_init_flatten s l1 l2 f_ini :
  istar (ls_init s l1 (fun i =>
    istar (ls_init 0 l2 (fun j => f_ini (j + i * l2))))) ==
  istar (ls_init (s * l2) (l1 * l2) (fun i => f_ini i)).
Proof.
  revert s; induction l1; simpl; [reflexivity|]; introv.
  rewrite ls_init_app, istar_app.
  apply res_star_proper.
  - lazymatch goal with
    | [|- equiv_res (istar ?X) (istar ?Y)] => cutrewrite (X = Y); [reflexivity|applys (>>eq_from_nth Emp)]
    end.
    rewrite !init_length; eauto.
    intros i; rewrite init_length, !ls_init_spec; intros.
    destruct lt_dec; eauto; f_equal; ring.
  - rewrite IHl1.
    cutrewrite (S s * l2 = s * l2 + l2); [|ring]; reflexivity.
Qed.

Lemma conj_xs_init_flatten0 l1 l2 f_ini :
  istar (ls_init 0 l1 (fun i =>
    istar (ls_init 0 l2 (fun j => f_ini (j + i * l2))))) ==
  istar (ls_init 0 (l1 * l2) (fun i => f_ini i)).      
Proof.
  cutrewrite (0 = 0 * l2); [|omega].
  rewrite <-conj_xs_init_flatten.
  reflexivity.
Qed.

Ltac simpl_nested_istar := match goal with
| [|- context [istar (ls_init 0 ?n (fun i => istar (ls_init 0 ?m (fun j => @?f i j)))) ]] =>
  idtac f;
  lazymatch f with
  | fun i => fun j => array' ?loc (ith_vals ?dist ?vals (j + i * m) 0) 1%Qc =>
    idtac vals;
    rewrites (>>conj_xs_init_flatten0 n m (fun x => array' loc (ith_vals dist vals x 0) 1%Qc))
  | fun i => fun j => arrays' ?loc (ith_vals ?dist ?vals (j + i * m) 0) 1%Qc =>
    idtac vals;
    rewrites (>>conj_xs_init_flatten0 n m (fun x => arrays' loc (ith_vals dist vals x 0) 1%Qc))
  | fun i => fun j => ?X =>
    idtac X;
    rewrites (>>conj_xs_init_flatten0 n m (fun x : nat => X))
  end
| [H : context [istar (ls_init 0 ?n (fun i => istar (ls_init 0 ?m (fun j => @?f i j)))) ] |- _] =>
  idtac f;
  lazymatch f with
  | fun i => fun j => array' ?loc (ith_vals ?dist ?vals (j + i * m) 0) 1%Qc =>
    idtac vals;
    rewrites (>>conj_xs_init_flatten0 n m (fun x => array' loc (ith_vals dist vals x 0) 1%Qc)) in H
  | fun i => fun j => arrays' ?loc (ith_vals ?dist ?vals (j + i * m) 0) 1%Qc =>
    idtac vals;
    rewrites (>>conj_xs_init_flatten0 n m (fun x => arrays' loc (ith_vals dist vals x 0) 1%Qc)) in H
  | fun i => fun j => ?X =>
    idtac X;
    rewrites (>>conj_xs_init_flatten0 n m (fun x : nat => X)) in H
  end
end.

Lemma aenv_ok_params GA (avenv : AVarEnv GA) apenv aeenv x v :
  aenv_ok avenv
  -> In (x |-> v) (arrInvVar avenv apenv aeenv)
  -> prefix "_" (str_of_var x) = true.
Proof.
  intros; forwards* (? & ? & [? | ?]): arrInvVar_in; substs;
  destruct H as (? & ?); eauto.
Qed.

Lemma CSL_prop_prem n (tid : Fin.t n) BS R R' (P P' : Prop) Env Env' C :
  (P -> CSL BS tid (Assn R P Env) C (Assn R' P' Env'))
  -> CSL BS tid (Assn R P Env) C (Assn R' P' Env').
Proof.
  intros ? ? ?; simpl; unfold Assn in *; intros Hsat; sep_split_in Hsat; unfold Apure in *.
  applys* H.
  sep_split; eauto.
Qed.


Lemma CSLkfun_body ntrd nblk P k Q n:
  CSLg_n ntrd nblk P (body_of k) Q n ->
  CSLkfun_n_simp' ntrd nblk P k Q n.
Proof.
  unfold CSLkfun_n_simp', CSLg_n; intros; eauto.
Qed.

Lemma CSLg_float ntrd nblk R (P : Prop) E p Q n :
  (P -> CSLg_n ntrd nblk (Assn R P E) p Q n)
  -> CSLg_n ntrd nblk (Assn R P E) p Q n.
Proof.
  unfold CSLg_n; intros; eauto.
  applys* H.
  unfold Assn in *; sep_split_in H1; eauto.
Qed.

Lemma CSLg_weaken_pure ntrd nblk R (P : Prop) E p Q n :
  CSLg_n ntrd nblk (Assn R True E) p Q n
  -> CSLg_n ntrd nblk (Assn R P E) p Q n.
Proof.
  unfold CSLg_n; intros; eauto.
  applys* H.
  clear H0; revert H1; generalize (as_gheap gh); revert stk; prove_imp.
Qed.
