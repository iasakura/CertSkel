Require Import GPUCSL scan_lib LibTactics Psatz CSLLemma SetoidClass Skel_lemma scan_lib CodeGen.
Notation val := Z.
Arguments Z.add _ _ : simpl never.

Coercion Var : string >-> var.
Open Scope string_scope.
Open Scope list_scope.

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

Lemma cond_prop_in Res P P' Env cond :
  evalBExp Env cond  P' ->
  (Assn Res P Env ** !(cond)) ==
  (Assn Res (P /\ P') Env).
Proof.
  intros Heval s h; split; intros Hsat.
  - unfold Assn in *; sep_split_in Hsat.
    sep_split; eauto.
    split; eauto.
    rewrites <-(>>evalBExp_ok Heval); eauto. 
  - unfold Assn in *; sep_split_in Hsat.
    sep_split; eauto.
    rewrites (>>evalBExp_ok Heval); unfold_conn_all; tauto.
    eauto; sep_split; eauto.
    unfold_conn_all; tauto.
Qed.

Lemma cond_prop ntrd BS (tid : Fin.t ntrd) Res P P' Env C Q cond :
  evalBExp Env cond  P' ->
  CSL BS tid (Assn Res (P /\ P') Env) C Q ->
  CSL BS tid (Assn Res P Env ** !(cond)) C Q.
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

Ltac evalExp := 
  repeat match goal with
  | [|- evalExp _ _ _] => constructor
  end;
  simpl; eauto 20.

Ltac evalBExp := 
  repeat match goal with
         | [|- evalBExp _ _ _] => constructor
         | [|- _] => evalExp
  end;
  simpl; eauto 20.

Ltac evalLExp := 
  repeat match goal with
         | [|- evalLExp _ _ _] => constructor
         | [|- _] => evalExp
  end;
  simpl; eauto 20.

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
  revert i ys; induction xs; intros [|i] [|? ?]; do 2 destruct lt_dec; simpl in *; eauto; try lia;
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

Lemma nth_skip_ls T i (arr : list (list T)) dist j s :
  nth i (ith_vals dist arr j s) None =
  (if Nat.eq_dec (dist (s + i)) j
   then if lt_dec i (Datatypes.length arr) then Some (nth i arr nil) else None
   else None).
Proof.
  apply nth_skip.
Qed.

Hint Rewrite length_set_nth ith_vals_length app_length zipWith_length : pure.
Hint Rewrite nth_app nth_skip_Z nth_skip_ls nth_set_nth nth_firstn nth_skipn : pure.

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
  intros H s h H'; unfold sat_res, sat in *; simpl in *; sep_cancel; eauto.
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
  (l -->p (p, v)) == (l -->p (p, v')).
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
  intros; eapply scRw; eauto.
Qed.

Lemma array'_eq ls ls' ptr p: 
  ls = ls' -> array' ptr ls p |=R array' ptr ls' p.
Proof.
  intros; substs; eauto.
Qed.

Ltac matches P Q :=
  match constr:(P, Q) with
  | (?P, ?P) => constr:(Some true)
  | ((?l |->p (_, _)), (?l |->p (_, _))) => constr:(Some mps_eq)
  | ((array ?l _ _), (array ?l _ _)) => constr:(Some array_eq)
  | ((array' ?l _ _), (array' ?l _ _)) => constr:(Some array'_eq)
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
    | sat_res _ _ (?P *** ?Q) =>
      eapply res_mono in H; [| clear H; intros ? ? H; apply H |
                             clear H; intros ? ? H; lift_in idx H; apply H];
      first [rewrite res_CA in H | rewrite res_comm in H]
    end
  end.

Goal forall s h P Q R S T U, sat_res s h (P *** Q *** R *** S *** T *** U) -> False.
Proof.
  intros.
  Time lift_in 4 H.
  Time lift_in 5 H.
Abort.

Ltac prove_prim :=
  lazymatch goal with
  | [|- ?P |=R ?Q] => 
    lazymatch matches P Q with
    | Some true => let H := fresh "H" in intros ? ? H; apply H
    | Some ?lem => apply lem; eauto
    end
  end.

Lemma emp_unit_r_res R :
  (R *** Emp) == R.
Proof.
  apply emp_unit_r.
Qed.

Lemma emp_unit_l_res R :
  (Emp *** R) == R.
Proof.
  apply emp_unit_l.
Qed.

Create HintDb sep_eq.
Hint Rewrite emp_unit_l emp_unit_r sep_assoc : sep_eq.

Ltac sep_cancel' :=
  lazymatch goal with
  | [H : sat_res ?s ?h (?P1 *** ?P2) |- sat_res ?s ?h (?Q1 *** ?Q2) ] =>
    idtac "sep_cancel': match star case";
    let idx := find_idx Q1 (P1 *** P2) in
    lift_in idx H; revert s h H; apply res_mono; [
      prove_prim
    |intros s h H]
  | [H : sat_res ?s ?h (?P1 *** ?P2) |- sat_res ?s ?h ?Q ] =>
    idtac "sep_cancel': match goal is atom case";
    rewrite <-emp_unit_r_res; sep_cancel'
  | [H : sat_res ?s ?h ?P |- sat_res ?s ?h (?Q1 *** ?Q2) ] =>
    idtac "sep_cancel': match hypo is atom case ";
    rewrite <-emp_unit_r_res in H; sep_cancel'
  | [H : sat_res ?s ?h ?P |- sat_res ?s ?h ?Q ] =>
    idtac "sep_cancel': match both is atom case ";
    revert s h H; prove_prim
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
Qed.

Ltac sep_auto' := 
  intros ? ? ?;
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
    is_evar R; intros s h H;
    match P with
    | ?P1 *** ?P2 =>
      idtac "find_res': match sep conj case";
      same_res P1 Q;
      let P' := append_assn acc P2 in
      assert (H' : sat_res s h (P1 *** P')) by (unfold sat in *; sep_cancel');
      clear H; revert H'; apply scC2; eauto
    | _ =>
      idtac "find_res': match atom case";
      same_res P Q;
      idtac "succeed to unify";
      assert (H' : sat s h (P ** Emp));
      [  rewrite emp_unit_r; apply H | apply H']
    | _ => 
      find_res' (P ** acc)
    end
  end.

Ltac find_res := find_res' Emp.

Ltac sep_auto := 
  intros ? ? ?;
  repeat autorewrite with sep_eq in *;
  unfold sat in *; 
  repeat sep_cancel.

Ltac lift_ex_in H :=
  repeat match type of H with
         | sat _ _ ((Ex i, @?f i) ** ?P) =>
           let i := fresh i in
           rewrite ex_lift_r in H; destruct H as (i & H); fold_sat_in H
         end.

Ltac des_disj H :=
  repeat match type of H with
  | _ \/ _ => 
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    destruct H as [H1 | H2]; 
      des_disj H1; des_disj H2
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
  des_disj H; substs; eauto 10;
  let rec tac :=
      match goal with
      | [|- ?x |-> ?v = ?x |-> ?v' \/ ?H] =>
        left; cutrewrite (v = v'); eauto;
        solve_zn
      | [|- _ \/ ?H] => right; tac
      end in tac.

Ltac prove_imp :=
  let s := fresh "s" in
  let h := fresh "h" in
  let H := fresh "H" in
  intros s h H; 
    try match type of H with
        | sat _ _ (_ ** _) =>
          lift_ex_in H;
            rewrites cond_prop_in in H; [|evalBExp]
        | sat _ _ (AssnDisj _ _ _ _ _ _) =>
          destruct H as [H|H]; fold_sat_in H
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
        choose_var_vals |
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
    | array' le (ith_vals ?dist ?arr ?j ?s) _ =>
      idtac "apply read rule: match sarray case.";
      idtac dist i;
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr /\ dist (s + i) = j); [simpl; prove_pure|
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
    | array' le (ith_vals ?dist ?arr ?j ?s) _ =>
      idtac "apply read rule: match sarray case.";
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr /\ dist (s + i) = j); [prove_pure|
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
  apply rule_frame; try rewrite <-Hpre, <-Hpost; eauto using CSL.rule_barrier.
  simpl; intros ? ? ? ?; simpl; destruct 1.
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
  | [|- CSL _ _ ?P (?x ::T _ ::= ?e) ?Q] =>
    idtac "hoare_forward_prim: match assign case";
    eapply rule_assign; evalExp

  | [|- CSL _ _ _ (WhileI ?inv _ _) _ ] =>
    idtac "hoare_forward_prim: match while case";
    eapply backwardR; [applys (>>rule_while inv)|]

  | [|- CSL _ _ _ (Cif _ _ _) _] =>
    eapply rule_if_disj; evalBExp

  | [|- CSL _ _ _ Cskip _] =>
    apply rule_skip

  | [|- CSL _ _ _ (Cbarrier ?i) _] =>
    let unify_bspec := rewrite MyVector.init_spec; reflexivity in
    eapply rule_barrier; simpl;
    [unify_bspec | unify_bspec | prove_imp | ..]
  | _ => idtac
  end.

Lemma merge_var_val R1 R2 P1 P2 E1 E2 x v v' s h:
  sat s h (Assn R1 P1 (x |-> v :: E1) ** Assn R2 P2 E2) ->
  evalExp E2 x v' ->
  sat s h (Assn R1 (v = v' /\ P1) E1 ** Assn R2 P2 E2).
Proof.
  unfold Assn, sat; intros Hsat Heval;
  sep_normal_in Hsat; sep_normal; sep_split_in Hsat; sep_split; eauto;
  simpl in *; repeat sep_cancel.
  destruct HP0.
  eapply evalExp_ok in Heval; eauto.
  unfold_conn_all; simpl in *; split; try tauto.
  congruence.
  destruct HP0; eauto.
Qed.

Ltac merge_pre H :=
  lazymatch type of H with
  | sat _ _ (Assn _ _ (_ :: _) ** Assn _ _ _) =>
    eapply merge_var_val in H; [|evalExp]; merge_pre H
  | sat _ _ (Assn _ _ nil ** Assn _ _ _) =>
    rewrite Assn_combine in H; simpl in H
  end.

Ltac hoare_forward :=
  lazymatch goal with
  | [|- CSL _ _ (Assn _ _ _ ** Assn _ _ _) _ _] =>
    let H := fresh "H" in
    eapply backward; [intros ? ? H; merge_pre H; apply H|]
  | [|- CSL _ _ ((Ex _, _) ** _) _ _] =>
    idtac "hoare_forward: match ex case";
    lift_ex; hoare_forward
  | [|- CSL _ _ (AssnDisj _ _ _ _ _ _) _ _] =>
    idtac "hoare_forward: match disj case";
    apply rule_disj
  | [|- CSL _ _ (_ ** !(_)) _ _] =>
    idtac "hoare_forward: match conditional case";
    eapply cond_prop; [evalBExp|]; hoare_forward
  | [|- CSL _ _ ?P (_ ;; _) ?Q ] =>
    idtac "hoare_forward: match seq case";
    eapply rule_seq; [hoare_forward |]; simpl_env
  | [|- CSL _ _ _ _ ?Q] =>
    idtac "hoare_forward: match prim case";
    first [is_evar Q; hoare_forward_prim; idtac "ok" |
           idtac "hoare_forward: match back case";
           eapply forwardR; [hoare_forward_prim|]];
    simpl_env
end.

Lemma div_spec x y :
  y <> 0 ->
  exists q r,  x / y = q /\ x = y * q + r /\ r < y.
Proof.
  intros; exists (x / y) (x mod y); repeat split; eauto.
  applys* div_mod.
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
  pure (length sdecs = length locs /\ length sdecs = length vals).

Lemma array_is_array' pl loc len vs f s :
  length vs = len ->
  (forall i, i < len -> nth i vs 0%Z = f (s + i)) ->
  res_denote (array (loc_off (Loc pl loc) (Z.of_nat s)) vs 1) == is_array (Addr pl loc) len f s.
Proof.
  revert len s; induction vs; intros [|len] s Hlen Heq; simpl in *; try omega.
  reflexivity.
  cutrewrite (loc + Zn s + 1 = loc + Zn (s + 1))%Z; [|rewrite Nat2Z.inj_add; lia].
  rewrites* (>>IHvs len (s + 1)); try lia.
  intros; forwards*Heq': (Heq (S i)); [lia|].
  rewrite Heq'; f_equal; lia.
  cutrewrite (S s = s +1); [apply* star_proper; [|reflexivity]|lia].
  assert (Heq' : a = f s); [|rewrite Heq'; clear Heq'].
  { forwards*: (Heq 0); [lia|].
    rewrite H; f_equal; lia. }
  split; unfold_conn; intros H x; rewrite H; destruct loc; simpl; auto.
Qed.

Lemma array_is_array pl loc len vs f :
  length vs = len ->
  (forall i, i < len -> nth i vs 0%Z = f i) ->
  res_denote (array (Loc pl loc) vs 1) == is_array (Addr pl loc) len f 0.
Proof.
  intros; 
  forwards*: (>>array_is_array' loc len vs f 0); eauto.
  rewrite <- H1.
  unfold loc_off; rewrite Z.add_0_r; reflexivity.
Qed.


Lemma sh_spec_assn_ok sdecs locs :
  (Ex vals, (sh_ok sdecs locs vals) //\\ sh_spec_assn sdecs locs vals) == sh_inv sdecs locs.
Proof.
  unfold sh_spec_assn, sh_inv, sh_ok, GCSL.sh_ok; revert locs; induction sdecs as [|[? ? ?] ?];
  intros [|l locs]; split; intros [[|vs vals] [Hlen Hsat]]; unfold Apure in Hlen; simpl in *;
  try omega; unfold Assn in *; simpl in *; sep_split_in Hsat.
  - exists (@nil sh_val); split; eauto.
  - exists (@nil (list val)); split; sep_split; eauto using emp_emp_ph.
    unfold Apure; eauto.
  - destruct Hsat as (h1 & h2 & ? & ? & ?); eauto.
    forwards* [IH1 IH2]: (IHsdecs locs).
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
  unfold sh_spec_assn', sh_inv', sh_ok, GCSL.sh_ok; revert locs; induction sdecs as [|[? ? ?] ?];
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

Lemma inde_assn_vars:
  forall (R : res) (P : Prop) (Env : list entry) (E : list var),
    (forall (e : exp) (x : var) (v : val),
        In (e |-> v) Env -> In x (Skel_lemma.fv_E e) -> ~In x E) ->
    inde (Assn R P Env) E.
Proof.
  intros HEnv.
  unfold inde; simpl.
  unfold Assn; split; intros Hsat; sep_split_in Hsat; sep_split; eauto;
  induction Env as [|[? ?] ?]; simpl in *; eauto; destruct HP0; split;
  unfold_conn_all; simpl in *; eauto;
  [erewrite fv_edenot; eauto;
   unfold var_upd; intros; destruct var_eq_dec; substs; eauto;
   forwards*: H..].
Qed.

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
  | fun i => fun j => ?X =>
    idtac X;
    rewrites (>>conj_xs_init_flatten0 n m (fun x : nat => X)) in H
  end
end.