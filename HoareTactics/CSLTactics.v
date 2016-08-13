Require Import GPUCSL scan_lib LibTactics Psatz CSLLemma SetoidClass.

Arguments Z.add _ _ : simpl never.

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

Hint Rewrite app_length firstn_length skipn_length : pure.

Ltac prove_pure :=
  intros; 
  repeat match goal with
  | [H : _ /\ _ |- _] => destruct H as [H ?]
  end; substs; repeat split;
  repeat match goal with
  | [H : context [Assn _ _ _]|- _] => clear H
  end;
  repeat autorewrite with pure in *;
  try now
      repeat (match goal with
       | [|- context [if ?b then _ else _]] => destruct b
       | [H : context [if ?b then _ else _] |- _] => destruct b
       | [|- context [match ?b with _ => _ end]] => destruct b
       | [H : context [if ?b then _ else _] |- _] => destruct b
       end);
  first [prove_mod_eq |now (eauto with pure_lemma) | nia].

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
  intros H s h H'; unfold sat_res in *; simpl in *; sep_cancel; eauto.
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

Ltac sep_cancel' :=
  lazymatch goal with
  | [H : sat_res ?s ?h (?P1 *** ?P2) |- sat_res ?s ?h (?Q1 *** ?Q2) ] =>
    let idx := find_idx Q1 (P1 *** P2) in
    lift_in idx H; revert s h H; apply res_mono; [
      prove_prim
    |intros s h H]
  | [H : sat_res ?s ?h (?P1 *** ?P2) |- sat_res ?s ?h ?Q ] =>
    rewrite <-emp_unit_r_res; sep_cancel'
  | [H : sat_res ?s ?h ?P |- sat_res ?s ?h (?Q1 *** ?Q2) ] =>
    rewrite <-emp_unit_r_res in H; sep_cancel'
  | [H : sat_res ?s ?h ?P |- sat_res ?s ?h ?Q ] =>
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
  repeat autorewrite with sep in *;
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

Create HintDb sep.
Hint Rewrite emp_unit_l emp_unit_r sep_assoc : sep.

Ltac sep_auto := 
  intros ? ? ?;
  repeat autorewrite with sep in *;
  unfold sat in *; 
  repeat sep_cancel.

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
      assert (Hres : Res |=R R *** Res') by sep_auto';
      assert (Hbnd : P -> i < length arr) by prove_pure;
      applys (>> rule_read_array Hle Hv Hres Hn Hbnd)
    | array' le (ith_vals ?dist ?arr ?j ?s) _ =>
      idtac "apply read rule: match sarray case.";
      idtac dist i;
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr /\ dist (s + i) = j); [simpl; prove_pure|
      applys (>> rule_read_array' Hle Hv Hres Hn Hbnd); eauto with novars_lemma pure_lemma]]
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
      assert (Hres : Res |=R R *** Res') by sep_auto';
      assert (Hbnd : P -> i < length arr) by prove_pure;
      applys (>> rule_write_array Hle Hix Hn Hbnd He Hres)
    | array' le (ith_vals ?dist ?arr ?j ?s) _ =>
      idtac "apply read rule: match sarray case.";
      assert (Hres : Res |=R R *** Res'); [sep_auto'|
      assert (Hbnd : P -> i < length arr /\ dist (s + i) = j); [prove_pure|
      applys (>> rule_write_array' Hle Hix Hres He Hn Hbnd); eauto with novars_lemma pure_lemma]]
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

  | [|- CSL _ _ _ Cbarrier ?i _] =>
    idtac

  | _ => idtac
  end.

Ltac hoare_forward :=
  lazymatch goal with
  | [|- CSL _ _ ((Ex _, _) ** _) _ _] =>
    idtac "hoare_forward: match ex case";
    lift_ex; hoare_forward
  | [|- CSL _ _ (AssnDisj _ _ _ _ _ _) _ _] =>
    idtac "hoare_forward: match disj case";
      apply rule_disj
  | [|- CSL _ _ (_ ** _) _ _] =>
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

Ltac des_conj H :=
  repeat match type of H with
  | _ /\ _ => 
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    destruct H as [H1 H2]; 
      des_conj H1; des_conj H2
  end.

Ltac des_disj H :=
  repeat match type of H with
  | _ \/ _ => 
    let H1 := fresh "H" in
    let H2 := fresh "H" in
    destruct H as [H1 | H2]; 
      des_disj H1; des_disj H2
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

Ltac lift_ex_in H :=
  repeat match type of H with
         | sat _ _ ((Ex i, @?f i) ** ?P) =>
           let i := fresh i in
           rewrite ex_lift_r in H; destruct H as (i & H); fold_sat_in H
         end.

Ltac prove_imp :=
  let s := fresh "s" in
  let h := fresh "h" in
  let H := fresh "H" in
  intros s h H; 
    try match type of H with
        | sat _ _ (_ ** _) =>
          lift_ex_in H;
            rewrites cond_prop_in in H; [|evalBExp]
        end;
    repeat
      match goal with
      | [|- sat _ _ (Ex _, _)] => eexists; fold_sat
      | [|- sat _ _ ((Ex _, _) ** _)] => rewrite ex_lift_r
      | [|- sat _ _ (Assn _ _ _ ** Assn _ _ _)] => rewrite Assn_combine
      end;
    repeat autorewrite with sep in *;
    applys (>>Assn_imply s h H);
    [ (* proof impl. on environment *)
      choose_var_vals |
      (* proof impl. on resource assertion *)
      intros Hp; des_conj Hp; sep_auto' |
      (* proof impl. on pure assertion *)
      let H' := fresh "H" in
      intros H'; des_conj H'; repeat split; substs; try prove_pure].

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
  
Hint Rewrite length_set_nth ith_vals_length app_length : pure.
Hint Rewrite nth_app nth_skip nth_set_nth nth_firstn nth_skipn : pure.

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

Fixpoint zipWith {A B C : Type} (f : A -> B -> C) xs ys :=
  match xs, ys with
  | x :: xs, y :: ys => f x y :: zipWith f xs ys
  | _, _ => nil
  end.

Definition next (x : nat * list val):=
  let (l, ls) := x in
  let d := ((l + 1) / 2) in
  (d, zipWith Z.add (firstn (l - d) ls) (firstn (l - d) (skipn d ls)) ++ skipn (l - d) ls).

Fixpoint iter {T : Type} n f (x : T) := 
  match n with
  | 0 => x
  | S n => f (iter n f x)
  end.

Variable init_vals : list val.
Variable arr : val.

Local Notation c_state c := (iter c next (length init_vals, init_vals)).

Definition reduce inv := 
  "c" ::= 0%Z ;;
  "st" ::= "l" ;;
  WhileI inv (1%Z <C "st") (
    "d" ::= ("st" +C 1%Z)>>1 ;;
    Cif ("tid" +C "d" <C "st") (
      "t1" ::= [ Sh "arr" +o "tid" ] ;;
      "t2" ::= [ Sh "arr" +o ("tid" +C "d") ] ;;
      [ Sh "arr" +o "tid" ] ::= "t1" +C "t2"
    ) Cskip ;;
    Cbarrier 0 ;;
    "st" ::= "d" ;;
    "c" ::= "c" +C 1%Z
  ).

Definition dist st i :=
  let d := (st + 1) / 2 in
  if lt_dec (i + d) st then i
  else if lt_dec i st then (i - d)
  else 0.

Definition inv :=
  Ex st vals c,
  Assn (array' (SLoc arr) (ith_vals (dist st) vals (nf tid) 0) 1)
       (st = fst (c_state c) /\ vals = snd (c_state c))
       ("tid" |-> Zn (nf tid) ::
        "st" |-> Zn st ::
        "arr" |-> arr ::
        "c" |-> Zn c ::
        nil).

Definition BS0 :=
  (MyVector.init (fun i : Fin.t ntrd =>
     Ex st c vals,
     Assn (array' (SLoc arr) (ith_vals (dist st) vals (nf i) 0) 1)
          (st = fst (c_state c) /\ vals = snd (c_state (S c)))
          ("st" |-> Zn st :: "c" |-> Zn c :: nil)),
   MyVector.init (fun i : Fin.t ntrd =>
     Ex st c vals,
     Assn (array' (SLoc arr) (ith_vals (dist st) vals (nf i) 0) 1)
          (st = fst (c_state c) /\ vals = snd (c_state (S c)))
          ("st" |-> Zn st :: "c" |-> Zn c :: nil))).

Notation BS := (fun i => if Nat.eq_dec i 0 then BS0 else default ntrd).

Lemma zipWith_length (A B C : Type) (f : A -> B -> C) xs ys :
  length (zipWith f xs ys) = if lt_dec (length xs) (length ys) then length xs else length ys.
Proof.
  revert ys; induction xs; intros [|? ?]; simpl; eauto.
  destruct lt_dec; rewrite IHxs; destruct lt_dec; omega.
Qed.

Lemma div_spec x y :
  y <> 0 ->
  exists q r,  x / y = q /\ x = y * q + r /\ r < y.
Proof.
  intros; exists (x / y) (x mod y); repeat split; eauto.
  applys* div_mod.
Qed.

Lemma Zdiv_spec x y :
  (0%Z < y ->
   exists q r,  (x / y = q /\ x = y * q + r /\ r < y))%Z.
Proof.
  intros; exists (x / y)%Z (x mod y)%Z; repeat split; eauto.
  applys* Z.div_mod; lia.
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
Hint Rewrite zipWith_length : pure.

Lemma st_decrease c :
  fst (c_state (S c)) <= fst (c_state c).
Proof.
  induction c; simpl; try div_lia.
  unfold next; destruct (iter c _ _); simpl.
  div_lia.
Qed.

Lemma st_length c :
  fst (c_state c) <= length init_vals.
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
  1 < fst (c_state c) ->
  (fst (c_state c) - (fst (c_state (S c)))) <= length init_vals.
Proof.
  intros; induction c. simpl in *. div_lia.
  simpl in *.
  unfold next in *; destruct (iter c _ _); simpl in *.
  div_lia.
Qed.  
  
Lemma st_inv2 c :
  1 < fst (c_state c) ->
  length (snd (c_state c)) = length init_vals.
Proof.
  intros; induction c; simpl; eauto.
  lets: (st_decrease c).
  lets: (st_length c).
  unfold next in *; simpl in *; destruct (iter c _ _) eqn:Heq; simpl in *.
  autorewrite with pure.
  repeat destruct lt_dec; try div_lia.
Qed.  
  
Lemma reduce_ok :
  length init_vals = ntrd ->
  CSL BS tid 
      (Assn (array' (SLoc arr) (ith_vals (dist (length init_vals)) init_vals (nf tid) 0) 1)
            True
            ("arr" |-> arr ::
             "l" |-> Zn (length init_vals) ::
             nil))
      (reduce inv)
      (Ex vals st,
         Assn (array' (SLoc arr) (ith_vals (dist st) vals (nf tid) 0) 1)
              True
              nil).
Proof.
  intros; unfold reduce, inv, dist.
  assert (nf tid < ntrd) by eauto.
  hoare_forward.
  hoare_forward.
  hoare_forward.
  hoare_forward.

  lets: (st_decrease c); rewrite stS in *.

  hoare_forward. 
  hoare_forward.
  rewrite st_inv2; eauto; lia.
  repeat (destruct lt_dec; eauto); div_lia.

  hoare_forward.
  forwards*: (st_length c).
  forwards*: (st_inv2 c); try div_lia.
  
  repeat (destruct lt_dec; eauto); div_lia.

  hoare_forward.
  rewrite st_inv2; eauto; lia.
  repeat (destruct lt_dec; eauto); div_lia.
  
  eauto.
  hoare_forward.
  eauto.

  hoare_forward.
  Lemma rule_barrier n bs (i : Fin.t n) b A_pre Res_F A_post Res P Env:
    (Vector.nth (fst (bs b)) i) = A_pre ->
    (Vector.nth (snd (bs b)) i) = A_post ->
    Assn Res P Env |= A_pre ** Assn Res_F P Env ->
    CSL bs i (Assn Res P Env) (Cbarrier b) (Assn Res_F P Env ** A_post).
  Proof.
    intros Hpre Hpost Himp.
    eapply backward.
    { intros ? ? H; apply Himp in H; eauto. }
    eapply forward.
    { intros ? ? H; rewrite sep_comm; eauto. }
    apply rule_frame; try rewrite <-Hpre, <-Hpost; eauto using CSL.rule_barrier.
    simpl; intros ? ? ? ?; simpl; destruct 1.
  Qed.
  eapply rule_seq.
  lazymatch goal with
  | [|- CSL _ _ _ (Cbarrier ?i) _] =>
    let unify_bspec := rewrite MyVector.init_spec; reflexivity in
    eapply rule_barrier; simpl;
    [unify_bspec | unify_bspec |
     prove_imp | ..]
  end.
  eauto.
  admit.

  rewrite Assn_combine; [
    applys (>> Assn_imply s h H3);
    [choose_var_vals | intros Hp; des_conj Hp; sep_auto' |
     let H' := fresh "H" in
     intros H'; des_conj H'; repeat split; substs; try prove_pure | ..] |
    .. ]; eauto with novars_lemma.
  substs; eauto.
  
  revert s0 h0 H6; sep_auto'.
  rewrite <-emp_unit_r.
  instantiate (1 := emp).
  fold_sat; fold_sat_in H5; autorewrite with sep in *.
  eapply array'_eq; [|eauto]; simpl.