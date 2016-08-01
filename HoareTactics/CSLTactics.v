Require Import GPUCSL scan_lib LibTactics Psatz CSLLemma SetoidClass.

Arguments Z.add _ _ : simpl never.

Notation "x |-> v" := (Ent x v) (at level 58).

Lemma Ent_eq_dec (e1 e2 : entry) : {e1 = e2} + {e1 <> e2}.
Proof. repeat decide equality. Qed.

Lemma remove_var_cons x Env :
  ent_assn_denote x //\\ env_assns_denote (remove Ent_eq_dec x Env)
  ===> env_assns_denote Env.
Proof.
  induction Env; simpl.
  - intros s h [? ?]; eauto using env_assns_emp.
  - destruct Ent_eq_dec; simpl; substs.
    + intros; split; eauto.
      destruct H; eauto.
    + intros s h (? & ? & ?); split; eauto.
      apply IHEnv; split; eauto.
Qed.

Lemma in_remove T dec (a : T) x l :
  In a (remove dec x l) -> a <> x /\ In a l.
Proof.
  induction l; simpl; eauto.
  destruct (dec _ _); substs; simpl; intros; split; eauto; try tauto.
  destruct H; substs; eauto; try tauto.
Qed.

Lemma env_incl_imp (Env1 Env2 : list entry ) :
  incl Env2 Env1 ->
  (env_assns_denote Env1 ===> env_assns_denote Env2).
Proof.
  revert Env2; induction Env1 as [|[x v] Env1]; unfold incl; intros Env2.
  - simpl; intros H.
    assert (Env2 = nil).
    { destruct Env2; eauto.
      false; eapply H; simpl; eauto. }
    subst; simpl; eauto.
  - simpl; intros H s h Hsat; destruct Hsat as [? Hsat].
    applys (>>remove_var_cons (x |-> v)); simpl.
    split; eauto.
    apply IHEnv1; eauto.
    unfold incl; intros.
    forwards*(? & ?): in_remove.
    forwards*[? | ?]: H; substs.
    congruence.
Qed.

Lemma Assn_imply (Res1 Res2 : assn) (P1 P2 : Prop) Env1 Env2 :
  incl Env2 Env1 ->
  (P1 -> (Res1 ===> Res2)) ->
  (P1 -> P2) ->
  has_no_vars Res2 ->
  Assn Res1 P1 Env1 ===> Assn Res2 P2 Env2.
Proof.
  unfold Assn; intros Henv HP Hres ? s h Hsat.
  destruct Hsat as [? Hsat]; sep_split_in Hsat; 
  split; eauto; sep_split; eauto.
  - unfold_conn; eauto.
  - applys* env_incl_imp.
Qed.

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
    destruct Hsat as (? & Hsat); sep_split_in Hsat.
    split; eauto.
    sep_split; eauto.
    split; eauto.
    rewrites <-(>>evalBExp_ok Heval); eauto. 
  - unfold Assn in *; sep_split_in Hsat.
    destruct Hsat as (? & Hsat); sep_split_in Hsat.
    sep_split; eauto.
    rewrites (>>evalBExp_ok Heval); unfold_conn_all; tauto.
    split; eauto; sep_split; eauto.
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
  simpl; eauto.
Ltac evalBExp := 
  repeat match goal with
         | [|- evalBExp _ _ _] => constructor
         | [|- _] => evalExp
  end;
  simpl; eauto.
Ltac evalLExp := 
  repeat match goal with
         | [|- evalLExp _ _ _] => constructor
         | [|- _] => evalExp
  end;
  simpl; eauto.

Ltac elim_remove env x := simpl.
Ltac simpl_env := 
  lazymatch goal with
  | [|- context [remove_var ?env ?x]] => elim_remove env x
  | _ => idtac
  end.

Lemma backwardR ntrd BS (tid : Fin.t ntrd) P P' Q C :
  CSL BS tid P C Q -> P' |= P -> CSL BS tid P' C Q.
Proof.
  intros; forwards*: backward.
Qed.

Lemma forwardR ntrd BS (tid : Fin.t ntrd) P Q Q' C :
  CSL BS tid P C Q -> Q |= Q' -> CSL BS tid P C Q'.
Proof.
  intros; forwards*: forward.
Qed.

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
  revert arr; induction i; intros [|? ?]; destruct lt_dec; simpl in *; try omega.
  rewrite IHi; destruct lt_dec; simpl in *; try omega.
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
  | Zn ?v => v
  | ?v =>
    match is_const v with
    | true => let t := eval compute in (Z.to_nat v) in t
    end
  end.

Create HintDb zn.
Hint Rewrite 
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
  Q |= R -> (P ** Q) |= (P ** R).
Proof.
  intros H s h H'; unfold sat in *; sep_cancel; eauto.
Qed.
  
Ltac same_res P Q := unify P Q.

Ltac append_assn P Q :=
  match P with
  | emp => Q
  | (?P1 ** ?P2) => 
    let t := append_assn P2 Q in
    constr:(P1 ** t)
  | _ => constr:(P ** Q)
  end.

Ltac remove_last_emp P :=
  match P with
  | (?P1 ** emp) => P1
  | (?P1 ** ?P2) => 
    let t := remove_last_emp P2 in
    constr:(P1 ** t)
  end.

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
  | [|- ?P |= ?Q ** ?R] =>
    idtac "find_res': P = " P;
    idtac "find_res': P = " Q;
    is_evar R; intros s h H;
    match P with
    | ?P1 ** ?P2 =>
      idtac "find_res': match sep conj case";
      same_res P1 Q;
      let P' := append_assn acc P2 in
      assert (H' : sat s h P1 ** P') by (unfold sat in *; sep_cancel);
      clear H; revert H'; apply scC2; eauto
    | _ =>
      idtac "find_res': match atom case";
      same_res P Q;
      idtac "succeed to unify";
      assert (H' : sat s h (P ** emp));
      [  rewrite emp_unit_r; apply H | apply H']
    | _ => 
      find_res' (P ** acc)
    end
  end.

Ltac find_res := find_res' emp.

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
      assert (Hres : Res |= R ** Res') by sep_auto;
      assert (Hbnd : P -> i < length arr) by prove_pure;
      applys (>> rule_read_array Hle Hv Hres Hn Hbnd)
    | array' le (skip ?arr ?d ?j) _ =>
      idtac "apply read rule: match sarray case.";
      assert (Hres : Res |= R ** Res') by sep_auto;
      assert (Hbnd : P -> i < length arr /\ i mod d = j); [prove_pure|
      applys (>> rule_read_sarray Hle Hv Hres Hn Hbnd); eauto with novars_lemma pure_lemma]
    end in
  let rec iter acc Res :=
    match Res with
    | ?R ** ?Res =>
      first [let Res' := append_assn acc Res in checkR Res' R |
             iter (R ** acc) Res]
    | ?R => checkR acc R
    end in
  iter emp Res.

(*
  find an R in Res that contains le in its arguments, 
  and prove resource and bound check condution, then apply appropriate rule
 *)
Ltac apply_write_rule Hle Hix He Hn P Res le i :=
  let checkR Res' R :=
    idtac "checkR: Res', R, le = " Res' "," R ", " le;
    let Hres := fresh "Hres" in
    let Hbnd := fresh "Hbnd" in
    match R with
    | array le ?arr _ =>
      idtac "apply read rule: match array case.";
      assert (Hres : Res |= R ** Res') by sep_auto;
      assert (Hbnd : P -> i < length arr) by prove_pure;
      applys (>> rule_write_array Hle Hix Hn Hbnd He Hres)
    | array' le (skip ?arr ?d ?j) _ =>
      idtac "apply read rule: match sarray case.";
      assert (Hres : Res |= R ** Res') by sep_auto;
      assert (Hbnd : P -> i < length arr /\ i mod d = j); [prove_pure|
      applys (>> rule_write_sarray' Hle Hix Hres He Hn Hbnd); eauto with novars_lemma pure_lemma]
    end in
  let rec iter acc Res :=
    match Res with
    | ?R ** ?Res =>
      first [let Res' := append_assn acc Res in 
             idtac "append_assn: P, Q = " acc Res;
               checkR Res' R |
             iter (R ** acc) Res]
    | ?R => let Res' := remove_last_emp acc in checkR Res' R
    end in
  iter emp Res.

Ltac hoare_forward_prim :=
  lazymatch goal with
  | [|- CSL _ _ (Assn ?Res ?P ?Env) (?x ::T _ ::= [?le +o ?ix]) ?Q] =>
    let Hle := fresh "Hle" in let l := fresh "l" in
    evar (l : loc); assert (Hle : evalLExp Env le l) by (unfold l; evalLExp); unfold l in *;
    let Hv := fresh "Hv" in let v := fresh "v" in
    evar (v : val); assert (Hv : evalExp Env ix v) by (unfold v; evalLExp); unfold v in *;
    let Hn := fresh "Hn" in let n := fresh "n" in
    evar (n : nat); assert (Hn : v = Zn n) by (unfold v, n; solve_zn); unfold n in *;
    let le := eval cbv in l in
    let i := eval cbv in n in
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
    
    let l' := eval cbv in l in
    let n' := eval cbv in n in
    unfold l, i, v, n in *; clear l i v n;
      
    apply_write_rule Hle Hix He Hn P Res l' n'
  | [|- CSL _ _ ?P (?x ::T _ ::= ?e) ?Q] =>
    idtac "hoare_forward_prim: match assign case";
    eapply rule_assign; evalExp
  | [|- CSL _ _ _ (WhileI ?inv _ _) _ ] =>
    idtac "hoare_forward_prim: match while case";
    eapply backwardR; [applys (>>rule_while inv)|]
  | _ => idtac
  end.

Ltac hoare_forward :=
  lazymatch goal with
  | [|- CSL _ _ ((Ex _, _) ** _) _ _] =>
    idtac "hoare_forward: match ex case";
    lift_ex; hoare_forward
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
      end;
    repeat autorewrite with sep in *;
    applys (>>Assn_imply s h H);
    [ (* proof impl. on environment *)
      choose_var_vals |
      (* proof impl. on resource assertion *)
      intros Hp; des_conj Hp; sep_auto |
      (* proof impl. on pure assertion *)
      let H' := fresh "H" in
      intros H'; des_conj H'; repeat split; substs; try prove_pure |
      (* proof resource assertion does'nt have any vars *)
      eauto with novars_lemma ].


Lemma array'_eq ls ls' ptr p: 
  ls = ls' -> array' ptr ls p |= array' ptr ls' p.
Proof.
  intros; substs; eauto.
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
  
Hint Rewrite length_set_nth ith_vals_length app_length : pure.
Hint Rewrite nth_app nth_skip nth_set_nth nth_firstn nth_skipn : pure.