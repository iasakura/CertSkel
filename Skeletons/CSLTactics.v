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
  (P1 -> P2) ->
  (P1 -> (Res1 ===> Res2)) ->
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
Create HintDb no_vars_lemma.

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
      [rewrite Nat.mod_add; [|eauto] | ring];
      apply Nat.mod_small; first [now eauto; nia]
    end
  end.

Ltac prove_pure :=
  intros; 
  repeat match goal with
  | [H : _ /\ _ |- _] => destruct H as (H & ?)
  end; substs; repeat split;
  repeat match goal with
  | [H : context [Assn _ _ _]|- _] => clear H
  end;
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
    constr:(P ** t)
  | _ => constr:(P ** Q)
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
  sep_cancel.

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
    | sarray ?j ?d le ?arr _ _ =>
      idtac "apply read rule: match sarray case.";
      assert (Hres : Res |= R ** Res') by sep_auto;
      assert (Hbnd : P -> i < length arr /\ i mod d = j) by prove_pure;
      applys (>> rule_read_sarray Hle Hv Hres Hn Hbnd); eauto
    end in
  let rec iter acc Res :=
    match Res with
    | ?R ** ?Res =>
      first [let Res' := append_assn acc Res in checkR Res' R |
             iter (R ** acc) Res]
    | ?R => checkR acc R
    end in
  iter emp Res.

Ltac hoare_forward_prim :=
  lazymatch goal with
  | [|- CSL _ _ (Assn ?Res ?P ?Env) (?x ::T _ ::= [?le +o ?ix]) ?Q] =>
    let Hle := fresh "Hle" in let l := fresh "l" in
    evar (l : loc); assert (Hle : evalLExp Env le l) by (unfold l; evalLExp); unfold l in Hle;
    let Hv := fresh "Hv" in let v := fresh "v" in
    evar (v : val); assert (Hv : evalExp Env ix v) by (unfold v; evalLExp); unfold v in Hv;
    let Hn := fresh "Hn" in let n := fresh "n" in
    evar (n : nat); assert (Hn : v = Zn n) by (unfold v, n; solve_zn); unfold n in Hn;
    let le := eval cbv in l in
    let i := eval cbv in n in
    apply_read_rule Hle Hv Hn P Res le i
  | [|- CSL _ _ ?P (?x ::T _ ::= [?e]) ?Q] =>
    idtac "hoare_forward_prim: match read case";
    eapply rule_read; [evalExp | find_res | ]
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
      idtac "ok"
  end.

Ltac fold_sat :=
  match goal with
  | [|- ?P ?s ?h] =>
    lazymatch type of s with
    | stack => cutrewrite (P s h = sat s h P); [|reflexivity]
    end
  | _ => idtac
  end.

Ltac fold_sat_in H :=
  lazymatch type of H with
  | ?P ?s ?h => 
    lazymatch type of s with
    | stack => cutrewrite (P s h = sat s h P) in H; [|reflexivity]
    end
  | _ => idtac
  end.

Ltac choose_var_vals :=
  let H := fresh in
  let e := fresh in
  unfold incl; simpl; intros e H; 
  repeat destruct H as [? | H]; substs; eauto 10;
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
      (* proof impl. on pure assertion *)
      let H' := fresh "H" in
      intros H'; repeat destruct H' as (H' & ?); repeat split; substs; try prove_pure |
      (* proof impl. on resource assertion *)
      eauto |
      (* proof resource assertion does'nt have any vars *)
      eauto with novars_lemma ].

Hint Resolve
     has_no_vars_star
     has_no_vars_mp
     has_no_vars_emp : novars_lemma.

Lemma has_no_vars_array l vs p : has_no_vars (array l vs p).
Proof.
  revert l; induction vs; intros l; simpl; eauto with novars_lemma.
  apply has_no_vars_star; eauto.
  apply has_no_vars_mp; simpl; eauto.
  destruct l; simpl; eauto.
Qed.

Hint Resolve has_no_vars_array : novars_lemma.

Module SumOf.

Definition sum_of vs := List.fold_right Z.add 0%Z vs.

Local Notation I := (Var "I").
Local Notation T := (Var "T").
Local Notation L := (Var "L").
Local Notation SUM := (Var "SUM").
Local Notation ARR := (Var "ARR").

Definition sum_of_array inv :=
  I :T Int ::= 0%Z ;;
  SUM :T Int ::= 0%Z ;;
  WhileI inv (I <C L) (
    T :T Int ::= [Gl ARR +o I] ;;
    SUM :T Int ::= SUM +C T ;;
    I ::= 1%Z +C I
  ).

Notation ArrL := (Gl ARR).

Definition inv arr vs :=
  Ex i sum, 
    Assn (array (GLoc arr) vs 1%Qc)
         (i <= length vs /\ sum = sum_of (firstn i vs))
         (Ent SUM sum  ::
          Ent ARR arr ::
          Ent I (Zn i) :: 
          Ent L (Zn (length vs)) :: nil).

Lemma sum_ofS i vs :
  (Zn i < Zn (length vs) ->
   (sum_of (firstn i vs) + nth i vs 0) = sum_of (firstn (1 + i) vs))%Z.
Proof.
  intros H.
  assert (H' : i < length vs) by nia.
  clear H; revert H'.
  revert i; induction vs; intros i ?; simpl; try nia.
  - unfold sum_of in *; destruct i; try (simpl; nia).
  - simpl in *.
    intros; destruct i; simpl; try omega.
    rewrite <-IHvs; omega.
Qed.

Lemma firstn_full i (vs : list Z) :
  i <= length vs ->
  ~ (Zn i < Zn (length vs))%Z ->
  sum_of (firstn i vs) = sum_of vs.
Proof.
  intros; assert (Heq : i = length vs) by nia; substs.
  clear.
  induction vs; simpl; congruence.
Qed.

Hint Resolve sum_ofS firstn_full : pure_lemma.

Lemma sum_of_array_ok ntrd BS (tid : Fin.t ntrd) vs arr :
  CSL BS tid
      (Assn (array (GLoc arr) vs 1%Qc)
            (True)
            (ARR |-> arr :: L |-> (Zn (length vs)) :: nil))
      (sum_of_array (inv arr vs))
      (Ex s, Assn (array (GLoc arr) vs 1%Qc)
                  (s = sum_of vs)
                  (SUM |-> s :: ARR |-> arr :: nil)).
Proof.
  unfold sum_of_array, inv.
  hoare_forward.
  hoare_forward.
  hoare_forward.
  hoare_forward.
  
  hoare_forward.
  hoare_forward.
  prove_imp.
  prove_imp.
  prove_imp. 
Qed.
End SumOf.

Module ParMap.

Variable ntrd : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.
Hint Resolve ntrd_neq_0.
Variable tid : Fin.t ntrd.

Local Notation I := (Var "I").
Local Notation T := (Var "T").
Local Notation L := (Var "L").
Local Notation ARR := (Var "ARR").
Notation OUT := (Var "out").
Notation TID := (Var "tid").

Definition map inv :=
  I :T Int ::= TID ;;
  WhileI inv (I <C L) (
    T :T Int ::= [Gl ARR +o I] ;;
    [Gl OUT +o I] ::= T ;;
    I ::= Zn ntrd +C I
  ).

Definition inv arr out varr :=
  Ex j i vout, 
    Assn (sarray (nf tid) ntrd (GLoc arr) varr 1%Qc 0 **
          sarray (nf tid) ntrd (GLoc out) vout 1%Qc 0)
         (i = j * ntrd + nf tid /\
          i <= length varr /\
          firstn i varr = firstn i vout)
         (ARR |-> arr ::
          OUT |-> out ::
          I   |-> Zn i ::
          L   |-> (Zn (length varr)) :: nil).

Lemma map_ok BS arr out varr vout : 
  CSL BS tid 
      (Assn (sarray (nf tid) ntrd (GLoc arr) varr 1%Qc 0 **
             sarray (nf tid) ntrd (GLoc arr) vout 1%Qc 0)
            True
            (TID |-> Zn (nf tid) ::
             L   |-> Zn (length varr) :: 
             ARR |-> arr ::
             OUT |-> out :: nil))
      (map (inv arr out varr))
      (Assn (sarray (nf tid) ntrd (GLoc arr) varr 1%Qc 0 **
             sarray (nf tid) ntrd (GLoc arr) varr 1%Qc 0)
            True
            (TID |-> Zn (nf tid) ::
             L   |-> Zn (length varr) ::
             ARR |-> arr ::
             OUT |-> out :: nil)).
Proof.
  unfold map, inv.
  hoare_forward.
  hoare_forward.
  hoare_forward.
  