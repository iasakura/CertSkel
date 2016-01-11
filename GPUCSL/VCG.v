Set Implicit Arguments.
Unset Strict Implicit.

Require Import Omega.
Require Import Qcanon.
Require Import assertions.
Require Import Lang.
Require Import CSL.
Require Import PHeap.
Require Import array_dist.
Require Import MyList.
Require Import LibTactics.
Open Scope exp_scope.
Open Scope bexp_scope.
(* Require Import scan_lib. *)

Section independent_prover.
  Ltac inde_simpl :=
    unfold inde in *; simpl in *; intros ? ? ? ? ?.

  Lemma inde_sconj (P Q : assn) (vs : list var) :
    inde P vs -> inde Q vs -> inde (P ** Q) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    unfold_conn; split; intros (ph1 & ph2 & Hp' & Hq' & Hdis' & Heq).
    exists ph1 ph2; repeat split; [apply Hp | apply Hq | idtac..]; auto.
    exists ph1 ph2; repeat split; [apply<-Hp | apply<-Hq | idtac..]; eauto.
  Qed.

  Lemma inde_pure (P : assn) (vs : list var) : inde P vs -> inde !(P) vs.
  Proof.
    intros Hp; inde_simpl.
    unfold_conn; split; intros [H1 H2].
    split; [auto | apply Hp]; auto.
    split; [auto | apply<-Hp]; eauto.
  Qed.

  Lemma inde_conj (P Q : assn) (vs : list var) : inde P vs -> inde Q vs -> inde (P //\\ Q) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    unfold_conn; split; intros [Hp' Hq'].
    split; [apply Hp | apply Hq]; auto.
    split; [apply <-Hp | apply <-Hq]; eauto.
  Qed.

  Lemma inde_disj (P Q : assn) (vs : list var) : inde P vs -> inde Q vs -> inde (P \\// Q) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    unfold_conn; split; intros H'.
    destruct H'; [left; apply Hp | right; apply Hq]; auto.
    destruct H'; [left; apply <-Hp | right; apply <-Hq]; eauto.
  Qed.

  Lemma inde_pointto (E : loc_exp) (E' : exp) (q : Qc) (vs : list var) :
    List.Forall (indelE E) vs -> List.Forall (indeE E') vs ->
    inde (E -->p (q, E')) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    rewrite List.Forall_forall in *.
    unfold_conn; split; intros H'.
    rewrite<-(Hp x H s); rewrite<-(Hq x H s); auto.
    erewrite (Hp x H s); erewrite (Hq x H s); eauto.
  Qed.

  Lemma inde_eeq (E E' : exp) (vs : list var) :
    List.Forall (indeE E) vs -> List.Forall (indeE E') vs ->
    inde (E === E') vs.
  Proof.
    intros H H'; inde_simpl.
    rewrite List.Forall_forall in *.
    unfold_conn; split; intros Heq.
    rewrite<-(H x H0 s); rewrite<-(H' x H0 s); auto.
    erewrite (H x H0 s); erewrite (H' x H0 s); eauto.
  Qed.

  Lemma inde_leeq (E E' : loc_exp) (vs : list var) :
    List.Forall (indelE E) vs -> List.Forall (indelE E') vs ->
    inde (E ===l E') vs.
  Proof.
    intros H H'; inde_simpl.
    rewrite List.Forall_forall in *.
    unfold_conn; split; intros Heq.
    rewrite<-(H x H0 s); rewrite<-(H' x H0 s); auto.
    erewrite (H x H0 s); erewrite (H' x H0 s); eauto.
  Qed.

  Definition indeB (B : bexp) (x : var) :=
    forall (s : var -> Z) (v : Z), bdenot B s = bdenot B (var_upd s x v).

  Lemma inde_bexp (B : bexp) (vs : list var) :
    List.Forall (indeB B) vs -> inde (bexp_to_assn B) vs.
  Proof.
    intros H v s h n; revert v.
    rewrite List.Forall_forall in *.
    unfold_conn_all; simpl in *;split; intros Heq.
    rewrite<-(H v H0 s); auto.
    rewrite (H v H0 s n); auto.
  Qed.

  Lemma add_nth_overflow (j : nat) : forall P Ps,
    (List.length Ps <= j)%nat -> add_nth j P Ps = Ps.
  Proof.
    induction j; destruct Ps; simpl in *; try omega; auto.
    intros H; rewrite IHj; auto; omega.
  Qed.    
    
  Lemma inde_nth_add_nth j Ps i P  vs : 
    inde P vs ->
    inde (List.nth i Ps emp) vs ->
    inde (List.nth i (add_nth j P Ps) emp) vs.
  Proof.
    intros.
    assert (j < List.length Ps \/ List.length Ps <= j)%nat as [|] by omega.
    assert (i < List.length Ps \/ List.length Ps <= i)%nat as [|] by omega.
    - rewrite nth_add_nth; auto; destruct (EqNat.beq_nat); [apply inde_sconj|] ; auto.
    - rewrite List.nth_overflow; [unfold inde, var_upd; simpl; try tauto|].
      rewrite add_nth_length; auto.
    - rewrite add_nth_overflow; auto.
  Qed.
  
  Lemma inde_distribute nt arr l f dist (i : nat) (vs : list var) : forall s,
    List.Forall (indelE arr) vs  ->
    inde (List.nth i (distribute nt arr l f dist s) emp) vs.
  Proof.
    induction l; intros; simpl.
    - simpl_nth. destruct (Compare_dec.leb _ _); inde_simpl; simpl; try tauto.
    - apply inde_nth_add_nth.
      + apply inde_pointto; auto; rewrite List.Forall_forall in *; intros;
        unfold indeE, indelE in *; simpl; intros; auto.
        forwards: H; eauto.
        destruct arr; simpl in *; inversion H1; rewrite H3; eauto.
      + apply IHl; auto.
  Qed.      

  Lemma inde_is_array len arr f vs : forall s,
    List.Forall (indelE arr) vs ->
    inde (is_array arr len f s) vs.
  Proof.
    induction len; intros; simpl.
    - unfold inde; intros; cbv; tauto.
    - apply inde_sconj; [apply inde_pointto|]; eauto.
      rewrite List.Forall_forall in *; intros. unfold indeE, indelE in *; simpl in *; intros.
      erewrite H; [reflexivity|eauto].
      apply List.Forall_forall; unfold indeE; intros; simpl; reflexivity.
  Qed.

  Lemma inde_is_array_p len arr f vs p : forall s,
    List.Forall (indelE arr) vs ->
    inde (is_array_p arr len f s p) vs.
  Proof.
    induction len; intros; simpl.
    - unfold inde; intros; cbv; tauto.
    - apply inde_sconj; [apply inde_pointto|]; eauto.
      rewrite List.Forall_forall in *; intros. unfold indeE, indelE in *; simpl in *; intros.
      erewrite H; [reflexivity|eauto].
      apply List.Forall_forall; unfold indeE; intros; simpl; reflexivity.
  Qed.

  Lemma inde_meta_if A B (b : {A} + {B}) Pt Pe vs :
    inde Pt vs -> inde Pe vs ->
    inde (if b then Pt else Pe) vs.
  Proof.
    destruct b; eauto.
  Qed.
End independent_prover.

Ltac prove_indeE := unfold indeE, indelE, var_upd in *; intros; simpl; auto.
Ltac prove_indeB := unfold indeB, var_upd in *; intros; simpl; auto.

Ltac prove_inde :=
  match goal with
    | [ |- inde (?P ** ?Q) _ ] => apply inde_sconj; prove_inde
    | [ |- inde !(?P) _ ] => apply inde_pure; prove_inde
    | [ |- inde (?P //\\ ?Q) _ ] => apply inde_conj; prove_inde
    | [ |- inde (?P \\// ?Q) _ ] => apply inde_disj; prove_inde
    | [ |- inde (?E -->p (_, ?E')) _ ] => apply inde_pointto; repeat (constructor; prove_indeE)
    | [ |- inde (?E === ?E') _ ] => apply inde_eeq; repeat (constructor; prove_indeE)
    | [ |- inde (?E ===l ?E') _ ] => apply inde_leeq; repeat (constructor; prove_indeE)
    | [ |- inde (bexp_to_assn ?B) _ ] => apply inde_bexp; repeat (constructor; prove_indeB)
    | [ |- inde (List.nth _ (distribute _ _ _ _ _ _) emp) _ ] =>
      apply inde_distribute; auto; repeat (constructor; prove_indeE)
    | [ |- inde (is_array _ _ _ _) _ ] =>
      apply inde_is_array; auto; repeat (constructor; prove_indeE)
    | [ |- inde (is_array_p _ _ _ _ _) _ ] =>
      apply inde_is_array_p; auto; repeat (constructor; prove_indeE)
    | [ |- inde (if _ then _ else _) _] => apply inde_meta_if; prove_inde
    | [ |- _ ] => try now (unfold inde, var_upd; simpl; try tauto) 
  end.

Section subA_simpl.
  Lemma subA_pointto (X : var) (E1 : loc_exp) (E2 E  : exp) (q : Qc) s h : 
    (subA X E (E1 -->p (q, E2))) s h ->
    (sublE X E E1 -->p (q, subE X E E2)) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn_all; simpl in *;
    repeat rewrite <-subE_assign, sublE_assign in *; auto.
  Qed.

  Lemma subA_sconj (P Q : assn) (X : var) (E : exp) s h :
    subA X E (P ** Q) s h -> (subA X E P  ** subA X E Q) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn.
    destruct H as (ph1 & ph2 & ? & ? & ? & ?); eexists; eauto.
  Qed.

  Lemma subA_conj (P Q : assn) (X : var) (E : exp) s h :
    subA X E (P //\\ Q) s h -> (subA X E P //\\ subA X E Q) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn; auto.
  Qed.

  Lemma subA_disj (P Q : assn) (X : var) (E : exp) s h :
    subA X E (P \\// Q) s h -> (subA X E P \\// subA X E Q) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn; auto.
  Qed.

  Lemma subA_pure (P : assn) (X : var) (E : exp) s h :
    subA X E !(P) s h -> !(subA X E P) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn; auto.
  Qed.

  Lemma subA_eeq (X : var) (E E1 E2 : exp) s h :
    subA X E (E1 === E2) s h -> (subE X E E1 === subE X E E2) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn_all; simpl in *;
    repeat rewrite <-subE_assign in *; auto.
  Qed.

  Lemma subA_leeq (X : var) (E : exp) (E1 E2 : loc_exp) s h :
    subA X E (E1 ===l E2) s h -> (sublE X E E1 ===l sublE X E E2) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn_all; simpl in *;
    repeat rewrite <-sublE_assign in *; auto.
  Qed.

  Lemma distribute_subA nt arr l f dist (i : nat) x e : forall s,
    subA x e (List.nth i (distribute nt arr l f dist s) emp) |=
    List.nth i (distribute nt (sublE x e arr) l f dist s) emp.
  Proof.
    induction l; [unfold subA'|]; intros s st hp H; simpl in *.
    - simpl_nth; destruct (Compare_dec.leb _ _); auto;
      split; intros; simpl; auto.
    - assert (dist s < nt \/ nt <= dist s)%nat as [|] by omega.
      + assert (i < nt \/ nt <= i)%nat as [|] by omega.
        * rewrite nth_add_nth in *; [|rewrite distribute_length; auto..].
          destruct (EqNat.beq_nat _ _); intuition.
          apply subA_sconj in H.
          revert st hp H; apply scRw; intros st hp H.
          apply subA_pointto in H; simpl in H. 
          destruct arr; eauto.
          applys* IHl.
        * rewrite List.nth_overflow in *; [|rewrite add_nth_length, distribute_length..]; auto.
      + rewrite add_nth_overflow in *; (try rewrite distribute_length); auto.
  Qed.

  (* Lemma skip_arr_subA x e arr st len skip f_ini i : *)
  (*   subA x e (skip_arr arr st len skip f_ini i) |= *)
  (*   skip_arr (sublE x e arr) st len skip f_ini i. *)
  (* Proof. *)
  (*   unfold skip_arr. *)
  (*   apply distribute_subA. *)
  (* Qed. *)

  Lemma subA_is_array (arr : loc_exp) (len : nat) (f : nat -> Z) x e: forall s,
    subA x e (is_array arr len f s) |= is_array (sublE x e arr) len f s.
  Proof.
    induction len; simpl; intros s stc h H.
    - apply H.
    - apply subA_sconj in H; revert h H; apply scRw_stack; intros h H; eauto.
      apply subA_pointto in H; destruct arr; apply H.
  Qed.

  Lemma subA_is_array_p (arr : loc_exp) (len : nat) (f : nat -> Z) x e p: forall s,
    subA x e (is_array_p arr len f s p) |= is_array_p (sublE x e arr) len f s p.
  Proof.
    induction len; simpl; intros s stc h H.
    - apply H.
    - apply subA_sconj in H; revert h H; apply scRw_stack; intros h H; eauto.
      apply subA_pointto in H; destruct arr; apply H.
  Qed.
End subA_simpl.

Lemma conj_mono (P Q P' Q' : assn) s h : (P s h -> P' s h) -> (Q s h -> Q' s h) ->
                                         (P //\\ Q) s h -> (P' //\\ Q') s h.
Proof.
  intros ? ? [? ?]; split; auto.
Qed.

Lemma disj_mono (P Q P' Q' : assn) s h : (P s h -> P' s h) -> (Q s h -> Q' s h) ->
                                         (P \\// Q) s h -> (P' \\// Q') s h.
Proof.
  intros ? ? [? | ?]; ((left; tauto) || (right; tauto)).
Qed.

Lemma pure_mono (P P' : assn) s h : (P s h -> P' s h) ->
                                    !(P) s h -> !(P') s h.
Proof.
  intros ? [? ?]; split; auto.
Qed.

Lemma subA_bexp_to_assn (x : var) (e : exp) (b : bexp) :
  subA x e (bexp_to_assn b) |= bexp_to_assn (subB x e b).
Proof.
  intros.
  unfold bexp_to_assn, subA' in *; simpl.
  rewrite <-subB_assign in H; auto.
Qed.

Lemma subA_emp (x : var) (e : exp) : subA x e emp |= emp.
Proof. unfold_conn; auto. Qed.

Lemma subA_pure' x e (P : Prop) : subA x e (pure P) |= (pure P).
Proof.
  unfold_conn; simpl; auto.
Qed.

Lemma subA_if_dec x e A B (d : {A} + {B}) (P Q : assn) :
  subA x e (if d then P else Q) |= if d then (subA x e P) else (subA x e Q).
Proof.
  destruct d; eauto.
Qed.

Lemma if_mono A B (d : {A} + {B}) (P P' Q Q' : assn) :
  P |= P' -> Q |= Q' ->
  (if d then P else Q) |= if d then P' else Q'.
Proof. destruct d; eauto. Qed.

Ltac subA_normalize_in H tac :=
  let Hf := fresh in
  match goal with _ => idtac end;
  match goal with [H : ?ty|- _] => idtac ty end;
  lazymatch type of H with
    | (_ ** _) _ _ =>
      eapply scRw in H;
        [ idtac | clear; intros ? ? Hf; subA_normalize_in Hf tac; exact Hf ..]
    | subA _ _ (_ ** _) _ _ =>
      apply subA_sconj in H; eapply scRw in H;
        [ idtac | clear; intros ? ? Hf; subA_normalize_in Hf tac; exact Hf .. ]
    | subA _ _ (_ //\\ _) _ _ =>
      apply subA_conj in H;  eapply conj_mono in H;
        [ idtac | clear; intros Hf; subA_normalize_in Hf tac; exact Hf .. ]
    | subA _ _ (_ \\// _) _ _ =>
      apply subA_disj in H;  eapply disj_mono in H;
        [ idtac | clear; intros Hf; subA_normalize_in Hf tac; exact Hf .. ]
    | subA _ _ (_ -->p (_, _)) _ _ => apply subA_pointto in H
    | subA _ _ !(_) _ _ => eapply subA_pure in H; eapply pure_mono in H;
        [ idtac | clear; intros Hf; subA_normalize_in Hf tac; exact Hf ]
    | subA _ _ (pure _) _ _ => apply subA_pure' in H
    | subA _ _ (_ === _) _ _ => apply subA_eeq in H
    | subA _ _ (_ ===l _) _ _ => apply subA_leeq in H
    | subA _ _ emp _ _ => apply subA_emp in H
    | subA _ _ (bexp_to_assn ?b) _ _ => apply subA_bexp_to_assn in H
    | subA _ _ (List.nth _ (distribute _ _ _ _ _ _) _) _ _ => apply distribute_subA in H; auto
    (* | subA _ _ (skip_arr _ _ _ _ _) _ _ => apply distribute_subA in H; auto *)
    | subA _ _ (is_array _ _ _ _) _ _ => apply subA_is_array in H; auto
    | subA _ _ (is_array_p _ _ _ _ _) _ _ => apply subA_is_array_p in H; auto
    | subA _ _ (if _ then _ else _) _ _ =>
      apply subA_if_dec in H; eapply if_mono in H;
      [ idtac | clear; intros ? ? Hf; subA_normalize_in Hf tac; exact Hf ..]
    | _ => try tac H; simpl in H
  end.
Tactic Notation "subA_normalize_in" hyp(H) "with" tactic(tac)  := subA_normalize_in H tac.
Tactic Notation "subA_normalize_in" hyp(H) := subA_normalize_in H with (fun x => idtac).

Example subA_test6 (E1 E2 : exp) (X : var) (E : exp) s h :
  subA X E (E1 === E2) s h -> (subE X E E1 === subE X E E2) s h.
Proof.
  intros. subA_normalize_in H.
Abort.
Ltac find_addr P E k :=
  idtac "find_addr debug:" P;
  match P with
    | (E -->p (?q, ?E1)) ** ?Q => k (Some 0)
    | _ ** ?Q => find_addr Q E ltac:(fun n =>
        match n with false => k false | Some ?n => k (Some (S n)) end)
    | _ => k false
  end.

Example find_addr_test E E1 P Q s h :(P ** (E -->p (1%Qc, E1)) ** Q) s h.
Proof.
  match goal with [ |- ?H ?s ?h ] => find_addr H E ltac:(fun n => idtac n) end.
  sep_lift 1. 
Abort.

Section hoare_lemmas.
  Variable ntrd : nat.
  Variable bspec : Bdiv.barrier_spec ntrd.
  Variable tid : Fin.t ntrd.
  Lemma Hbackward (P P' Q : assn) (C : cmd) :
    CSL bspec tid P' C Q -> (P |= P') -> CSL bspec tid P C Q.
  Proof.
    intros; eapply rule_conseq; eauto.
  Qed.

  Lemma Hforward (P Q Q' : assn) (C : cmd) :
    CSL bspec tid P C Q' -> (Q' |= Q) -> CSL bspec tid P C Q.
  Proof.
    intros; eapply rule_conseq; eauto.
  Qed.
End hoare_lemmas.

(* Definition equiv_sep (P Q : assn) := (forall s h, P s h <-> Q s h). *)
(* Notation "P <=> Q" := (equiv_sep P Q) (at level 87). *)

(* Ltac ltac_bug E H := *)
(*   match type of H with *)
(*     | ((_ ** _) _ _) => *)
(*       let Hf := fresh in *)
(*       eapply scRw_stack in H; [idtac | clear; intros ? Hf; exact Hf | *)
(*                                intros ? Hf; ltac_bug E Hf; exact Hf]; *)
(*       match goal with _ => idtac  end; *)
(*       match type of H with *)
(*         | ((_ ** _ ** _) _ _) => apply scCA in H *)
(*         | ((_ ** _) _ _) => apply scC in H *)
(*       end  *)
(*     | _ => idtac *)
(*   end. *)
(*
Example ltac_bug P Q s h n (tid : Fin.t n) :
  (P ** Q ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid))) s h -> False.
Proof.
  intros.
  sep_split_in H.
  ltac_bug (ARR + Z_of_fin tid) H.
Abort.

Example find_test P Q s h n (tid : Fin.t n) :
  (P ** Q ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid))) s h -> False.
Proof.
  intros.
  sep_split_in H.
  find_enough_resource (ARR + Z_of_fin tid) H.
Abort.
*)
Example sep_combine_test P Q R S s h : (P ** Q ** !(R) ** !(S)) s h -> True.
Proof.
  intros H; sep_split_in H.
  sep_combine_in H.
Abort.

Lemma rule_assign_forward (ntrd : nat) (bspec : Bdiv.barrier_spec ntrd) (tid : Fin.t ntrd) (X : var) (E : exp) (P : assn) :
  CSL bspec tid P (X ::= E) (Ex v, subA X (Enum v) P ** !(X === subE X v E)).
Proof.
  unfold subA'.
  eapply Hbackward.
  apply rule_assign.
  intros s h H; exists (s X).
  sep_split; unfold_conn; simpl.
  rewrite subE_assign; unfold var_upd; simpl.
  destruct (var_eq_dec X X) as [_|]; try congruence.
  f_equal; extensionality x.
  destruct (var_eq_dec _ _); subst; congruence.

  assert (Heq : s = var_upd (var_upd s X (edenot E s)) X (s X)); [|rewrite <-Heq; auto].
  extensionality x; unfold var_upd; destruct (var_eq_dec _ _); subst; congruence.
Qed.

Global Create HintDb sep.

Ltac simplify :=
  autounfold; simpl; autorewrite with sep.

Ltac frame_analysis P :=
  let Pe := fresh in
  evar (Pe : assn);
  let Hf := fresh in
  let s := fresh in
  let h := fresh in
  intros s h Hf;
  let Hf' := fresh in
  assert (Hf' : (P ** Pe) s h);
  [ simplify;
    repeat match goal with
      | [P' := ?ev : assn, H : ?Q ?s ?h |- ?P ?s ?h] => match P with
           | P' => is_evar ev; sep_combine_in H; exact H
        end
      | _ => progress (sep_split_in Hf; unfold lt in *; sep_cancel; sep_combine_in Hf)
    end | exact Hf' ].

Lemma rule_if_disj (ntrd : nat) (bspec : Bdiv.barrier_spec ntrd) (tid : Fin.t ntrd) (P Q1 Q2 : assn)
      (b : bexp) (C1 C2 : cmd) :
  CSL bspec tid (P ** !(b)) C1 Q1 -> CSL bspec tid (P ** !(Bnot b)) C2 Q2 ->
  CSL bspec tid (P) (Cif b C1 C2) (Q1 \\// Q2).
Proof.
  intros.
  eapply rule_if;
  eapply Hforward; unfold Apure; unfold bexp_to_assn in *;
  [eapply Hbackward; [apply H |] | | eapply Hbackward; [apply H0 |] |];
  try(intros; destruct H1; exists h (@emp_ph loc); repeat split; auto using disj_emp1); intros; unfold_conn; tauto.
Qed.

Definition WhileI (I : assn) (b : bexp) (c : cmd) := nosimpl (Cwhile b c).

Lemma safe_ex {T : Type} (Q : T -> assn) ntrd bspec tid n C s h x:
  @safe_nt ntrd bspec tid n C s h (Q x) ->
  @safe_nt ntrd bspec tid n C s h (Ex x, Q x).
Proof.
  revert n C s h ; induction n; intros C s h H; simpl in *; eauto.
  repeat split; intuition.
  - eexists; eauto.
  - destruct (H3 hF h0 c' ss' H4 H6 H7) as (? & ? & ? & ? & ? & ?).
    exists x0 x1; intuition.
  - destruct (H5 j c' H4) as (? & ? & ? & ? & ? & ? ).
    exists x0 x1; intuition.
Qed.  
    
Lemma rule_ex {T : Type} (P : T -> assn) Q ntrd bspec tid C:
  (forall x, @CSL ntrd bspec tid (P x) C Q) ->
  @CSL ntrd bspec tid (Ex x, P x) C Q.
Proof.
  intros H; simpl; intros s h [x Hsat] n; specialize (H x s h Hsat n); simpl in *.
  apply H.
Qed.

Corollary rule_ex' {T : Type} (P Q : T -> assn) ntrd bspec tid C:
  (forall x, @CSL ntrd bspec tid (P x) C (Q x)) ->
  @CSL ntrd bspec tid (Ex x, P x) C (Ex x, Q x).
Proof.
  intros.
  apply rule_ex.
  intros x s h; simpl; intros Hp n.
  apply H in Hp.
  apply safe_ex with x; auto.
Qed.

Ltac hoare_forward :=
  match goal with
    | [ |- CSL ?bspec ?tid (?P1 \\// ?P2) ?C ?Q ] =>
      eapply rule_disj; hoare_forward
    | [ |- CSL ?bspec ?tid (Ex _, _) ?C ?Q ] =>
      eapply rule_ex; intros ?
    | [ |- CSL ?bspec ?tid ?P (?X ::= [?E]) ?Q ] => 
      idtac "case: read";
      let Hf := fresh in
      let s := fresh in
      eapply Hbackward; [idtac |
        intros s ? Hf;
        sep_normal_in Hf;
        sep_split_in Hf;
        find_enough_resource E Hf;
        sep_combine_in Hf;
        exact Hf];
      eapply Hforward; [
        eapply rule_frame;
        [eapply rule_read; idtac "ok!!!"; prove_indeE | prove_inde] | prove_inde ]
    | [ |- CSL ?bspec ?tid ?P ([?E] ::= _) ?Q ] =>
      idtac "case: write";
      let Hf := fresh in
      let s := fresh in
      eapply Hbackward; [idtac |
        intros s ? Hf;
        sep_normal_in Hf;
        sep_split_in Hf;
        find_enough_resource E Hf;
        sep_combine_in Hf;
        exact Hf];
      eapply Hforward; [
        eapply rule_frame;
        [eapply rule_write; idtac "ok!!!" | prove_inde ] | idtac]
    | [ |- CSL ?bspec ?tid ?P (?X ::= _) ?Q] =>
      let Hf := fresh in
      eapply Hforward; [
        apply rule_assign_forward | idtac ]
    | [ |- CSL ?bspec ?tid ?P (Cbarrier ?i) ?Q] =>
      idtac "called";
      eapply Hforward; [
        eapply Hbackward; [
          eapply rule_frame; 
          [apply rule_barrier | prove_inde] |
           autounfold; simpl; repeat rewrite MyVector.init_spec in *] | 
        (* frame_analysis (Vector.nth (fst (bspec i)) tid) *)]
    | [ |- CSL ?bspec ?tid ?P (Cif ?b ?c1 ?c2) ?Q ] =>
      eapply Hbackward; [
          eapply Hforward; [
            eapply rule_if_disj | idtac] |
          idtac
        ]
    | [ |- CSL ?bspec ?tid ?P (WhileI ?I ?b ?c) ?Q ] => 
      let Hf := fresh in
      eapply Hbackward; [
        eapply Hforward; [apply (@rule_while _ _ _ I) | idtac] |
        idtac
      ]
  end.