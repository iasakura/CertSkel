Require Import SetoidClass.

Require Import Lang PHeap MyList CSL assertions assertion_lemmas VCG Qcanon array_dist.

Instance app_proper (s : stack) (h : pheap) : Proper (equiv_sep s ==> iff) (fun P => P s h).
Proof.
  intros P Q H.
  specialize (H h); auto.
Qed.

Ltac fold_pure H s :=
  lazymatch type of H with
    | ?X =>
      let Hf := fresh in
      assert (Hf : !(pure X) s emp_ph) by (apply pure_emp; [auto|apply emp_emp_ph]);
        clear H; rename Hf into H
end.

Ltac sep_rewrite_in lem H :=
  match type of H with
    | ?X _ _ => pattern X in H
  end; erewrite lem in H; cbv beta in H. 

Notation nf tid := (nat_of_fin tid).

Lemma ex_lift_l {T : Type} (P : T -> assn) (Q : assn) :
  (Ex x, P x ** Q) |= (Ex x, P x) ** Q.
Proof.
  intros; unfold_conn; destruct H as (x & H & ? & ? & ? & ? & ?).
  repeat eexists; eauto.
Qed.

Lemma sep_rewrite_var (v : var) (E : exp) (P : assn) s h:
  (v === E) s (emp_ph loc) -> P s h -> subA v E P s h.
Proof.
  unfold eeq, ban, subA'; simpl; intros.
  assert (Heq: var_upd s v (edenot E s) = s); [|rewrite Heq; auto].
  extensionality v'; unfold var_upd; rewrite <-H; destruct var_eq_dec; congruence.
Qed.

Lemma mps_eq1 (E1 E1' : loc_exp) (E2  : exp) (q : Qc) :
  forall s,
    (E1 ===l E1') s (emp_ph loc) ->
    s ||= E1 -->p (q, E2) <=> E1' -->p (q, E2).
Proof.
  intros s H1 h; split; intros; eapply mapsto_rewrite1; eauto;
  unfold_conn_all; simpl in *; auto.
Qed.

Lemma mps_eq2 (E1 : loc_exp) (E2 E2'  : exp) (q : Qc) :
  forall s,
    (E2 === E2') s (emp_ph loc) ->
    s ||= E1 -->p (q, E2) <=> E1 -->p (q, E2').
Proof.
  intros s H1 h; split; intros; eapply mapsto_rewrite2; eauto;
  unfold_conn_all; simpl in *; auto.
Qed.

Ltac sep_rewrite_in_r lem H :=
  match type of H with
    | ?X _ _ => pattern X in H
  end; rewrite <-lem in H; cbv beta in H.

Lemma ex_lift_r_in (T : Type) (P : assn) (Q : T -> assn) :
  (P ** Ex x, Q x) |= (Ex x : T, P ** Q x).
Proof.
  unfold_conn. intros ? ? (? & ? & ? & [? ?] & ? & ?).
  repeat eexists; eauto.
Qed.
Lemma ex_lift_l_in (T : Type) (P : T -> assn) (Q : assn) :
  ((Ex x, P x) ** Q) |= (Ex x : T, P x ** Q).
Proof.
  unfold_conn. intros ? ? (? & ? & [? ?] & ? & ? & ?).
  repeat eexists; eauto.
Qed.

Ltac change_in H :=
  lazymatch type of H with
    | _ ?s ?h =>
      let P := fresh "P" in 
      let Hf := fresh "H" in
      evar (P : assn); assert (Hf : P s h); unfold P in *; clear P; [| clear H; rename Hf into H]
  end.

Ltac change_ :=
  lazymatch goal with
    | [|-_ ?s ?h] =>
      let P := fresh "P" in 
      let Hf := fresh "H" in
      evar (P : assn); cut (P s h); unfold P in *; clear P; [|]
  end.


Ltac forward_barr := lazymatch goal with
  | [ |- CSL ?bspec ?tid ?P (Cbarrier ?i) ?Q] =>
    eapply Hbackward; [
        eapply Hforward; [
          eapply rule_frame; 
          [eapply rule_barrier |
           unfold inde; simpl; intros; match goal with [H : False |- _] => destruct H end] |
          autounfold; simpl; repeat rewrite MyVector.init_spec in *] | ] end.

Ltac bexp H :=
  unfold_conn_in H; simpl in H;
  lazymatch type of H with
    | context [if ?X then _ else _] => destruct X; simpl in H; try (congruence ||omega)
  end.

Ltac subst_expr E :=
  repeat lazymatch goal with
    | [H : (Enum E === _) _ (emp_ph loc) |- _] => try (unfold_conn_in H; simpl in H; rewrite H in *; clear H)
    | [H : pure (E = _) _ (emp_ph loc) |- _] => try (unfold_conn_in H; rewrite H in *; clear H)
end.

Ltac sep_rewrite_r lem :=
  match goal with
    | [|- ?X _ _] => pattern X
  end; erewrite <-lem; cbv beta. 


Lemma mps_eq1' (E : loc_exp) (E1 E1' E2 : exp) (p : Qc) (s : stack) :
  (E1 === E1') s (emp_ph loc) ->
  s ||= (E +o E1) -->p (p, E2) <=> (E +o E1') -->p (p, E2).
Proof.
  unfold_conn; simpl; split; intros; destruct (ledenot E _);
  try rewrite H in *; eauto.
Qed.

