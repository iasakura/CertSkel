Require Import List Omega.
Require Import TLC.LibTactics.
Require Import Lang CSLLemma Bdiv SeqRules.

Inductive fv_assn : assn -> list var -> Prop :=
| fv_assn_base R P E xs : incl (List.map ent_e E) xs -> fv_assn (Assn R P E) xs
| fv_assn_Ex T (P : T -> assn) xs :
    (forall v, fv_assn (P v) xs) -> fv_assn (Ex v, P v) xs
| fv_assn_sep P Q xs ys zs :
    fv_assn P ys -> fv_assn Q zs -> (forall x, In x xs <-> In x ys \/ In x zs) ->
    fv_assn (P ** Q) xs.

Lemma inde_equiv R ls:
  (forall x s h v, In x ls -> sat s h R -> sat (var_upd s x v) h R)
  -> inde R ls.
Proof.
  unfold inde; intros; splits; eauto.
  intros.
  forwards*: (>> H (s x)).
  equates 3; eauto.
  extensionality y; unfold var_upd; destruct var_eq_dec; congruence.
Qed.

Lemma disjoint_nil_r (T : Type) (l : list T) : disjoint l nil.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma disjoint_cons_r (T : Type) (x : T) (l1 l2 : list T) :
  disjoint l1 l2 -> ~(List.In x l1) -> disjoint l1 (x :: l2).
Proof.
  induction l1; simpl; eauto.
  intros; intuition.
Qed.

Hint Resolve disjoint_nil_r disjoint_cons_r.

Lemma disjoint_comm (T : Type) (l1 l2 : list T) : disjoint l1 l2 -> disjoint l2 l1.
Proof.
  revert l2; induction l1; simpl; eauto.
  intros.
  apply disjoint_cons_r; jauto.
Qed.  

Lemma disjoint_not_in_r (T : Type) (l1 l2 : list T) (x : T) :
  disjoint l1 l2 -> In x l2 -> ~In x l1.
Proof.
  intros. apply disjoint_comm in H; induction l2; eauto.
  simpl in *.
  destruct H0; subst; intuition.
Qed.

Lemma not_in_disjoint (T : Type) (l1 l2 : list T)  :
  (forall x, In x l1 -> ~In x l2) -> disjoint l1 l2.
Proof.
  revert l2; induction l1; simpl; eauto.
  intros l2 Hx.
  split.
  - apply Hx; eauto.
  - apply IHl1; intros; eauto.
Qed.

Lemma fv_assn_ok : forall P xs ys,
  fv_assn P xs -> disjoint xs ys -> inde P ys.
Proof.
  introv; induction 1.
  - intros.
    apply inde_equiv; intros.
    unfold sat in *; simpl in *; splits; jauto.
    destruct H2 as (? & ? & Henv); revert H H0 H1 Henv; clear.
    induction E as [|[y n] E]; simpl; eauto.
    intros.
    split.
    + unfold ent_assn_denote, var_upd in *; destruct var_eq_dec; simpl in *; try tauto.
      substs.
      assert (In x xs) by (unfold incl in *; specialize (H x); simpl in *; eauto).
      forwards*: (>>disjoint_not_in_r xs ys).
    + apply IHE; jauto.
      unfold incl in *; simpl in *; eauto.
  - intros; apply inde_equiv; unfold sat; simpl; intros.
    destruct H3 as [a H3]; exists a.
    apply H0; eauto.
  - intros; apply inde_equiv; unfold sat; simpl; intros.
    destruct H4 as (h1 & h2 & ? & ? & ? & ?); exists h1 h2; splits; jauto.
    + apply IHfv_assn1; eauto.
      apply not_in_disjoint; intros; intros Hc; eauto.
      assert (In x0 xs) by (specialize (H1 x0); tauto).
      forwards*: (>>disjoint_not_in_r H2).
    + apply IHfv_assn2; eauto.
      apply not_in_disjoint; intros; intros Hc; eauto.
      assert (In x0 xs) by (specialize (H1 x0); tauto).
      forwards*: (>>disjoint_not_in_r H2).
Qed.

Definition has_no_vars (P : assn) : Prop := fv_assn P nil.

Lemma has_no_vars_ok P h :
  has_no_vars P -> forall s s', sat s h P <-> sat s' h P.
Proof.
  cut (forall s s', has_no_vars P -> sat s h P -> sat s' h P); [intros; splits; eauto|].
  unfold has_no_vars; introv.
  Require Import Program.
  intros Hfv; revert h; dependent induction Hfv; introv.
  - assert (E = nil).
    { unfold incl in *; simpl in *; destruct E as [|[x ?] ?]; eauto; specialize (H x); simpl in *; tauto. }
    substs; unfold sat; simpl; tauto.
  - unfold sat; simpl.
    intros [x Hsat]; exists x; apply H0; eauto.
  - simpl in *.
    assert (ys = nil) by (destruct ys as [|y ys]; eauto; specialize (H y); simpl in *; tauto).
    assert (zs = nil) by (destruct zs as [|z zs]; eauto; specialize (H z); simpl in *; tauto).
    substs.
    unfold sat; simpl; intros (h1 & h2 & ? & ? & ? & ?); exists h1 h2; splits; unfold sat in *; jauto.
Qed.            

Lemma fv_assn_novars : forall P, has_no_vars P -> fv_assn P nil.
Proof.
  unfold has_no_vars; eauto.
Qed.
Lemma fv_assn_sep_eq : forall P Q xs, fv_assn (P ** Q) xs <-> exists ys zs, fv_assn P ys /\ fv_assn Q zs /\ (forall x, In x xs <-> In x ys \/ In x zs).
Proof.
  split; intros.
  - inverts H; do 2 eexists; jauto.
  - destruct H as (? & ? & ?); econstructor; jauto.
Qed.

Lemma fv_assn_base_eq :
  forall R P E xs, fv_assn (Assn R P E) xs <-> incl (List.map ent_e E) xs.
Proof.
  split; intros.
  - inverts H; jauto.
  - constructor; eauto.
Qed.

Lemma fv_assn_Ex_eq :
  forall T (P : T -> assn) xs, fv_assn (Ex v, P v) xs <-> (forall v, fv_assn (P v) xs).
Proof.
  split; intros.
  - inverts H.
    cutrewrite (P v = P1 v); eauto.
    assert (id (fun v : T => P1 v) v = id (fun v : T => P v) v) by (rewrites* H0).
    eauto.
  - constructor; eauto.
Qed.