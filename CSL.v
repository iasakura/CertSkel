Require Import QArith.
Require Import Qcanon.
Require Import MyVector.
Require Import List.
Add LoadPath "../../src/cslsound".
Require Import Lang.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import PHeap.
Require Import Bdiv.

Section SeqCSL.
  Variable ntrd : nat.
  Variable bspec : nat -> (Vector.t assn ntrd * Vector.t assn ntrd)%type.
  Variable E : env.

  Definition low_assn (P : assn) : Prop := low_assn E P.

  Section Vnotation.
    Section For_Vector_Notation.
      Import VectorNotations.
    Hypothesis brr_lowassn : forall (i : nat),
                               (forall tid : Fin.t ntrd, low_assn (fst (bspec i))[@tid]) /\
                               (forall tid : Fin.t ntrd, low_assn (fst (bspec i))[@tid]).
    Hypothesis brr_wf : forall (i : nat) (st : pstate),
                          sat st (Aistar_v (fst (bspec i))) <-> sat st (Aistar_v (snd (bspec i))).
    Hypothesis bc_precise :
      forall i (tid : Fin.t ntrd), precise (fst (bspec i))[@tid] /\
                                   precise (snd (bspec i))[@tid].
    End For_Vector_Notation.
  End Vnotation.
  Variable tid : Fin.t ntrd.
  Definition safe_nt := safe_nt bspec tid.

  Definition CSL (p : assn) (c : cmd) (q : assn) := 
    forall s ph, sat (s, ph) p -> forall (n : nat), safe_nt n c s ph q.

  Lemma rule_skip (Q : assn) : CSL Q Cskip Q.
  Proof.
    unfold CSL; intros st ph H n; induction n; simpl; eauto; repeat split; simpl; eauto.
    - intros; inversion 1.
    - intros ? ? ? ? ? ? hred; inversion hred.
    - intros ? ? heq; inversion heq.
  Qed.

  Lemma access_ok_mono (C : cmd) (s : stack) (ph phF : pheap) (dis : pdisj ph phF) :
    access_ok C s ph -> access_ok C s (phplus_pheap dis).
  Proof.
    intros hok; induction C; eauto; unfold access_ok in *; simpl in *;
    destruct hok as [[q v] H]; unfold phplus; rewrite H; 
    match goal with
          [  |- context [match ?v with | Some _ => _ | None => _ end] ] => 
            destruct v as [[? ?]|] end; eexists; eauto.
  Qed.

  Lemma write_ok_mono (C : cmd) (s : stack) (ph phF : pheap) (dis : pdisj ph phF) :
    write_ok C s ph -> write_ok C s (phplus_pheap dis).
  Proof.
    intros hok; induction C; eauto; unfold write_ok in *; simpl in *;
    destruct phF as [phF ispF], ph as [ph isp]; unfold phplus; simpl in *.
    specialize (dis (edenot e1 s)); specialize (ispF (edenot e1 s)).
    destruct hok as [v H]; unfold phplus; rewrite H in *; simpl.
    match goal with
        [  |- context [match ?v with | Some _ => _ | None => _ end] ] => 
        destruct v as [[? ?]|] end.
    - assert (full_p + q <= 1) by tauto.
      assert (0 < q) by tauto.
      apply frac_contra1 in H0; [tauto| eauto ].
    - exists v; eauto.
  Qed.

  Fixpoint writes_var (c : cmd) : list var :=
    match c with
      | Cskip | Cwrite _ _ | Cbarrier _ => nil
      | Cassign v _ | Cread v _ => v :: nil
      | Cseq c1 c2 => writes_var c1 ++ writes_var c2
      | Cif _ c1 c2 => writes_var c1 ++ writes_var c2
      | Cwhile _ c => writes_var c
    end%list.

  Lemma writes_agrees (c1 c2 : cmd) (st1 st2 : state) :
    c1 / st1 ==>s c2 / st2 ->
    fst st1 = fst st2 \/
    exists x v : Z, In x (writes_var c1) /\ fst st2 = upd (fst st1) x v.
  Proof.
    induction 1; try (left; now eauto).
    - destruct IHred as [ ? | [x [ v [Hin Heq] ]] ]; [tauto | right].
      exists x, v; split; eauto.
      apply In_app; eauto.
    - right; exists x, (edenot e s); split; [constructor | subst]; eauto.
    - right; exists x, v; split; [constructor | subst]; eauto.
    - left; subst; eauto.
  Qed.

  Definition inde (R : assn) (ls : list var) :=
    forall (x : var) (s : stack) (h : pheap) (v : Z),
      In x ls -> (sat (s, h) R <-> sat ((upd s x v), h) R).

  Lemma writes_agrees' (c1 c2 : cmd) (st1 st2 : state) (h : pheap) (R : assn):
    c1 / st1 ==>s c2 / st2 ->
    inde R (writes_var c1) ->
    sat (fst st1, h) R -> sat (fst st2, h) R.
  Proof.
    intros hred hinde hsat; apply writes_agrees in hred as [heq | [x [v [Hin Heq]]]].
    - rewrite <-heq; eauto.
    - rewrite Heq; apply hinde; eauto.
  Qed.

  Lemma writes_inv (c1 c2 : cmd) (st1 st2 : state) :
    c1 / st1 ==>s c2 / st2 -> forall x, In x (writes_var c2) -> In x (writes_var c1).
  Proof.
    induction 1; simpl; eauto.
    - intros x H'; specialize (IHred x); apply In_app; apply In_app in H'; tauto.
    - intros x H; apply In_app; tauto.
    - intros x H; apply In_app; tauto.
    - intros x H; apply In_app in H; destruct H.
      + apply In_app in H; tauto.
      + inversion H.
  Qed.

  Lemma wait_writes (c1 c2 : cmd) (j : nat) :
    wait c1 = Some (j, c2) -> forall x, In x (writes_var c2) -> In x (writes_var c1).
  Proof.
    revert j c2; induction c1; simpl; try now inversion 1.
    intros j c2; destruct (wait c1_1) as [[? ?]|]; intros H; inversion H; inversion H2.
    simpl; intros x H'; apply In_app in H'; apply In_app.
    specialize (IHc1_1 n c eq_refl x); tauto.
  Qed.

  Lemma inde_inv1 (c1 c2 : cmd) (st1 st2 : state) (R : assn) :
    c1 / st1 ==>s c2 / st2 -> inde R (writes_var c1) -> inde R (writes_var c2).
  Proof.
    intros H hinde x s h v Hin; specialize (hinde x s h v). 
    apply (writes_inv H) in Hin; tauto.
  Qed.

  Lemma inde_inv2 (c1 c2 : cmd) (j : nat) (R : assn) :
    wait c1 = Some (j, c2) -> inde R (writes_var c1) -> inde R (writes_var c2).
    intros H hinde x s h v Hin; specialize (hinde x s h v). 
    apply (wait_writes H) in Hin; tauto.
  Qed.

  Lemma writes_agrees_mul (c1 c2 : cmd) (st1 st2 : state) (h : pheap) (R : assn):
    c1 / st1 ==>s* c2 / st2 ->
    inde R (writes_var c1) ->
    sat (fst st1, h) R -> sat (fst st2, h) R.
  Proof.
    unfold multi_red, multi_red_tup. 
    remember (c1, st1) as s1; remember (c2, st2) as s2. 
    cutrewrite (c1 = fst s1); [|subst; eauto]; cutrewrite (st1 = snd s1); [|subst; eauto];
    cutrewrite (st2 = snd s2); [|subst; eauto].
    clear c1 c2 st1 st2  Heqs1 Heqs2.
    induction 1; intros hinde hsat; eauto.
    destruct x as [c1 st1], y as [c2 st2], z as [c3 st3].
    unfold red_tup in H.
    apply IHclos_refl_trans_1n.
    apply (inde_inv1 H); eauto.
    apply (writes_agrees' H); eauto.
  Qed.

  Lemma safe_frame : 
    forall (n : nat) (C : cmd) (s : stack) (ph phR : pheap) (Q R : assn) (disR : pdisj ph phR),
      safe_nt n C s ph Q -> sat (s, phR) R -> inde R (writes_var C) ->
      safe_nt n C s (phplus_pheap disR) (Astar Q R).
  Proof.
    induction n; intros C s ph phR Q R disR hsafe hsatR hinde; unfold safe_nt; simpl; eauto; 
    repeat split; unfold safe_nt in hsafe; simpl in *.
    - intros ?; subst; repeat eexists; eauto.
      destruct hsafe as [hsafe _]; specialize (hsafe eq_refl);
      tauto.
    - intros hf h hdis heq.
      destruct hsafe as [_ [hsafe _]].
      assert (pdisj hf phR) as disfh by (apply pdisjC in hdis; apply pdisjE2 in hdis; eauto).
      assert (pdisj hf ph) as disf by (apply pdisjC in hdis; apply pdisjE1 in hdis; eauto).
      assert (phplus (phplus ph phR) hf = phplus (phplus ph hf) phR) as heqp.
      { rewrite <-(phplus_eq disR), phplus_comm; eauto; simpl. 
        rewrite (phplus_comm disR), padd_left_comm; eauto; 
        [ | rewrite (phplus_comm (pdisjC disR)); eauto].
        rewrite <-(phplus_eq disf), phplus_comm; simpl; rewrite (@phplus_comm hf ph); eauto.
        Hint Resolve pdisjC.
        apply pdisj_padd_expand; eauto; rewrite (@phplus_comm phR ph); eauto. }
      rewrite heqp, padd_assoc, <-(phplus_eq  disfh) in heq; eauto.
      assert (pdisj ph (phplus_pheap disfh)) as dis' by (apply pdisj_padd_comm; eauto).
      apply (hsafe _ _ dis' heq).
    - apply access_ok_mono; tauto.
    - apply write_ok_mono; tauto.
    - intros hF h c' ss' hdis heq hred.
      assert (phplus (phplus ph phR) hF = phplus ph (phplus phR hF)).
      { apply padd_assoc; eauto.
        apply pdisj_padd_expand in hdis; tauto.
        apply pdisjC in hdis; apply pdisjE2 in hdis; eauto. }
      destruct hsafe as [_ [_ [_ [_ [hsafe _]]]]].
      assert (pdisj ph (phplus phR hF)) as hdis'.
      { apply pdisj_padd_expand in hdis; eauto; tauto. }
      apply pdisjC in hdis; apply pdisjE2 in hdis; apply pdisjC in hdis.
      rewrite H, <- (phplus_eq hdis) in heq.
      rewrite <-(phplus_eq hdis) in hdis'.
      destruct (hsafe _ _ _ _ hdis' heq hred) as  [h' [ph' [? [hdis'' [? ?]]]]]. 
      assert (pdisj ph' phR) as dis'R by (simpl in hdis''; apply pdisjE1 in hdis''; eauto).
      assert (pdisj (phplus_pheap dis'R) hF) as dis''' by (simpl; apply pdisj_padd_expand; eauto).
      exists h', (phplus_pheap dis'R); repeat split; eauto.
      cutrewrite (phplus (phplus_pheap dis'R) hF = phplus ph' (phplus_pheap hdis));
        [eauto| apply padd_assoc; eauto].
      apply IHn; eauto.
      apply (writes_agrees' hred); eauto. apply (inde_inv1 hred); eauto.
      apply pdisjE1 in hdis'; eauto.
      apply pdisjC, pdisjE2, pdisjC in hdis; eauto.
    - destruct hsafe as [_ [_ [_ [_ [_ hsafe]]]]].
      intros j c' H; destruct (hsafe j c' H) as [phP [ph' [hdisP' [heqP' [Hsat Hq]]]]].
      assert (pdisj ph' phR) as hdis'R by (rewrite <-heqP' in disR; 
                                           apply pdisjC, pdisjE2 in disR; eauto).
      exists phP, (phplus_pheap hdis'R); repeat split; eauto; simpl.
      apply pdisj_padd_expand; eauto; rewrite <-heqP' in disR; eauto.
      rewrite <- heqP', padd_assoc; eauto.
      apply pdisj_padd_expand; eauto; rewrite <-heqP' in disR; eauto.
      intros phQ H0 Hsatq.
      assert (pdisj phQ ph') by (apply pdisjE1 in H0; eauto).
      specialize (Hq phQ H1 Hsatq).
      assert (pdisj (phplus phQ ph') phR).
      { apply pdisj_padd_expand; eauto. }
      cutrewrite (phplus_pheap (h1:=phQ) (h2:=phplus_pheap (h1:=ph') (h2:=phR) hdis'R) H0 = 
                  phplus_pheap (h1:=phplus_pheap H1) (h2:=phR) H2); 
        [|apply pheap_eq; simpl; rewrite padd_assoc; eauto].
      apply IHn; eauto; unfold safe_nt.
      apply (inde_inv2 H); eauto.
  Qed.
  
  Lemma rule_frame (C : cmd) (P Q R : assn) :
    CSL P C Q -> inde R (writes_var C) ->
    CSL (Astar P R) C (Astar Q R).
  Proof.
    unfold CSL; intuition. ins. desf. 
    cutrewrite (ph = phplus_pheap H3); [|destruct ph; apply pheap_eq; eauto].
    apply safe_frame; eauto.
  Qed.

End SeqCSL.