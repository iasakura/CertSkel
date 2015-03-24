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
    Import VectorNotations.
    Hypothesis brr_lowassn : forall (i : nat),
                               (forall tid : Fin.t ntrd, low_assn (fst (bspec i))[@tid]) /\
                               (forall tid : Fin.t ntrd, low_assn (fst (bspec i))[@tid]).
    Hypothesis brr_wf : forall (i : nat) (st : pstate),
                          sat st (Aistar_v (fst (bspec i))) <-> sat st (Aistar_v (snd (bspec i))).
    Hypothesis bc_precise :
      forall i (tid : Fin.t ntrd), precise (fst (bspec i))[@tid] /\
                                   precise (snd (bspec i))[@tid].
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

  Import Lists.List.ListNotations.
  Open Scope list_scope.
  Fixpoint writes_var (c : cmd) : list var :=
    match c with
      | Cskip | Cwrite _ _ | Cbarrier _ => [ ]
      | Cassign v _ | Cread v _ => v :: []
      | Cseq c1 c2 => writes_var c1 ++ writes_var c2
      | Cif _ c1 c2 => writes_var c1 ++ writes_var c2
      | Cwhile _ c => writes_var c
    end%list.

  Lemma safe_frame : 
    forall (n : nat) (C : cmd) (s : stack) (ph phR : pheap) (Q R : assn) (disR : pdisj ph phR),
      safe_nt n C s ph Q -> sat (s, phR) R -> 
      safe_nt n C s (phplus_pheap disR) (Astar Q R).
    Proof.
      induction n; intros C s ph phR Q R disR hsafe hsatR; unfold safe_nt; simpl; eauto; 
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
(*        apply pdisjC, pdisjE1, pdisjC in hdis.*)
        rewrite <-(phplus_eq hdis) in hdis'.
        destruct (hsafe _ _ _ _ hdis' heq hred) as  [h' [ph' [? [hdis'' [? ?]]]]]. 
        assert (pdisj ph' phR) as dis'R by (simpl in hdis''; apply pdisjE1 in hdis''; eauto).
        assert (pdisj (phplus_pheap dis'R) hF) as dis''' by (simpl; apply pdisj_padd_expand; eauto).
        exists h', (phplus_pheap dis'R); repeat split; eauto.
        cutrewrite (phplus (phplus_pheap dis'R) hF = phplus ph' (phplus_pheap hdis));
          [eauto| apply padd_assoc; eauto].
        apply IHn; eauto.