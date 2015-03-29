Require Import QArith.
Require Import Qcanon.
Require Import MyVector.
Require Import List.
Require Import ZArith.
Add LoadPath "../../src/cslsound".
Require Import Lang.
Require Import Relation_Operators.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import PHeap.
Require Import Bdiv.

Notation "P '|=' Q" := (forall x, sat x P -> sat x Q) (at level 100).

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

  Lemma safe_skip : forall n s h Q, sat (s,h) Q -> safe_nt n Cskip s h Q.
  Proof.
    intros; destruct n; simpl; eauto; repeat split; eauto.
    intros. intros Hc; inversion Hc.
    intros ? ? ? ? ? ? Hc; inversion Hc.
    intros ? ? Hc; inversion Hc.
  Qed.

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
      assert (pdisj ph (phplus phR hF)) as hdis'.
      { apply pdisj_padd_expand in hdis; eauto; tauto. }
      assert (phplus (phplus ph phR) hF = phplus ph (phplus phR hF)).
      { apply padd_assoc; eauto.
        apply pdisjC in hdis; apply pdisjE2 in hdis; eauto. }
      destruct hsafe as [_ [_ [_ [_ [hsafe _]]]]].
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

  (* what happen !?*)
  Local Open Scope nat_scope.
  Lemma safe_mon :
    forall n C s h Q (OK: safe_nt n C s h Q) m (LEQ: m <= n),
      safe_nt m C s h Q.
  Proof.
    unfold safe_nt.
    induction [C s n h OK] m; ins.
    destruct n; clarify; simpls; des; repeat split; ins.
    exploit OK3; eauto; ins; des; eauto 10.
    exploit OK4; eauto; ins; des; eauto 10.
  Qed.

  Lemma safe_seq : forall (n : nat) (C C2 : cmd) (s : stack) (ph : pheap) (Q R : assn),
    safe_nt n C s ph Q ->
    (forall m s' ph', m <= n -> sat (s', ph') Q -> safe_nt m C2 s' ph' R)%nat ->
    safe_nt n (C ;; C2) s ph R.
  Proof.
    induction n; intros C C2 s ph Q R hsafe H; simpl; eauto; unfold safe_nt in *.
    repeat split; [congruence| | | | | ].
    - intros hf h hdis heq Haborts; inversion Haborts; subst; simpl in *.
      destruct hsafe as [_ [Ha _]]. eapply Ha in A; eauto.
    - destruct hsafe as [_ [_ [Hok _]]]; eauto.
    - destruct hsafe as [_ [_ [_ [Hok _]]]]; eauto.
    - intros hF h c' ss hdis heq hred; inversion hred; subst.
      + repeat eexists; simpl; eauto; apply H; eauto; simpl in hsafe.
        destruct hsafe as [hsafe _]; apply (hsafe eq_refl).
      + simpl in hsafe. destruct hsafe as [_ [_ [_ [_ [hsafe _]]]]].
        destruct (hsafe _ _ _ _ hdis heq R0) as [h' [ph' Hs]].
        exists h', ph'; repeat split; try tauto.
        apply (IHn c1' C2 _ _ Q R); eauto; tauto.
    - destruct hsafe as [_ [_ [_ [_ [_ hsafe]]]]].
      intros j c' Heqw; inversion Heqw; destruct (wait C) as [[j' C']|]; inversion H1; subst.
      destruct (hsafe j C' eq_refl) as [phP [ph' Hs]].
      exists phP, ph'; repeat split; try tauto.
      intros phQ H0 Hsat.
      destruct Hs as [_ [_ [_ hsafen]]]. specialize (hsafen phQ H0 Hsat).
      apply (IHn _ _ _ _ Q _); eauto.
  Qed.

  Lemma rule_seq (C1 C2 : cmd) (P Q R : assn) :
    CSL P C1 Q -> CSL Q C2 R -> CSL P (C1 ;; C2) R.
  Proof.
    unfold CSL, safe_nt. intuition; simpl.
    apply (safe_seq (Q := Q)); unfold safe_nt; eauto.
  Qed.
  
  Lemma rule_if (C1 C2 : cmd) (B : bexp) (P Q : assn) :
    CSL (Aconj P (Apure B)) C1 Q ->
    CSL (Aconj P (Apure (Bnot B))) C2 Q ->
    CSL P (Cif B C1 C2) Q.
  Proof.
    unfold CSL, safe_nt; intuition; destruct n; [simpl; eauto|]; ins; intuition; des.
    - inversion H2.
    - inversion H4.
    - unfold access_ok; simpl; eauto.
    - unfold write_ok; simpl; eauto.
    - inversion H4; subst; repeat eexists; eauto; simpl.
      apply H0; split; eauto; simpl in *; eauto; rewrite B0; eauto.
    - inversion H2.
  Qed.

  Lemma safe_while :
    forall P B C (OK: CSL (Aconj P (Apure B)) C P) s h (SAT_P: sat (s, h) P) n,
      safe_nt n (Cwhile B C) s h (Aconj P (Apure (Bnot B))).
  Proof.
    unfold safe_nt.
    intros; revert s h SAT_P; generalize (lenn n); generalize n at -2 as m.
    induction[] n [m]; ins; intuition; desf; [by inv H2|].
    inv H2; repeat eexists; eauto; simpl.
    destruct m; ins; intuition; desf; [by inv H5|].
    inv H5; repeat eexists; eauto; simpls.
    - eapply safe_seq; [eapply OK| ]; simpls. unfold safe_nt; eauto using len_trans.
    - apply safe_skip; simpl; rewrite B0; split; eauto.
  Qed.

  Lemma rule_while P B C :
    CSL (Aconj P (Apure B)) C P ->
    CSL P (Cwhile B C) (Aconj P (Apure (Bnot B))).  
  Proof.
    unfold CSL, safe_nt; ins; intuition; eapply safe_while; unfold CSL; eauto.
  Qed.

  Section For_Vector_Notation.
    Import VectorNotations.
    Lemma rule_barrier : forall j, CSL (fst (bspec j))[@tid] (Cbarrier j) (snd (bspec j))[@tid].
    Proof.
      unfold CSL, safe_nt; intros j s ph Hsat n.
      destruct n; simpl; [eauto|]; repeat split.
      - inversion 1.
      - intros. inversion 1.
      - intros; inversion H1.
      - intros j' c' H; inversion H; subst.
        exists ph, emp_ph; repeat split; eauto.
        + simpl; apply pdisj_empty2.
        + rewrite phplus_comm; eauto using pdisj_empty2.
        + intros phQ H0 hsatq.
          apply safe_skip; simpl.
          cutrewrite (phplus_pheap H0 = phQ); 
            [eauto | 
             destruct phQ; apply pheap_eq; rewrite phplus_comm; eauto using pdisj_empty2  ].
    Qed.
  End For_Vector_Notation.

  (* from CSLsound.v *)
  Fixpoint subE x e e0 := 
    match e0 with 
      | Evar y => (if Z.eq_dec x y then e else Evar y)
      | Enum n => Enum n
      | Eplus e1 e2 => Eplus (subE x e e1) (subE x e e2)
    end.
  (* b[x/e]*)
  Fixpoint subB x e b :=
    match b with
      | Beq e1 e2 => Beq (subE x e e1) (subE x e e2)
      | Band b1 b2 => Band (subB x e b1) (subB x e b2)
      | Bnot b => Bnot (subB x e b)
    end.

  Fixpoint subA x e p := 
    match p with
      | Aemp => Aemp
      | Apure B => Apure (subB x e B)
      | Apointsto q e1 e2 => Apointsto q (subE x e e1) (subE x e e2)
      | Astar P Q => Astar (subA x e P) (subA x e Q)
      | Aconj P Q => Aconj (subA x e P) (subA x e Q)
      | Adisj P Q => Adisj (subA x e P) (subA x e Q)
      | Aex PP => Aex (fun n => subA x e (PP n))
    end.

  Lemma subE_assign : forall (x : var) (e e' : exp) (s : stack),
    edenot (subE x e e') s = edenot e' (upd s x (edenot e s)).
  Proof.
    intros; induction e'; simpl; eauto; unfold upd; 
    repeat match goal with [ |- context[if Z.eq_dec ?x ?y then _ else _]] => destruct (Z.eq_dec x y) end; try congruence; eauto; f_equal; eauto.
  Qed.

  Lemma subB_assign : forall (x : var) (e : exp) (b : bexp) (s : stack),
    bdenot (subB x e b) s = bdenot b (upd s x (edenot e s)).
  Proof.
    intros; induction b; simpl;
    repeat match goal with [ |- context[if Z.eq_dec ?x ?y then _ else _]] => 
                           destruct (Z.eq_dec x y) end; 
    repeat rewrite subE_assign in *; congruence.
  Qed.

  Lemma subA_assign : forall (x : var) (e : exp) (P : assn) (s : stack) (ph : pheap),
    sat (s, ph) (subA x e P)  = sat (upd s x (edenot e s), ph) P.
  Proof.
    induction P; intros; simpl; eauto; unfold upd; 
    repeat match goal with [ |- context[if Z.eq_dec ?x ?y then _ else _]] => 
                           destruct (Z.eq_dec x y) end; simpl;
    repeat rewrite subB_assign in *; repeat rewrite subE_assign in *; unfold upd in *;
    try congruence.
    - rewrite IHP1, IHP2; eauto.
    - rewrite IHP1, IHP2; eauto.
    - repeat (f_equal; apply functional_extensionality; intros).
      rewrite IHP1, IHP2; eauto.
    - f_equal; apply functional_extensionality; intros.
      rewrite H; eauto.
  Qed.

  Theorem rule_assign x Exp Q : CSL (subA x Exp Q) (x ::=  Exp) Q.
  Proof.
    unfold CSL, safe_nt; intros s ph hsat n; destruct n; 
    [simpl; eauto | 
     repeat split; try congruence].
    - intros; try inversion 1.
    - intros hF h c' ss' hdis heq hred; inversion hred; subst; repeat eexists; 
      match goal with [ H : (_, _) = (_, _) |- _ ] => inversion H end; 
      subst; simpl in *; eauto using safe_skip.
      apply safe_skip.
      rewrite <-subA_assign; eauto.
    - intros j c' H; inversion H.
  Qed.

  Definition indeE (Exp : exp) (x : var) :=
    forall s v, edenot Exp s = edenot Exp (upd s x v).

  Lemma htop_eq (h : heap) (ph : pheap) :
    ph = htop h -> forall x, h x = match this ph x with | Some (_, x) => Some x | None => None end.
  Proof.
    intros heq x.
    destruct ph as [ph ?]; unfold htop in heq; inversion heq; simpl in *.
    rewrite H0; unfold htop'; destruct (h x); eauto.
  Qed.

  Theorem rule_read (x : var) (E1 E2 : exp) (p : Qc) :
    indeE E1 x -> indeE E2 x -> 
    CSL (Apointsto p E1 E2) (x ::= [ E1 ]) 
        (Aconj (Apointsto p E1 E2) (Apure (Beq (Evar x) E2))).
  Proof.
    unfold indeE, CSL, safe_nt; intros hinde1 hinde2 s h hsat; destruct n; 
    [simpl; eauto | simpl; repeat split; try congruence].
    - intros hF h' hdis heq hc; inversion hc; subst; simpl in *.
      specialize (hsat (edenot E1 s)); simpl in *.
      destruct (Z.eq_dec (edenot E1 s) (edenot E1 s)) as [_ | ?]; [| try congruence].
      rewrite <-(phplus_eq hdis) in heq; apply ptoheap_eq in heq.
      pose proof (htop_eq heq) as heq'; specialize (heq' (edenot E1 s)).
      simpl in *; unfold phplus in *; rewrite hsat in heq'. 
      destruct (this hF (edenot E1 s)) as [[? ?] | ]; congruence.
    - unfold access_ok; simpl in *; specialize (hsat (edenot E1 s)).
      destruct (Z.eq_dec (edenot E1 s) (edenot E1 s)) as [_ | ?]; [eexists; eauto | congruence].
    - intros hF h0 c' ss' hdis heq hred; inversion hred; clear hred; subst.
      inversion EQ1; clear EQ1; subst; simpl in *.
      repeat eexists; eauto. 
      apply safe_skip; simpl. split; [intros x0|];
      repeat match goal with [ |- context [Z.eq_dec ?x ?y] ] => destruct (Z.eq_dec x y) end;
      (try specialize (hsat x0)); subst; repeat rewrite <-hinde1 in hsat;
      repeat match goal with [ H : context [Z.eq_dec ?x ?y] |- _ ] => destruct (Z.eq_dec x y) end;
      try congruence.
      contradict n0.
      rewrite <-hinde2.
      unfold upd; destruct (Z.eq_dec x x); try congruence.
      rewrite <-(phplus_eq hdis) in heq; apply ptoheap_eq in heq.
      pose proof (htop_eq heq); simpl in *.
      unfold phplus in H; specialize (H (edenot E1 s0)). rewrite hsat in H.
      match goal with [ H : context [Z.eq_dec ?x ?y] |- _ ] => destruct (Z.eq_dec x y) end; 
        try congruence; destruct (this hF (edenot E1 s0)) as [[? ?]|]; congruence.
  Qed.

  Lemma ph_upd_phplus (ph1 ph2 : pheap) (x : Z) (v w : Z):
    pdisj ph1 ph2 -> this ph1 x = Some (full_p, w) -> 
    phplus (ph_upd ph1 x v) ph2 = ph_upd (phplus ph1 ph2) x v.
  Proof.
    intros hdis heq.
    destruct ph1 as [ph1 isp1], ph2 as [ph2 isp2]; simpl in *.
    unfold phplus, ph_upd; extensionality y.
    specialize (isp1 y); specialize (isp2 y); specialize (hdis y).
    destruct (Z.eq_dec x y) as [eqxy | neqxy]; subst;
    destruct (ph1 y) as [[? ?]|], (ph2 y) as [[? ?]|]; eauto; try congruence.
    inversion heq; subst; 
    destruct hdis as [? [? Hc]]. apply frac_contra1 in Hc; tauto.
  Qed.

  Lemma ph_upd_ptoheap (ph : pheap) (h : heap) (x : Z) (v : Z) :
    ptoheap ph h -> ptoheap (ph_upd ph x v) (upd h x (Some v)).
  Proof.        
    intros heq y.
    unfold ptoheap, ph_upd, upd in *; specialize (heq y).
    destruct (Z.eq_dec x y) as [eqxy | neqxy]; subst.
    destruct (Z.eq_dec y y) as [_ | ?]; try congruence; tauto.
    destruct (this ph y) as [[? ?]|].
    destruct (Z.eq_dec y x); try congruence; tauto.
    destruct (Z.eq_dec y x); try congruence; tauto.
  Qed.

  Theorem rule_write (E0 E1 E2 : exp) :
    CSL (Apointsto full_p E1 E0) ([E1] ::= E2) (Apointsto full_p E1 E2).
  Proof.
    unfold CSL, safe_nt; intros s ph hsat n.
    pose proof (hsat (edenot E1 s)) as hsat'; simpl in *.
    destruct (Z.eq_dec (edenot E1 s) (edenot E1 s)) as [_|?]; try congruence.
    destruct n; [simpl; eauto| simpl; repeat split; try congruence].
    - intros hF h hdis heq hc; inversion hc; subst; simpl in *.
      rewrite <-(phplus_eq hdis) in heq; apply ptoheap_eq in heq; pose proof (htop_eq heq) as heq'.
      specialize (heq' (edenot E1 s)); simpl in *.
      unfold phplus in *. destruct ph as [ph ?]; simpl in *; rewrite hsat' in heq'.
      destruct (this hF (edenot E1 s)) as [[? ?]| ]; congruence.
    - simpl in hsat'. unfold access_ok; simpl.
      eexists; eauto.
    - simpl in hsat'. unfold write_ok; simpl.
      eexists; eauto.
    - intros hF h c' ss' hdis heq hred; inversion hred; clear hred; subst; simpl in *.
      inversion EQ1; clear EQ1; subst.
      eexists; exists (ph_upd2 ph (edenot E1 s0) (edenot E2 s0)); repeat split; eauto.
      + unfold ph_upd2; simpl; apply (pdisj_upd _ _ hsat'); eauto.
      + unfold ph_upd2; simpl.
        erewrite ph_upd_phplus; eauto.
        cutrewrite (phplus ph hF = phplus_pheap hdis); [|simpl; eauto].
        apply ph_upd_ptoheap; eauto.
      + apply safe_skip; simpl; intros x.
        unfold ph_upd.
        destruct (Z.eq_dec (edenot E1 s0) x); subst; eauto.
        * destruct (Z.eq_dec (edenot E1 s0) (edenot E1 s0)); congruence.
        * rewrite hsat; eauto.
          destruct (Z.eq_dec x (edenot E1 s0)); congruence.
  Qed.

  Lemma safe_conseq:
    forall n C s h Q (OK: safe_nt n C s h Q) Q' (IMP: Q |= Q'),
      safe_nt n C s h Q'.
  Proof.
    unfold safe_nt; induction n; ins; intuition.
    exploit H3; eauto; ins; desf; repeat eexists; eauto.
    exploit H5; eauto; ins; desf; repeat eexists; eauto.
  Qed.

  Theorem rule_conseq P C Q P' Q':
    CSL P C Q -> (P' |= P) -> (Q |= Q') -> CSL P' C Q'.
  Proof.
    unfold CSL; intuition; eauto using safe_conseq.
  Qed.

  Theorem rule_disj P1 P2 C Q1 Q2:
    CSL P1 C Q1 -> CSL P2 C Q2 ->
    CSL (Adisj P1 P2) C (Adisj Q1 Q2).
  Proof.
    unfold CSL; ins; intuition; eapply safe_conseq; eauto; vauto.
  Qed.
End SeqCSL.

Section ParCSL.
  Import VectorNotations.

  Variable ntrd : nat.
  Variable bspec : nat -> (Vector.t assn ntrd * Vector.t assn ntrd)%type.
  Variable E : env.
  Hypothesis brr_lowassn : forall (i : nat),
                             (forall tid : Fin.t ntrd, low_assn E (fst (bspec i))[@tid]) /\
                             (forall tid : Fin.t ntrd, low_assn E (snd (bspec i))[@tid]).
  Hypothesis brr_wf : forall (i : nat) (st : pstate),
                        sat st (Aistar_v (fst (bspec i))) <-> sat st (Aistar_v (snd (bspec i))).
  Hypothesis bc_precise :
    forall i (tid : Fin.t ntrd), precise (fst (bspec i))[@tid] /\
                                 precise (snd (bspec i))[@tid].
  Lemma ew : env_wellformed bspec E.
  Proof.
    unfold env_wellformed, bwf, low_assn in *; split; try tauto; intros i; specialize (brr_lowassn i); split; destruct brr_lowassn; eauto.
  Qed.

  Close Scope Q_scope.
  Close Scope Qc_scope.
  Definition low_eq_repr1 (n : nat) (ss : Vector.t stack (S n)) :
    low_eq_l2 E ss -> { x : stack & forall tid : Fin.t (S n), low_eq E ss[@tid] x } :=
    fun heq => existT (fun x => forall tid : Fin.t (S n), low_eq E ss[@tid] x)
                      ss[@Fin.F1] (fun tid : Fin.t (S n) => loweq_l2_leq heq tid Fin.F1).

  Definition fin_0 (i : Fin.t 0) : Empty_set :=
    (fun n (i : Fin.t n) =>
       match i in Fin.t n return 
             match n with
               | 0 => Empty_set
               | S n => unit
             end with
         | Fin.F1 _ => tt
         | Fin.FS _ _ => tt
       end) 0 i.

  Definition low_eq_repr (n : nat) : 
    forall (ss : Vector.t stack n),
      low_eq_l2 E ss -> { x : stack & forall tid : Fin.t n, low_eq E ss[@tid] x } :=
    match n return forall (ss : Vector.t stack n), 
                     low_eq_l2 E ss ->
                     { x : stack & forall tid : Fin.t n, low_eq E ss[@tid] x } with
      | 0 => fun ss  _ => existT _ ((fun _ => 0%Z) : stack) (fun tid : Fin.t 0 => 
                                                               match fin_0 tid with end)
      | S n => fun ss heq => low_eq_repr1 heq
    end.
  
  Definition sat_k (ss : Vector.t stack ntrd) (h : heap) (H : low_eq_l2 E ss) Q :=
    match low_eq_repr H with
      | existT x P => sat (x, htop h) Q
    end.

  Fixpoint safe_nk (n : nat) (ks : klist ntrd) (h : heap) (Q : assn) :=
    match n with
      | 0 => True
      | S n =>
        let ss := Vector.map (fun s => snd s) ks in
        ((forall tid : Fin.t ntrd, fst ks[@tid] = Cskip) -> 
         exists H : low_eq_l2 E ss, @sat_k ss h H Q) /\
        (forall hF : heap, hdisj h hF -> ~ abort_k (ks, hplus h hF)) /\
        (forall ws : Vector.t (nat * cmd) ntrd, 
           (forall tid : Fin.t ntrd, wait (fst ks[@tid]) = Some (ws[@tid])) ->
           (low_eq_l2 E ss) /\ exists b, (forall tid, fst ws[@tid] = b)) /\
        (forall (hF h' : heap) (ks' : klist ntrd), 
           hdisj h hF -> (ks, hplus h hF) ==>k (ks', h') ->
           exists h'' : heap, hdisj h'' hF /\ h' = hplus h'' hF /\ 
                              safe_nk n ks' h'' Q)
    end.

  Lemma red_k_step (ks1 ks2 ks3 : kstate ntrd) :
    ks1 ==>k* ks2 -> ks2 ==>k ks3 -> ks1 ==>k* ks3.
    intros.
    apply Operators_Properties.clos_rt_rt1n_iff.
    apply Operators_Properties.clos_rt_rt1n_iff in H.
    apply (rt_trans _ _ _ ks2); eauto.
    apply rt_step; eauto.
  Qed.

  Lemma safe_par (n : nat) (ks : klist ntrd) (h : heap) (Q : assn) 
        (hs : Vector.t pheap ntrd) (Qs : Vector.t assn ntrd) :
    let cs := Vector.map (fun cs => fst cs) ks in
    let ss := Vector.map (fun cs => snd cs) ks in
    (forall tid : Fin.t ntrd, low_assn E Qs[@tid]) ->
    disj_eq hs (htop h) ->
    (forall tid : Fin.t ntrd, safe_nt bspec tid n cs[@tid] ss[@tid] hs[@tid] Qs[@tid]) ->
    ((Aistar_v Qs) |= Q) ->
    (exists ks1 hs1 ss1 c ty,
       ks1 ==>k* (ks, h) /\       
       typing_cmd E c ty /\
       disj_eq hs1 (htop (snd ks1)) /\
       ss1 = get_ss_k ks1 /\ low_eq_l2 E ss1 /\
       (forall tid : Fin.t ntrd, (get_cs_k ks1)[@tid] = c) /\
       (forall tid : Fin.t ntrd, safe_aux bspec tid c (ss1[@tid]) (hs1[@tid]))) ->
    safe_nk n ks h Q.
  Proof.
    revert ks h hs. induction n; [intros; simpl; tauto | ].
    intros ks h hs cs ss hlowQ hdis hsafei Hq h_for_bdiv.
    assert (forall hF : heap, hdisj h hF -> ~ abort_k (ks, hplus h hF)) as not_aborts.
    { intros hF hdisF [tid Hc]; simpl in *.
      destruct (hsafei tid) as [_ [hsafe _]].
      unfold cs, ss in hsafe.
      destruct (disj_tid tid hdis) as [h' [hres [hdis' hph]]].
      erewrite !Vector.nth_map in hsafe; eauto.
      destruct (ks[@tid]) as [c s]; simpl in *.
      assert (ptoheap (phplus hs[@tid] h') h) by (rewrite hph; apply ptoheap_htop).
      cutrewrite (phplus hs[@tid] h' = phplus_pheap hdis') in H; [|eauto].
      pose proof (ptoheap_plus H hdisF) as heq'.
      cutrewrite (this (phplus_pheap hdis') = phplus hs[@tid] h') in heq'; [|eauto].
      apply hdisj_pdisj in hdisF.
      cutrewrite (this (htop h) = htop' h) in hdisF; [|eauto]; rewrite <-hph in hdisF.
      apply pdisj_padd_expand in hdisF; eauto.
      rewrite padd_assoc in heq'; try tauto; destruct hdisF as [hdisF hd].
      cutrewrite (phplus h' (htop hF) = phplus_pheap hd) in hdisF; [|eauto].
      specialize (hsafe _ _ hdisF heq'); apply hsafe; eauto. }
    simpl. split; [ | split; [| split] ]; eauto.
    - intros cskip.
      destruct h_for_bdiv as [ks1 [hs1 [ss1 [c [? [? [? [? [? [? [? ?]]]]]]]]]]].
      assert (low_eq_l2 E (get_ss_k (ks, h))) as hleq.
      { eapply (when_stop ew bc_precise ); eauto.
        intros tid; unfold get_cs_k; simpl; erewrite Vector.nth_map; eauto. }
      cutrewrite (get_ss_k (ks, h) = Vector.map (fun s => snd s) ks)in hleq;
        [|unfold get_ss_k; eauto].
      exists hleq; unfold sat_k. destruct (low_eq_repr hleq) as [st Hst].
      apply Hq, (aistar_eq (hs := (Vector.map2 (fun s h => (s, h)) ss hs))).
      + unfold get_hs. rewrite map_map2, map2_snd'; eauto.
      + intros tid; specialize (hsafei tid); destruct hsafei as [hsafei _].
        erewrite Vector.nth_map2; eauto; simpl.
        unfold low_assn, Bdiv.low_assn, indeP in hlowQ.
        specialize (Hst tid); erewrite Vector.nth_map in Hst; eauto.
        cutrewrite (snd ks[@tid] = ss[@tid]) in Hst; [|unfold ss; erewrite Vector.nth_map; eauto].
        apply (hlowQ tid _ _ _ Hst), hsafei.
        unfold cs; erewrite Vector.nth_map; eauto.
    - intros ws Hbrr.
      cutrewrite (Vector.map (fun s => snd s) ks = get_ss_k (ks, h)); [|eauto].
      destruct h_for_bdiv as [ks1 [hs1 [ss1 [c [? [? [? [? [? [? [? ?]]]]]]]]]]].
      eapply (when_barrier ew bc_precise); eauto.
      intros tid; unfold get_cs_k; erewrite Vector.nth_map; eauto.
    - intros hF h' ks' hdis' hred1.
      remember (ks', h') as kss'.
      cutrewrite (ks' = fst kss'); [| rewrite Heqkss'; eauto ].
      cutrewrite (h' = snd kss'); [| rewrite Heqkss'; eauto ]. clear Heqkss'.
      remember (hplus h hF) as hhF. remember (ks, hhF) as kss.
      pose proof hred1 as hred2.
      destruct hred2.
      + rewrite H in Heqkss. rewrite HeqhhF in Heqkss. rewrite H2, H3 in H1.
        inversion Heqkss. rewrite H5, H6 in *.
        destruct (hsafei i) as [_ [_ [_ [_ [hsafe _]]]]].
        assert (pdisj (htop h) (htop hF)) as pdisF by (apply hdisj_pdisj; eauto).
        destruct (disjeq_phplus i hdis pdisF) as [h'' [hdisi'' [hdisF [heq hdisiF]]]].
        cutrewrite (phplus h'' (htop hF) = phplus_pheap hdisF) in hdisiF; eauto.
        assert (cs[@i] / (ss[@i], hplus h hF) ==>s c' / (s', h'0)) as hred.
        { unfold cs, ss; erewrite !Vector.nth_map; eauto. rewrite H0; simpl; eauto. }
        assert (ptoheap (phplus hs[@i] (phplus_pheap hdisF))  (hplus h hF)) as heqF.
        { cutrewrite (this (phplus_pheap hdisF) = phplus h'' (htop hF)); [| eauto]. 
          rewrite <-padd_assoc, heq, <-hplus_phplus; eauto.
          cutrewrite (htop' (hplus h hF) = htop (hplus h hF)); [apply ptoheap_htop | eauto]. }
        destruct (hsafe _ _ _ _ hdisiF heqF hred) as [snd_ss [ph' [heq' [hdisF' [heqA safe]]]]].
        simpl in heq'; rewrite <- heq' in *; clear snd_ss heq'.
        assert (pdisj ph' h'') as disjph'h'' by
            (cutrewrite (this (phplus_pheap hdisF) = phplus h'' (htop hF)) in hdisF'; 
             [apply pdisjE1 in hdisF'; eauto |eauto]).
        assert (exists h''0, ptoheap (phplus_pheap disjph'h'') h''0) as [h''0 heq''0].
        { cutrewrite (this (phplus_pheap hdisF) = phplus h'' (htop hF)) in heqA; eauto.
          rewrite <-padd_assoc in heqA; eauto.
          cutrewrite (phplus ph' h'' = phplus_pheap disjph'h'') in heqA; eauto.
          cutrewrite (this (phplus_pheap hdisF) = phplus h'' (htop hF)) in hdisF'; eauto.
          apply pdisjC in hdisF'; rewrite phplus_comm in hdisF'; apply pdisj_padd_expand in hdisF'; 
          eauto; destruct hdisF' as [dis1 dis2]; apply pdisjC in dis1; rewrite phplus_comm in dis1;
          eauto.
          cutrewrite (phplus ph' h'' = phplus_pheap disjph'h'') in dis1; eauto.
          apply (ptoheap_phplus dis1 heqA). }
        assert (hdisj h''0 hF) as dis''F.
        { apply hdisj_pdisj.
          apply ptoheap_eq in heq''0; rewrite <-heq''0.
          cutrewrite (this (phplus_pheap disjph'h'') = phplus ph' h''); eauto.
          cutrewrite (this (phplus_pheap hdisF) = phplus h'' (htop hF)) in hdisF'; eauto.
          apply pdisj_padd_expand; eauto. }
        assert (h'0 = hplus h''0 hF) as Heq'_''F.
        { simpl.
          cutrewrite (phplus ph' (phplus_pheap hdisF) = phplus_pheap hdisF') in heqA; eauto.
          apply ptoheap_eq in heqA; apply ptoheap_eq in heq''0.
          apply heap_pheap_eq. 
          rewrite hplus_phplus; eauto; simpl.
          inversion heq''0. inversion heqA.
          cutrewrite (htop' hF = htop hF); eauto.
          rewrite padd_assoc; eauto. }
        exists h''0; repeat split; eauto.
        * set (hs' := replace hs i ph').
          apply (IHn _ _ hs'); eauto.
          { unfold hs'.
            apply ptoheap_eq in heq''0; rewrite <-heq''0.
            apply (disj_tid i) in hdis. destruct hdis as [h'1 [hdis1 [pdis1 heqh]]].
            assert (h'1 = h'') as heq'' by (apply (@padd_cancel hs[@i]); eauto; congruence); 
            rewrite heq'' in *; clear heq''.
            destruct (disj_upd hdis1 disjph'h'') as [? [Hcon heqh']].
            cutrewrite (phplus_pheap disjph'h'' = x); [|destruct x; apply pheap_eq]; eauto. }

          { intros tid; unfold hs'.
            erewrite !Vector.nth_map; eauto; simpl.
            rewrite !replace_nth.
            destruct (fin_eq_dec i tid) as [eq | neq]; [rewrite <-eq in *; clear eq|]; simpl; eauto.
            cutrewrite (fst ks[@tid] = cs[@tid]); [|unfold cs; erewrite Vector.nth_map; eauto].
            cutrewrite (snd ks[@tid] = ss[@tid]); [|unfold ss; erewrite Vector.nth_map; eauto].
            apply (safe_mon (hsafei tid)). 
            eauto. }
          { destruct h_for_bdiv as [ks1 [hs1 [ss1 [cini [ty [red1 [? [? [? [? [? ?]]]]]]]]]]].
            exists ks1, hs1, ss1, cini, ty; repeat split; eauto; simpl.
            rewrite H, Heq'_''F in hred1.
            assert ((ks, h) ==>k (replace ks i (c', s'), h''0)).
            { apply (naborts_red_k (hF := hF)); eauto.
              cutrewrite (h = hplus h (fun _ => None)); 
                [|unfold hplus; extensionality x; destruct (h x); eauto].
              apply not_aborts.
              intros x; right; eauto. }
            apply (@red_k_step _ (ks, h) _); eauto. }
      + assert ((ss0, hplus h hF) ==>k (ss', hplus h hF)) as hred.
        { destruct ks0, ks'0; inversion Heqkss; inversion H; inversion H0; subst; eauto.
          rewrite H5, <-H6 in hred1; eauto. }
        rewrite !H0; simpl.
        exists h; eauto; repeat split; eauto.
        * destruct ks0; inversion H; inversion Heqkss; congruence.
        * subst; inversion H. rewrite <-H2, <-H3 in *.
          assert (forall tid : Fin.t ntrd, wait cs[@tid] = Some (j, fst ss'[@tid])) as Hwait.
          { intros tid; destruct (H1 tid) as [? [? [? [? [? ?]]]]];
            unfold cs; erewrite Vector.nth_map; eauto.
            rewrite H0, H5; simpl; eauto. }
          assert (forall tid : Fin.t ntrd, exists phP ph' : pheap,
                    pdisj phP ph' /\ phplus phP ph' = hs[@tid] /\ 
                    sat (ss[@tid], phP) (pre_j bspec tid j) /\
                    (forall (phQ : pheap) (H : pdisj phQ ph'),
                       sat (ss[@tid], phQ) (post_j bspec tid j) ->
                       safe_nt bspec tid n (fst ss'[@tid]) ss[@tid] 
                               (phplus_pheap (h1:=phQ) (h2:=ph') H) Qs[@tid])) as hsafe0.
          { intros tid; destruct (hsafei tid) as [_ [_ [_ [_ [_ ?]]]]]; eauto. }
          destruct (vec_exvec hsafe0) as [phPs Hp]; destruct (vec_exvec Hp) as [phFs Hp']; clear Hp.
          assert (forall tid : Fin.t ntrd, pdisj phPs[@tid] phFs[@tid] /\ 
                                           phplus phPs[@tid] phFs[@tid] = hs[@tid]) as Hp''.
          { intros tid; destruct (Hp' tid) as [? [? _]]; eauto. }
          destruct (disj_eq_sub hdis Hp'') as [phP [phF [HeqP [HeqF [HdisPF HeqPF]]]]]; clear Hp''.
          assert (low_eq_l2 E ss) as leq2ss.
          { destruct h_for_bdiv as [? [? [? [? [? [Hred [? [? [? [? [? ?]]]]]]]]]]].
            set (ws := init (fun i => (j, fst ss'[@i]))).
            eapply (when_barrier (ws := ws) ew bc_precise Hred); eauto.
            intros tid; unfold cs in Hwait; unfold get_cs_k, ws. rewrite init_spec; eauto. }
          destruct (low_eq_repr leq2ss) as [s Hs].
          assert (forall tid, sat (s, phPs[@tid]) (pre_j bspec tid j)) as Hsati.
          { intros tid; destruct (Hp' tid) as [_ [_ [? _]]].
            destruct (brr_lowassn j) as [Hlow _]; specialize (Hlow tid).
            apply (Hlow ss[@tid] s _ (Hs tid)); eauto. }
          assert (sat (s, phP) (Aistar_v (fst (bspec j)))) as Hsat.
          { apply (aistar_eq (hs := Vector.map (fun h => (s, h)) phPs)).
            - unfold get_hs. rewrite MyVector.map_map.
              rewrite (MyVector.map_ext (f := fun x => snd (s, x)) (g := id) phPs), MyVector.map_id; eauto.
            - intros tid; erewrite Vector.nth_map; eauto. }
          apply brr_wf, aistar_disj in Hsat. destruct Hsat as [phQs [HeqQ Hsatiq]].
          assert (forall tid, pdisj phQs[@tid] phFs[@tid]) as HdisQF.
          { apply (disj_eq_each_disj HeqQ HeqF); eauto. }
          assert (forall tid, safe_nt bspec tid n (fst ss'[@tid]) ss[@tid]
                                      (phplus_pheap (HdisQF tid)) Qs[@tid]) as Hsafe.
          { intros tid; destruct (Hp' tid) as [_ [_ [_ Hsafe]]]; apply Hsafe; eauto.
            destruct (brr_lowassn j) as [_ Hlow]; specialize (Hlow tid).
            apply (Hlow ss[@tid] s _ (Hs tid)); eauto. }
          apply (IHn _ _ (init (fun tid => phplus_pheap (HdisQF tid)))); eauto.
          { cutrewrite (htop h = (phplus_pheap HdisPF)); 
            [|unfold htop in *; simpl in *; apply pheap_eq; congruence].
            apply (disj_eq_sum HdisPF HeqQ HeqF); intros tid; rewrite init_spec; eauto. }
          { intros tid. erewrite !Vector.nth_map; eauto; rewrite init_spec. 
            cutrewrite (snd ss'[@tid] = ss[@tid]); [apply Hsafe|].
            destruct (H1 tid) as [? [? [? [? [? ?]]]]]. 
            unfold ss; erewrite Vector.nth_map; eauto. rewrite H0, H5; eauto. }
          { destruct h_for_bdiv as [ks1 [hs1 [ss1 [c [ty ?]]]]].
            exists ks1, hs1, ss1, c, ty; repeat split; try tauto.
            apply naborts_red_k in hred1; eauto.
            apply (red_k_step (ks2 := (ks, h))); tauto.
            cutrewrite (h = hplus h (fun _ => None)); [apply not_aborts| ].
            intros x; right; eauto.
            extensionality x; unfold hplus; destruct (h x); eauto. }
  Qed.

  Definition CSLp (P : assn) (c : cmd) (Q : assn) :=
    forall (ks : klist ntrd) (h : heap) (leqks : low_eq_l2 E (Vector.map (fun s => snd s) ks)),
      (forall tid : Fin.t ntrd, fst ks[@tid] = c) ->
      sat_k h leqks P ->
      forall n, safe_nk n ks h Q.

  Theorem rule_par (Ps : Vector.t assn ntrd) (Qs : Vector.t assn ntrd) 
          (P : assn) (c : cmd) (Q : assn) (ty : type):
    (P |= Aistar_v Ps) -> (Aistar_v Qs |= Q) ->
    (forall tid, low_assn E Ps[@tid]) -> (forall tid, low_assn E Qs[@tid]) ->
    typing_cmd E c ty ->
    (forall tid : Fin.t ntrd, CSL bspec tid Ps[@tid] c Qs[@tid]) ->
    CSLp P c Q.
  Proof.
    unfold CSL, CSLp, sat_k in *.
    intros PPs QsQ HlowP HlowQ Hty Hsafei ks h leqks Heqc Hsat n.
    destruct (low_eq_repr leqks) as [s Hlows].
    apply PPs in Hsat.
    destruct (aistar_disj Hsat) as [prehs [Hdisj Hsati]].
    assert (forall tid, Bdiv.sat ((Vector.map (fun s => snd s) ks)[@tid], prehs[@tid]) Ps[@tid]) as
        Hsat'.
    { intros tid; apply ((HlowP tid) (Vector.map [eta snd (B:=stack)] ks)[@tid] s _ (Hlows tid));
      eauto. }
    apply (safe_par (hs := prehs) (Qs := Qs)); eauto.
    - intros tid; specialize (Hsafei tid); specialize (Hsat' tid); erewrite !Vector.nth_map in *; 
      eauto.
      rewrite Heqc; apply Hsafei.
      erewrite Vector.nth_map in Hsat'; eauto.
    - exists (ks, h), prehs, (Vector.map [eta snd (B:=stack)] ks), c, ty; repeat split; eauto.
      + apply rt1n_refl. 
      + unfold get_cs_k; simpl; intros tid; erewrite Vector.nth_map; eauto.
      + intros tid; unfold safe_aux; exists Qs[@tid]; intros n'.
        erewrite Vector.nth_map; eauto; apply Hsafei.
        specialize (Hsat' tid); erewrite Vector.nth_map in Hsat'; eauto.
  Qed.
End ParCSL.