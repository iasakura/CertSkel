Require Import QArith.
Require Import Qcanon.
Require Import MyVector.
Require Import List.
Require Import ZArith.
Require Import PHeap.

Require Import Lang.
Require Import Relation_Operators.
Require Import assertions.
Set Implicit Arguments.
Unset Strict Implicit.

Coercion Evar : var >-> exp.
Coercion Enum : Z >-> exp.

Require Import Bdiv.
Require Import assertions.
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
                            sat st (Aistar_v (fst (bspec i))) -> sat st (Aistar_v (snd (bspec i))).
      Hypothesis bc_precise :
        forall i (tid : Fin.t ntrd), precise (fst (bspec i))[@tid] /\
                                     precise (snd (bspec i))[@tid].
    End For_Vector_Notation.
  End Vnotation.
  Variable tid : Fin.t ntrd.
  Definition safe_nt := safe_nt bspec tid.

  Definition CSL (p : assn) (c : cmd) (q : assn) := 
    forall s ph, sat (s, ph) p -> forall (n : nat), safe_nt n c s ph q.

  Lemma safe_skip : forall n s h (Q : assn), sat (s,h) Q -> safe_nt n Cskip s h Q.
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
  Require Import TLC.LibTactics.

  Lemma write_ok_mono (C : cmd) (s : stack) (ph phF : pheap) (dis : pdisj ph phF) :
    write_ok C s ph -> write_ok C s (phplus_pheap dis).
  Proof.
    clears.
    intros hok; induction C; eauto; unfold write_ok in *; simpl in *;
    destruct phF as [phF ispF], ph as [ph isp]; unfold phplus; simpl in *.
    specialize (dis (ledenot e1 s)); specialize (ispF (ledenot e1 s)).
    destruct hok as [v H]; unfold phplus; rewrite H in *; simpl.
    match goal with
        [  |- context [match ?v with | Some _ => _ | None => _ end] ] => 
        destruct v as [[? ?]|] end.
    - assert (full_p + q <= 1)%Qc by jauto.
      assert (0 < q)%Qc by jauto.
      apply frac_contra1 in H0; [destruct H0 | eauto ].
    - exists v; eauto.
  Qed.

  Fixpoint writes_var (c : cmd) : list var :=
    match c with
      | Cskip | Cwrite _ _ | Cbarrier _ => nil
      | Cassign _ v _ | Cread _ v _ => v :: nil
      | Cseq c1 c2 => writes_var c1 ++ writes_var c2
      | Cif _ c1 c2 => writes_var c1 ++ writes_var c2
      | Cwhile _ c => writes_var c
    end%list.

  Lemma writes_agrees (c1 c2 : cmd) (st1 st2 : state) :
    c1 / st1 ==>s c2 / st2 ->
    fst st1 = fst st2 \/
    exists (x : var) (v : Z), In x (writes_var c1) /\ fst st2 = var_upd (fst st1) x v.
  Proof.
    induction 1; try (left; now eauto).
    - destruct IHred as [ ? | [x [ v [Hin Heq] ]] ]; [tauto | right].
      exists x v; split; eauto.
      apply in_app_iff; eauto.
    - right; exists x (edenot e s); split; [constructor | subst]; eauto.
    - right; exists x v; split; [constructor | subst]; eauto.
    - left; subst; eauto.
  Qed.

  Definition inde (R : assn) (ls : list var) :=
    forall (x : var) (s : stack) (h : pheap) (v : Z),
      In x ls -> (sat (s, h) R <-> sat ((var_upd s x v), h) R).

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
    - intros x H'; specialize (IHred x); apply in_app_iff. apply in_app_iff in H'; tauto.
    - intros x H; apply in_app_iff; tauto.
    - intros x H; apply in_app_iff; tauto.
    - intros x H; apply in_app_iff in H; destruct H.
      + apply in_app_iff in H; tauto.
      + inversion H.
  Qed.

  Lemma wait_writes (c1 c2 : cmd) (j : nat) :
    wait c1 = Some (j, c2) -> forall x, In x (writes_var c2) -> In x (writes_var c1).
  Proof.
    revert j c2; induction c1; simpl; try now inversion 1.
    intros j c2; destruct (wait c1_1) as [[? ?]|]; intros H; inversion H; inversion H2.
    simpl; intros x H'; apply in_app_iff in H'; apply in_app_iff.
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
        rewrite <-(phplus_eq disf), phplus_comm; simpl; rewrite (@phplus_comm _ hf ph); eauto.
        Hint Resolve pdisjC.
        apply pdisj_padd_expand; eauto; rewrite (@phplus_comm _ phR ph); eauto. }
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
        (* apply pdisjC in hdis; apply pdisjE2 in hdis; eauto.  *)}
      destruct hsafe as [_ [_ [_ [_ [hsafe _]]]]].
      apply pdisjC in hdis; apply pdisjE2 in hdis; apply pdisjC in hdis.
      rewrite H, <- (phplus_eq hdis) in heq.
      rewrite <-(phplus_eq hdis) in hdis'.
      destruct (hsafe _ _ _ _ hdis' heq hred) as  [h' [ph' [? [hdis'' [? ?]]]]]. 
      assert (pdisj ph' phR) as dis'R by (simpl in hdis''; apply pdisjE1 in hdis''; eauto).
      assert (pdisj (phplus_pheap dis'R) hF) as dis''' by (simpl; apply pdisj_padd_expand; eauto).
      exists h' (phplus_pheap dis'R); repeat split; eauto.
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
      exists phP (phplus_pheap hdis'R); repeat split; eauto; simpl.
      apply pdisj_padd_expand; eauto; rewrite <-heqP' in disR; eauto.
      rewrite <- heqP', padd_assoc; eauto.
      (* apply pdisj_padd_expand; eauto; rewrite <-heqP' in disR; eauto. *)
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
    unfold CSL; intuition. simpl in *; eauto; intros. destruct H1 as (? & ? & ? & ? & ? & ?).
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
    intros n C s h Q OK m; revert C s n h OK; induction m; simpl in *; eauto; intros.
    destruct n; simpl in *; eauto; intuition; try omega; repeat split; simpl in *; eauto; intros.
    - refine ((fun x y => y x) (H3 _ _ _ _ _ _ _) _); eauto; simpl in *; eauto; intros;
      destruct x0 as (? & ? & ? & ? & ? & ?).
      exists x x0; repeat split; eauto.
      assert (m <= n) by omega; eauto.
    - refine ((fun x y => y x) (H5 _ _ _) _); eauto; simpl in *; eauto; intros;
      destruct x0 as (? & ? & ? & ? & ? & ?).
      repeat eexists; eauto.
      assert (m <= n) by omega; eauto.
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
        exists h' ph'; repeat split; try tauto.
        apply (IHn c1' C2 _ _ Q R); eauto; tauto.
    - destruct hsafe as [_ [_ [_ [_ [_ hsafe]]]]].
      intros j c' Heqw; inversion Heqw; destruct (wait C) as [[j' C']|]; inversion H1; subst.
      destruct (hsafe j C' eq_refl) as [phP [ph' Hs]].
      exists phP ph'; repeat split; try tauto.
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
    CSL (Aconj P (B)) C1 Q ->
    CSL (Aconj P ((Bunary OP_not B))) C2 Q ->
    CSL P (Cif B C1 C2) Q.
  Proof.
    unfold CSL, safe_nt; intuition; destruct n; [simpl; eauto|]; simpl in *; eauto; intros;
    intuition.
    - inversion H2.
    - inversion H4.
    - unfold access_ok; simpl; eauto.
    - unfold write_ok; simpl; eauto.
    - inversion H4; subst; repeat eexists; eauto; simpl.
      apply H; split; eauto; simpl in *; eauto; rewrite B0; eauto.
      apply H0; split; auto; unfold_conn_all; simpl in *; rewrite B0; auto.
    - inversion H2.
  Qed.

  Lemma safe_while :
    forall P (B : bexp) C (OK: CSL (P ** !(B)) C P) s h (SAT_P: sat (s, h) P) n,
      safe_nt n (Cwhile B C) s h (P ** !((Bunary OP_not B))).
  Proof.
    unfold safe_nt.
    intros; revert s h SAT_P. 
    assert (lenn : n <= n) by omega; revert lenn; generalize n at -2 as m.
    induction n; simpl in *; eauto; intros; intuition. (* desf; [by inv H2|]*)
    { destruct m; inversion lenn; simpl; eauto. }
(*    inv H2; repeat eexists; eauto; simpl.
    destruct m; ins; intuition; desf; [by inv H5|].
    inv H5; repeat eexists; eauto; simpls.*)
    inversion lenn; subst; [|apply IHn; eauto].
    simpl; repeat split; eauto; try congruence.
    intros; intros Hc; inversion Hc.
    intros hF h0 c' ss' hdis htoh hred.
    inversion hred; subst.
    exists h0 h; repeat split; eauto; simpl.
    destruct n; simpl; repeat split; eauto; intros; try congruence.
    intros Hc; inversion Hc.
    inversion H1; subst; repeat eexists; eauto.
    - eapply safe_seq; simpl; eauto; intros; [| apply IHn; try omega; eauto].
      apply OK. apply scban_r; auto.
    - eapply safe_skip; repeat split; simpl in *; eauto.
      apply scban_r; auto.
      unfold bexp_to_assn; simpl. rewrite B0; auto.
  Qed.

  Lemma rule_while P (B : bexp) C :
    CSL (P ** !(B)) C P ->
    CSL P (Cwhile B C) (P ** !((Bunary OP_not B))).  
  Proof.
    unfold CSL, safe_nt; intros; intuition; eapply safe_while; unfold CSL; eauto.
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
        exists ph (emp_ph loc); repeat split; eauto; auto; [simpl; auto|..].
        + intros phQ H0 hsatq.
          apply safe_skip; simpl.
          cutrewrite (phplus_pheap H0 = phQ); 
            [eauto | 
             destruct phQ; apply pheap_eq; rewrite phplus_comm; eauto using pdisj_empty2  ].
    Qed.
  End For_Vector_Notation.

  Notation subA x e P := (fun (s : stack) (h : pheap) => P (var_upd s x (edenot e s)) h).

(*
  Lemma subA_assign : forall (x : var) (e : exp) (P : assn) (s : stack) (ph : pheap),
    sat (s, ph) (subA x e P)  = sat (upd s x (edenot e s), ph) P.
  Proof.
    intros; eauto.
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
*)
  Theorem rule_assign x ctyp Exp Q : CSL (subA x Exp Q) (x ::T ctyp ::=  Exp) Q.
  Proof.
    unfold CSL, safe_nt; intros s ph hsat n; destruct n; 
    [simpl; eauto | 
     repeat split; try congruence].
    - intros; try inversion 1.
    - intros hF h c' ss' hdis heq hred; inversion hred; subst; repeat eexists; 
      match goal with [ H : (_, _) = (_, _) |- _ ] => inversion H end; 
      subst; simpl in *; eauto using safe_skip.
      apply safe_skip; eauto.
    - intros j c' H; inversion H.
  Qed.

  Definition indeE (Exp : exp) (x : var) :=
    forall s v, edenot Exp s = edenot Exp (var_upd s x v).

  Definition indelE (Exp : loc_exp) (x : var) :=
    forall s v, ledenot Exp s = ledenot Exp (var_upd s x v).

  Lemma htop_eq (h : heap) (ph : pheap') :
    ph = htop h -> forall x, h x = match ph x with | Some (_, x) => Some x | None => None end.
  Proof.
    intros heq x.
    (*destruct ph as [ph ?];  *) unfold htop, htop' in *; inversion heq; simpl in *.
    (* rewrite H; unfold htop';  *)destruct (h x); eauto.
  Qed.

  Theorem rule_read (x : var) (E1 : loc_exp) (E2 : exp) (p : Qc) (cty : option CTyp):
    indelE E1 x -> indeE E2 x -> 
    CSL (E1-->p(p, E2)) (x ::T cty ::= [ E1 ]) 
        ((E1-->p(p, E2)) ** !(x === E2)).
  Proof.
    unfold indeE, CSL, safe_nt; intros hinde1 hinde2 s h hsat; destruct n; 
    [simpl; eauto | simpl; repeat split; try congruence].
    - intros hF h' hdis heq hc; inversion hc; subst; simpl in *.
      specialize (hsat (ledenot E1 s)); simpl in *.
      destruct (eq_dec (ledenot E1 s) (ledenot E1 s)) as [_ | ?]; [| try congruence].
      rewrite <-(phplus_eq hdis) in heq; apply ptoheap_eq in heq.
      pose proof (htop_eq heq) as heq'; specialize (heq' (ledenot E1 s)).
      simpl in *; unfold phplus in *; rewrite hsat in heq'. 
      destruct (this hF (ledenot E1 s)) as [[? ?] | ]; congruence.
    - unfold access_ok; simpl in *; specialize (hsat (ledenot E1 s)).
      destruct (eq_dec (ledenot E1 s) (ledenot E1 s)) as [_ | ?]; [eexists; eauto | congruence].
    - intros hF h0 c' ss' hdis heq hred. inversion hred; clear hred; subst.
      inversion EQ1; clear EQ1; subst; simpl in *.
      repeat eexists; eauto. 
      apply safe_skip; simpl.
      apply scban_r; unfold_conn_all; simpl in *; [intros x0|].
      repeat match goal with [ |- context [eq_dec ?x ?y] ] => destruct (eq_dec x y) end;
      (try specialize (hsat x0)); subst; repeat rewrite <-hinde1 in hsat;
      repeat match goal with [ H : context [eq_dec ?x ?y] |- _ ] => destruct (eq_dec x y) end;
      try congruence.
      rewrite <-hinde2;
      unfold var_upd; destruct (var_eq_dec x x) as [|]; try congruence.
      rewrite <-(phplus_eq hdis) in heq; apply ptoheap_eq in heq.
      pose proof (htop_eq heq); simpl in *.
      unfold phplus in H; specialize (H (ledenot E1 s0)).
      rewrite hsat in H.
      lazymatch goal with [ H : context [eq_dec ?x ?y] |- _ ] => destruct (eq_dec x y) end; 
        try congruence; destruct (this hF (ledenot E1 s0)) as [[? ?]|]; congruence.
  Qed.

  Lemma ph_upd_phplus (ph1 ph2 : pheap) (x : loc) (v w : Z):
    pdisj ph1 ph2 -> this ph1 x = Some (full_p, w) -> 
    phplus (ph_upd ph1 x v) ph2 = ph_upd (phplus ph1 ph2) x v.
  Proof.
    intros hdis heq.
    destruct ph1 as [ph1 isp1], ph2 as [ph2 isp2]; simpl in *.
    unfold phplus, ph_upd; extensionality y.
    specialize (isp1 y); specialize (isp2 y); specialize (hdis y).
    destruct (eq_dec x y) as [eqxy | neqxy]; subst;
    destruct (ph1 y) as [[? ?]|], (ph2 y) as [[? ?]|]; eauto; try congruence.
    inversion heq; subst; 
    destruct hdis as [? [? Hc]]. apply frac_contra1 in Hc; tauto.
  Qed.

  Lemma ph_upd_ptoheap (ph : pheap) (h : heap) (x : loc) (v : Z) :
    ptoheap ph h -> ptoheap (ph_upd ph x v) (upd h x (Some v)).
  Proof.        
    intros heq y.
    unfold ptoheap, ph_upd, upd in *; specialize (heq y).
    destruct (eq_dec x y) as [eqxy | neqxy]; subst.
    destruct (eq_dec y y) as [_ | ?]; try congruence; tauto.
    destruct (this ph y) as [[? ?]|].
    destruct (eq_dec y x); try congruence; tauto.
    destruct (eq_dec y x); try congruence; tauto.
  Qed.

  Theorem rule_write (E0 : loc_exp) (E1 E2 : exp) :
    CSL (Apointsto full_p E0 E1) ([E0] ::= E2) (Apointsto full_p E0 E2).
  Proof.
    unfold CSL, safe_nt; intros s ph hsat n.
    pose proof (hsat (ledenot E0 s)) as hsat'; simpl in *.
    destruct (eq_dec (ledenot E0 s) (ledenot E0 s)) as [_|?]; try congruence.
    destruct n; [simpl; eauto| simpl; repeat split; try congruence].
    - intros hF h hdis heq hc; inversion hc; subst; simpl in *.
      rewrite <-(phplus_eq hdis) in heq; apply ptoheap_eq in heq; pose proof (htop_eq heq) as heq'.
      specialize (heq' (ledenot E0 s)); simpl in *.
      unfold phplus in *. destruct ph as [ph ?]; simpl in *; rewrite hsat' in heq'.
      destruct (this hF (ledenot E0 s)) as [[? ?]| ]; congruence.
    - simpl in hsat'. unfold access_ok; simpl.
      eexists; eauto.
    - simpl in hsat'. unfold write_ok; simpl.
      eexists; eauto.
    - intros hF h c' ss' hdis heq hred; inversion hred; clear hred; subst; simpl in *.
      inversion EQ1; clear EQ1; subst.
      eexists; exists (ph_upd2 ph (ledenot E0 s0) (edenot E2 s0)); repeat split; eauto.
      + unfold ph_upd2; simpl; apply (pdisj_upd _ _ hsat'); eauto.
      + unfold ph_upd2; simpl.
        erewrite ph_upd_phplus; eauto.
        cutrewrite (phplus ph hF = phplus_pheap hdis); [|simpl; eauto].
        apply ph_upd_ptoheap; eauto.
      + apply safe_skip; simpl; intros x.
        unfold_conn_all; simpl in *; unfold ph_upd.
        destruct (eq_dec (ledenot E0 s0) x); subst; eauto.
        * destruct (eq_dec (ledenot E0 s0) (ledenot E0 s0)); congruence.
        * rewrite hsat; eauto.
          destruct (eq_dec x (ledenot E0 s0)); congruence.
  Qed.

  Lemma safe_conseq:
    forall n C s h (Q : assn) (OK: safe_nt n C s h Q) (Q' : assn) (IMP: Q |= Q'),
      safe_nt n C s h Q'.
  Proof.
    unfold safe_nt; induction n; intros; intuition.
    simpl in *; intuition; repeat split; eauto.
    refine ((fun x y => y x) (H3 _ _ _ _ _ _ _) _); eauto; intros.
    destruct x0 as (? & ? & ? & ? & ? & ?); repeat eexists; eauto.
    rewrite H8; eauto.
    refine ((fun x y => y x) (H5 _ _ _ ) _); eauto; intros.
    destruct x0 as (? & ? & ? & ? & ? & ?); repeat eexists; eauto.
  Qed.

  Theorem rule_conseq (P : assn) C (Q P' Q' : assn) :
    CSL P C Q -> (P' |= P) -> (Q |= Q') -> CSL P' C Q'.
  Proof.
    unfold CSL; intuition; eauto using safe_conseq.
  Qed.

  Theorem rule_disj P1 P2 C Q1 Q2:
    CSL P1 C Q1 -> CSL P2 C Q2 ->
    CSL (Adisj P1 P2) C (Adisj Q1 Q2).
  Proof.
    unfold CSL; unfold_conn; intros; intuition; eapply safe_conseq; eauto; eauto.
  Qed.
End SeqCSL.

Section ParCSL.
  Import VectorNotations.

  Variable ntrd : nat.
  Hypothesis ntrd_gt_0 : (exists n', ntrd = S n').
  Variable bspec : nat -> (Vector.t assn ntrd * Vector.t assn ntrd)%type.
  Variable E : env.
  Hypothesis brr_lowassn : forall (i : nat),
                             (forall tid : Fin.t ntrd, low_assn E (fst (bspec i))[@tid]) /\
                             (forall tid : Fin.t ntrd, low_assn E (snd (bspec i))[@tid]).
  Hypothesis brr_wf : forall (i : nat) (st : pstate),
                        sat st (Aistar_v (fst (bspec i))) -> sat st (Aistar_v (snd (bspec i))).
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
         | Fin.F1 => tt
         | Fin.FS _ => tt
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
  
  Definition sat_k (ss : Vector.t stack ntrd) (h : pheap) (H : low_eq_l2 E ss) (Q : assn) :=
    match low_eq_repr H with
      | existT _ x P => sat (x, h) Q
    end.

  Fixpoint safe_nk (n : nat) (ks : klist ntrd) (ph : pheap) (Q : assn) :=
    match n with
      | 0 => True
      | S n =>
        let ss := Vector.map (fun s => snd s) ks in
        ((forall tid : Fin.t ntrd, fst ks[@tid] = Cskip) -> 
         exists (H : low_eq_l2 E ss), @sat_k ss ph H Q) /\
        (forall (hF : pheap) (h : heap), pdisj ph hF -> ptoheap (phplus ph hF) h ->
                                         ~ abort_k (ks, h)) /\
        ~ bdiv (ks, ph) /\
        (forall ws : Vector.t (nat * cmd) ntrd, 
           (forall tid : Fin.t ntrd, wait (fst ks[@tid]) = Some (ws[@tid])) ->
           (low_eq_l2 E ss) /\ exists b, (forall tid, fst ws[@tid] = b)) /\
        (forall (hF : pheap) (h' h : heap) (ks' : klist ntrd), 
           pdisj ph hF -> ptoheap (phplus ph hF) h ->
           (ks, h) ==>k (ks', h') ->
           exists (ph'' : pheap), pdisj ph'' hF /\ ptoheap (phplus ph'' hF) h' /\ 
                              safe_nk n ks' ph'' Q)
    end.

  Lemma red_k_step (ks1 ks2 ks3 : kstate ntrd) :
    ks1 ==>k* ks2 -> ks2 ==>k ks3 -> ks1 ==>k* ks3.
    intros.
    apply Operators_Properties.clos_rt_rt1n_iff.
    apply Operators_Properties.clos_rt_rt1n_iff in H.
    apply (rt_trans _ _ _ ks2); eauto.
    apply rt_step; eauto.
  Qed.

  Lemma safe_par (n : nat) (ks : klist ntrd) (ph : pheap) (Q : assn) 
        (hs : Vector.t pheap ntrd) (Qs : Vector.t assn ntrd) :
    let cs := Vector.map (fun cs => fst cs) ks in
    let ss := Vector.map (fun cs => snd cs) ks in
    (forall tid : Fin.t ntrd, low_assn E Qs[@tid]) ->
    disj_eq hs ph ->
    (forall tid : Fin.t ntrd, safe_nt bspec tid n cs[@tid] ss[@tid] hs[@tid] Qs[@tid]) ->
    ((Aistar_v Qs) |= Q) ->
    (exists ks1 ph_ini hs1 c ty,
       (ks1, ph_ini) ==>kp* (ks, ph) /\
       typing_cmd E c ty /\
       disj_eq hs1 ph_ini /\
       low_eq_l2 E (Vector.map snd ks1) /\
       (forall tid : Fin.t ntrd, fst ks1[@tid] = c) /\
       (forall tid : Fin.t ntrd, safe_aux bspec tid c (snd ks1[@tid]) (hs1[@tid]))) ->
    safe_nk n ks ph Q.
  Proof.
    revert ks ph hs. induction n; [intros; simpl; tauto | ].
    intros ks ph hs cs ss hlowQ hdis hsafei Hq h_for_bdiv.
    assert (forall (hF : pheap) (h : heap),
              pdisj ph hF -> (ptoheap (phplus ph hF) h) -> ~ abort_k (ks, h)) as not_aborts.
    { intros hF h hdisF Htop [tid Hc]; simpl in *.
      destruct (hsafei tid) as [_ [hsafe _]].
      unfold cs, ss in hsafe.
      destruct (disj_tid tid hdis) as [h' [hres [hdis' hph]]].
      erewrite !Vector.nth_map in hsafe; eauto.
      destruct (ks[@tid]) as [c s]; simpl in *.
      assert (pdisj h' hF).
      { assert (Heq : ph = phplus_pheap hdis').
        { destruct ph; apply pheap_eq; eauto. }
        rewrite Heq in hdisF; simpl in hdisF.
        apply pdisjC, pdisjE2 in hdisF; eauto. }
      specialize (hsafe (phplus_pheap H) h); apply hsafe; eauto.
      - simpl.
        apply pdisj_padd_expand; eauto.
        rewrite hph; eauto.
      - simpl.
        rewrite <-padd_assoc, hph; eauto.
        (* apply pdisj_padd_expand; eauto. *)
        (* rewrite hph; eauto. *) }
    (* assert (ptoheap (phplus hs[@tid] h') ph). *)
    (* {  *)
    (*   by (rewrite hph; apply ptoheap_htop). *)
    (* cutrewrite (phplus hs[@tid] h' = phplus_pheap hdis') in H; [|eauto]. *)
    (* pose proof (ptoheap_plus H hdisF) as heq'. *)
    (* cutrewrite (this (phplus_pheap hdis') = phplus hs[@tid] h') in heq'; [|eauto]. *)
    (* apply hdisj_pdisj in hdisF. *)
    (* cutrewrite (this (htop h) = htop' h) in hdisF; [|eauto]; rewrite <-hph in hdisF. *)
    (* apply pdisj_padd_expand in hdisF; eauto. *)
    (* rewrite padd_assoc in heq'; try tauto; destruct hdisF as [hdisF hd]. *)
    (* cutrewrite (phplus h' (htop hF) = phplus_pheap hd) in hdisF; [|eauto]. *)
    (* specialize (hsafe _ _ hdisF heq'); apply hsafe; eauto. } *)
    simpl. split; [ | split; [| split; [| split]] ]; eauto.
    - intros cskip.
      Definition emp_hp : heap := fun l => None.
      destruct h_for_bdiv as (ks1 & ph_ini & hs1 & c & ty & ? & ? & ? & ? & ? & ?).
      assert (low_eq_l2 E (get_ss_k (ks, ph))) as hleq.
      { eapply (when_stop ew ntrd_gt_0 bc_precise ); eauto;
        intros tid; unfold get_cs_k, get_ss_k in *; simpl; repeat erewrite Vector.nth_map in *; eauto;
        destruct H4 as [Hc Hsafe]; specialize (Hc tid); specialize (Hsafe tid);
        erewrite Vector.nth_map in Hc; eauto. }
      cutrewrite (get_ss_k (ks, ph) = Vector.map (fun s => snd s) ks) in hleq;
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
    - intros Hc.
      Lemma bdiv_weaken {ntrd' : nat} (ks : klist ntrd) (h h' : pheap) :
        bdiv (ks, h) -> bdiv (ks, h').
      Proof.
        unfold bdiv; intros (tid1 & tid2 & ?); exists tid1 tid2; apply H.
      Qed.
      destruct h_for_bdiv as (ks1 & ph_ini & hs1 & c & ty & H).
      (* apply (@bdiv_weaken ntrd _ _ h') in Hc. *)
      eapply barrier_divergence_freedom in Hc; destructs H; unfold get_cs_k, get_ss_k in *; simpl in *; eauto.
      apply ew.
      introv; simpl; erewrite Vector.nth_map; eauto.
      introv; simpl; erewrite Vector.nth_map; eauto.
    - intros ws Hbrr.
      destruct h_for_bdiv as (ks1 & ph_ini & hs1 & c & ty & H).
      cutrewrite (Vector.map (fun s => snd s) ks = get_ss_k (ks, ph)); [|eauto].
      eapply (when_barrier ew ntrd_gt_0 bc_precise); destructs H; eauto;
      intros tid; unfold get_cs_k, get_ss_k; erewrite Vector.nth_map; eauto.
    - intros hF h' h ks' hdis' Htop hred1.
      remember (ks', h') as kss'.
      cutrewrite (ks' = fst kss'); [| rewrite Heqkss'; eauto ].
      cutrewrite (h' = snd kss'); [| rewrite Heqkss'; eauto ]. clear Heqkss'.
      remember (phplus ph hF) as hhF. remember (ks, h) as kss.
      pose proof hred1 as hred2.
      destruct hred2.
      + (* rewrite HeqhhF in Heqkss. *) rewrite H2, H3 in H1. rewrite H in Heqkss. 
        inversion Heqkss. rewrite H5, H6 in *.
        destruct (hsafei i) as [_ [_ [_ [_ [hsafe _]]]]].
        (* assert (pdisj (htop h) (htop hF)) as pdisF by (apply hdisj_pdisj; eauto). *)
        destruct (disjeq_phplus i hdis hdis') as [h'' [hdisi'' [hdisF [heq hdisiF]]]].
        cutrewrite (phplus h'' hF = phplus_pheap hdisF) in hdisiF; eauto.
        assert (cs[@i] / (ss[@i], h) ==>s c' / (s', h'0)) as hred.
        { unfold cs, ss; erewrite !Vector.nth_map; eauto. rewrite H0; simpl; eauto. }
        assert (ptoheap (phplus hs[@i] (phplus_pheap hdisF)) h) as heqF.
        { cutrewrite (this (phplus_pheap hdisF) = phplus h'' hF); [| eauto]. 
          rewrite <-padd_assoc, heq;(* <-hplus_phplus *) eauto.
          subst; eauto. }
          (* cutrewrite ((phplus ph hF) =  (hplus h hF)); [apply ptoheap_htop | eauto]. } *)
        destruct (hsafe _ _ _ _ hdisiF heqF hred) as [snd_ss [ph' [heq' [hdisF' [heqA safe]]]]].
        simpl in heq'; rewrite <- heq' in *; clear snd_ss heq'.
        assert (pdisj ph' h'') as disjph'h'' by
            (cutrewrite (this (phplus_pheap hdisF) = phplus h'' hF) in hdisF'; 
             [apply pdisjE1 in hdisF'; eauto |eauto]).
        exists (phplus_pheap disjph'h'').
        simpl; repeat split; eauto.
        * apply pdisj_padd_expand; eauto.
        * rewrite padd_assoc; eauto.
        (* assert (exists h''0, ptoheap (phplus_pheap disjph'h'') h''0) as [h''0 heq''0]. *)
        (* { cutrewrite (this (phplus_pheap hdisF) = phplus h'' hF) in heqA; eauto. *)
        (*   rewrite <-padd_assoc in heqA; eauto. *)
        (*   cutrewrite (phplus ph' h'' = phplus_pheap disjph'h'') in heqA; eauto. *)
        (*   cutrewrite (this (phplus_pheap hdisF) = phplus h'' hF) in hdisF'; eauto. *)
        (*   apply pdisjC in hdisF'; rewrite phplus_comm in hdisF'; apply pdisj_padd_expand in hdisF';  *)
        (*   eauto; destruct hdisF' as [dis1 dis2]; apply pdisjC in dis1; rewrite phplus_comm in dis1; *)
        (*   eauto. *)
        (*   cutrewrite (phplus ph' h'' = phplus_pheap disjph'h'') in dis1; eauto. *)
        (*   simpl in *. *)
        (*   apply (ptoheap_phplus dis1 heqA). } *)
        (* assert (hdisj h''0 hF) as dis''F. *)
        (* { apply hdisj_pdisj. *)
        (*   apply ptoheap_eq in heq''0; rewrite <-heq''0. *)
        (*   cutrewrite (this (phplus_pheap disjph'h'') = phplus ph' h''); eauto. *)
        (*   cutrewrite (this (phplus_pheap hdisF) = phplus h'' (htop hF)) in hdisF'; eauto. *)
        (*   apply pdisj_padd_expand; eauto. } *)
        (* assert (h'0 = hplus h''0 hF) as Heq'_''F. *)
        (* { simpl. *)
        (*   cutrewrite (phplus ph' (phplus_pheap hdisF) = phplus_pheap hdisF') in heqA; eauto. *)
        (*   apply ptoheap_eq in heqA; apply ptoheap_eq in heq''0. *)
        (*   apply heap_pheap_eq.  *)
        (*   rewrite hplus_phplus; eauto; simpl. *)
        (*   inversion heq''0. inversion heqA. *)
        (*   cutrewrite (htop' hF = htop hF); eauto. *)
        (*   rewrite padd_assoc; eauto. } *)
        (* exists h''0; repeat split; eauto. *)
        * set (hs' := replace hs i ph').
          apply (IHn _ _ hs'); eauto.
          { unfold hs'; simpl.
            (* apply ptoheap_eq in heq''0; rewrite <-heq''0. *)
            apply (disj_tid i) in hdis. destruct hdis as [h'1 [hdis1 [pdis1 heqh]]].
            assert (h'1 = h'') as heq'' by (apply (@padd_cancel _ hs[@i]); eauto; congruence); 
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
          { destruct h_for_bdiv as (ks1 & ph_ini & hs1 & cini & ty & h_for_bdiv). 
            exists ks1 ph_ini hs1 cini ty; repeat split; destructs h_for_bdiv; eauto; simpl.
            subst.
            apply Operators_Properties.clos_rt_rt1n_iff, Operators_Properties.clos_rt_rtn1_iff.
            apply Operators_Properties.clos_rt_rt1n_iff, Operators_Properties.clos_rt_rtn1_iff in H4.
            econstructor; [|apply H4].
            Lemma safe_red_k {n : nat} (ks ks' : klist n) (ph phF ph' : pheap) h h' phs m bspec' Qs:
              pdisj ph phF -> pdisj ph' phF ->
              (ks, h) ==>k (ks', h') ->
              ptoheap (phplus ph phF) h ->
              ptoheap (phplus ph' phF) h' ->
              disj_eq phs ph ->
              (forall tid, safe_nt bspec' tid (S m) (fst ks[@tid]) (snd ks[@tid]) phs[@tid] Qs[@tid]) ->
              red_pk (ks, ph) (ks', ph').
            Proof.
              intros Hdis1 Hdis2 Hred Heq Heq' Hdiseq Hsafe; inversion Hred; subst.
              applys (>> redk_Seq c c' (s, ph) (s', ph') ph ph' i); eauto.
              - inversion H1; f_equal; eauto.
              - inversion H1; subst.
                lets (_ & _ & Haok & Hwok & _) : (>> Hsafe i); clear Hsafe; rewrite H2 in *; simpl in *.
                lets (hrest' & Hdeq' & Hdisji' & Heqi') : (>> disj_tid phs ph i Hdiseq).
                econstructor; eauto.
                lets Hok : (access_ok_mono Hdisji' Haok); simpl in *.
                applys_eq Hok 1; destruct ph; apply pheap_eq; auto.
                lets Hok : (write_ok_mono Hdisji' Hwok); simpl in *.
                applys_eq Hok 1; destruct ph; apply pheap_eq; auto.
              - applys redk_Barrier; eauto.
                f_equal; eauto.
                inverts H; inverts H0.
                assert (phplus ph phF = phplus ph' phF) by eauto using ptoD.
                apply padd_cancel2 in H; auto.
                intros; destruct (H1 i) as (? & ? & ? & H1'); destructs H1'; repeat eexists; eauto;
                inverts H; inverts H0; eauto.
            Qed.
            applys (>> (@safe_red_k) n hdis' Htop hdis).
            - simpl; apply pdisj_padd_expand; eauto.
            - eauto.
            - simpl; rewrite padd_assoc; eauto.
            - intros tid; lets hsafei': (hsafei tid); unfold cs, ss in hsafei'.
              repeat (erewrite Vector.nth_map in hsafei'; eauto). } 
      + (* assert ((ss0, hplus h hF) ==>k (ss', hplus h hF)) as hred. *)
        (* { destruct ks0, ks'0; inversion Heqkss; inversion H; inversion H0; subst; eauto. *)
        (*   rewrite H5, <-H6 in hred1; eauto. } *)
        subst.
        exists ph; eauto; repeat split; simpl; eauto.
        * inversion H; subst h; eauto.
        * subst; inversion H. rewrite <-H2, <-H3 in *.
          assert (forall tid : Fin.t ntrd, wait cs[@tid] = Some (j, fst ss'[@tid])) as Hwait.
          { intros tid; destruct (H1 tid) as [? [? [? [? [? ?]]]]];
            unfold cs; erewrite Vector.nth_map; eauto.
            rewrite H0, H5; simpl; eauto. }
          assert (forall tid : Fin.t ntrd, exists (phP ph' : pheap),
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
          { destruct h_for_bdiv as [? [? [? [? [? [Hred [? [? [? [? ?]]]]]]]]]].
            set (ws := init (fun i => (j, fst ss'[@i]))).
            eapply (when_barrier (ws := ws) ew ntrd_gt_0  bc_precise Hred); eauto;
            unfold get_cs_k, get_ss_k; intros; repeat (erewrite Vector.nth_map; eauto).
            unfold cs in Hwait; unfold get_cs_k, ws. rewrite init_spec; simpl.
            rewrite <-Hwait; erewrite Vector.nth_map; eauto. }
          destruct (low_eq_repr leq2ss) as [s Hs].
          assert (forall tid, sat (s, phPs[@tid]) (pre_j bspec tid j)) as Hsati.
          { intros tid; destruct (Hp' tid) as [_ [_ [? _]]].
            destruct (brr_lowassn j) as [Hlow _]; specialize (Hlow tid).
            apply (Hlow ss[@tid] s _ (Hs tid)); eauto. }
          assert (sat (s, phP) (Aistar_v (fst (bspec j)))) as Hsat.
          { apply (aistar_eq (hs := Vector.map (fun h => (s, h)) phPs)).
            - unfold get_hs. rewrite MyVector.map_map.
              rewrite (MyVector.map_ext (f := fun x => snd (s, x)) (g := id) phPs), MyVector.map_id; eauto.
            - intros tid; erewrite Vector.nth_map; eauto; apply Hsati. }
          apply brr_wf, aistar_disj in Hsat. destruct Hsat as [phQs [HeqQ Hsatiq]].
          assert (forall tid, pdisj phQs[@tid] phFs[@tid]) as HdisQF.
          { apply (disj_eq_each_disj HeqQ HeqF); eauto. }
          assert (forall tid, safe_nt bspec tid n (fst ss'[@tid]) ss[@tid]
                                      (phplus_pheap (HdisQF tid)) Qs[@tid]) as Hsafe.
          { intros tid; destruct (Hp' tid) as [_ [_ [_ Hsafe]]]; apply Hsafe; eauto.
            destruct (brr_lowassn j) as [_ Hlow]; specialize (Hlow tid).
            apply (Hlow ss[@tid] s _ (Hs tid)); eauto. }
          apply (IHn _ _ (init (fun tid => phplus_pheap (HdisQF tid)))); eauto.
          { cutrewrite (ph = (phplus_pheap HdisPF)); 
            [|unfold htop in *; simpl in *; destruct ph; apply pheap_eq; eauto].
            apply (disj_eq_sum HdisPF HeqQ HeqF); intros tid; rewrite init_spec; eauto. }
          { intros tid. erewrite !Vector.nth_map; eauto; rewrite init_spec. 
            cutrewrite (snd ss'[@tid] = ss[@tid]); [apply Hsafe|].
            destruct (H1 tid) as [? [? [? [? [? ?]]]]]. 
            unfold ss; erewrite Vector.nth_map; eauto. rewrite H0, H5; eauto. }
          { destruct h_for_bdiv as [ks1 [hs1 [ss1 [c [ty ?]]]]].
            exists ks1 hs1 ss1 c ty; repeat split; try tauto.
            destructs H0.
            apply Operators_Properties.clos_rt_rt1n_iff, Operators_Properties.clos_rt_rtn1_iff.
            apply Operators_Properties.clos_rt_rt1n_iff, Operators_Properties.clos_rt_rtn1_iff in H0.
            econstructor; eauto.
            applys (>> (@safe_red_k) n hdis' Htop hdis); eauto.
            intros tid; lets hsafei': (hsafei tid); unfold cs, ss in hsafei'.
            repeat (erewrite Vector.nth_map in hsafei'; eauto). }
  Qed.

(*  Definition nat_of_fin (i : Fin.t ntrd) : nat := proj1_sig (Fin.to_nat i).*)
(*  Definition Z_of_fin (i : Fin.t ntrd) : Z := Z.of_nat (nat_of_fin i).*)

  Definition CSLp (P : assn) (c : cmd) (Q : assn) :=
    forall (ks : klist ntrd) (h : pheap) (leqks : low_eq_l2 E (Vector.map (fun s => snd s) ks)),
      (forall tid : Fin.t ntrd, fst ks[@tid] = c) ->
      (forall tid : Fin.t ntrd, (snd ks[@tid]) (Var "tid") = Z_of_fin tid) ->
      sat_k h leqks P ->
      forall n, safe_nk n ks h Q.

  Theorem rule_par (Ps : Vector.t assn ntrd) (Qs : Vector.t assn ntrd) 
          (P : assn) (c : cmd) (Q : assn) (ty : type):
    (P |= Aistar_v Ps) -> (Aistar_v Qs |= Q) ->
    (forall tid, low_assn E Ps[@tid]) -> 
    (forall tid, low_assn E Qs[@tid]) ->
    typing_cmd E c ty ->
    (forall tid : Fin.t ntrd, 
       CSL bspec tid 
           (Ps[@tid] ** !((Var "tid") === Z_of_fin tid))
           c 
           Qs[@tid]) ->
    CSLp P c Q.
  Proof.
    unfold CSL, CSLp, sat_k in *.
    intros PPs QsQ HlowP HlowQ Hty Hsafei ks h leqks Heqc Htid Hsat n.
    destruct (low_eq_repr leqks) as [s Hlows].
    apply PPs in Hsat.
    destruct (aistar_disj Hsat) as [prehs [Hdisj Hsati]].
    assert (forall tid, sat ((Vector.map (fun s => snd s) ks)[@tid], prehs[@tid]) Ps[@tid]) as
        Hsat'.
    { intros tid; (*simpl; erewrite Vector.nth_map; eauto.*)
      apply ((HlowP tid) (Vector.map (snd (B:=stack)) ks)[@tid] s _ (Hlows tid));
      eauto. }
    apply (safe_par (hs := prehs) (Qs := Qs)); eauto.
    - unfold_conn_all; simpl in *; intros tid; specialize (Hsafei tid);
      specialize (Hsat' tid); erewrite !Vector.nth_map in *; 
      eauto.
      rewrite Heqc; apply Hsafei.
      erewrite Vector.nth_map in Hsat'; eauto.
      repeat eexists; unfold emp_ph; eauto.
      intros x; unfold emp_ph; auto.
      unfold_conn_all; simpl; auto. 
    - exists ks h prehs c ty; repeat split; eauto; unfold_conn_all; simpl in *.
      + apply rt1n_refl. 
      (* + unfold get_cs_k; simpl; intros tid; erewrite Vector.nth_map; eauto. *)
      + intros tid; unfold safe_aux; exists Qs[@tid]; intros n'.
        (* erewrite Vector.nth_map; eauto; *) apply Hsafei.
        specialize (Hsat' tid); erewrite Vector.nth_map in Hsat'; eauto.
        repeat eexists; eauto.
        unfold_conn_all; simpl in *; intros; unfold emp_ph; auto.
        apply disj_emp1.
  Qed.
End ParCSL.