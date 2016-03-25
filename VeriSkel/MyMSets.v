Require Export MSets.
Require Import GPUCSL.
Require Import assertions.
Require Import LibTactics.
Require Import ZArith.

Module Type DecType <: DecidableType.
  Parameter t : Type.
  Definition eq := @eq t.
  Lemma eq_equiv : Equivalence eq.
    repeat constructor; unfolds; unfold eq; intros; congruence.
  Qed.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End DecType.

Require Import SetoidClass.

Infix "==" := equiv.

Module MSets (D : DecType).
  Module SE := MSetWeakList.Make D.

  Instance eq_type_dt : eq_type D.t := {| eq_dec := D.eq_dec |}.

  Instance eqset_setoid : Setoid SE.t :=
    {| equiv := SE.Equal; setoid_equiv := _ |}.

  Lemma eqset_empty s s' : SE.Empty s -> s == s' -> SE.Empty s'.
  Proof.
    unfold not, SE.Empty, "=="; firstorder.
  Qed.

  Lemma choose_remove s x : SE.In x s -> s == SE.add x (SE.remove x s).
  Proof.
    revert s x; clear; intros s x; simpl.
    unfold SE.Equal; intros.
    rewrite SE.add_spec, SE.remove_spec.
    lets [? | ?]: (eq_dec a x); split; intros; substs; intuition.
  Qed.

  Lemma remove_id s x : ~SE.In x s -> s == SE.remove x s.
  Proof.
    simpl; unfold SE.Equal; intros; rewrite SE.remove_spec.
    split; intros; jauto.
    split; eauto; intros Hc; substs*.
  Qed.    
    
  Lemma equal_in x s s' : SE.In x s -> s == s' -> SE.In x s'.
  Proof.
    unfold SE.Equal, SE.In; intros.
    apply H0; auto.
  Qed.

  Lemma cardinal0_empty s : SE.cardinal s = 0 <-> SE.Empty s.
  Proof.
    unfold SE.Empty, SE.cardinal; intros; split; intros H.
    - destruct s as [[|? ?] ?]; simpl in *; try congruence.
      cbv; inversion 1.
    - destruct s as [[| ? ? ] ?]; simpl; auto.
      false; lets: (H e); apply H0; left; auto.
  Qed.

  Lemma cardinal_add x s : ~SE.In x s -> SE.cardinal (SE.add x s) = S (SE.cardinal s).
  Proof.
    destruct s as [s ?]; unfold SE.In, SE.add, SE.cardinal; simpl.
    remember (SE.Raw.cardinal s) as car_s eqn:Heqc.
    clear is_ok.
    revert s Heqc; induction car_s using lt_wf_ind; intros s Heqc Hnin.
    destruct car_s.
    - unfold SE.cardinal in *; destruct s as [|? ?]; simpl in *; congruence.
    - unfold SE.cardinal in *; destruct s as [|? ?]; simpl in *; try congruence.
      destruct (D.eq_dec x e); simpl in *; substs.
      + false; unfold SE.Raw.In in Hnin; apply Hnin.
        constructor; auto.
      + forwards* :(>>H car_s s).
        intros Hc; apply Hnin; right; auto.
  Qed.  

  Lemma remove_nin x s : ~SE.In x (SE.remove x s).
  Proof.
    rewrite SE.remove_spec; intros [? ?]; congruence.
  Qed.

  Lemma eqset_cardinal s s' : s == s' -> SE.cardinal s = SE.cardinal s'.
  Proof.
    destruct s as [s oks], s' as [s' oks'].
    simpl; unfold SE.Equal, SE.In, SE.cardinal.
    revert s' oks'; induction s; simpl in *; intros s' oks'.
    - destruct s'; simpl; auto.
      intros H; lets [? ?]: (H e); unfold SE.Raw.In in *; simpl in *.
      false; forwards: H1; [left; auto|inversion H2].
    - intros Heq.
      inverts oks.
      assert (SE.Raw.Ok s) by apply H2.
      cutrewrite (SE.Raw.cardinal s' = S (SE.Raw.cardinal (SE.Raw.remove a s'))).
      erewrite IHs; eauto using SE.Raw.remove_ok.
      { intros b; rewrite SE.Raw.remove_spec; eauto.
        split; intros.
        + split.
          rewrite <-Heq; right; auto.
          intros Hc; substs; unfold SE.Raw.In in *; auto.
        + destruct H0.
          rewrite <-Heq in H0; inverts H0; try congruence.
          unfold SE.Raw.In; auto. }
      { assert (SE.Raw.In a s').
        { rewrite <-Heq; left; auto. }
        revert H0 oks'; clear.
        induction s'; simpl.
        - inversion 1.
        - destruct D.eq_dec as [Heq | Heq]; simpl in *; substs; auto.
          simpl.
          intros; rewrite <-IHs'; eauto.
          inversion H0; substs; eauto; congruence.
          inversion oks'; substs; auto. }
  Qed.

  Lemma eqset_remove a s s' : s == s' -> SE.remove a s == SE.remove a s'.
  Proof.
    simpl; unfold SE.Equal; intros; rewrite !SE.remove_spec.
    firstorder.
  Qed.

  Lemma add_eq a s :
    ~In a s ->
    SE.Raw.add a s = s ++ a :: nil.
  Proof.
    induction s; simpl; eauto.
    intros Hc.
    destruct D.eq_dec; simpl.
    - false; apply Hc; left; auto.
    - f_equal; rewrite IHs; auto.
  Qed.

  Lemma set_eq s s' H H' : s = s' -> {| SE.this := s; SE.is_ok := H |} = {| SE.this := s'; SE.is_ok := H' |}.
  Proof.
    intros Heq.
    destruct Heq.
    assert (H = H') by (apply proof_irrelevance); substs; eauto.
  Qed.

  Lemma add_spec' a b s :
    SE.In a (SE.add b s) <-> a = b \/ (a <> b /\ SE.In a s).
  Proof.
    splits; [|rewrite SE.add_spec; intros [?|[? ?]]; eauto].
    destruct s as [s ok]; unfold SE.In, SE.add; simpl.
    induction s; simpl.
    - intros H; inverts H as H; eauto.
      inverts H.
    - destruct D.eq_dec as [Heq | Hneq]; [substs|].
      + destruct (eq_dec a a0); eauto.
      + intros H; inverts H; [right; split; eauto|].
        * left; eauto.
        * inverts ok; forwards*: IHs.
          destruct H as [? | [? ?]]; eauto.
          right; split; eauto.
          right; eauto.
  Qed.

  Lemma add_already a s :
    SE.In a s -> SE.add a s = s.
  Proof.
    destruct s as [s ok]; unfold SE.In, SE.add; simpl.
    induction s; simpl.
    - inversion 1.
    - intros H.
      apply set_eq.
      destruct D.eq_dec; eauto.
      inverts H.
      congruence.
      inverts ok.
      forwards * :(IHs H3).
      apply (f_equal SE.this) in H; simpl in *; congruence.
  Qed.
  
  Lemma add_inverts a s s' :
    ~SE.In a s -> ~SE.In a s' ->
    SE.add a s == SE.add a s' -> s == s'.
  Proof.
    unfold "=="; intros ? ? H b.
    lets ? ?: (H b); rewrite !SE.add_spec in *.
    split; intros H';
      [lets [?|?]: (H2 (or_intror H')) | lets [?|?]: (H3 (or_intror H'))]; eauto;
        [assert (a <> b); [intros Hc; substs; eauto|congruence ]..].
  Qed.
  
  Lemma choose_card s :
    0 < SE.cardinal s -> exists v, SE.In v s.
  Proof.
    destruct s as [[|a s] ok].
    - unfold SE.cardinal; simpl; omega.
    - exists a; cbv.
      left; auto.
  Qed.

  Lemma remove_card a s :
    SE.In a s ->
    SE.cardinal (SE.remove a s) = SE.cardinal s - 1.
  Proof.
    intros H; forwards*: (choose_remove s a).
    lets: (>>eqset_cardinal H0).
    rewrite cardinal_add in H1; [|apply remove_nin].
    omega.
  Qed.

  Lemma union_emp_l s : SE.union SE.empty s == s.
  Proof.
    unfold SE.Equal; intros a.
    rewrite SE.union_spec.
    lets: (SE.empty_spec); unfold SE.Empty in H.
    split; [intros [|]|intros]; eauto.
    intros; false; eapply H; eauto.
  Qed.

  Lemma union_emp_r s : SE.union s SE.empty == s.
  Proof.
    unfold SE.Equal; intros a.
    rewrite SE.union_spec.
    lets: (SE.empty_spec); unfold SE.Empty in H.
    split; [intros [|]|intros]; eauto.
    intros; false; eapply H; eauto.
  Qed.

  Lemma cardinal0_empty' s :
    SE.cardinal s = 0 -> s = SE.empty.
  Proof.
    destruct s as [[|a s ] ok]; cbv; try omega.
    intros; apply set_eq; auto.
  Qed.

  Lemma diff_emp_r s : SE.diff s SE.empty == s.
  Proof.
    unfold "=="; intros a; rewrite SE.diff_spec.
    lets: SE.empty_spec; unfold SE.Empty in *; firstorder.
  Qed.

  Instance union_proper_l : Proper (SE.Equal ==> SE.Equal ==> SE.Equal) SE.union.
  Proof.
    unfold SE.Equal; intros s1 s2 Heq s3 s4 Heq' a.
    rewrite !SE.union_spec; firstorder.
  Qed.

  Instance diff_proper_l : Proper (SE.Equal ==> SE.Equal ==> SE.Equal) SE.diff.
  Proof.
    unfold SE.Equal; intros s1 s2 Heq s3 s4 Heq' a.
    rewrite !SE.diff_spec; firstorder.
  Qed.

  Instance add_proper_l a : Proper (SE.Equal ==> SE.Equal) (SE.add a).
  Proof.
    unfold SE.Equal; intros s1 s2 Heq a'.
    rewrite !SE.add_spec; firstorder.
  Qed.

  Section Assns.
  Variable Vals : Type.
  Variable find : D.t -> option Vals.
  Variable den : D.t -> Vals -> assn.

  Definition assn_of_vs s :=
    SE.fold (fun x rec =>
               match find x with
               | Some vs => den x vs ** rec
               | None => FalseP
               end) s emp.
  
  Tactic Notation "simpl_avs" "in" hyp(HP) := unfold assn_of_vs, SE.fold in HP; simpl in HP.
  Tactic Notation "simpl_avs" := unfold assn_of_vs, SE.fold; simpl.
  Tactic Notation "simpl_avs" "in" "*" := unfold assn_of_vs, SE.fold in *; simpl in *.

  Arguments flip / _ _ _ _ _ _.

  Lemma assn_empty s stk : SE.Empty s -> stk ||= assn_of_vs s <=> emp.
  Proof.
    destruct s as [[| ? ?] ?]; rewrite <-SE.is_empty_spec; simpl; 
      simpl_avs; unfold SE.is_empty; simpl; try congruence.
    reflexivity.
  Qed.

  Lemma assn_empty' stk : stk ||= assn_of_vs SE.empty <=> emp.
  Proof.
    cbv; eauto.
  Qed.

  Lemma add_equiv a s stk :
    ~SE.In a s ->
    stk ||= assn_of_vs (SE.add a s) <=>
        match find a with
        | Some v => den a v ** assn_of_vs s
        | None => FalseP 
        end.
  Proof.
    unfold assn_of_vs, SE.add, SE.In; rewrite !SE.fold_spec.
    destruct s as [s oks]; simpl.
    intros; rewrite add_eq; [|intros Hc; eapply In_InA in Hc; eauto using SE.E.eq_equiv].
    rewrite fold_left_app; simpl.
    destruct (find a); [|reflexivity].
    reflexivity.
  Qed.

  Lemma fold_left_assns (s : list D.t) (P : assn) (stk : stack):
    stk ||=
        fold_left (fun rec x => match find x with
                                         | Some v => den x v ** rec
                                         | None => FalseP end) s P <=>
        P ** fold_left (fun rec x => match find x with
                                     | Some v => den x v ** rec
                                     | None => FalseP end) s emp.
  Proof.
    revert P; induction s; simpl; intros P.
    - rewrite emp_unit_r; reflexivity.
    - rewrite IHs.
      destruct (find a); simpl.
      rewrite (IHs (_ ** emp)).
      repeat rewrite <-sep_assoc, emp_unit_r; split; intros; repeat sep_cancel.
      rewrite (IHs FalseP).
      split; intros; destruct H as (? & ? & ? & ? & ?);
        try lazymatch goal with [H : False|- _] => destruct H end.
      destruct H0 as (? & ? & ? & ? & ?);
        try lazymatch goal with [H : False|- _] => destruct H end.
  Qed.

  Lemma add_equiv'   a s stk :
    SE.In a s ->
    stk ||= assn_of_vs s <=>
            assn_of_vs (SE.add a (SE.remove a s)).
  Proof.
    destruct s as [s oks].
    unfold "==", SE.In, SE.cardinal; simpl.
    unfold assn_of_vs, SE.fold, SE.Raw.fold at 1; simpl.
    generalize emp; induction s;  intros P Hin.
    - inversion Hin.
    - inverts Hin.
      + simpl; destruct D.eq_dec as [? | Hneq].
        2: congruence.
        rewrite add_eq; [|inverts oks; rewrite InA_alt in *; eauto].
        unfold SE.Raw.fold; rewrite fold_left_app; simpl.
        destruct (find a0); simpl.
        * rewrite fold_left_assns. rewrites (>>fold_left_assns s P).
          rewrite <-sep_assoc; reflexivity.
        * rewrite fold_left_assns; split; [|destruct 1].
          intros (? & ? & ? & ? & ?); eauto.
      + inverts keep oks.
        forwards*: (>> (IHs H3)).
        simpl; rewrite H.
        assert (a <> a0).
        { intros Hc; substs; eauto. }
        destruct D.eq_dec; try congruence.
        simpl; destruct D.eq_dec; try congruence; simpl.
        destruct (find a0); [|reflexivity].
        reflexivity.
  Qed.

  Lemma eqset_equiv s s' stk :
    SE.Equal s s' ->
    stk ||= assn_of_vs s <=> assn_of_vs s'.
  Proof.
    remember (SE.cardinal s) as car_s eqn:Heqc.
    revert s s' Heqc; induction car_s using lt_wf_ind; intros s s' Heqc Heqss'.
    destruct car_s.
    - assert (SE.Empty s).
      { unfold SE.Empty; intros.
        rewrite SE.cardinal_spec in Heqc.
        destruct s as [[|? ?] ?]; simpl in *; try congruence.
        cbv; inversion 1. }
      forwards* : (eqset_empty).
      forwards* Heq: (assn_empty s); rewrite Heq.
      forwards* Heq': (assn_empty s'); rewrite Heq'; reflexivity.
    - lets a Ha: (>>choose_card s); try omega.
      assert (SE.In a s') by (applys* Heqss').
      rewrites* (>>add_equiv' a s).
      rewrites* (>>add_equiv' a s').
      rewrites* (>>add_equiv (SE.remove a s)); [apply remove_nin|].
      rewrites* (>>add_equiv (SE.remove a s')); [apply remove_nin|].
      destruct (find a); [|reflexivity].
      rewrites H; try reflexivity.
      forwards*: (remove_card a s); omega.
      apply (add_inverts a); eauto using remove_nin.
      rewrite <-!choose_remove; eauto.
  Qed.          

  Instance eqset_proper stk : Proper (SE.Equal ==> equiv_sep stk) assn_of_vs.
  Proof.
    intros s1 s2 Heq; apply eqset_equiv; auto.
  Qed.

  Lemma union_add_l a s s' : SE.union (SE.add a s) s' == SE.add a (SE.union s s').
  Proof.
    simpl; unfold SE.Equal; intros.
    repeat (try rewrite SE.union_spec; try rewrite SE.add_spec); intuition.
  Qed.

  Lemma union_comm s1 s2 :
    SE.union s1 s2 == SE.union s2 s1.
  Proof.
    simpl; unfold SE.Equal; intros;
    rewrite !SE.union_spec; split; intros [|]; eauto.
  Qed.

  Lemma union_add_r a s s' : SE.union s (SE.add a s') == SE.add a (SE.union s s').
  Proof.
    simpl; unfold SE.Equal; intros.
    repeat (try rewrite SE.union_spec; try rewrite SE.add_spec); intuition.
  Qed.
  
  Lemma union_assns s s' stk :
    stk ||= 
        assn_of_vs (SE.union s s') <=>
        assn_of_vs s **
        assn_of_vs (SE.diff s' s).
  Proof.
    remember (SE.cardinal s) as car_s eqn:Heqc.
    revert s s' Heqc; induction car_s using lt_wf_ind; intros s s' Heqc.
    destruct car_s.
    - forwards*: cardinal0_empty'; substs.
      rewrites (union_emp_l s').
      rewrite assn_empty'.
      rewrites (diff_emp_r s').
      rewrite emp_unit_l; reflexivity.
    - forwards* (a & Hin): (choose_card s); try omega.
      forwards* Heq: (choose_remove s).
      rewrite Heq at 1 2.
      rewrite union_add_l, <-union_add_r.
      rewrite (H car_s); try omega; try (rewrites* remove_card; omega).
      assert (Heq' : SE.diff (SE.add a s') (SE.remove a s) ==
                     SE.add a (SE.remove a (SE.diff s' s))).
      { simpl; unfold SE.Equal; intros;
        repeat (try rewrite SE.diff_spec;
                try rewrite SE.add_spec;
                try rewrite SE.remove_spec).
        assert (Decidable.decidable (SE.In a0 s)).
        { unfolds; destruct (SE.mem a0 s) eqn:Heq'.
          rewrite SE.mem_spec in *; eauto.
          right; intros Hc; rewrite <-SE.mem_spec in Hc; congruence. }
        clear; intros; intuition.
        destruct (eq_dec a0 a); eauto. }
      rewrite Heq'.
      repeat rewrite add_equiv; [|apply remove_nin..].
      destruct (find a).
      2: split; intros (? & ? & ? & ? & ? & ?); lazymatch goal with [H : False |- _] => destruct H end.
      assert (Heq'' : SE.remove a (SE.diff s' s) == SE.diff s' s).
      { simpl; unfold SE.Equal; intros;
        repeat (try rewrite SE.diff_spec;
                try rewrite SE.add_spec;
                try rewrite SE.remove_spec).
        intuition; subst; eauto. }
      rewrite Heq''.
      rewrite <-!sep_assoc; split; intros; repeat sep_cancel.
  Qed.
  End Assns.

  Lemma assn_of_vs_eq Vals find den find' den' s stk :
    (forall x, SE.In x s -> find x = find' x) ->
    (forall x, SE.In x s -> den x = den' x) ->
    stk ||= assn_of_vs Vals find den s <=>
            assn_of_vs Vals find' den' s.
  Proof.
    revert find den find' den' stk.
    destruct s as [s isok]; simpl.
    unfold SE.In, assn_of_vs, SE.fold, SE.Raw.fold, flip; simpl.
    induction s; simpl.
    - reflexivity.
    - introv Hfind Hden.
      rewrite fold_left_assns.
      rewrites (>>fold_left_assns find').
      rewrite Hfind, Hden; destruct (find' a); try (simpl; left; eauto).
      inverts isok.
      rewrite IHs; [reflexivity|..]; eauto.
      intros; apply Hfind; right; eauto.
      intros; apply Hden; right; eauto.
      split; intros (? & ? & [] & ? & ? & ?).
  Qed.

  Lemma in_dec s x : {SE.In x s} + {~SE.In x s}.
  Proof.
    destruct (SE.mem x s) eqn:Heq; [left|right; intros Hc];
      forwards* (? & ?): (SE.mem_spec s x).
    forwards*: H0; congruence.
  Qed.
  Include SE.
End MSets.
