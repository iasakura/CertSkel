Require Import PeanoNat Arith Omega Psatz Classical SetoidClass Qcanon.
Require Import LibTactics.
Require Import PHeap Lang CSLLemma Bdiv.
Require Import List.

Definition CSL {ntrd} BS (tid : Fin.t ntrd) P C Q :=
  forall s h, sat s h P -> forall (n : nat), safe_nt BS tid n C s h Q.

Lemma safe_skip ntrd (tid : Fin.t ntrd) BS : forall n s h (Q : assn), sat s h Q -> safe_nt BS tid n Cskip s h Q.
Proof.
  intros; destruct n; simpl; eauto; repeat split; eauto.
  intros. intros Hc; inversion Hc.
  intros ? ? ? ? ? ? Hc; inversion Hc.
  intros ? ? Hc; inversion Hc.
Qed.

Lemma rule_assign ntrd BS (tid : Fin.t ntrd) e x cty (v : val) Env P Res :
  evalExp Env e v ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= e)
      (Assn Res P (Ent x v :: remove_var Env x)).
Proof.
  intros HevalLe.
  unfold CSL; intros s h Hsat; destruct n; [now (simpl; eauto)|].
  unfold sat in Hsat; simpl in Hsat.
  simpl; repeat split; try congruence.
  - introv ? ? HC; inverts HC.
  - introv Hdis Htoh Hred.
    inverts Hred; inverts EQ1; simpl.
    repeat eexists; repeat split; eauto.
    apply safe_skip; splits; jauto.
    cutrewrite (edenot e s0 = v); [|applys (>> evalExp_ok HevalLe); jauto].
    split.
    + unfold var_upd in *; simpl; destruct var_eq_dec; try congruence.
    + applys* disjoint_inde_env.
      apply remove_var_inde; simpl in *; auto.
      simpl; eauto.
      applys* remove_var_imp.
Qed.

Lemma htop_eq (h : heap) (ph : pheap') :
  ph = htop h -> forall x, h x = match ph x with | Some (_, x) => Some x | None => None end.
Proof.
  intros heq x.
  unfold htop, htop' in *; inversion heq; simpl in *.
  destruct (h x); eauto.
Qed.

Lemma rule_read ntrd BS (tid : Fin.t ntrd) le l x cty p (v : val) Env (P : Prop) (Res Res' : res) :
  evalLExp Env le l ->
  (P -> (Res |=R l |->p (p, v) *** Res')) ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= [le])
      (Assn Res P (Ent x v :: remove_var Env x)).
Proof.
  intros HevalLe Hres.
  unfold CSL, sat; intros s h Hsat; destruct n; [now (simpl; eauto)|].
  simpl in *.
  assert (exists p, PHeap.this h l = Some (p, v)) as [p' Heq].
  { forwards* (? & ? & ? & ? & ? & ?): (>> Hres Hsat).
    simpl in *.
    rewrite <-H2; unfold phplus.
    rewrite H; simpl.
    destruct l; try destruct pl; simpl in *; destruct (eq_dec _ _); try congruence;
    destruct (PHeap.this x1 _) as [[? ?]|]; eexists; eauto. }
  assert (Hle : ledenot le s = l).
  { forwards*: (>>evalLExp_ok HevalLe). }
  simpl; repeat split; try congruence.
  - intros hF h' Hdis Htoh HC.
    inverts HC; simpl in *.
    apply ptoheap_eq in Htoh.
    rewrites* (>>htop_eq Htoh) in NIN.
    unfold phplus in NIN.
    rewrite Hle, Heq in NIN.
    destruct (PHeap.this hF l) as [[? ?]|]; congruence.
  - hnf.
    eexists; rewrite Hle, Heq; eauto.
  - introv Hdis Htoh Hred.
    destruct ss' as [s' h'].
    inverts Hred; simpl in *.
    inverts EQ1; inverts EQ2.
    repeat eexists; eauto.
    apply safe_skip; simpl.
    unfold sat; simpl; splits; jauto.
    + auto; simpl.
      unfold var_upd; destruct (var_eq_dec _ _); try congruence.
      rewrite Hle in RD.
      apply ptoheap_eq in Htoh.
      apply (f_equal (fun x => x l)) in Htoh.
      unfold phplus, htop in Htoh.
      simpl in Htoh; unfold htop' in Htoh; rewrite Heq in Htoh.
      rewrite RD in Htoh.
      destruct (PHeap.this hF _) as [[? ?] |], (h1 _) as [|]; simpl in *;
      inverts* Htoh.
    + applys* disjoint_inde_env.
      apply remove_var_inde; simpl in *; auto.
      simpl; eauto.
      applys* remove_var_imp.
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

Lemma rule_write ntrd BS (tid : Fin.t ntrd) le l e (v : val) v' Env (P : Prop) (Res Res' : res) :
  evalLExp Env le l ->
  evalExp Env e v' ->
  (P -> Res |=R ((l |->p (1, v)) *** Res')) ->
  CSL BS tid
      (Assn Res P Env)
      ([le] ::= e)
      (Assn (l |->p (1, v') *** Res') P Env).
Proof.
  intros HevalLe Henv Hres.
  unfold CSL, sat; intros s h Hsat; destruct n; [now (simpl; eauto)|].
  (* destruct Hsat as [HnvR Hsat]; simpl in *. *)
  simpl in *.
  assert (Heq : PHeap.this h l = Some (1%Qc, v)).
  { forwards* (? & ? & ? & ? & ? & ?): (>> Hres Hsat).
    simpl in *.
    rewrite <-H2; unfold phplus.
    forwards* Heq: (H l).
    destruct (eq_dec _ _); try congruence.
    rewrite H; simpl.
    assert (PHeap.this x0 l = None).
    { forwards*Hdis: (H1 l); rewrite Heq in Hdis.
      destruct x0; simpl.
      forwards*: (is_p  l); simpl in *.
      destruct (this l) as [[? ?]|]; auto.
      lra_Qc. }
    rewrite H3.
    destruct l; simpl in *; destruct (eq_dec _ _); try congruence; auto. }
  assert (Hle : ledenot le s = l).
  { forwards*: (>>evalLExp_ok HevalLe). }
  assert (Hv : edenot e s = v').
  { forwards*: (>>evalExp_ok Henv). }
  simpl; repeat split; try congruence.
  - intros hF h' Hdis Htoh HC.
    inverts HC; simpl in *.
    apply ptoheap_eq in Htoh.
    rewrites* (>>htop_eq Htoh) in NIN.
    unfold phplus in NIN.
    rewrite Hle, Heq in NIN.
    destruct (PHeap.this hF l) as [[? ?]|]; congruence.
  - hnf.
    eexists; rewrite Hle, Heq; eauto.
  - hnf; eexists; rewrite Hle; eauto.
  - introv Hdis Htoh Hred.
    destruct ss' as [s' h'].
    inverts Hred; simpl in *.
    inverts EQ1; inverts EQ2.
    eexists; exists (ph_upd2 h l v'); repeat split.
    + unfold ph_upd2; simpl; apply (pdisj_upd _ _ Heq); eauto.
    + unfold ph_upd2; simpl.
      erewrite ph_upd_phplus; eauto.
      cutrewrite (phplus h hF = phplus_pheap Hdis); [|simpl; eauto].
      rewrite Hle, Hv.
      apply (ph_upd_ptoheap); eauto.
    + apply safe_skip.
      (* split; eauto. *)
      splits; jauto.
      destruct Hsat as (Hsat & Hp & _).
      apply Hres in Hsat; eauto.
      destruct Hsat as (? & ? & ? & ? & ? & ?).
      exists (ph_upd2 x l v') x0; repeat split; eauto.
      { simpl in *; intros.
        unfold ph_upd2, ph_upd; simpl.
        specialize (H l0).
        destruct (eq_dec l l0), (eq_dec l0 l); try congruence; simpl; eauto. }
      { unfold pdisj, ph_upd2, ph_upd in *; intros x'; specialize (H1 x'); simpl in *.
        specialize (H x'); rewrite H in *.
        destruct x0 as [? ispx0]; simpl in *; clear H0.
        specialize (ispx0 x').
        destruct (eq_dec x' l), (eq_dec l x'), (this x') as [[? ?]|]; simpl in *;
        repeat split; try congruence; try lra_Qc. }
      unfold phplus, ph_upd2, ph_upd in *; simpl; extensionality t.
      rewrite <- H2.
      destruct (eq_dec _ _); eauto.
      cutrewrite (PHeap.this x0 t = None); auto.
      specialize (H t); specialize (H1 t).
      rewrite H in H1.
      destruct x0 as [x0 ispx0]; simpl in *; clear H0; specialize (ispx0 t).
      destruct (x0 t) as [[? ?]|]; subst; repeat rewrite ledenot_id, e0 in *; auto.
      destruct (eq_dec _ _); try congruence.
      lra_Qc.
Qed.

Lemma safe_conseq ntrd BS (tid : Fin.t ntrd) :
  forall n C s h (Q : assn) (OK: safe_nt BS tid n C s h Q) (Q' : assn) (IMP: Q |= Q'),
    safe_nt BS tid n C s h Q'.
Proof.
  induction n; intros; intuition.
  simpl in *; intuition; repeat split; eauto.
  refine ((fun x y => y x) (H3 _ _ _ _ _ _ _) _); eauto; intros.
  destruct x0 as (? & ? & ? & ? & ? & ?); repeat eexists; eauto.
  rewrite H8; eauto.
  refine ((fun x y => y x) (H5 _ _ _ ) _); eauto; intros.
  destruct x0 as (? & ? & ? & ? & ? & ?); repeat eexists; eauto.
Qed.

Theorem rule_conseq ntrd BS (tid : Fin.t ntrd) (P : assn) C (Q P' Q' : assn) :
  CSL BS tid P C Q -> (P' |= P) -> (Q |= Q') -> CSL BS tid P' C Q'.
Proof.
  unfold CSL; intuition; eauto using safe_conseq.
Qed.

Lemma forward ntrd BS (tid : Fin.t ntrd) P Q Q' C :
  (Q |= Q') ->
  CSL BS tid P C Q ->
  CSL BS tid P C Q'.
Proof.
  intros; eapply rule_conseq; eauto.
Qed.

Lemma backward ntrd BS (tid : Fin.t ntrd) P P' Q C :
  (P' |= P) ->
  CSL BS tid P C Q ->
  CSL BS tid P' C Q.
Proof.
  intros; eapply rule_conseq; eauto.
Qed.

Lemma rule_if_disj ntrd BS (tid : Fin.t ntrd) b c1 c2 P cond Res Env Q1 Q2 :
  evalBExp Env b cond ->
  CSL BS tid (Assn Res (P /\ cond) Env) c1 Q1 ->
  CSL BS tid (Assn Res (P /\ ~cond) Env) c2 Q2 -> 
  CSL BS tid (Assn Res P Env) (Cif b c1 c2) (Disj_assn Q1 Q2).
Proof.
  unfold CSL; intuition; destruct n; [simpl; eauto|]; simpl in *; eauto; intros; intuition.
  - inversion H3.
  - inversion H5.
  - unfold access_ok; simpl; eauto.
  - unfold write_ok; simpl; eauto.
  - inverts H5; substs; repeat eexists; eauto; simpl.
    + unfold sat in *; simpl in *.
      forwards*: evalBExp_ok.
      eapply safe_conseq; [apply H0; unfold sat in *; simpl in *; splits; jauto; tauto|].
      unfold sat; simpl; eauto.
    + unfold sat in *; simpl in *.
      forwards*: evalBExp_ok.
      eapply safe_conseq; [apply H1; unfold sat in *; simpl in *; splits; jauto|].
      destruct bdenot eqn:Heq; try congruence; rewrite <-H5; split; jauto; congruence.
      unfold sat; simpl; eauto.
  - inverts H3.
Qed.

Lemma rule_disj ntrd BS (tid : Fin.t ntrd) c P1 P2 Q :
  CSL BS tid P1 c Q ->
  CSL BS tid P2 c Q ->
  CSL BS tid (Disj_assn P1 P2) c Q.
Proof.
  intros; intros s h Hsat; destruct Hsat; unfold CSL, sat in *; eauto.
Qed.

(* Lemma has_no_vars_mp (l : loc) (v : val) p : has_no_vars (l -->p (p, v)). *)
(* Proof. *)
(*   apply has_no_vars_mp; *)
(*   destruct l; simpl; eauto. *)
(* Qed. *)

(* Lemma has_no_vars_array l vs p : has_no_vars (array l vs p). *)
(* Proof. *)
(*   revert l; induction vs; intros l; simpl; eauto with novars_lemma. *)
(*   apply has_no_vars_star; eauto. *)
(*   apply has_no_vars_mp; simpl; eauto. *)
(* Qed. *)

(* Hint Resolve has_no_vars_array has_no_vars_mp : novars_lemma. *)

(* Ltac fold_sat := *)
(*   match goal with *)
(*   | [|- ?P ?s ?h] => *)
(*     lazymatch type of s with *)
(*     | stack => cutrewrite (P s h = sat s h P); [|reflexivity] *)
(*     end *)
(*   | _ => idtac *)
(*   end. *)

(* Ltac fold_sat_in H := *)
(*   lazymatch type of H with *)
(*   | ?P ?s ?h =>  *)
(*     lazymatch type of s with *)
(*     | stack => cutrewrite (P s h = sat s h P) in H; [|reflexivity] *)
(*     end *)
(*   | _ => idtac *)
(*   end. *)

Lemma rule_read_array ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var)
      (cty : option CTyp) (p : Qc) (Env : list entry)
      (P : Prop) (Res Res' : res) (arr : list val) ix i iz:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array l arr p *** Res' ->
  iz = Zn i ->
  (P -> i < length arr) ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= [le +o ix])
      (Assn Res P (Ent x (nth i arr 0%Z) :: (remove_var Env x))).
Proof.
  intros.
  eapply forward; [|applys (>>rule_read (loc_off l iz) p (nth i arr 0%Z) ) ].
  2: constructor; eauto.
  Focus 2.
  { intros Hp h Hres.
    apply H1 in Hres.
    rewrites* (array_unfold i arr) in Hres; simpl in Hres.
    repeat rewrite <-res_assoc in *.
    subst; unfold sat in *.
    rewrite res_CA in Hres; apply Hres. } Unfocus.
  auto.
Qed.

Lemma rule_read_array' ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var)
      (cty : option CTyp) (p : Qc) (Env : list entry)
      (P : Prop) (Res Res' : res) (arr : list val) dist ix i iz j st:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array' l (ith_vals dist arr j st) p *** Res' ->
  iz = Zn i ->
  (P -> i < length arr /\ dist (st + i) = j) ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= [le +o ix])
      (Assn Res P (Ent x (nth i arr 0%Z) :: (remove_var Env x))).
Proof.
  intros.
  eapply forward; [|applys (>>rule_read (loc_off l iz) p (nth i arr 0%Z) ) ].
  2: constructor; eauto.
  Focus 2.
  { intros Hp h Hres.
    apply H1 in Hres.
    rewrites* (array'_unfold i) in Hres.
    2: rewrite ith_vals_length; tauto.
    cutrewrite (nth i (ith_vals dist arr j st) None = Some (get arr i)) in Hres.
    repeat rewrite <-res_assoc in *.
    rewrite res_CA in Hres.
    subst; eauto.
    rewrite (nth_skip _ 0%Z); simpl.
    destruct Nat.eq_dec; try tauto.
    destruct lt_dec; try tauto.
  } Unfocus.
  auto.
Qed.

Lemma rule_read_sarray ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (x : var)
      (cty : option CTyp) (p : Qc) (Env : list entry)
      (P : Prop) (Res Res' : res) (arr : list val) ix i iz d j:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array' l (skip arr d j) p *** Res' ->
  iz = Zn i ->
  (P -> i < length arr /\ i mod d = j) ->
  CSL BS tid
      (Assn Res P Env)
      (x ::T cty ::= [le +o ix])
      (Assn Res P (Ent x (nth i arr 0%Z) :: (remove_var Env x))).
Proof.
  intros; eapply rule_read_array'; eauto.
Qed.

Lemma rule_write_array :
  forall (ntrd : nat) BS
         (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (e : exp)
         (v : val) (Env : list entry) (P : Prop) (Res Res' : res) arr ix iz i,
    evalLExp Env le l ->
    evalExp Env ix iz ->
    iz = Zn i ->
    (P -> i < length arr) ->
    evalExp Env e v ->
    Res |=R array l arr 1 *** Res' ->
    CSL BS tid
        (Assn Res P Env)
        ([le +o ix]::=e)
        (Assn (array l (set_nth i arr v) 1 *** Res') P Env).
Proof.
  intros.
  eapply forward; [|applys (>>rule_write (loc_off l iz) (nth i arr 0%Z))].
  2: do 1 constructor; eauto.
  2: eauto.
  Focus 2.
  { intros h Hp Hsat; apply H4 in Hsat.
    rewrite (array_unfold i) in Hsat; [|forwards*: H2; lia].
    repeat rewrite <-res_assoc in Hsat.
    rewrite res_CA in Hsat.
    substs; eauto. } Unfocus.
  apply Assn_imply; eauto.
  - intros; apply incl_refl.
  - intros Hp h Hsat.
    rewrite (array_unfold i); eauto.
    rewrite firstn_set_nth_ignore.
    rewrite skipn_set_nth_ignore; substs.
    rewrite <-!res_assoc in *; rewrite res_CA; eauto.
    rewrite nth_set_nth; destruct Nat.eq_dec; try omega.
    destruct lt_dec; try omega; eauto.
    false; apply n; eauto.
    rewrites* length_set_nth.
Qed.

(* Lemma has_no_vars_array' ptr arr p : has_no_vars (array' ptr arr p). *)
(* Proof. *)
(*   revert ptr; induction arr; simpl; eauto with novars_lemma. *)
(*   destruct a; eauto with novars_lemma. *)
(* Qed. *)

(* Hint Resolve has_no_vars_array' : novars_lemma. *)

(* Notation set_nth' i arr v := (set_nth i arr (Some v)). *)

(* Lemma ith_vals_set_nth T dist ls (x : T) s i: *)
(*   ith_vals dist (set_nth i ls x) (dist (s + i)) s = *)
(*   set_nth i (ith_vals dist ls (dist (s + i)) s) (Some x). *)
(* Proof. *)
(*   revert s i; induction ls; simpl; intros s i; simpl; eauto. *)
(*   - destruct i; simpl; eauto. *)
(*   - destruct i; simpl. *)
(*     + rewrite <-plus_n_O; destruct Nat.eq_dec; try omega; eauto. *)
(*     + rewrite <-plus_Snm_nSm; rewrite IHls; eauto. *)
(* Qed. *)

(* Lemma ith_vals_set_nth0 T dist ls (x : T) i j: *)
(*   j = dist i -> *)
(*   ith_vals dist (set_nth i ls x) j 0 = *)
(*   set_nth i (ith_vals dist ls j 0) (Some x). *)
(* Proof. intros; substs; forwards*: (>>ith_vals_set_nth x 0). Qed. *)

Lemma rule_write_array'  ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc)
      (Env : list entry) (P : Prop) (Res Res' : res) (arr : list val) dist ix i iz j e v st:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array' l (ith_vals dist arr j st) 1 *** Res' ->
  evalExp Env e v ->
  iz = Zn i ->
  (P -> i < length arr /\ dist (st + i) = j) ->
  CSL BS tid
      (Assn Res P Env)
      ([le +o ix] ::= e)
      (Assn (array' l (ith_vals dist (set_nth i arr v) j st) 1 *** Res') P Env).
Proof.
  intros.
  eapply forward; [|applys (>>rule_write (loc_off l iz) (nth i arr 0%Z) )].
  2: constructor; eauto.
  2: eauto.
  Focus 2.
  { intros Hp h Hres.
    apply H1 in Hres.
    rewrites* (array'_unfold i (ith_vals dist arr j st) l 1) in Hres; [|rewrites* ith_vals_length].
    repeat rewrite <-res_assoc in *; substs.
    rewrite res_CA in Hres.
    rewrite (nth_skip _ 0%Z) in Hres.
    forwards*: H4.
    destruct Nat.eq_dec, (lt_dec i (length arr)); try now (simpl in *; omega).
    apply Hres. } Unfocus.
  apply Assn_imply; eauto using incl_refl.
  intros Hp h Hsat.
  rewrites* (>>array'_unfold i l 1%Qc); [rewrite ith_vals_length, length_set_nth; tauto|].
  forwards*[? ?]: H4; substs.
  repeat rewrite <-res_assoc in *; substs.
  rewrite (nth_skip _ 0%Z); destruct Nat.eq_dec; try (simpl in *; omega).
  destruct lt_dec; try (tauto).
  2:rewrite length_set_nth in *; tauto.
  rewrite nth_set_nth; destruct (Nat.eq_dec i i), (lt_dec i (length arr)); try omega.
  rewrites* ith_vals_set_nth.
  rewrite firstn_set_nth_ignore.
  rewrite skipn_set_nth_ignore.
  rewrite res_CA in Hsat.
  eauto.
Qed.

Lemma rule_write_sarray'  ntrd BS
      (tid : Fin.t ntrd) (le : loc_exp) (l : loc) (Env : list entry)
      (P : Prop) (Res Res' : res) (arr : list val) ix i iz d j e v:
  evalLExp Env le l ->
  evalExp Env ix iz ->
  Res |=R array' l (skip arr d j) 1 *** Res' ->
  evalExp Env e v ->
  iz = Zn i ->
  (P -> i < length arr /\ i mod d = j) ->
  CSL BS tid
      (Assn Res P Env)
      ([le +o ix] ::= e)
      (Assn ((array' l (skip (set_nth i arr v) d j) 1) *** Res') P Env).
Proof.
  intros; applys* rule_write_array'.
Qed.

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

Definition inde (R : assn) (ls : list var) :=
  forall (x : var) (s : stack) (h : pheap) (v : Z),
    In x ls -> (sat s h R <-> sat (var_upd s x v) h R).

Fixpoint writes_var (c : cmd) : list var :=
  match c with
    | Cskip | Cwrite _ _ | Cbarrier _ => nil
    | Cassign _ v _ | Cread _ v _ => v :: nil
    | Cseq c1 c2 => writes_var c1 ++ writes_var c2
    | Cif _ c1 c2 => writes_var c1 ++ writes_var c2
    | Cwhile _ c => writes_var c
  end%list.

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

Lemma inde_inv1 (c1 c2 : cmd) (st1 st2 : state) (R : assn) :
  c1 / st1 ==>s c2 / st2 -> inde R (writes_var c1) -> inde R (writes_var c2).
Proof.
  intros H hinde x s h v Hin; specialize (hinde x s h v). 
  forwards*: (>>writes_inv Hin).
Qed.

Lemma writes_agrees' (c1 c2 : cmd) (st1 st2 : state) (h : pheap) (R : assn):
  c1 / st1 ==>s c2 / st2 ->
  inde R (writes_var c1) ->
  sat (fst st1) h R -> sat (fst st2) h R.
Proof.
  intros hred hinde hsat; apply writes_agrees in hred as [heq | [x [v [Hin Heq]]]].
  - rewrite <-heq; eauto.
  - rewrite Heq; apply hinde; eauto.
Qed.

Lemma wait_writes (c1 c2 : cmd) (j : nat) :
  wait c1 = Some (j, c2) -> forall x, In x (writes_var c2) -> In x (writes_var c1).
Proof.
  revert j c2; induction c1; simpl; try now inversion 1.
  intros j c2; destruct (wait c1_1) as [[? ?]|]; intros H; inversion H; inversion H2.
  simpl; intros x H'; apply in_app_iff in H'; apply in_app_iff.
  specialize (IHc1_1 n c eq_refl x); tauto.
Qed.

Lemma inde_inv2 (c1 c2 : cmd) (j : nat) (R : assn) :
  wait c1 = Some (j, c2) -> inde R (writes_var c1) -> inde R (writes_var c2).
  intros H hinde x s h v Hin; specialize (hinde x s h v). 
  forwards*: (>>wait_writes Hin).
Qed.

Lemma safe_frame ntrd (tid : Fin.t ntrd) BS : 
  forall (n : nat) (C : cmd) (s : stack) (ph phR : pheap) (Q R : assn) (disR : pdisj ph phR),
    safe_nt BS tid n C s ph Q
    -> sat s phR R
    -> inde R (writes_var C)
    -> safe_nt BS tid n C s (phplus_pheap disR) (Q ** R).
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
    applys (>>writes_agrees' hred); eauto.
    applys (>>inde_inv1 hred); eauto.
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
    applys (>>inde_inv2 H); eauto.
Qed.

Lemma rule_frame ntrd BS (tid : Fin.t ntrd) (C : cmd) (P Q R : assn) :
  CSL BS tid P C Q -> inde R (writes_var C) ->
  CSL BS tid (P ** R) C (Q ** R).
Proof.
  unfold CSL; intuition. simpl in *; eauto; intros. destruct H1 as (? & ? & ? & ? & ? & ?).
  cutrewrite (h = phplus_pheap H3); [|destruct h; apply pheap_eq; eauto].
  apply safe_frame; eauto.
Qed.

Section For_Vector_Notation.
  Import Vector.VectorNotations.
  Lemma rule_barrier0 ntrd (tid : Fin.t ntrd) BS :
    forall j, CSL BS tid (fst (BS j))[@tid] (Cbarrier j) (snd (BS j))[@tid].
  Proof.
    unfold CSL; intros j s ph Hsat n.
    destruct n; simpl; [eauto|]; repeat split.
    - inversion 1.
    - intros. inversion 1.
    - intros; inversion H1.
    - intros j' c' H; inverts H; subst.
      exists ph (emp_ph loc); repeat split; eauto; auto; [simpl; auto|..].
      apply disj_emp1.
      apply phplus_emp2.
      + intros phQ H0 hsatq.
        apply safe_skip; simpl.
        cutrewrite (phplus_pheap H0 = phQ); 
          [eauto | 
           destruct phQ; apply pheap_eq; rewrite phplus_comm; eauto using pdisj_empty2  ].
  Qed.
End For_Vector_Notation.

Lemma rule_barrier ntrd BS b (i : Fin.t ntrd) Res Res_pre Res_post Res_f P P_pre P_post Env Env_pre Env_post :
  Vector.nth (fst (BS b)) i = Assn Res_pre P_pre Env_pre ->
  Vector.nth (snd (BS b)) i = Assn Res_post P_post Env_post ->
  (Assn Res P Env |= Assn (Res_pre *** Res_f) P_pre Env_pre) ->
  CSL BS i
      (Assn Res P Env)
      (Cbarrier b)
      (Assn (Res_f *** Res_post) (P_pre /\ P_post) (Env_pre ++ Env_post)).
Proof.
  intros Heq1 Heq2 ?.
  eapply backward.
  { intros s h H'.
    apply H, Assn_split in H'; auto; eauto. }
  rewrite <- Heq1.
  eapply forwardR.
  eapply rule_frame; [| unfold inde; simpl; tauto ].
  eapply rule_barrier0.
  rewrite Heq2.
  intros; rewrite Assn_combine in *; eauto.
  revert H0; applys* Assn_imply; eauto using incl_refl.
  - unfold incl; intros; rewrite !in_app_iff in *; tauto.
  - intros; rewrite res_comm; eauto.
Qed.

Lemma safe_seq ntrd BS (tid : Fin.t ntrd) : forall (n : nat) (C C2 : cmd) (s : stack) (ph : pheap) (Q R : assn),
  safe_nt BS tid n C s ph Q ->
  (forall m s' ph', m <= n -> sat s' ph' Q -> safe_nt BS tid m C2 s' ph' R)%nat ->
  safe_nt BS tid n (C ;; C2) s ph R.
Proof.
  induction n; intros C C2 s ph Q R hsafe H; simpl; eauto.
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

Lemma rule_seq ntrd BS (tid : Fin.t ntrd) (C1 C2 : cmd) (P Q R : assn) :
  CSL BS tid P C1 Q -> CSL BS tid Q C2 R -> CSL BS tid P (C1 ;; C2) R.
Proof.
  unfold CSL. intuition; simpl.
  applys* safe_seq; unfold safe_nt; eauto.
Qed.

Lemma safe_while ntrd BS (tid : Fin.t ntrd) :
  forall P (B : bexp) C (OK: CSL BS tid (P ** (BEval_assn B true)) C P) s h (SAT_P: sat s h P) n,
    safe_nt BS tid n (Cwhile B C) s h (P ** (BEval_assn B false)).
Proof.
  intros; revert s h SAT_P. 
  assert (lenn : n <= n) by omega; revert lenn; generalize n at -2 as m.
  induction n; simpl in *; eauto; intros; intuition. (* desf; [by inv H2|]*)
  { destruct m; inversion lenn; simpl; eauto. }
  (*   inv H2; repeat eexists; eauto; simpl. *)
  (* destruct m; ins; intuition; desf; [by inv H5|]. *)
  (* inv H5; repeat eexists; eauto; simpls.*)
  inversion lenn; subst; [|apply IHn; eauto].
  simpl; repeat split; eauto; try congruence.
  intros ? ? ? ? Hc; inversion Hc.
  intros hF h0 c' ss' hdis htoh hred.
  inversion hred; subst.
  exists h0 h; repeat split; eauto; simpl.
  destruct n; simpl; repeat split; eauto; intros; try congruence.
  intros Hc; inversion Hc.
  inversion H1; subst; repeat eexists; eauto.
  - eapply safe_seq; simpl; eauto; intros. 
    apply OK.
    unfold sat; simpl.
    exists h (emp_ph loc); splits; eauto.
    apply disj_emp1.
    apply phplus_emp2.
  - eapply safe_skip; repeat split; simpl in *; eauto.
    unfold sat; simpl.
    exists h (emp_ph loc); splits; eauto.
    apply disj_emp1.
    apply phplus_emp2.
Qed.

Definition WhileI (I : assn) (b : bexp) (c : cmd) := (Cwhile b c).

Lemma rule_while ntrd BS (tid : Fin.t ntrd) P (B : bexp) C :
  CSL BS tid (P ** (BEval_assn B true)) C P ->
  CSL BS tid P (Cwhile B C) (P ** ((BEval_assn B false))).  
Proof.
  unfold CSL; intros; intuition; eapply safe_while; unfold CSL; eauto.
Qed.

Lemma rule_ex {T : Type} (P : T -> assn) Q ntrd bspec (tid : Fin.t ntrd) C:
  (forall x, CSL bspec tid (P x) C Q) ->
  CSL bspec tid (Ex x, P x) C Q.
Proof.
  intros H; simpl; intros s h [x Hsat] n; specialize (H x s h Hsat n); simpl in *.
  apply H.
Qed.

Notation nat_of_fin i := (proj1_sig (Fin.to_nat i)).
Notation Z_of_fin i := (Z.of_nat (nat_of_fin i)).

Section ParCSL.
  Require Vector.
  Import Vector.VectorNotations.

  Variable ntrd : nat.
  Hypothesis ntrd_gt_0 : (exists n', ntrd = S n').
  Variable bspec : nat -> (Vector.t assn ntrd * Vector.t assn ntrd)%type.
  Variable E : env.
  Hypothesis brr_lowassn : forall (i : nat),
                             (forall tid : Fin.t ntrd, low_assn E (fst (bspec i))[@tid]) /\
                             (forall tid : Fin.t ntrd, low_assn E (snd (bspec i))[@tid]).
  Hypothesis brr_wf : forall (i : nat) s h,
                        sat s h (Aistar_v (fst (bspec i))) ->
                        sat s h (Aistar_v (snd (bspec i))).
  Hypothesis bc_precise :
    forall i (tid : Fin.t ntrd), precise (fst (bspec i))[@tid] /\
                                 precise (snd (bspec i))[@tid].
  
  Lemma ew : env_wellformed bspec E.
  Proof.
    unfold env_wellformed, bwf, low_assn in *; split; try tauto; intros i. 
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
      | S n => fun ss heq => low_eq_repr1 _ _ heq
    end.
  
  Definition sat_k (ss : Vector.t stack ntrd) (h : pheap) (H : low_eq_l2 E ss) (Q : assn) :=
    match low_eq_repr _ _ H with
      | existT _ x P => sat x h Q
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
    apply (Relation_Operators.rt_trans _ _ _ ks2); eauto.
    apply Relation_Operators.rt_step; eauto.
  Qed.

  Lemma safe_mon BS (tid : Fin.t ntrd) :
    forall n C s h Q (OK: safe_nt BS tid n C s h Q) m (LEQ: m <= n),
      safe_nt BS tid m C s h Q.
  Proof.
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
      exists hleq; unfold sat_k. destruct (low_eq_repr _ _ hleq) as [st Hst].
      apply Hq, (aistar_eq (hs := (Vector.map2 (fun s h => (s, h)) ss hs))).
      + unfold get_hs. rewrite MyVector.map_map2, MyVector.map2_snd'; eauto.
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
        * set (hs' := Vector.replace hs i ph').
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
            rewrite !MyVector.replace_nth.
            destruct (MyVector.fin_eq_dec i tid) as [eq | neq]; [rewrite <-eq in *; clear eq|]; simpl; eauto.
            cutrewrite (fst ks[@tid] = cs[@tid]); [|unfold cs; erewrite Vector.nth_map; eauto].
            cutrewrite (snd ks[@tid] = ss[@tid]); [|unfold ss; erewrite Vector.nth_map; eauto].
            applys (>>safe_mon (hsafei tid)). 
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
                lets Hok : (access_ok_mono _ _ _ _ Hdisji' Haok); simpl in *.
                applys_eq Hok 1; destruct ph; apply pheap_eq; auto.
                lets Hok : (write_ok_mono _ _ _ _ Hdisji' Hwok); simpl in *.
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
                    sat ss[@tid] phP (pre_j bspec tid j) /\
                    (forall (phQ : pheap) (H : pdisj phQ ph'),
                       sat ss[@tid] phQ (post_j bspec tid j) ->
                       safe_nt bspec tid n (fst ss'[@tid]) ss[@tid] 
                               (phplus_pheap (h1:=phQ) (h2:=ph') H) Qs[@tid])) as hsafe0.
          { intros tid; destruct (hsafei tid) as [_ [_ [_ [_ [_ ?]]]]]; eauto. }
          destruct (MyVector.vec_exvec hsafe0) as [phPs Hp]; destruct (MyVector.vec_exvec Hp) as [phFs Hp']; clear Hp.
          assert (forall tid : Fin.t ntrd, pdisj phPs[@tid] phFs[@tid] /\ 
                                           phplus phPs[@tid] phFs[@tid] = hs[@tid]) as Hp''.
          { intros tid; destruct (Hp' tid) as [? [? _]]; eauto. }
          destruct (disj_eq_sub hdis Hp'') as [phP [phF [HeqP [HeqF [HdisPF HeqPF]]]]]; clear Hp''.
          assert (low_eq_l2 E ss) as leq2ss.
          { destruct h_for_bdiv as [? [? [? [? [? [Hred [? [? [? [? ?]]]]]]]]]].
            set (ws := MyVector.init (fun i => (j, fst ss'[@i]))).
            eapply (when_barrier (ws := ws) ew ntrd_gt_0  bc_precise Hred); eauto;
            unfold get_cs_k, get_ss_k; intros; repeat (erewrite Vector.nth_map; eauto).
            unfold cs in Hwait; unfold get_cs_k, ws. rewrite MyVector.init_spec; simpl.
            rewrite <-Hwait; erewrite Vector.nth_map; eauto. }
          destruct (low_eq_repr _ _ leq2ss) as [s Hs].
          assert (forall tid, sat s phPs[@tid] (pre_j bspec tid j)) as Hsati.
          { intros tid; destruct (Hp' tid) as [_ [_ [? _]]].
            destruct (brr_lowassn j) as [Hlow _]; specialize (Hlow tid).
            apply (Hlow ss[@tid] s _ (Hs tid)); eauto. }
          assert (sat s phP (Aistar_v (fst (bspec j)))) as Hsat.
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
          apply (IHn _ _ (MyVector.init (fun tid => phplus_pheap (HdisQF tid)))); eauto.
          { cutrewrite (ph = (phplus_pheap HdisPF)); 
            [|unfold htop in *; simpl in *; destruct ph; apply pheap_eq; eauto].
            apply (disj_eq_sum HdisPF HeqQ HeqF); intros tid; rewrite MyVector.init_spec; eauto. }
          { intros tid. erewrite !Vector.nth_map; eauto; rewrite MyVector.init_spec. 
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
      sat_k _ h leqks P ->
      forall n, safe_nk n ks h Q.

  Theorem rule_par (Ps : Vector.t assn ntrd) (Qs : Vector.t assn ntrd) 
          (P : assn) (c : cmd) (Q : assn) (ty : type):
    (P |= Aistar_v Ps) -> (Aistar_v Qs |= Q) ->
    (forall tid, low_assn E Ps[@tid]) -> 
    (forall tid, low_assn E Qs[@tid]) ->
    typing_cmd E c ty ->
    (forall tid : Fin.t ntrd, 
       CSL bspec tid 
           (Ps[@tid] ** (Assn Emp True (Var "tid" |-> Z_of_fin tid :: nil)))
           c 
           Qs[@tid]) ->
    CSLp P c Q.
  Proof.
    unfold CSL, CSLp, sat_k in *.
    intros PPs QsQ HlowP HlowQ Hty Hsafei ks h leqks Heqc Htid Hsat n.
    destruct (low_eq_repr _ _ leqks) as [s Hlows].
    apply PPs in Hsat.
    destruct (aistar_disj Hsat) as [prehs [Hdisj Hsati]].
    assert (forall tid, sat (Vector.map (fun s => snd s) ks)[@tid] prehs[@tid] Ps[@tid]) as
        Hsat'.
    { intros tid; (*simpl; erewrite Vector.nth_map; eauto.*)
      apply ((HlowP tid) (Vector.map (snd (B:=stack)) ks)[@tid] s _ (Hlows tid));
      eauto. }
    applys* (>>safe_par prehs Qs); eauto.
    - simpl in *; intros tid; specialize (Hsafei tid);
      specialize (Hsat' tid); erewrite !Vector.nth_map in *; 
      eauto.
      rewrite Heqc; apply Hsafei.
      erewrite Vector.nth_map in Hsat'; eauto.
      exists prehs[@tid] (emp_ph loc); simpl; splits; eauto.
      apply disj_emp1.
      apply phplus_emp2.
    - exists ks h prehs c ty; repeat split; eauto; simpl in *.
      + apply Relation_Operators.rt1n_refl. 
      (* + unfold get_cs_k; simpl; intros tid; erewrite Vector.nth_map; eauto. *)
      + intros tid; unfold safe_aux; exists Qs[@tid]; intros n'.
        (* erewrite Vector.nth_map; eauto; *) apply Hsafei.
        specialize (Hsat' tid); erewrite Vector.nth_map in Hsat'; eauto.
        exists prehs[@tid] (emp_ph loc); simpl; splits; eauto.
        apply disj_emp1.
        apply phplus_emp2.
  Qed.
End ParCSL.