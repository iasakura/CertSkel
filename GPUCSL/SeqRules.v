Require Import PeanoNat Arith Omega Psatz Classical SetoidClass Qcanon.
Require Import LibTactics.
Require Import PHeap Lang Top.CSLLemma Top.Bdiv.
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
    exists h (emp_ph loc); splits; eauto.
    apply disj_emp1.
    apply phplus_emp2.
  - eapply safe_skip; repeat split; simpl in *; eauto.
    exists h (emp_ph loc); splits; eauto.
    apply disj_emp1.
    apply phplus_emp2.
Qed.

Lemma rule_while ntrd BS (tid : Fin.t ntrd) P (B : bexp) C :
  CSL BS tid (P ** (BEval_assn B true)) C P ->
  CSL BS tid P (Cwhile B C) (P ** ((BEval_assn B false))).  
Proof.
  unfold CSL; intros; intuition; eapply safe_while; unfold CSL; eauto.
Qed.
