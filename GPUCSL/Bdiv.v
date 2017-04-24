Require Import QArith.
Require Import Qcanon.
Require Import Coq.Relations.Relations.
Require Import MyVector.
Require Import List.
Require Import PHeap.
Require Import Lang.
Require Import CSLLemma.
Set Implicit Arguments.
Unset Strict Implicit.


Import VectorNotations.

(*  Inductive assn : Set := 
    Aemp
  | Apure (b: bexp)
  | Aconj (p1: assn) (p2: assn)
  | Adisj (p1: assn) (p2: assn)
  | Astar (p1: assn) (p2: assn)
  | Apointsto (p : Qc) (e1 e2: exp)
  | Aex (pp: nat -> assn).*)
(*Definition assn := stack -> pheap -> Prop.
Notation Aemp := (fun (s : stack) (ph : pheap) => forall x, this ph x = None).
Notation Astar P1 P2 := (let tt := tt in (fun (s : stack) (ph : pheap) => 
  exists (ph1 ph2 : pheap), P1 s ph1 /\ P2 s ph2 /\ pdisj ph1 ph2 /\ phplus ph1 ph2 = ph)).
Notation Aconj P1 P2 := (fun (s : stack) (ph : pheap) => P1 s ph /\ P2 s ph).
Notation Adisj P1 P2 := (fun (s : stack) (ph : pheap) => P1 s ph \/ P2 s ph).
Notation Apure b := (fun (s : stack) (ph : pheap) => bdenot b s = true).
Notation Apointsto p e1 e2 := (fun (s : stack) (ph : pheap) =>
  forall x, this ph x = if Z.eq_dec x (edenot e1 s) then Some (p, edenot e2 s) else None).
Notation Aex P := (fun (s : stack) (h : pheap) => exists v, P v s h).
  Fixpoint sat (ss : pstate) (p : assn) : Prop := 
  match p with
    | Aemp => (forall x, this (snd ss) x = None) 
    | Apure b => bdenot b (fst ss)
    | Aconj p q => sat ss p /\ sat ss q
    | Adisj p q => sat ss p \/ sat ss q
    | Astar p q => exists (h1 h2 : pheap), sat (fst ss, h1) p /\ sat (fst ss, h2) q 
        /\ pdisj h1 h2 /\ phplus h1 h2 = snd ss
    | Apointsto q e1 e2 => forall x, this (snd ss) x = 
        (if Z.eq_dec x (edenot e1 (fst ss)) then Some (q, edenot e2 (fst ss)) else None)
    | Aex pp => exists v, sat ss (pp v)
  end.*)
(*Notation sat ss P := (P (fst ss) (snd ss)).*)
(*  Definition sat (ss : pstate) (P : assn) : Prop := P (fst ss) (snd ss).*)

(*  Lemma sat_istar_map_expand :
    forall (r : Z) (l : list Z) (ss : pstate) (f : Z -> assn) (IN: In r l)
           (DL: disjoint_list l),
      sat ss (Aistar (map f l))
      <-> exists (h1 h2 : pheap), sat (fst ss, h1) (f r)
            /\ sat (fst ss, h2) (Aistar (map f (removeAll Z.eq_dec l r)))
            /\ pdisj h1 h2 /\ phplus h1 h2 = snd ss.
  Proof.
    destruct ss as [s h]; ins.
    induction[h] l; ins. des. clarify.
    by destruct Z.eq_dec; clarify; rewrite removeAll_notin.
    destruct Z.eq_dec; simpls; clarify.
    split; intros; des; clarify; eauto.
    - eapply IHl in H0; eauto; desf. rewrite <-H5 in H1. pose proof (pdisj_padd H4 H1) as [H10 H13].
      rewrite <-H2.
      rewrite <- H5.
      do 2 eexists; split; eauto.
      split; [do 2 eexists; repeat split; eauto | ].
      assert (phplus h1 h3 = (Pheap (pdisj_is_pheap H13))) by done.
      rewrite H6; apply eq_refl. simpl.
      pose proof (pdisj_padd_comm H1 H4) as H14.
      split; [ eauto | auto using padd_left_comm].
    - rewrite <-H5 in H1; pose proof (pdisj_padd H4 H1) as [H10 H13]. 
      rewrite  <-H2, <-H5.
      pose proof (pdisj_padd_comm H1 H4); eauto.
      do 2 eexists; repeat split; [eauto | | | ].
      apply (IHl IN DL0); do 2 eexists.
      (repeat split); [eauto | eauto | eauto | ].
      cutrewrite (phplus h1 h3 = (Pheap (pdisj_is_pheap H13))); [ eauto | by done].
      simpl; eauto.
      simpl; auto using padd_left_comm.
  Qed.*)

(*
  Lemma precise_istar : forall (l : list assn), (forall x, In x l -> precise x) -> precise (Aistar l).
  Proof.
    induction l; ins; auto using precise_emp, precise_star.
  Qed.*)
Import VectorNotations.
Fixpoint Aistar_v (n : nat) (assns : Vector.t assn n) :=
  match assns with
    | [] => Emp_assn
    | (a :: assns) => a ** (Aistar_v assns)
  end.

Lemma aistar_disj (n : nat) (assns : Vector.t assn n) (s : stack) (h : pheap) :
  sat s h (Aistar_v assns) ->
  exists (hs : Vector.t pheap n), disj_eq hs h /\ 
                                  (forall tid : Fin.t n, sat s hs[@tid] assns[@tid]).
Proof.
  revert h; induction assns; intros h' hsat.
  - exists []; split; simpl in hsat.
           + apply emp_is_emp in hsat; rewrite hsat; constructor.
           + inversion 0.
           - simpl in hsat; destruct hsat as [h1 [h2 [H1 [H2 [hdis hplus]]]]].
             apply (IHassns h2) in H2; destruct H2 as [hs1 [heq1 hsat]].
             exists (h1 :: hs1); split.
             + assert (h' = Pheap (pdisj_is_pheap hdis)).
               { destruct h' as [h' ph']; apply pheap_eq; simpl in hplus; congruence. }
               rewrite H; econstructor; eauto.
             + intros tid; destruct (finvS tid) as [|[tid' ?]]; subst; simpl; eauto.
Qed.

Definition indeP (R : stack -> stack -> Prop) (P : assn) :=
  forall (s1 s2 : stack) (h : pheap), R s1 s2 -> (sat s1 h P <-> sat s2 h P).

Section Low_eq.
  Variable env : Lang.env.

  Fixpoint low_eq_l (n : nat) (s : stack) (sts : Vector.t stack n) :=
    match sts with
      | [] => True
      | x :: xs => low_eq env s x /\ low_eq_l s xs
    end.

  Fixpoint low_eq_l2 (ng : nat) (sts : Vector.t stack ng) :=
    match sts with
      | [] => True
      | x :: xs => low_eq_l x xs /\ low_eq_l2 xs
    end.
  Lemma loweq_l_leq (n : nat) (ss : Vector.t stack n) (s : stack) (leq : low_eq_l s ss) (i : Fin.t n) :
    low_eq env s ss[@i].
  Proof.
    induction ss as [| sh ss]; [inversion i|].
    destruct (finvS i) as [? | [i' ?]]; subst; simpl in *; try tauto.
    apply IHss; tauto.
  Qed.

  Lemma low_eq_sym (s1 s2 : stack) : low_eq env s1 s2 -> low_eq env s2 s1.
  Proof.
    unfold low_eq; intros H x Hl; specialize (H x Hl); congruence.
  Qed.

  Lemma loweq_l2_leq (n : nat) (ss : Vector.t stack n) (leq : low_eq_l2 ss) (i j : Fin.t n) :
    low_eq env (ss[@i]) (ss[@j]).
  Proof.
    induction ss as [| s ss]; [inversion i |].
    destruct (finvS i) as [? | [i' ?]], (finvS j) as [? | [j' ?]]; subst; try congruence; simpl in *.
    - apply loweq_l_leq; tauto.
    - apply low_eq_sym; apply loweq_l_leq; tauto.
    - apply IHss; tauto.
  Qed.

  Lemma leq_low_eq_l (n : nat) (s : stack) (ss : Vector.t stack n) : 
    (forall i : Fin.t n, low_eq env s ss[@i]) -> low_eq_l s ss.
  Proof.
    induction ss as [| s' ss]; intros H; simpl; eauto.
    split; [apply (H Fin.F1) | apply IHss; intros i; apply (H (Fin.FS i))].
  Qed.

  Lemma leq_low_eq_l2 (n : nat) (ss : Vector.t stack n) : (forall i j : Fin.t n, i <> j -> low_eq env ss[@i] ss[@j]) -> low_eq_l2 ss.
  Proof.
    intros H; induction ss as [| s ss]; simpl; eauto.
    split; [apply leq_low_eq_l; intros j; apply (H (Fin.F1) (Fin.FS j)) | ].
    intros H'; inversion H'.
    apply IHss; intros i j ineqj. eapply (H (Fin.FS i) (Fin.FS j)); inversion 1.
    apply inj_pair2 in H2; congruence.
  Qed.
End Low_eq.

Definition pkstate (n : nat) := (klist n * pheap)%type.

Reserved Notation "pks1 ==>kp pks2" (at level 40).
Inductive red_pk (ntrd : nat) : pkstate ntrd -> pkstate ntrd -> Prop :=
  redk_Seq : forall (ks : pkstate ntrd) (ss : klist ntrd) 
                    (c c' : cmd) (st st' : pstate) (s s' : stack) 
                    (h h' : pheap) (i : kidx ntrd),
             ks = (ss, h) ->
             ss[@i] = (c, s) ->
             c / st ==>p  c' / st' ->
             st = (s, h) ->
             st' = (s', h') ->
             red_pk ks (replace ss i (c', s'), h')
| redk_Barrier : forall (ks ks' : pkstate ntrd) (ss ss' : klist ntrd)
                   (h : pheap) (j : nat),
                 ks = (ss, h) ->
                 ks' = (ss', h) ->
                 (forall i : kidx ntrd,
                  exists (c : cmd) (s : stack) (c' : cmd),
                    ss[@i] = (c, s) /\
                    wait c = Some (j, c') /\ ss'[@i] = (c', s)) ->
                 red_pk ks ks'.
  
Definition red_pk_multi {n : nat} := clos_refl_trans_1n _ (@red_pk n).
Notation "pks1 ==>kp* pks2" := (red_pk_multi pks1 pks2) (at level 40).

Section Barrier.
  Variable ngroup : nat.
  Definition barrier_spec := nat -> (Vector.t assn ngroup * Vector.t assn ngroup)%type.
  Variable bspec : barrier_spec.
  Variable env : var -> type.
  Definition low_assn (P : assn) := indeP (fun s1 s2 => low_eq env s1 s2) P.

  (* fv(bspec) \cup V_hi = \empty *)
  Definition bwf := forall (j : nat),
    (forall tid : Fin.t ngroup, low_assn (fst (bspec j))[@tid]) /\
    (forall tid : Fin.t ngroup, low_assn (snd (bspec j))[@tid]). 

  Definition jth_pre (j : nat) := Aistar_v (fst (bspec j)).
  Definition jth_post (j : nat) := Aistar_v (snd (bspec j)).
  Definition env_wellformed := 
    bwf /\ forall (j : nat) s h, sat s h (jth_pre j) -> sat s h (jth_post j).
  Hypothesis env_wf : env_wellformed.

  Definition get_ss (n : nat) (sts : Vector.t pstate n) : Vector.t stack n := 
    Vector.map (fun st => fst st) sts.
  Definition get_hs (n : nat) (sts : Vector.t pstate n) : Vector.t pheap n := 
    Vector.map (fun st => snd st) sts.

  (* Hint Resolve emp_emp_ph. *)
  Lemma aistar_eq (n : nat) (s : stack) (assns : Vector.t assn n) (hs : Vector.t pstate n)
        (h : pheap) :
    disj_eq (get_hs hs) h -> (forall tid : Fin.t n, sat s (snd hs[@tid]) assns[@tid]) ->
    sat s h (Aistar_v assns).
  Proof.
    intros heq hsat.
    revert h heq assns hsat; induction hs; intros h' heq assns hsat.
    - assert (assns = []) by (apply (case0 (fun (v : t assn 0) => v = [])); eauto).
      simpl in heq; inversion heq.
      rewrite H; simpl; intros; simpl; unfold emp_h; eauto.
      unfold sat; simpl; eauto.
    - destruct (vinvS assns) as [a [assns' ha]]; subst.
      destruct h; simpl in heq.
      inversion heq; subst; apply inj_pair2 in H2; subst; simpl.
      repeat eexists; eauto. 
      + specialize (hsat Fin.F1); simpl in *; eauto.
      + apply IHhs; eauto.
        intros tid; specialize (hsat (Fin.FS tid)); eauto.
  Qed.

  Lemma sync_barrier (n : nat) (s : stack) (hs : Vector.t pstate n) (h : pheap)
        (prs pss : Vector.t assn n) (bf1 : forall tid : Fin.t n, low_assn prs[@tid])
        (bf2 : forall tid : Fin.t n, low_assn pss[@tid]) (heq : disj_eq (get_hs hs) h)
        (eq : forall s h, sat s h (Aistar_v prs) -> sat s h (Aistar_v pss))
        (hp : forall tid : Fin.t n, sat s (snd hs[@tid]) prs[@tid]) :
    exists (hs' : Vector.t pheap n),
      disj_eq hs' h /\ forall tid : Fin.t n, sat s hs'[@tid] pss[@tid].
  Proof.
    eapply (aistar_eq heq) in hp.
    apply eq in hp.
    apply aistar_disj in hp.
    intuition; repeat eexists; eauto.
  Qed.

  Lemma loweq_sat (n : nat) (s : stack) (sts : Vector.t pstate n)
        (low_eq : low_eq_l2 env (s :: get_ss sts)) (ps : Vector.t assn n) 
        (bf : forall tid : Fin.t n, low_assn ps[@tid]) :
    (forall tid : Fin.t n, sat (fst sts[@tid]) (snd sts[@tid]) ps[@tid]) <->
    (forall tid : Fin.t n, sat s (snd sts[@tid]) ps[@tid]).
  Proof.
    clear env_wf bspec.
    induction sts.
    - pose proof (vinv0 ps); subst; split; intros ? tid; inversion tid.
    - pose proof (vinvS ps) as [pr [prs hpr]]; subst.
(*      split; intros Hsat; inversion Hsat; subst; apply inj_pair2 in H1; apply inj_pair2 in H4; 
      subst; constructor.*)
      split; intros Hsat tid; destruct (finvS tid) as [| [tid' ?]]; subst; simpl.
      + destruct low_eq as [leq _]; simpl in leq; destruct leq as [leq _].
        specialize (bf Fin.F1); simpl in bf.
(*        inversion bf; subst. apply inj_pair2 in H1; subst.*)
        pose proof (bf s (fst h) (snd h) leq) as bw'; apply bw'; eauto.
        specialize (Hsat Fin.F1); simpl in Hsat. destruct h as [? ?]; eauto.
       + apply IHsts; eauto.
        * simpl in low_eq; split; tauto.
        * intros tid; specialize (bf (Fin.FS tid)); simpl in bf; eauto. 
        * intros tid; specialize (Hsat (Fin.FS tid)); eauto.
      + destruct low_eq as [leq _]; simpl in leq; destruct leq as [leq _].
        specialize (Hsat Fin.F1); specialize (bf Fin.F1); simpl in *.
        destruct h as [s' h]; apply (bf s s' h); eauto.
      + apply IHsts; eauto.
        * simpl in low_eq; split; try tauto.
        * intros tid; apply (bf (Fin.FS tid)).
        * intros tid; apply (Hsat (Fin.FS tid)).
  Qed.

  Lemma sync_barrier' (sts : Vector.t pstate ngroup) (j : nat) (h : pheap)
        (heq : disj_eq (get_hs sts) h) (ss_leq : low_eq_l2 env (get_ss sts))
        (hp : forall tid : Fin.t ngroup, sat (fst sts[@tid]) (snd sts[@tid]) (fst (bspec j))[@tid]) :
    exists (sts' : Vector.t pstate ngroup),
      disj_eq (get_hs sts') h /\ 
      get_ss sts' = get_ss sts /\
      (forall tid : Fin.t ngroup, sat (fst sts'[@tid]) (snd sts'[@tid]) (snd (bspec j))[@tid]).
  Proof.
    unfold env_wellformed, bwf in *; destruct env_wf as [bwf H]; clear env_wf.
    unfold jth_pre, jth_post in *; specialize (H j); (specialize (bwf j));
    destruct (bspec j) as [pres posts].
    remember (get_hs sts) as phs; remember (get_ss sts) as ss.
    generalize dependent ngroup. clear bspec ngroup.
    destruct sts; intros phs phs_eq heq ss ss_eq ss_leq pres posts hsat bwf bwf'; subst.
    - exists [].
      simpl; repeat split; eauto; inversion 0.
    - destruct (vinvS pres) as [pr [pres' Hpr]], (vinvS posts) as [ps [posts' Hps]]; subst.
      destruct bwf as [bwf1 bwf2]. (*inversion bwf1; subst; inversion bwf2; subst.
      apply inj_pair2 in H1; apply inj_pair2 in H4; subst.
      rename H2 into hpr, H5 into hps, H6 into hposts, H3 into hpres.*)
(*      inversion hsat; subst.
      apply inj_pair2 in H1; apply inj_pair2 in H4; subst.
      rename H3 into hsathd, H5 into hsattl.*)
      set (sts' := Vector.map (fun st => (fst h0, snd st)) (h0 :: sts)).
      assert (forall tid : Fin.t (S n), sat (fst sts'[@tid]) (snd sts'[@tid]) (pr :: pres')[@tid]).
      { intros tid; destruct (finvS tid) as [ |[tid' ?]], h0; [specialize (hsat Fin.F1); eauto|];
        subst; simpl; eauto; unfold sts'.
        erewrite nth_map; eauto.
        apply loweq_sat; simpl; eauto.
        intros tid; specialize (bwf1 (Fin.FS tid)); eauto.
        intros tid; specialize (hsat (Fin.FS tid)); eauto. }
(*      rewrite Heqsts' in H; apply ->forall2_map in H; simpl in H.*)
      unfold sts' in *. 
      assert (forall tid : Fin.t (S n), sat (fst h0) (snd (h0 :: sts)[@tid]) (pr :: pres')[@tid]).
      { intros tid; specialize (H tid); erewrite Vector.nth_map in H; eauto. }
      eapply sync_barrier in H0; eauto; clear H; rename H0 into H.
      destruct H as [hs' [heqq hsatq]].
      set (stq := (Vector.map2 (fun st h => (fst st, h)) (h0 :: sts) hs')).
      assert (forall tid : Fin.t (S n), sat (fst stq[@tid]) (snd stq[@tid]) (ps:: posts')[@tid]). 
      { unfold stq; apply <-(loweq_sat (n := S n) (s := fst h0)); eauto.
        - cutrewrite (Vector.map2 (fun x y => (fst h0, snd (fst x, y))) (h0 :: sts) hs' =
                      Vector.map (pair (fst h0)) hs'); [ | ].
          + intros tid; specialize (hsatq tid); erewrite Vector.nth_map2; eauto.
          + rewrite map2_map; eauto.
        - unfold get_ss; rewrite map_map2.
        rewrite map2_fst.
        simpl in ss_leq.
        simpl; repeat split; try tauto. }
      exists stq; repeat split; eauto; unfold stq.
      unfold get_hs; rewrite map_map2, map2_snd; eauto.
      unfold get_ss; rewrite map_map2, map2_fst; simpl; eauto.
  Qed.
End Barrier.

Section BarrierDivergenceFreedom.
  Variable ngroup : nat.
  Variable bspec : barrier_spec ngroup.
  Variable env : var -> type.
  Hypothesis env_wf : env_wellformed bspec env.
  Hypothesis ngroup_gt_0 : (exists ng', ngroup = S ng')%nat.
  Hypothesis bc_precise : 
    forall i (tid : Fin.t ngroup), precise ((fst (bspec i))[@tid]) /\
                                   precise ((snd (bspec i))[@tid]).
  Definition pre_j tid (j : nat) := Vector.nth (fst (bspec j)) tid.
  Definition post_j tid (j : nat) := Vector.nth (snd (bspec j)) tid.

  Fixpoint safe_nt (tid : Fin.t ngroup) (n : nat) (c : cmd) (s : stack) (ph : pheap) (q : assn) :=
    match n with
      | O => True
      | S n => 
        (c = Cskip -> sat s ph q) /\

        (forall (hf : pheap) (h : heap), 
           (pdisj ph hf) -> ptoheap (phplus ph hf) h -> ~aborts c (s, h)) /\

        access_ok c s ph /\ write_ok c s ph /\

        (forall (hF : pheap) (h : heap) (c' : cmd) (ss' : state),
           (pdisj ph hF) -> (ptoheap (phplus ph hF) h ->
           (c / (s, h) ==>s c' / ss') ->
           exists h' (ph' : pheap),
             snd ss' = h' /\ pdisj ph' hF /\ ptoheap (phplus ph' hF) h' /\
             safe_nt tid n c' (fst ss') ph' q)) /\
          
        (forall j c', wait c = Some (j, c') ->
           exists (phP ph' : pheap), 
             pdisj phP ph' /\ phplus phP ph' = ph /\ sat s phP (pre_j tid j) /\
             (forall (phQ : pheap) (H : pdisj phQ ph'), sat s phQ (post_j tid j) ->
                safe_nt tid n c' s (phplus_pheap H) q))
    end.
  Definition safe_t (tid : Fin.t ngroup) (c : cmd) (s : stack) (ph : pheap) (q : assn) := 
    forall (n : nat), safe_nt tid n c s ph q.
  
  Definition safe_aux (tid : Fin.t ngroup) (c : cmd) (s : stack) (ph : pheap) :=
    exists (q : assn), forall n, safe_nt tid n c s ph q.

  Definition Vt := Vector.t.
  Import Vector.VectorNotations.
  
  Definition get_ss_k {T : Type} (ks : klist ngroup * T) := Vector.map (fun x => snd x) (fst ks).
  Definition get_cs_k {T : Type} (ks : klist ngroup * T) := Vector.map (fun x => fst x) (fst ks).

  Lemma safe_inv' (tid : Fin.t ngroup) (c c' : cmd) (ps ps' : pstate) : 
    (safe_aux tid c (fst ps) (snd ps)) -> (c / ps ==>p* c' / ps') ->
    (safe_aux tid c' (fst ps') (snd ps')).
  Proof.
    intros hsafe hred.
    apply clos_rt1n_rt, clos_rt_rtn1 in hred.
    remember (c, ps) as cps;
      assert (c = fst cps) as Heq by (subst; eauto); rewrite Heq in hsafe; clear Heq;
      assert (ps = snd cps) as Heq by (subst; eauto); rewrite Heq in hsafe; clear Heq.
    remember (c', ps') as cps';
      assert (c' = fst cps') as Heq by (subst; eauto); rewrite Heq; clear Heq;
      assert (ps' = snd cps') as Heq by (subst; eauto); rewrite Heq; clear Heq.
    clear Heqcps Heqcps' c ps c' ps'. 
    induction hred as [|cps' cps'' hred]; eauto.
    destruct IHhred as [q IH]; exists q; intros n.
    destruct cps as [c ps], cps' as [c' ps'], cps'' as [c'' ps'']; simpl in *.
    destruct (IH (S n)) as [_ [_ [_ [_ [IH' _]]]]].
    unfold red_p_tup in hred; simpl in *.
    destruct hred as [c' c'' st' st'' ps' ps'' s' s'' ph' ph'' phF h' h'' ? ? ? ? _ _ 
                     hdis1 hptoh1 hred hdis2 hptoh2]; subst; simpl in *.
    destruct (IH' phF h' c'' (s'', h'') hdis1 hptoh1 hred) as 
        [? [ph''2 [? [? [? ?]]]]]; subst; simpl in *.
    assert (phplus ph''2 phF = phplus ph'' phF) as Heq1 by (eapply ptoD; eauto).
    assert (ph''2 = ph'') by (eapply padd_cancel2; eauto); subst; eauto.
  Qed.

  Lemma safe_inv (tid : Fin.t ngroup) (c c' : cmd) (s s' : stack) (ph ph' : pheap) :
    (safe_aux tid c s ph) -> (c / (s, ph) ==>p* c' / (s', ph')) ->
    (safe_aux tid c' s' ph').
  Proof.
    remember (s, ph) as ps;
      assert (s = fst ps) as Heq by (subst; eauto); rewrite Heq; clear Heq;
      assert (ph = snd ps) as Heq by (subst; eauto); rewrite Heq; clear Heq.
    remember (s', ph') as ps';
      assert (s' = fst ps') as Heq by (subst; eauto); rewrite Heq; clear Heq;
      assert (ph' = snd ps') as Heq by (subst; eauto); rewrite Heq; clear Heq.    
    apply safe_inv'.
  Qed.
  Require Import TLC.LibTactics.

  Lemma safe_red_sp (c1 c2 : cmd) (st1 st2 : state) (pst1 : pstate) (hF : pheap) (tid : Fin.t ngroup) n q:
    c1 / st1 ==>s c2 / st2 -> 
    fst st1 = fst pst1 ->
    safe_nt tid (S n) c1 (fst pst1) (snd pst1) q ->
    pdisj (snd pst1) hF -> ptoheap (phplus (snd pst1) hF) (snd st1) ->
    exists pst2, 
      c1 / pst1 ==>p c2 / pst2 /\
      fst pst2 = fst st2 /\
      pdisj (snd pst2) hF /\
      ptoheap (phplus (snd pst2) hF) (snd st2).
  Proof.
    intros red_s heq hsafe hdis1 hto1;
    destruct hsafe as [_ [ha [haok [hwok _]]]].
    destruct (red_s_safe red_s (eq_sym heq) hdis1 hto1 haok hwok) as [ph [? [? ?]]].
    eauto.
  Qed.

  Lemma safe_red_p (c1 c2 : cmd) (st1 st2 : pstate) (pst1 : pstate)
        (hF : pheap) (tid : Fin.t ngroup) (n : nat) (q : assn) :
    c1 / st1 ==>p c2 / st2 -> 
    fst st1 = fst pst1 ->
    safe_nt tid (S n) c1 (fst pst1) (snd pst1) q ->
    pdisj (snd pst1) hF -> phplus (snd pst1) hF = snd st1 ->
    exists pst2, 
      c1 / pst1 ==>p c2 / pst2 /\
      fst pst2 = fst st2 /\
      pdisj (snd pst2) hF /\
      phplus (snd pst2) hF = snd st2.
  Proof.
    intros red_s heq hsafe hdis1 hto1;
    destruct hsafe as [_ [ha [haok [hwok (Hstep & _)]]]].
    inversion red_s; subst; eauto; simpl in *.
    assert (Hdis : pdisj hF phF).
    { rewrite <-hto1 in H5; apply pdisjC, pdisjE2, pdisjC in H5; eauto. }
    forwards (h' & ph' & ? & ? & ? &  _): (Hstep (phplus_pheap Hdis) h1 c2 (s2, h2)); simpl; eauto.
    - apply pdisj_padd_expand; eauto.
      rewrite hto1; eauto.
    - rewrite <-padd_assoc; eauto.
      rewrite hto1; eauto.
      (* apply pdisj_padd_expand; eauto. *)
      (* rewrite hto1; eauto. *)
    - rewrite <-heq; eauto.
    - exists (s2, ph'); repeat split; simpl; eauto.
      eapply (@redp_ster c1 c2 (s1, h1) (s2, h2) pst1 (s2, ph') (fst pst1) s2 (snd pst1) ph' (phplus_pheap Hdis) h1 h2); eauto; try congruence.
      + destruct pst1; eauto.
      + rewrite <-hto1 in H5; apply pdisj_padd_expand; eauto.
      + simpl; rewrite <-padd_assoc; eauto.
        rewrite hto1; eauto.
        (* apply pdisj_padd_expand; eauto; rewrite hto1; eauto. *)
      + simpl; subst; eauto.
      + eauto using pdisjE1.
      + subst h'; lets Heq: (>> (@ptoD) H1 H9).
        rewrite <-padd_assoc in Heq; eauto.
        assert (pdisj ph' hF) by eauto using pdisjE1.
        assert (phplus ph' hF = phplus_pheap H) by eauto.
        rewrite H2 in Heq; apply padd_cancel2 in Heq; simpl in *; subst; eauto.
        apply pdisj_padd_expand; eauto.
  Qed.

  Lemma red_p_step (c1 c2 c3 : cmd) (pst1 pst2 pst3 : pstate) : 
    c1 / pst1 ==>p* c2 / pst2 -> c2 / pst2 ==>p c3 / pst3 -> c1 / pst1 ==>p* c3 / pst3.
  Proof.
    unfold multi_red_p, multi_red_p_tup, red_p_tup.
    intros H1 H2.
    apply (clos_rt1n_step _ (fun st1 st2 => fst st1 / snd st1 ==>p  fst st2 / snd st2)
           (c2, pst2) (c3, pst3)) in H2.
    apply clos_rt1n_rt in H1. apply clos_rt1n_rt in H2. apply clos_rt_rt1n.
    eapply rt_trans; eauto.
  Qed.

  Lemma step_inv (ks1 ks2 : pkstate ngroup) (red_k : (ks1 ==>kp* ks2))
        (hs1 : Vector.t pheap ngroup) (ss1 : Vector.t stack ngroup) (c : cmd) :
    (exists (ty : type), typing_cmd env c ty) ->
    disj_eq hs1 (snd ks1) ->
    ss1 = get_ss_k ks1 -> low_eq_l2 env ss1 ->
    (forall tid : Fin.t ngroup, (get_cs_k ks1)[@tid] = c) -> 
    (forall tid : Fin.t ngroup, safe_aux tid c (ss1[@tid]) (hs1[@tid])) ->
    exists (pss' : Vector.t pstate ngroup) (pss2 : Vector.t pstate ngroup) (c' : cmd) 
           (cs : Vector.t cmd ngroup) (h' : pheap), 
      disj_eq (get_hs pss') h' /\  low_eq_l2 env (get_ss pss') /\
      disj_eq (get_hs pss2) (snd ks2) /\ 
      (exists (ty : type), typing_cmd env c' ty) /\
      (forall tid : Fin.t ngroup, 
         cs[@tid] = (get_cs_k ks2)[@tid] /\
         (get_ss pss2)[@tid] = (get_ss_k ks2)[@tid] /\
         safe_aux tid c' (fst pss'[@tid]) (snd pss'[@tid]) /\
         c' / (pss'[@tid]) ==>p* cs[@tid] / pss2[@tid]).
  Proof.
    intros hty hdis1 heq hloweq1 hc hsafe.
    apply clos_rt1n_rt, clos_rt_rtn1 in red_k.
    induction red_k as [| ks' ks2]. 
    Hint Unfold low_eq_l2 get_hs get_ss.
    Hint Rewrite map_map2 map2_fst' map2_snd'.
    - remember (Vector.map2 (fun s h => (s, h)) ss1 hs1) as pss'.
      exists pss' pss' c (Vector.const c ngroup) (snd ks1).
      subst; repeat split; autounfold; autorewrite with core; eauto.
      + rewrite const_nth; pose proof (hc tid); eauto.
      + assert ((Vector.map2 (fun (s : stack) h => (s, h)) (get_ss_k ks1) hs1)[@tid] = 
                ((get_ss_k ks1)[@tid], hs1[@tid])); erewrite nth_map2; eauto.
      + rewrite const_nth; econstructor.
    - generalize dependent ks'. intros ks' H; case H.
      { intros ? ss c1 c2 st1 st2 s1 s2 h1 h2 tid ? sstid red' ? ? red_k IHred_k; subst.
        destruct IHred_k as [pss' [pss2 [c' [cs [h' [H1 [H2 [H3 [H4 H5]]]]]]]]]; simpl in *.
        destruct (H5 tid) as [Hi1 [Hi2 [Hi3 Hi4]]].
        assert (cs[@tid] = c1) as Hceq.
        { unfold get_cs_k in Hi1; simpl in Hi1. rewrite Hi1.
          rewrite (Vector.nth_map _ _ tid tid); eauto; rewrite sstid; eauto. }
        assert (fst pss2[@tid] = s1) as Hseq.
        { unfold get_ss_k, get_ss in Hi2; simpl in Hi2.
          repeat rewrite (Vector.nth_map _ _ tid tid eq_refl) in Hi2. 
          rewrite sstid in Hi2; eauto; simpl in Hi2. }
        rewrite <-Hceq,<-Hseq in red'.
        pose proof (safe_inv' Hi3 Hi4) as hsafei.
        destruct (disj_tid tid H3) as [h_ni [eqni [h_ntid hnip]]].
        assert ((get_hs pss2)[@tid] = snd pss2[@tid]) as H'
          by (unfold get_hs; erewrite Vector.nth_map; eauto).
          rewrite H' in h_ntid, hnip; clear H'.
        (* assert ((phplus (snd pss2[@tid]) h_ni) = h1) as hto  *)
        (*   by (rewrite hnip; apply ptoheap_htop). *)
        destruct hsafei as [? hsafei].
        lets (pst2 & seq & tred & tdisj & tto): (>> safe_red_p red' (hsafei 1) h_ntid); eauto.
        destruct (disj_upd eqni h_ntid) as [hq [hdeq_q  heq_q]].
        exists pss' (replace pss2 tid pst2) c' (replace cs tid c2) h'.
        repeat split; eauto.
        + (* rewrite heq_q in tto; simpl in tto. *)
          assert (get_hs (replace pss2 tid pss2[@tid]) = replace (get_hs pss2) tid (snd pss2[@tid])) as Ht.
          { apply eq_nth_iff; intros p1 p2 peq; rewrite peq. 
            unfold get_hs; erewrite Vector.nth_map; eauto.
            repeat rewrite replace_nth. destruct (fin_eq_dec tid p2); eauto.
            erewrite Vector.nth_map; eauto. }
          lets (h2' & Hdeq2' & Heq): (>>(@disj_upd) eqni tdisj).
          simpl in *.
          cutrewrite (h2 = h2'); eauto.
          unfold get_hs in *.
          rewrite map_replace; eauto.
          destruct h2, h2'; apply pheap_eq; simpl in *; congruence.
        + unfold get_cs_k; simpl; erewrite Vector.nth_map, !replace_nth; eauto.
          destruct (fin_eq_dec tid tid0); simpl; eauto.
          destruct (H5 tid0) as [Hc _]; unfold get_cs_k in Hc; erewrite Vector.nth_map in Hc; eauto.
        + unfold get_ss, get_ss_k; erewrite !Vector.nth_map; eauto; simpl; 
          rewrite !replace_nth; destruct (fin_eq_dec tid tid0); eauto.
          destruct (H5 tid0) as [_ [Ht _]].
          unfold get_ss, get_ss_k in Ht; erewrite !Vector.nth_map in Ht; eauto; simpl. 
        + destruct (H5 tid0) as [_ [_ [Ht _]]]; eauto.
        + destruct (H5 tid0) as [_ [_ [_ Ht]]]; eauto.
          rewrite !replace_nth; destruct (fin_eq_dec tid tid0); subst; eauto.
          eapply red_p_step; eauto. }
      { clear ks' ks2 H.
        intros ? ? ss' ss2 h j ? ? Hbrr Hmulred IH; subst; simpl in *.
        destruct IH as [pss' [pss2 [c' [cs [h' [hdeq' [hseq' [hdeq2 [hty' H]]]]]]]]].
        assert (forall tid : Fin.t ngroup, safe_aux tid c' (fst pss'[@tid]) (snd pss'[@tid])) 
          as hsafe' by (intros tid; destruct (H tid) as [? [? [? ?]]]; tauto).
        assert (forall tid : Fin.t ngroup, safe_aux tid cs[@tid] (fst pss2[@tid]) (snd pss2[@tid])) 
          as hsafe2.
        { intros; specialize (hsafe' tid); destruct (H tid) as [? [? [? ?]]], pss'[@tid], pss2[@tid];
          simpl in *; apply (safe_inv hsafe'); eauto. }
        assert (forall tid : Fin.t ngroup, ss'[@tid] = (cs[@tid], fst pss2[@tid])) as heqss'.
        { intros tid; destruct (H tid) as [H1 [H2 [_ _]]]; unfold get_ss, get_ss_k, get_cs_k in *;
          simpl in *.
          do 1 erewrite (Vector.nth_map) in H1; do 2 erewrite (Vector.nth_map) in H2; eauto;
          destruct ss'[@tid]; f_equal; eauto. }
        assert (forall tid : Fin.t ngroup, wait cs[@tid] = Some (j, fst ss2[@tid])) as cswait.
        { intros tid; destruct (Hbrr tid) as [cp [s [cq' [H1 [H2 H3]]]]]. specialize (heqss' tid).
          rewrite heqss' in H1; destruct ss2[@tid]; inversion H1; inversion H2; inversion H3; 
          subst; eauto. }
        assert (forall tid, exists (phP phF : pheap), 
                  pdisj phP phF /\ phplus phP phF = snd pss2[@tid] /\ 
                  sat (fst pss2[@tid]) phP (pre_j tid j)) as hpre.
        { intros tid; specialize (hsafe2 tid); destruct hsafe2 as [q hsafe2];
          specialize (hsafe2 1%nat); destruct hsafe2 as [_ [_ [_ [_ [_ hsafe2]]]]];
          specialize (hsafe2 j (fst ss2[@tid]) (cswait tid));
          destruct hsafe2 as [phP [phF [? [? [? _]]]]]; eexists; eauto. }
        assert (exists (phPs phFs : t pheap ngroup), forall tid : Fin.t ngroup,
                  pdisj phPs[@tid] phFs[@tid] /\
                  phplus phPs[@tid] phFs[@tid] = snd pss2[@tid] /\
                  sat (fst pss2[@tid]) phPs[@tid] (pre_j tid j)) as [phPs [phFs Hpre]].
        { destruct (@vec_exvec pheap ngroup (fun tid phP => exists (phF : pheap), pdisj phP phF /\
           phplus phP phF = snd pss2[@tid] /\
           sat (fst pss2[@tid]) phP (pre_j tid j)) hpre) as [phPs Hp].
          destruct (@vec_exvec pheap ngroup (fun tid phF => pdisj phPs[@tid] phF /\
            phplus phPs[@tid] phF = snd pss2[@tid] /\
            sat (fst pss2[@tid]) phPs[@tid] (pre_j tid j)) Hp) as [phFs Hp'].
          eexists; eauto. }
        assert (forall tid : Fin.t ngroup, 
                  pdisj phPs[@tid] phFs[@tid] /\ phplus phPs[@tid] phFs[@tid] = (get_hs pss2)[@tid]) 
        as H'.
        { intros tid; specialize (Hpre tid); split; try tauto.
          unfold get_hs; erewrite Vector.nth_map; eauto; intuition; tauto. }
        destruct (disj_eq_sub hdeq2 H') as [hP [hF [HhP [HhF [hdispf hppf]]]]].
        destruct hty' as [ty hty'].
        set (psspre := Vector.map2 (fun x y => (fst x, y)) pss2 phPs).
        assert (forall tid1 tid2 : Fin.t ngroup, tid1 <> tid2 -> st_compat env pss'[@tid1] pss'[@tid2]) as pss'compat.
        { unfold st_compat; split; eauto;
          rewrite <-(Vector.nth_map _ _ tid1 tid1); eauto;
          rewrite <-(Vector.nth_map _ _ tid2 tid2); eauto.
          - apply loweq_l2_leq; eauto.
          - eapply disjeq_disj; eauto. }
        assert (low_eq_l2 env (get_ss pss2)).
        { apply leq_low_eq_l2; intros tid1 tid2 hneq.
          unfold get_ss, psspre; erewrite !Vector.nth_map; eauto.
          cut (j = j /\ fst ss2[@tid1] = fst ss2[@tid2] /\ st_compat env pss2[@tid1] pss2[@tid2]); 
            unfold st_compat; try tauto.
          destruct (H tid1) as [_ [_ [_ hred1]]], (H tid2) as [_ [_ [_ hred2]]].
          eapply (fun x => non_interference_p2 hty' x hred1 hred2 (cswait tid1) (cswait tid2)).
          apply pss'compat; eauto. }
        assert (exists (phQs : Vector.t pheap ngroup), 
                  disj_eq phQs hP /\ 
                  forall tid : Fin.t ngroup, 
                    pdisj phQs[@tid] phFs[@tid] /\ 
                    sat (fst pss2[@tid]) phQs[@tid] (post_j tid j)) as hq.
        { assert (disj_eq (get_hs psspre) (hP)) as disj1 by
          (cutrewrite (get_hs psspre = phPs); [eauto|
             (apply Vector.eq_nth_iff; intros i1 i2 ?; subst; unfold get_hs, psspre;
              erewrite Vector.nth_map; eauto; erewrite Vector.nth_map2; simpl; eauto)]).
          assert (forall tid : Fin.t ngroup, sat (fst psspre[@tid]) (snd psspre[@tid]) (fst (bspec j))[@tid]).
          { intros tid; destruct (Hpre tid) as [? [? ?]].
            unfold psspre; erewrite Vector.nth_map2; eauto. } 
          assert (get_ss psspre = get_ss pss2).
          { apply Vector.eq_nth_iff; intros tid1 tid2 ?; subst.
            unfold get_ss, psspre; erewrite !Vector.nth_map; eauto; erewrite Vector.nth_map2; 
            simpl; eauto. }
          rewrite <-H2 in H0; clear H2.
          destruct (sync_barrier' env_wf disj1 H0 H1) as [psspos [dis2 [heq hsat']]].
          exists (Vector.map (fun st => snd st) psspos); repeat split; eauto.
          - apply (disj_eq_each_disj dis2 HhF); eauto.
          - specialize (hsat' tid); erewrite Vector.nth_map; eauto.
            unfold get_ss,psspre in heq.
            assert (forall i, (Vector.map (fun x => fst x) psspos)[@i] = 
                              (Vector.map (fun x => fst x) pss2)[@i]).
            { intros i; erewrite heq, !Vector.nth_map, Vector.nth_map2; simpl; eauto. }
            cutrewrite (fst pss2[@tid] = fst psspos[@tid]); 
              [|(specialize (H2 tid); erewrite !Vector.nth_map in H2; eauto)].
            cutrewrite (psspos[@tid] = (fst psspos[@tid], snd psspos[@tid])) in hsat';
              [eauto |(destruct (psspos[@tid])); eauto]. }
        assert (forall tid1 tid2 : Fin.t ngroup, fst ss2[@tid1] = fst ss2[@tid2]).
        { intros tid1 tid2; 
          destruct (H tid1) as [_ [_ [_ hred1]]], (H tid2) as [_ [_ [_ hred2]]].
          destruct (fin_eq_dec tid1 tid2); subst; eauto.
          cut (j = j /\ fst ss2[@tid1] = fst ss2[@tid2] /\ st_compat env pss2[@tid1] pss2[@tid2]);
          [tauto | 
           eapply (non_interference_p2 hty' (pss'compat tid1 tid2 n) 
                         hred1 hred2 (cswait tid1) (cswait tid2)) ]. }
        destruct (vec_eq_ex Cskip H1) as [c'' Hc].
        destruct hq as [phQs [hdisq hid]].
        assert (forall tid, pdisj phQs[@tid] phFs[@tid]) as hiddis by (intros tid; specialize (hid tid); tauto).
        set (phs := init (fun (tid : Fin.t ngroup) => phplus_pheap (hiddis tid))).
        set (pssq := Vector.map2 (fun x y => (fst x, y)) pss2 phs).
        exists pssq pssq c'' (Vector.const c'' ngroup) h.
        Hint Unfold low_eq_l2 get_hs get_ss.
        Hint Rewrite map_map2 map2_fst' map2_snd' init_spec.
        unfold pssq, phs.
        repeat split; eauto.
        - autounfold; autorewrite with core.
          cutrewrite (h = phplus_pheap hdispf); [| destruct h; apply pheap_eq; eauto].
          apply (disj_eq_sum hdispf hdisq HhF).
          intros i; rewrite init_spec; eauto.
        - unfold get_ss.
          cutrewrite (Vector.map (fun x => fst x)
                    (Vector.map2 (fun x y => (fst x, y)) pss2
                       (init
                          (fun tid : Fin.t ngroup =>
                             phplus_pheap (h1:=phQs[@tid]) (h2:=phFs[@tid]) (hiddis tid)))) = 
          get_ss pss2); [eauto|].
          unfold get_ss; apply Vector.eq_nth_iff; intros i1 i2 ?; subst.
          erewrite !Vector.nth_map; eauto; erewrite Vector.nth_map2; eauto; rewrite init_spec; eauto.
        - autounfold; autorewrite with core; 
          cutrewrite (h = phplus_pheap hdispf); [| destruct h; apply pheap_eq; eauto].
          apply (disj_eq_sum hdispf hdisq HhF).
          intros i; rewrite init_spec; eauto.
        - assert (forall tid, c' / pss'[@tid] || Some (j, fst ss2[@tid]) / pss2[@tid]).
          { intros tid; specialize (H tid); destruct H as (_ & _ & _ & H).
            eapply eval_mred2; eauto. }
          assert (forall tid, exists ty0, typing_cmd env (fst ss2[@tid]) ty0) as Hty.
          { intros tid; eapply preservation_big; eauto. }
          destruct ngroup_gt_0 as [ng' Hr]; set (tid := Fin.F1 (n := ng')); rewrite<- Hr in tid.
          specialize (Hty tid); rewrite Hc in Hty; eauto.
        - unfold get_cs_k; erewrite Vector.nth_map; eauto; rewrite const_nth; simpl; congruence.
        - unfold get_ss, get_ss_k;
          erewrite !Vector.nth_map; eauto; erewrite Vector.nth_map2; eauto; rewrite init_spec; simpl.
          destruct (Hbrr tid) as [? [? [? [? [? ?]]]]]; subst.
          specialize (heqss' tid); destruct ss'[@tid], ss2[@tid].
          repeat match goal with [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H end; subst; simpl; eauto.
        - erewrite Vector.nth_map2; eauto; rewrite init_spec; simpl; 
          destruct (hsafe2 tid) as [q hsafen].
          unfold safe_aux; exists q; intros n; specialize (hsafen (S n)); simpl in hsafen.
          destruct hsafen as [_ [_ [_ [_ [_ hsafeb]]]]].
          destruct (hsafeb j (fst ss2[@tid]) (cswait tid)) as [phP [phF [dispf [hplus [hsat hres]]]]].
          assert (phF = phFs[@tid]).
          destruct (bc_precise j tid) as [Hprec _]; unfold precise in Hprec.
          destruct (H' tid) as [Hdis Heq], (Hpre tid) as [_ [_ Hsati]].
          assert (phplus phP phF = phplus phPs[@tid] phFs[@tid]) as heq by
              (rewrite hplus, Heq; unfold get_hs; erewrite Vector.nth_map; eauto).
          assert (phP = phPs[@tid]) as eqF by apply (Hprec _ _ _ _ _ hsat Hsati dispf Hdis heq).
          rewrite eqF in heq; apply (padd_cancel heq); eauto; rewrite <-eqF; eauto.
          assert (pdisj phQs[@tid] phF) as hdQiF by (rewrite H2; eauto).
          specialize (hres phQs[@tid] hdQiF (proj2 (hid tid))).
          cutrewrite (phplus_pheap (hiddis tid) = phplus_pheap hdQiF); 
            [|apply pheap_eq; f_equal; congruence].
          rewrite <-(Hc tid); apply hres.
        - rewrite const_nth; constructor. }
  Qed.

  Definition diverge (c1 c2 : option (nat * cmd)) :=
    match c1, c2 with
      | Some (j1, c1'), Some (j2, c2') => j1 <> j2
      | _, _ => False
    end.

  Definition bdiv (ks : pkstate ngroup) :=
    exists (tid1 tid2 : Fin.t ngroup), 
      let c1 := (get_cs_k ks)[@tid1] in
      let c2 := (get_cs_k ks)[@tid2] in
      (exists j1 c1', wait c1 = Some (j1, c1') /\ c2 = Cskip) \/ 
      (exists j2 c2', c1 = Cskip                /\ wait c2 = Some (j2, c2')) \/ 
      diverge (wait c1) (wait c2).

  Lemma when_stop (ks1 ks2 : pkstate ngroup) (red_k : (ks1 ==>kp* ks2))
        (hs1 : Vector.t pheap ngroup) (ss1 : Vector.t stack ngroup) (c : cmd) :
    (exists (ty : type), typing_cmd env c ty) ->
    disj_eq hs1 ((snd ks1)) ->
    ss1 = get_ss_k ks1 -> low_eq_l2 env ss1 ->
    (forall tid : Fin.t ngroup, (get_cs_k ks1)[@tid] = c) -> 
    (forall tid : Fin.t ngroup, safe_aux tid c (ss1[@tid]) (hs1[@tid])) ->
    (forall tid : Fin.t ngroup, (get_cs_k ks2)[@tid] = Cskip) ->
    low_eq_l2 env (get_ss_k ks2).
  Proof.
    intros ? ? ? ? ? ? Hskip; eapply step_inv in red_k; eauto.
    destruct red_k as [pss' [pss2 [c' [cs [h' [hdis1 [lleq [hdis2 [hty Htid]]]]]]]]].
    assert (forall tid, cs[@tid] = SKIP) as Hskip' by
        (intros tid; destruct (Htid tid) as [Heq _]; specialize (Hskip tid); congruence).
    assert (forall tid1 tid2 : Fin.t ngroup, 
              tid1 <> tid2 -> st_compat env pss2[@tid1] pss2[@tid2]) as Hcomp.
    { intros tid1 tid2 hneq; destruct (Htid tid1) as [_ [_ [_ Hred1]]], 
                                      (Htid tid2) as [_ [_ [_ Hred2]]].
      rewrite Hskip' in Hred1, Hred2.
      destruct hty as [ty hty].
      assert (st_compat env pss'[@tid1] pss'[@tid2]) as hcomp1.
      { unfold st_compat; split. 
        - rewrite <-(Vector.nth_map _ _ tid1 tid1), 
                  <-(Vector.nth_map _ _ tid2 tid2); eauto; apply loweq_l2_leq.
          unfold get_ss in lleq; eauto.
        - rewrite <-(Vector.nth_map _ _ tid1 tid1), 
                  <-(Vector.nth_map _ _ tid2 tid2); eauto; eapply disjeq_disj; eauto. }
      eapply (non_interference_p1 hty hcomp1 Hred1 Hred2). }
    assert (forall tid1 tid2 : Fin.t ngroup, 
              tid1 <> tid2 -> low_eq env (fst pss2[@tid1]) (fst pss2[@tid2])) as hleq by
        (intros tid1 tid2; specialize (Hcomp tid1 tid2); unfold st_compat in Hcomp; tauto).
    apply leq_low_eq_l2; intros tid1 tid2 hneq; specialize (hleq tid1 tid2 hneq).
    destruct (Htid tid1) as [_ [heq1 _]], (Htid tid2) as [_ [heq2 _]];
      rewrite <-heq1, <-heq2; unfold get_ss; erewrite !Vector.nth_map; eauto.
  Qed.

  Lemma when_barrier (ks1 ks2 : pkstate ngroup) (red_k : (ks1 ==>kp* ks2))
        (hs1 : Vector.t pheap ngroup) (ss1 : Vector.t stack ngroup) (c : cmd) 
        (ws : Vector.t (nat * cmd) ngroup):
    (exists (ty : type), typing_cmd env c ty) ->
    disj_eq hs1 (snd ks1) ->
    ss1 = get_ss_k ks1 -> low_eq_l2 env ss1 ->
    (forall tid : Fin.t ngroup, (get_cs_k ks1)[@tid] = c) -> 
    (forall tid : Fin.t ngroup, safe_aux tid c (ss1[@tid]) (hs1[@tid])) ->
    (forall tid : Fin.t ngroup, wait ((get_cs_k ks2)[@tid]) = Some ws[@tid]) ->
    low_eq_l2 env (get_ss_k ks2) /\ exists b, (forall tid, fst ws[@tid] = b).
  Proof.
    intros ? ? ? ? ? ? Hbrr; eapply step_inv in red_k; eauto.
    destruct red_k as [pss' [pss2 [c' [cs [h' [hdis1 [lleq [hdis2 [hty Htid]]]]]]]]].
    assert (forall tid, wait cs[@tid] = Some ws[@tid]) as Hskip' by
        (intros tid; destruct (Htid tid) as [Heq _]; specialize (Hbrr tid); congruence).
    assert (forall tid1 tid2 : Fin.t ngroup, 
              tid1 <> tid2 -> ws[@tid1] = ws[@tid2] /\
                              st_compat env pss2[@tid1] pss2[@tid2]) as Hcomp.
    { intros tid1 tid2 hneq; destruct (Htid tid1) as [_ [_ [_ Hred1]]], 
                                      (Htid tid2) as [_ [_ [_ Hred2]]].
      destruct hty as [ty hty].
      assert (st_compat env pss'[@tid1] pss'[@tid2]) as hcomp1.
      { unfold st_compat; split. 
        - rewrite <-(Vector.nth_map _ _ tid1 tid1), 
                  <-(Vector.nth_map _ _ tid2 tid2); eauto; apply loweq_l2_leq.
          unfold get_ss in lleq; eauto.
        - rewrite <-(Vector.nth_map _ _ tid1 tid1), 
                  <-(Vector.nth_map _ _ tid2 tid2); eauto; eapply disjeq_disj; eauto. }
      pose proof (Hskip' tid1); pose proof (Hskip' tid2).
      destruct ws[@tid1] as [j1 c1], ws[@tid2] as [j2 c2].
      destruct (non_interference_p2 hty hcomp1 Hred1 Hred2 H5 H6) as [? [? ?]];
      split; eauto; congruence. }
    assert (forall tid1 tid2 : Fin.t ngroup, 
              tid1 <> tid2 -> low_eq env (fst pss2[@tid1]) (fst pss2[@tid2])) as hleq by
        (intros tid1 tid2; specialize (Hcomp tid1 tid2); unfold st_compat in Hcomp; tauto).
    split.
    - apply leq_low_eq_l2; intros tid1 tid2 hneq; specialize (hleq tid1 tid2 hneq).
      destruct (Htid tid1) as [_ [heq1 _]], (Htid tid2) as [_ [heq2 _]];
        rewrite <-heq1, <-heq2; unfold get_ss; erewrite !Vector.nth_map; eauto.
    - assert (exists (b : nat), forall tid : Fin.t ngroup, (Vector.map (fst (B:=cmd)) ws) [@tid] = b)
        as [b H'].
      { apply (vector_eq2_ex 0%nat); intros i j neq.
        destruct  (Hcomp i j neq) as [? ?]; 
          rewrite (Vector.nth_map _ _ i i), (Vector.nth_map _ _ j j); congruence. }
      exists b. intros tid; specialize (H' tid); erewrite Vector.nth_map in H'; eauto.
  Qed.
  
  Theorem barrier_divergence_freedom  (ks1 ks2 : pkstate ngroup) (red_k : (ks1 ==>kp* ks2))
          (hs1 : Vector.t pheap ngroup) (ss1 : Vector.t stack ngroup) (c : cmd) :
    (exists (ty : type), typing_cmd env c ty) ->
    disj_eq hs1 (snd ks1) ->
    ss1 = get_ss_k ks1 -> low_eq_l2 env ss1 ->
    (forall tid : Fin.t ngroup, (get_cs_k ks1)[@tid] = c) -> 
    (forall tid : Fin.t ngroup, safe_aux tid c (ss1[@tid]) (hs1[@tid])) ->
    ~(bdiv ks2).
  Proof.
    intros; eapply step_inv in red_k; eauto.
    destruct red_k as [pss' [pss2 [c' [cs [h' [hdis1 [hleq1 [hdis2 [hty hid]]]]]]]]].
    intros [tid1 [tid2 hdiv]]; pose proof (hid tid1) as [hcs1 [hss1 [hsafe1 hred1]]]; 
    pose proof (hid tid2) as [hcs2 [hss2 [hsafe2 hred2]]].
    rewrite <-hcs1, <-hcs2 in hdiv.
    destruct (fin_eq_dec tid1 tid2) as [? | hneq]; subst.
    - simpl in hdiv; destruct hdiv as [ [? [? [hw1 hw2]]] | [[? [? [hw2 hw1]]] | hdiv]];
      (rewrite hw2 in hw1; simpl in hw1; inversion hw1) ||
      (destruct (wait cs[@tid2]) as [[? ?]|]; eauto).
    - assert (st_compat env pss'[@tid1] pss'[@tid2]) as hcompat.
      { unfold st_compat; split.
        - pose proof (loweq_l2_leq hleq1 tid1 tid2) as hleq; unfold get_ss in hleq;
          erewrite !Vector.nth_map in hleq; eauto.
        - pose proof (disjeq_disj hdis1 hneq) as hpdisj; unfold get_hs in hpdisj;
          erewrite !Vector.nth_map in hpdisj; eauto. }
      destruct hty as [ty hty'].
      destruct hdiv as [ [? [? [hw1 hw2]]] | [[? [? [hw2 hw1]]] | hdiv]];
        [rewrite hw2 in hred2 | rewrite hw2 in hred1 | ].
      + destruct (non_interference_p3 hty' hcompat hred1 hred2 hw1).
      + destruct (non_interference_p3 hty' (st_compat_sym hcompat) hred2 hred1 hw1).
      + remember (wait cs[@tid1]) as wc1; remember (wait cs[@tid2]) as wc2.
        destruct wc1 as [[? ?]|], wc2 as [[? ?]|]; try (simpl in hdiv; eauto).
        (destruct (non_interference_p2 hty' hcompat hred1 hred2 (eq_sym Heqwc1) (eq_sym Heqwc2)) 
          as [? [? ?]]; congruence).
  Qed.
End BarrierDivergenceFreedom.