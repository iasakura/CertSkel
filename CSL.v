Require Import Logic.Eqdep.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import QArith.
Require Import Qcanon.
Require Import Coq.Relations.Relations.
Require Import Vector.
Require Import List.
Add LoadPath "../../src/cslsound".
Require Import Lang.

Require ClassicalFacts.
Require Export FunctionalExtensionality.
Require Export ProofIrrelevance.

Require Export Coq.ZArith.BinInt.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import PHeap.
Import VectorNotations.

Lemma finvS (n : nat) (i : Fin.t (S n)) : (i = Fin.F1 \/ exists i', i = Fin.FS i').
Proof.
  apply (Fin.caseS (fun n (i : Fin.t (S n)) =>  i = Fin.F1 \/ (exists i' : Fin.t n, i = Fin.FS i'))).
  - intros n0; tauto.
  - intros n0 p; right; eexists; tauto.
Qed.

Section Vector.
  Variable T : Type.
  Variable n : nat.

  Lemma vec_exvec (P : Fin.t n -> T -> Prop) : 
    (forall i : Fin.t n, exists x : T, P i x) -> 
    exists v : Vector.t T n, forall i : Fin.t n, P i v[@i].
  Proof.
    induction n as [|n']; [exists []; inversion 0 | intros H].
    destruct n' as [|n'']; [destruct (H Fin.F1) as [x Hx]; exists [x] | ].
    - intros i; destruct (finvS i) as [|[i' H']]; [subst; eauto|inversion i'].
    - set (P' := (fun (i : Fin.t (S n'')) x => P (Fin.FS i) x)).
      assert (forall i : Fin.t (S n''), exists x : T, P' i x) as Hex.
      { intros i; subst; apply (H (Fin.FS i)). }
      destruct (IHn' P' Hex) as [v IHP'].
      destruct (H Fin.F1) as [x1 H1].
      exists (x1 :: v); intros i; destruct (finvS i) as [|[i' ?]]; subst; unfold P' in *; eauto.
  Qed.
  Variable t : T.
  Lemma vec_eq_ex (f : Fin.t n -> T) :
    (forall i j : Fin.t n, f i = f j) -> (exists c, forall i : Fin.t n, f i = c).
  Proof.
    induction n; intros H; [exists t; intros i; inversion i | ].
    exists (f Fin.F1); intros i; destruct (finvS i) as [| [i' ?]]; subst; eauto.
  Qed.

  Fixpoint init (n : nat) : (Fin.t n -> T) -> Vector.t T n :=
    match n with
      | 0 => fun _ => []
      | S n' => fun f => (f Fin.F1) :: init (fun i => f (Fin.FS i)) 
    end%nat.

  Lemma init_spec (m : nat) (f : Fin.t m -> T) : forall i : Fin.t m, (init f)[@i] = f i.
  Proof.
    revert f; induction m; intros f i; [inversion i|].
    destruct (finvS i) as [|[i' ?]]; subst; simpl; [| rewrite IHm]; eauto.
  Qed.
End Vector.

Section Assertion.
  Inductive assn : Set := 
    Aemp
  | Apure (b: bexp)
  | Aconj (p1: assn) (p2: assn)
  | Adisj (p1: assn) (p2: assn)
  | Astar (p1: assn) (p2: assn)
  | Apointsto (p : Qc) (e1 e2: exp)
  | Aex (pp: nat -> assn).
  
  Local Open Scope list_scope.
  Import ListNotations.
  Fixpoint Aistar ps := 
  match ps with
    | nil => Aemp
    | p :: ps => Astar p (Aistar ps)
  end.

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
  end.
  
  Lemma sat_istar_map_expand :
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
  Qed.

  Definition precise p :=
    forall (h1 h2 h1' h2' : pheap) s,
      sat (s, h1) p -> sat (s, h1') p ->
      pdisj h1 h2 -> pdisj  h1' h2' ->
      phplus h1 h2 = phplus h1' h2' ->
      h1 = h1'.

  Lemma precise_emp : precise Aemp.
  Proof.
    red; intros h1 h2 h1' h2' s hsat hsat' hdis hdis' heq;
    destruct h1 as [h1 ?], h1' as [h1' ?]; apply pheap_eq; extensionality x; simpl in *;
    rewrite hsat, hsat'; eauto.
  Qed.

  Lemma precise_star (p q : assn) : precise p -> precise q -> precise (Astar p q).
  Proof.
    intros pp pq h1 h2 h1' h2' s hsat hsat' hdis hdis' heq;
    simpl in *; des; rewrite <-hsat2, <-hsat'2 in *.
    destruct h1 as [h1 ?], h1' as [h1' ?]; simpl; simpl in hsat2, hsat'2; apply pheap_eq.
    apply pdisj_padd_expand in hdis; apply pdisj_padd_expand in hdis'; eauto.
    rewrite !padd_assoc in heq; try tauto. 
    rewrite <-hsat2, <-hsat'2 in *; f_equal; destruct hdis, hdis'.
    - rewrite (pp h4 (Pheap (pdisj_is_pheap H0)) h0 (Pheap (pdisj_is_pheap H2)) s); eauto.
    - rewrite padd_left_comm in heq at 1; try tauto.
      rewrite (@padd_left_comm h0 h3 h2') in heq; try tauto.
      pose proof (pdisjE2 H H0); eauto. pose proof (pdisjE2 H1 H2); eauto.
      rewrite (pq h5 (Pheap (pdisj_is_pheap H3)) h3 (Pheap (pdisj_is_pheap H4)) s); simpl in *; eauto;       apply pdisj_padd_comm; eauto.
  Qed.

  Lemma precise_istar : forall (l : list assn), (forall x, In x l -> precise x) -> precise (Aistar l).
  Proof.
    induction l; ins; auto using precise_emp, precise_star.
  Qed.
End Assertion.

Section Barrier.
  Variable ngroup : nat.
  Definition barrier_spec := nat -> (Vector.t assn ngroup * Vector.t assn ngroup)%type.
  Variable bspec : barrier_spec.
  Variable env : var -> type.
  Definition low_assn (P : assn) : Prop := 
    forall (st st' : pstate), low_eq env (fst st) (fst st') -> (sat st P <-> sat st' P).

  (* fv(bspec) \cup V_hi = \empty *)
  Definition bwf := forall (j : nat),
      (forall tid : Fin.t ngroup, low_assn (fst (bspec j))[@tid]) /\
      (forall tid : Fin.t ngroup, low_assn (snd (bspec j))[@tid]). 

  Lemma emp_is_heap : is_pheap emp_h. unfold is_pheap, emp_h; eauto. Qed.
  Definition emp_ph : pheap := Pheap emp_is_heap.
  Inductive disj_eq : forall (n : nat), Vector.t pheap n -> pheap -> Prop :=
  | eq_nil  : disj_eq [] emp_ph
  | eq_cons : forall (n : nat) (hs : Vector.t pheap n) (ph : pheap) (h : pheap) (hdis : pdisj h ph),
                disj_eq hs ph -> disj_eq (h :: hs) (Pheap (pdisj_is_pheap hdis)).

  Fixpoint Aistar_v (n : nat) (assns : Vector.t assn n) :=
    match assns with
      | [] => Aemp
      | a :: assns => Astar a (Aistar_v assns)
    end.
  Definition v := 1.
  Definition jth_pre (j : nat) := Aistar_v (fst (bspec j)).
  Definition jth_post (j : nat) := Aistar_v (snd (bspec j)).
  Definition env_wellformed := 
    bwf /\ forall (j : nat) (st : pstate), sat st (jth_pre j) <-> sat st (jth_post j).
  Variable env_wf : env_wellformed.

  Lemma emp_is_emp (h : pheap) :
    (forall v : Z, this h v = None) -> h = emp_ph.
  Proof.
    destruct h as [h ?]; unfold emp_ph; intros hsat.
    assert (h = emp_h) by (extensionality x; specialize (hsat x); simpl in *; eauto).
    pose proof (emp_is_heap).
    cutrewrite (emp_is_heap = H0); [ | apply proof_irrelevance].
    destruct H.
    cutrewrite (is_p = H0); [ | apply proof_irrelevance].
    eauto.
  Qed.

  Lemma aistar_disj (n : nat) (assns : Vector.t assn n) (s : stack) (h : pheap) :
    sat (s, h) (Aistar_v assns) ->
    exists (hs : Vector.t pheap n), disj_eq hs h /\ 
      (forall tid : Fin.t n, sat (s, hs[@tid]) assns[@tid]).
  Proof.
    induction[h] assns; intros h' hsat.
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

  Fixpoint low_eq_l (s : stack) (ng : nat) (sts : Vector.t stack ng) :=
    match sts with
      | [] => True
      | x :: xs => low_eq env s x /\ low_eq_l s xs
    end.
  Fixpoint low_eq_l2 (ng : nat) (sts : Vector.t stack ng) :=
    match sts with
      | [] => True
      | x :: xs => low_eq_l x xs /\ low_eq_l2 xs
    end.

  Definition get_ss (n : nat) (sts : Vector.t pstate n) : Vector.t stack n := 
    Vector.map (fun st => fst st) sts.
  Definition get_hs (n : nat) (sts : Vector.t pstate n) : Vector.t pheap n := 
    Vector.map (fun st => snd st) sts.
  Lemma vinv0 (T : Type) (v : Vector.t T 0) : v = [].
  Proof.
    apply (case0 (fun v : Vector.t T 0 => v = [])); eauto.
  Qed.
  Lemma vinvS : (forall (T : Type) (n : nat) (v : Vector.t T (S n)), exists x y, v = x :: y).
    intros T n0 v0; 
    apply (caseS (fun n (v : Vector.t T (S n)) => exists x y, v = x :: y)).
    intros x n1 y; repeat eexists; eauto.
  Qed.

  Lemma aistar_eq (n : nat) (s : stack) (assns : Vector.t assn n) (hs : Vector.t pstate n)
        (h : pheap) :
    disj_eq (get_hs hs) h -> (forall tid : Fin.t n, sat (s, snd hs[@tid]) assns[@tid]) ->
    sat (s, h) (Aistar_v assns).
  Proof.
    intros heq hsat.
    induction [h heq assns hsat]hs; intros h' heq assns hsat.
    - assert (assns = []) by (apply (case0 (fun (v : t assn 0) => v = [])); eauto).
      simpl in heq; inversion heq.
      rewrite H; simpl; intros; simpl; unfold emp_h; eauto.
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
        (eq : forall st, sat st (Aistar_v prs) <-> sat st (Aistar_v pss))
        (hp : forall tid : Fin.t n, sat (s, snd hs[@tid]) prs[@tid]) :
    exists (hs' : Vector.t pheap n),
      disj_eq hs' h /\ forall tid : Fin.t n, sat (s, hs'[@tid]) pss[@tid].
  Proof.
    eapply (aistar_eq heq) in hp.
    apply eq in hp.
    apply aistar_disj in hp.
    des; repeat eexists; eauto.
  Qed.

  Lemma map_map (T U V : Type) (n : nat) (v : Vector.t T n) (f : T -> U) (g : U -> V) :
    (Vector.map g (Vector.map f v)) = Vector.map (fun x => g (f x)) v.
  Proof.
    induction v; simpl; eauto.
    rewrite IHv; eauto.
  Qed.

  Lemma loweq_sat (n : nat) (s : stack) (sts : Vector.t pstate n)
        (low_eq : low_eq_l2 (s :: get_ss sts)) (ps : Vector.t assn n) 
        (bf : forall tid : Fin.t n, low_assn ps[@tid]) :
    (forall tid : Fin.t n, sat sts[@tid] ps[@tid]) <->
    (forall tid : Fin.t n, sat (Vector.map (fun st => (s, snd st)) sts)[@tid] ps[@tid]).
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
        pose proof (bf (s, snd h) h) as bw'; apply bw'; eauto.
        specialize (Hsat Fin.F1); simpl in Hsat; apply bw'; tauto.
       + apply IHsts; eauto.
        * simpl in low_eq; split; try tauto.
        * intros tid; specialize (bf (Fin.FS tid)); simpl in bf; eauto. 
        * intros tid; specialize (Hsat (Fin.FS tid)); eauto.
      + destruct low_eq as [leq _]; simpl in leq; destruct leq as [leq _].
        specialize (Hsat Fin.F1); specialize (bf Fin.F1); simpl in *.
        apply (bf (s, snd h) h); eauto.
      + apply IHsts; eauto.
        * simpl in low_eq; split; try tauto.
        * intros tid; apply (bf (Fin.FS tid)).
        * intros tid; apply (Hsat (Fin.FS tid)).
  Qed.

  Lemma forall2_map (T U V : Type) (n : nat) (v : Vector.t T n) (u : Vector.t V n)
        (f : T -> U) (P : U -> V -> Prop) :
    Vector.Forall2 P (Vector.map f v) u <-> Vector.Forall2 (fun (x : T) y => P (f x) y) v u.
  Proof.
    induction v.
    - pose proof (vinv0 u); subst; split; intros; constructor.
    - pose proof (vinvS u) as [x [u' hu]]; subst; split; intros; simpl;
      inversion H; subst; apply inj_pair2 in H2; apply inj_pair2 in H5; subst; constructor;
      eauto; apply IHv; eauto.
  Qed.

  Lemma map_map2 (T U V W : Type) (n : nat) (f : T -> U) (g : V -> W -> T) 
        (v2 : Vector.t V n) (v3 : Vector.t W n) :
    Vector.map f (Vector.map2 g v2 v3) = Vector.map2 (fun x y => f (g x y)) v2 v3.
    induction v2.
    - rewrite (vinv0 v3) in *; simpl; eauto.
    - destruct (vinvS v3) as [? [? ?]]; subst; simpl; rewrite IHv2; eauto.
  Qed.
  
  Lemma map2_map (n : nat) (T U V : Type) (v1 : Vector.t (T * U) n) (v2 : Vector.t V n) (t : T) :
    Vector.map2 (fun x y => (t, snd (fst x, y))) v1 v2 = Vector.map (pair t) v2.
  Proof.
    induction v1.
    - rewrite (vinv0 v2); constructor.
    - destruct (vinvS v2) as [h' [v2' ?]]; subst.
      simpl. rewrite IHv1; eauto.
  Qed.

  Lemma map2_fst (T U V : Type) (n : nat) (v : Vector.t (T * V) n) (u : Vector.t U n):
    Vector.map2 (fun x y => fst (fst x, y)) v u = Vector.map (fun x => fst x) v.
    induction v; [rewrite (vinv0 u) | destruct (vinvS u) as [? [? ?]]; subst; simpl; rewrite IHv];
    simpl; try congruence. 
  Qed.

  Lemma map2_snd (T U V : Type) (n : nat) (v : Vector.t (T * V) n) (u : Vector.t U n):
    Vector.map2 (fun x y => snd (fst x, y)) v u = u.
    induction v; [rewrite (vinv0 u) | destruct (vinvS u) as [? [? ?]]; subst; simpl; rewrite IHv];
    simpl; try congruence. 
  Qed.

  Lemma sync_barrier' (sts : Vector.t pstate ngroup) (j : nat) (h : pheap)
        (heq : disj_eq (get_hs sts) h) (ss_leq : low_eq_l2 (get_ss sts))
        (hp : forall tid : Fin.t ngroup, sat sts[@tid] (fst (bspec j))[@tid]) :
    exists (sts' : Vector.t pstate ngroup),
      disj_eq (get_hs sts') h /\ 
      get_ss sts' = get_ss sts /\
      (forall tid : Fin.t ngroup, sat sts'[@tid] (snd (bspec j))[@tid]).
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
      destruct bwf0 as [bwf1 bwf2]. (*inversion bwf1; subst; inversion bwf2; subst.
      apply inj_pair2 in H1; apply inj_pair2 in H4; subst.
      rename H2 into hpr, H5 into hps, H6 into hposts, H3 into hpres.*)
(*      inversion hsat; subst.
      apply inj_pair2 in H1; apply inj_pair2 in H4; subst.
      rename H3 into hsathd, H5 into hsattl.*)
      set (sts' := Vector.map (fun st => (fst h0, snd st)) (h0 :: sts)).
      assert (forall tid : Fin.t (S n), sat sts'[@tid] (pr :: pres')[@tid]).
      { intros tid; destruct (finvS tid) as [ |[tid' ?]], h0; [specialize (hsat Fin.F1); eauto|];
        subst; simpl; eauto; unfold sts'.
        apply loweq_sat; eauto.
        - intros tid; specialize (bwf1 (Fin.FS tid)); eauto.
        - intros tid; specialize (hsat (Fin.FS tid)); eauto. }
(*      rewrite Heqsts' in H; apply ->forall2_map in H; simpl in H.*)
      unfold sts' in *. 
      assert (forall tid : Fin.t (S n), sat (fst h0, snd (h0 :: sts)[@tid]) (pr :: pres')[@tid]).
      { intros tid; specialize (H tid); erewrite Vector.nth_map in H; eauto. }
      eapply sync_barrier in H0; eauto; clear H; rename H0 into H.
      destruct H as [hs' [heqq hsatq]].
      set (stq := (Vector.map2 (fun st h => (fst st, h)) (h0 :: sts) hs')).
      assert (forall tid : Fin.t (S n), sat stq[@tid] (ps:: posts')[@tid]). 
      { unfold stq; apply <-(loweq_sat (n := S n) (s := fst h0)); eauto.
        - rewrite map_map2.
          cutrewrite (Vector.map2 (fun x y => (fst h0, snd (fst x, y))) (h0 :: sts) hs' =
                      Vector.map (pair (fst h0)) hs'); [ | ].
          + intros tid; specialize (hsatq tid); erewrite Vector.nth_map; eauto.
          + rewrite map2_map; eauto.
        - unfold get_ss; rewrite map_map2.
        rewrite map2_fst.
        simpl in ss_leq.
        simpl; repeat split; try tauto. }
      exists stq; repeat split; eauto; unfold stq.
      unfold get_hs; rewrite map_map2, map2_snd; eauto.
      unfold get_ss; rewrite map_map2, map2_fst; simpl; eauto.
  Qed.     
  
  Lemma disjeq_disj1 (n : nat) (h h' : pheap) (hs : Vector.t pheap n)
        (diseq : disj_eq hs h) (i : Fin.t n) :
    pdisj h' h -> pdisj h' hs[@i].
  Proof.
    intros hdisj; induction diseq; [inversion i|].
    assert (pdisj h' h /\ pdisj h' ph) by (apply pdisj_padd; eauto).
    destruct (finvS i) as [? | [i' ?]]; subst; simpl in *; try tauto.
    apply IHdiseq; tauto.
  Qed.

  Lemma disjeq_disj (n : nat) (h : pheap) (hs : Vector.t pheap n) (diseq : disj_eq hs h) 
        (i j : Fin.t n) :
    i <> j -> pdisj (Vector.nth hs i) (Vector.nth hs j).
  Proof.
    induction diseq; [inversion i |].
    intros hneq; destruct (finvS i) as [? | [i' ?]], (finvS j) as [? | [j' ?]]; subst; 
    try congruence; simpl.
    - eapply disjeq_disj1; eauto.
    - apply pdisjC; eapply disjeq_disj1; eauto.
    - apply IHdiseq. intros Hcontra; subst; tauto. 
  Qed.

  Lemma loweq_l_leq (n : nat) (ss : Vector.t stack n) (s : stack) (leq : low_eq_l s ss) (i : Fin.t n) :
    low_eq env s ss[@i].
  Proof.
    induction ss as [| sh ss]; [inversion i|].
    destruct (finvS i) as [? | [i' ?]]; subst; simpl in *; try tauto.
    apply IHss; tauto.
  Qed.

  Lemma low_eq_symm (s1 s2 : stack) : low_eq env s1 s2 -> low_eq env s2 s1.
  Proof.
    unfold low_eq; intros H x Hl; specialize (H x Hl); congruence.
  Qed.

  Lemma loweq_l2_leq (n : nat) (ss : Vector.t stack n) (leq : low_eq_l2 ss) (i j : Fin.t n) :
    low_eq env (ss[@i]) (ss[@j]).
  Proof.
    clear env_wf.
    induction ss as [| s ss]; [inversion i |].
    destruct (finvS i) as [? | [i' ?]], (finvS j) as [? | [j' ?]]; subst; try congruence; simpl in *.
    - apply loweq_l_leq; tauto.
    - apply low_eq_symm; apply loweq_l_leq; tauto.
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
    intros H.
    induction ss as [| s ss]; simpl; eauto.
    split; [apply leq_low_eq_l; intros j; apply (H (Fin.F1) (Fin.FS j)) | ].
    intros H'; inversion H'.
    apply IHss; intros i j ineqj. eapply (H (Fin.FS i) (Fin.FS j)); inversion 1.
    apply inj_pair2 in H2; congruence.
  Qed.
End Barrier.

Section SeqCSL.
  Variable ngroup : nat.
  Variable bspec : barrier_spec ngroup.
  Variable env : var -> type.
  Hypothesis env_wf : env_wellformed bspec env.
  Hypothesis bc_precise : 
    forall i (tid : Fin.t ngroup), precise ((fst (bspec i))[@tid]) /\
                                   precise ((snd (bspec i))[@tid]).
  Definition pre_j tid (j : nat) := Vector.nth (fst (bspec j)) tid.
  Definition post_j tid (j : nat) := Vector.nth (snd (bspec j)) tid.

  Fixpoint safe_nt (tid : Fin.t ngroup) (n : nat) (c : cmd) (s : stack) (ph : pheap) (q : assn) :=
    match n with
      | O => True
      | S n => 
        (c = Cskip -> sat (s, ph) q) /\

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
             pdisj phP ph' /\ phplus phP ph' = ph /\ sat (s, phP) (pre_j tid j) /\
             (forall (phQ : pheap) (H : pdisj phQ ph'), sat (s, phQ) (post_j tid j) ->
                safe_nt tid n c' s (phplus_pheap H) q))
    end.
  Definition safe_t (tid : Fin.t ngroup) (c : cmd) (s : stack) (ph : pheap) (q : assn) := 
    forall (n : nat), safe_nt tid n c s ph q.
  
  Definition CSL (tid : Fin.t ngroup) (p : assn) (c : cmd) (q : assn) := 
    (exists g, typing_cmd g c Lo) /\ wf_cmd c /\ 
    forall s ph, sat (s, ph) p -> safe_t tid c s ph q.

  Definition safe_aux (tid : Fin.t ngroup) (c : cmd) (s : stack) (ph : pheap) :=
    exists (q : assn), forall n, safe_nt tid n c s ph q.

  Definition Vt := Vector.t.
  Import Vector.VectorNotations.
  Inductive Forall3 (A B C : Type) (P : A -> B -> C -> Prop) : 
    forall n : nat, Vt A n -> Vt B n -> Vt C n -> Prop :=
  | Forall3_nil : Forall3 P (Vector.nil _) (Vector.nil _) (Vector.nil _)
  | Forall3_cons : forall (m : nat) (x1 : A) (x2 : B) (x3 : C) 
      (v1 : Vt _ m) (v2 : Vt _ m) (v3 : Vt _ m),
      P x1 x2 x3 -> Forall3 P v1 v2 v3 -> Forall3 P (x1 :: v1) (x2 :: v2) (x3 :: v3).
  
  Definition get_ss_k (ks : kstate ngroup) := Vector.map (fun x => snd x) (fst ks).
  Definition get_cs_k (ks : kstate ngroup) := Vector.map (fun x => fst x) (fst ks).

  Lemma map2_snd' (T U : Type) (n : nat) (v : Vt T n) (u : Vt U n) :
    Vector.map2 (fun x y => snd (x, y)) v u = u.
  Proof.
    induction v.
    - rewrite (vinv0 u); eauto.
    - destruct (vinvS u) as [x [t ?]]; subst; simpl; rewrite IHv; eauto.
  Qed.

  Lemma map2_fst' (T U : Type) (n : nat) (v : Vt T n) (u : Vt U n) :
    Vector.map2 (fun x y => fst (x, y)) v u = v.
  Proof.
    induction v.
    - rewrite (vinv0 u); eauto.
    - destruct (vinvS u) as [x [t ?]]; subst; simpl; rewrite IHv; eauto.
  Qed.

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

  Lemma disj_eq_fun (n : nat) (hs : Vt pheap n) (h h' : pheap) : 
    disj_eq hs h -> disj_eq hs h' -> h = h'.
  Proof.
    clear env_wf env bspec ngroup bc_precise.
    move: n h h' hs; induction n; intros h h' hs hdis hdis'.
    - rewrite (vinv0 hs) in *; inversion hdis; inversion hdis'; subst; eauto.
    - destruct (vinvS hs) as [h0 [hs' ?]]; subst; inversion hdis; inversion hdis'; 
      clear hdis hdis'; subst.
      repeat (match goal with [ H : existT _ _ _ = existT _ _ _ |- _] => 
                              apply inj_pair2 in H; subst end).
      apply pheap_eq; rewrite (IHn ph0 ph hs' H8 H3); eauto.
  Qed.

  Lemma disj_exclude (n : nat) (hs : Vt pheap n) (h h' : pheap) (i : Fin.t n) :
    disj_eq hs h -> disj_eq (replace hs i emp_ph) h' -> pdisj hs[@i] h' /\ this h = phplus hs[@i] h'.
  Proof.
    clear env_wf env bspec ngroup bc_precise; move: hs h h' i; induction n; 
    intros hs h h' i heq heq'; [inversion i|].
    destruct (vinvS hs) as [h0 [hs0 ?]]; subst.
    inversion heq; inversion heq';  
    repeat (match goal with [ H : existT _ _ _ = existT _ _ _ |- _] => 
                            apply inj_pair2 in H; subst end); subst; simpl in *; subst.
    destruct (finvS i) as [? | [i' ?]]; subst; simpl in *;
    inversion H5; clear H5; subst; apply inj_pair2 in H1; subst.
    - cutrewrite (phplus emp_ph ph0 = ph0); [ | extensionality x; unfold phplus; simpl; eauto].
      rewrite (disj_eq_fun H6 H3); eauto.
    - pose proof (IHn _ _ _ _ H3 H6) as IH.
      rewrite phplus_comm; eauto; split; destruct IH; subst.
      + apply pdisj_padd_expand; eauto.
        rewrite <-H0; eauto.
      + rewrite (phplus_comm (pdisjC hdis0)); rewrite padd_left_comm; eauto.
        rewrite <-H0; eauto.
        rewrite (phplus_comm hdis0); apply pdisj_padd_expand; eauto.
        rewrite <-H0; eauto.
  Qed.

  Lemma disj_weak (n : nat) (hs :  Vt pheap n) (h h' h'': pheap) (i : Fin.t n) :
    disj_eq hs h -> pdisj h'' h -> disj_eq (replace hs i emp_ph) h' -> pdisj h'' h'.
    clear env_wf env bspec ngroup bc_precise.
    move: h h' h''; generalize dependent n.
    induction n; intros hs i h h' h'' heq hdis heq'; [inversion i |].
    destruct (vinvS hs) as [h0 [hs0 ?]]; subst.
    destruct (finvS i) as [? | [i' ?]]; subst; simpl in *.
    - inversion heq; clear heq; subst. apply inj_pair2 in H2; subst; simpl in *.
      apply pdisj_padd in hdis; eauto.
      inversion heq'; clear heq'; subst. apply inj_pair2 in H2; subst; simpl in *.
      cutrewrite ((phplus emp_h ph0) = ph); [tauto | ].
      extensionality x; unfold phplus; simpl; rewrite (disj_eq_fun H4 H3); eauto.
    - inversion heq; inversion heq'; clear heq heq';
      repeat (match goal with [ H : existT _ _ _ = existT _ _ _ |- _] => 
                              apply inj_pair2 in H; subst end); subst; simpl in *.
      pose proof (disj_exclude H3 H8) as [hdall heq]; rewrite heq in *.
      rewrite padd_left_comm in hdis; eauto.
      cutrewrite (phplus h0 ph0 = this (Pheap (pdisj_is_pheap hdis1))) in hdis; [ | simpl; eauto].
      apply pdisj_padd in hdis; simpl in *; try tauto.
      apply pdisjC, pdisj_padd_expand; eauto; split; eauto.
      rewrite phplus_comm; eauto.
  Qed.

  Lemma disj_exclude_exists (n : nat) (hs : Vt pheap n) (h : pheap) (i : Fin.t n) :
    disj_eq hs h -> exists h', disj_eq (Vector.replace hs i emp_ph) h'.
  Proof.
    clear env_wf env bspec ngroup bc_precise; move: hs h i; induction n; 
    intros hs h i heq; [inversion i|].
    destruct (vinvS hs) as [h0 [hs0 ?]]; subst.
    inversion heq; 
      repeat (match goal with [ H : existT _ _ _ = existT _ _ _ |- _] => 
                              apply inj_pair2 in H; subst end); subst; simpl in *; subst.
    destruct (finvS i) as [? | [i' ?]]; subst; simpl in *.
    - assert (pdisj emp_ph ph) as hph by (unfold pdisj, emp_ph; intros x; simpl; eauto).
      exists (Pheap (pdisj_is_pheap hph)).
      apply (eq_cons hph H3).
    - destruct (IHn _ _ i' H3) as [ph' H].
      destruct (disj_exclude H3 H).
      assert (pdisj h0 ph') by apply (disj_weak H3 hdis H ).
      exists (Pheap (pdisj_is_pheap H2)).
      apply (eq_cons H2 H).
  Qed.

  Lemma disj_tid (n : nat) (hs : Vt pheap n) (h : pheap) (i : Fin.t n):
    disj_eq hs h -> exists h', disj_eq (Vector.replace hs i emp_ph) h' /\ 
                               pdisj hs[@i] h' /\ phplus hs[@i] h' = h.
  Proof.
    intros hdeq.
    destruct (disj_exclude_exists i hdeq) as [h' ?].
    exists h'; split; eauto.
    split; destruct (disj_exclude hdeq H); eauto; try congruence.
  Qed.

  Lemma disj_upd (n : nat) (hs : Vt pheap n) (i : Fin.t n) (h hq : pheap):
    disj_eq (replace hs i emp_ph) h -> 
    pdisj hq h ->
    exists h', 
      disj_eq (replace hs i hq) h' /\ phplus hq h = h'.
  Proof.
    clear env_wf env bspec ngroup bc_precise; move: hs h i hq; induction n; 
    intros hs h i hq heq hdis; [inversion i|].
    destruct (vinvS hs) as [h0 [hs0 ?]]; subst.
    inversion heq; subst. apply inj_pair2 in H0; subst.
    destruct (finvS i) as [? | [i' ?]]; simpl in *; subst; inversion H0; subst; simpl in *.
    - cutrewrite (phplus emp_h ph = ph) in hdis; [ | unfold phplus, emp_h; extensionality x; eauto].
      exists (Pheap (pdisj_is_pheap hdis)); simpl.
      split; [constructor; eauto | ].
      cutrewrite (phplus emp_h ph = ph); [eauto | unfold phplus, emp_h; extensionality x; eauto].
    - apply inj_pair2 in H3; subst.
      apply pdisjC in hdis; eapply pdisj_padd_expand in hdis; eauto.
      destruct hdis as [hdis hd].
      assert (pdisj h0 (Pheap (pdisj_is_pheap hd))) as dis' by (simpl; eauto).
      exists (Pheap (pdisj_is_pheap dis')); split; eauto.
      + econstructor.
        destruct (IHn _ _ _ _ H1 (pdisjC hd)) as [h' [hdeq pheq]].
        rewrite phplus_comm in pheq; eauto.
        cutrewrite ( Pheap (pdisj_is_pheap hd) = h'); 
          [eauto | destruct h'; apply pheap_eq; simpl in *; eauto].
      + simpl. rewrite padd_left_comm, (@phplus_comm ph hq); eauto.
        apply pdisjC, pdisj_padd_expand; eauto.
  Qed.

  Lemma disj_eq_each_disj (n : nat) (hs1 hs2 : Vector.t pheap n) (h1 h2 : pheap) :
    disj_eq hs1 h1 -> disj_eq hs2 h2 -> pdisj h1 h2 -> 
    (forall i : Fin.t n, pdisj hs1[@i] hs2[@i]).
    revert h1 h2; generalize dependent n; induction n as [|n]; 
    intros hs1 hs2 h1 h2 hdeq1 hdeq2 hdis i; [inversion i|].
    destruct (vinvS hs1) as [hh1 [hs1' ?]], (vinvS hs2) as [hh2 [hs2' ?]]; subst.
    inversion hdeq1; clear hdeq1; apply inj_pair2 in H2; subst; rename H3 into heq1.
    inversion hdeq2; clear hdeq2; apply inj_pair2 in H2; subst; rename H3 into heq2.
    destruct (finvS i) as [| [i' ?]]; subst.
    - cutrewrite (this {|this := phplus hh2 ph0; is_p := pdisj_is_pheap (h1:=hh2) (h2:=ph0) hdis1 |} =
                  phplus hh2 ph0) in hdis; [|eauto].
      apply pdisjE1, pdisjC in hdis; simpl in hdis; eauto; apply pdisjE1 in hdis; eauto.
    - eapply IHn; eauto.
      cutrewrite (this {|this := phplus hh2 ph0; is_p := pdisj_is_pheap (h1:=hh2) (h2:=ph0) hdis1 |} =
                  phplus hh2 ph0) in hdis; [|eauto].      
      apply pdisjE2, pdisjC in hdis; simpl in hdis; eauto; apply pdisjE2 in hdis; eauto.
  Qed.

  Lemma pp_pdisj1 (h1 h2 h3 h4 : pheap) (dis12 : pdisj h1 h2) (dis34 : pdisj h3 h4) :
    pdisj (phplus_pheap dis12) (phplus_pheap dis34) ->
    pdisj h1 h3.
  Proof.
    clear bspec env env_wf bc_precise.
    unfold phplus_pheap.
    cutrewrite (this {| this := phplus h3 h4;
                   is_p := pdisj_is_pheap (h1:=h3) (h2:=h4) dis34 |} =
                phplus h3 h4); [|simpl; eauto]; intros H.
    apply pdisjE1, pdisjC in H; simpl in H; eauto; apply pdisjE1 in H; eauto.
  Qed.

  Lemma pp_pdisj2 (h1 h2 h3 h4 : pheap) (dis12 : pdisj h1 h2) (dis34 : pdisj h3 h4) :
    pdisj (phplus_pheap dis12) (phplus_pheap dis34) ->
    pdisj h2 h4.
  Proof.
    clear bspec env env_wf bc_precise.
    unfold phplus_pheap.
    cutrewrite (this {| this := phplus h3 h4;
                   is_p := pdisj_is_pheap (h1:=h3) (h2:=h4) dis34 |} =
                phplus h3 h4); [|simpl; eauto]; intros H.
    apply pdisjE2, pdisjC in H; simpl in H; eauto; apply pdisjE2 in H; eauto.
  Qed.

  Lemma disj_eq_sum (n : nat) (hs1 hs2 hs' : Vector.t pheap n) (h1 h2 : pheap) (hdis : pdisj h1 h2):
    disj_eq hs1 h1 -> disj_eq hs2 h2 -> 
    (forall i, this hs'[@i] = phplus hs1[@i] hs2[@i]) ->
    disj_eq hs' (phplus_pheap hdis).
  Proof.
    revert hs1 hs2 hs' h1 h2 hdis ; induction n;
    intros hs1 hs2 hs' h1 h2 hdis hdeq1 hdeq2 heqs.
    - rewrite (vinv0 hs1), (vinv0 hs2), (vinv0 hs') in *.
      inversion hdeq1; inversion hdeq2; subst.
      cutrewrite (phplus_pheap hdis = emp_ph); [constructor| apply pheap_eq; extensionality x; eauto].
    - destruct (vinvS hs1) as [ht1 [hs1' ?]], (vinvS hs2) as [ht2 [hs2' ?]], (vinvS hs') as [ht' [hs'' ?]] in *; subst.
      inversion hdeq1; clear hdeq1; apply inj_pair2 in H2; subst; rename H3 into hdeq1.
      inversion hdeq2; clear hdeq2; apply inj_pair2 in H2; subst; rename H3 into hdeq2.
(*      inversion hdeq'; clear hdeq'; apply inj_pair2 in H2; subst; rename H3 into hdeq'.*)
      pose proof (pp_pdisj1 hdis) as dh12; pose proof (pp_pdisj2 hdis) as dph12.
      assert (forall i : Fin.t n, this hs''[@i] = phplus hs1'[@i] hs2'[@i]) by
        (intros i; specialize (heqs (Fin.FS i)); eauto).
      pose proof (IHn _ _ _ _ _ dph12 hdeq1 hdeq2 H).
      pose proof (heqs Fin.F1).
      set (h1 := phplus_pheap dph12).
      set (h2 := phplus_pheap dh12). 
      assert (pdisj h2 h1).
      { apply pdisjC.
        assert (pdisj ph0 (phplus ht1 ht2)).
        { apply pdisj_padd_comm, pdisjC; eauto.
          cutrewrite (this {|this := phplus ht1 ph; is_p := pdisj_is_pheap hdis0|} = phplus ht1 ph) in
              hdis; [|simpl; eauto]; apply pdisjC in hdis.
          eapply pdisjE1, pdisjC in hdis; eauto; simpl; rewrite phplus_comm; eauto. }
        unfold h1, h2.
        cutrewrite (this (phplus_pheap dph12) = phplus ph ph0); [|eauto].
        apply pdisj_padd_expand; eauto; split; [|simpl; eauto].
        simpl; rewrite padd_left_comm; eauto.
        cutrewrite (phplus ph0 ht2 = phplus_pheap hdis1); [|rewrite phplus_comm; eauto].
        apply pdisj_padd_expand; eauto; simpl in hdis; rewrite phplus_comm; eauto. }
      cutrewrite (phplus_pheap hdis = phplus_pheap H2).
      + cutrewrite (ht' = h2); [| now (unfold h1; destruct ht'; apply pheap_eq; apply H1)].
        constructor; eauto.
      + apply pheap_eq;
        cutrewrite (this {| this := phplus ht1 ph;
                          is_p := pdisj_is_pheap hdis0 |} = phplus ht1 ph); 
        [|simpl; eauto].
        Hint Resolve pdisjC pdisj_padd_comm.
        pose proof (pp_pdisj1 hdis).
        pose proof (pp_pdisj2 hdis). 
        pose proof (pdisjE1 hdis hdis1).
        pose proof (pdisjE2 hdis hdis1).
        pose proof (pdisjE1 (pdisjC hdis) hdis0).
        pose proof (pdisjE2 (pdisjC hdis) hdis0).
        assert (pdisj ht1 (phplus ph (phplus ht2 ph0))).
        { cutrewrite (phplus ht2 ph0 = this {| this := phplus ht2 ph0;
                                               is_p := pdisj_is_pheap hdis1 |}); [|simpl; eauto].
          apply pdisj_padd_expand; eauto. }
        rewrite padd_assoc; eauto.
        simpl. rewrite padd_left_comm; eauto.
        cutrewrite (phplus ph ph0 = this {| this := phplus ph ph0;
                                            is_p := pdisj_is_pheap dph12 |}); [|simpl; eauto].
        rewrite <-padd_assoc; simpl; f_equal; eauto.
        rewrite <-padd_left_comm; eauto.
  Qed.

  Lemma safe_red_p (c1 c2 : cmd) (st1 st2 : state) (pst1 : pstate) (hF : pheap) (tid : Fin.t ngroup):
    c1 / st1 ==>s c2 / st2 -> 
    fst st1 = fst pst1 ->
    safe_aux tid c1 (fst pst1) (snd pst1) ->
    pdisj (snd pst1) hF -> ptoheap (phplus (snd pst1) hF) (snd st1) ->
    exists pst2, 
      c1 / pst1 ==>p c2 / pst2 /\
      fst pst2 = fst st2 /\
      pdisj (snd pst2) hF /\
      ptoheap (phplus (snd pst2) hF) (snd st2).
  Proof.
    intros red_s heq hsafe hdis1 hto1; destruct hsafe as [? hsafe]; 
    destruct (hsafe 1%nat) as [_ [ha [haok [hwok _]]]].
    destruct (red_s_safe red_s (eq_sym heq) hdis1 hto1 haok hwok) as [ph [? [? ?]]].
    eauto.
  Qed.

  Lemma fin_eq_dec : forall (n : nat) (i j : Fin.t n), {i = j} + {i <> j}.
  Proof.
    refine (
        fun n =>
          match n with
            | O => fun (i _ : Fin.t 0) => match (Fin.case0 (fun _ => False) i) with end
            | S n => 
              Fin.rect2 (fun n (i : Fin.t n) (j : Fin.t n) => {i = j} + {i <> j})
                        (fun n => left _ _)
                        (fun n f => right _ _)
                        (fun n f =>  right _ _)
                        (fun n f g (b : {f = g} + {f <> g}) => if b then left _ _ else right _ _)
          end); subst; try inversion 1; eauto.
    apply inj_pair2 in H1; congruence.
  Qed.

  Lemma replace_nth (T : Type) (n : nat) (i j : Fin.t n) (v : Vector.t T n) (x : T) : 
    (replace v i x)[@j] = if fin_eq_dec i j then x else v[@j].
  Proof.
    move:v; induction n; [inversion i | ]; intros v.
    destruct (finvS i) as [? | [i' ?]]; subst;
    destruct (finvS j) as [? | [j' ?]]; subst;
    destruct (vinvS v) as [t [v' ?]]; subst; simpl; eauto.
    destruct (fin_eq_dec Fin.F1 Fin.F1) as [h|h]; [eauto | congruence].
    destruct (fin_eq_dec Fin.F1 (Fin.FS j')) as [h|h]; [inversion h|eauto].
    destruct (fin_eq_dec (Fin.FS i') Fin.F1) as [h|h]; [inversion h|eauto].
    rewrite IHn; destruct (fin_eq_dec i' j') as [h|h];
    [subst; destruct (fin_eq_dec (Fin.FS j') (Fin.FS j')); eauto; try congruence|
     destruct (fin_eq_dec (Fin.FS i') (Fin.FS j')); eauto].
    inversion e. apply inj_pair2 in H0; subst; congruence.
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



  Lemma disj_eq_sub (n : nat) (hs hs1 hs2 : Vector.t pheap n) (h : pheap): 
    disj_eq hs h -> (forall i : Fin.t n, pdisj hs1[@i] hs2[@i] /\ phplus hs1[@i] hs2[@i] = hs[@i]) ->
      exists (h1 h2 : pheap), 
        disj_eq hs1 h1 /\ disj_eq hs2 h2 /\ pdisj h1 h2 /\ phplus h1 h2 = h.
  Proof.
    move: h; induction n; intros h hdis heq.
    - generalize (vinv0 hs), (vinv0 hs1), (vinv0 hs2); intros; subst; repeat eexists; 
      (repeat split); try constructor.
      inversion hdis; subst; unfold emp_ph; simpl; extensionality x; eauto.
    - destruct (vinvS hs) as [ph [hs' ?]], (vinvS hs1) as [ph1 [hs1' ?]], 
               (vinvS hs2) as [ph2 [hs2' ?]]; subst. inversion hdis; apply inj_pair2 in H2; subst.
      clear hdis.
      assert (forall i : Fin.t n, pdisj hs1'[@i] hs2'[@i] /\ phplus hs1'[@i] hs2'[@i] = hs'[@i]) 
        as H by (intros i; pose proof (heq (Fin.FS i)) as H; simpl in H; tauto).
      destruct (IHn _ _ _ _ H3 H) as [h1 [h2 IH]].
      assert (pdisj h1 ph1 /\ pdisj h2 ph2) as [dis1 dis2].
      { destruct IH as [? [? [H1 H2]]]; rewrite <-H2 in hdis0.
        destruct (heq Fin.F1) as [dis12 pp12]; simpl in *.
        assert (phplus_pheap dis12 = ph) by (destruct ph; apply pheap_eq; simpl in *; eauto).
        rewrite <-H5 in hdis0.
        apply pdisj_padd in hdis0; eauto.
        destruct hdis0 as [dis1 dis2]; apply pdisjC in dis1; apply pdisjC in dis2.
        simpl in *; apply pdisj_padd in dis1; apply pdisj_padd in dis2; tauto. }
      assert (pdisj h1 (phplus_pheap (pdisjC dis2))). 
      { simpl. rewrite (phplus_comm (pdisjC dis2)); apply pdisj_padd_expand; try tauto.
        destruct (heq Fin.F1) as [dis12 pp12]; simpl in dis12, pp12.
        destruct IH as [_ [_ [? ?]]].
        cutrewrite (ph0 = phplus_pheap H0) in hdis0;[|destruct ph0; eauto; apply pheap_eq; eauto].
        rewrite <-pp12 in hdis0.
        apply pdisjC in hdis0; apply pdisjE2 in hdis0; tauto. }
      assert (pdisj (phplus_pheap (h1:=ph1) (h2:=h1) (pdisjC (h1:=h1) (h2:=ph1) dis1))
                    (phplus_pheap (h1:=ph2) (h2:=h2) (pdisjC (h1:=h2) (h2:=ph2) dis2))).
      { apply (pdisj_padd_expand _ (pdisjC dis1)); split; auto.
        simpl; rewrite (padd_left_comm H0 (pdisjC dis2)).
        destruct IH as [? [? [hdis12 hpp12]]].
        cutrewrite (phplus h1 h2 = phplus_pheap hdis12); [| simpl; eauto].
        assert (pdisj ph1 (phplus ph2 (phplus_pheap (h1:=h1) (h2:=h2) hdis12)) /\
                pdisj ph2 (phplus_pheap (h1:=h1) (h2:=h2) hdis12)); [ | tauto].
        apply pdisj_padd_expand; [generalize (heq (Fin.F1)); tauto |].
        simpl; rewrite hpp12. 
        destruct (heq (Fin.F1)) as [? Heq]; simpl in *; rewrite Heq; eauto using pdisjC. }
      exists (phplus_pheap (pdisjC dis1)), (phplus_pheap (pdisjC dis2)); 
      repeat split; try econstructor; try tauto.
      + cutrewrite (this (phplus_pheap (h1:=ph1) (h2:=h1) (pdisjC (h1:=h1) (h2:=ph1) dis1)) =
                    phplus ph1 h1); [|eauto].
        rewrite padd_assoc; [simpl| apply (pdisj_padd_expand _ (pdisjC dis1))| ]; try tauto.
        destruct IH as [? [? [dis12 pp12]]].
        rewrite (phplus_comm (pdisjC dis2)). 
        rewrite<-padd_assoc; [| rewrite (@phplus_comm h2 ph2); try tauto| apply ( dis2)].
        cutrewrite (phplus h1 h2 = phplus_pheap dis12); [|eauto]. 
        assert (pdisj ph2 (phplus_pheap (h1:=h1) (h2:=h2) dis12)).
        { destruct (heq (Fin.F1)) as [? ?]; simpl in *; rewrite <-H6 in hdis0.
          apply pdisjC,pdisjE2,pdisjC in hdis0; try eauto; rewrite pp12; eauto. }
        rewrite (@phplus_comm _ ph2), <-padd_assoc; eauto.
        * simpl; rewrite pp12; destruct (heq (Fin.F1)) as [? ?]; simpl in *; congruence.
        * apply pdisj_padd_expand; destruct (heq Fin.F1); simpl in *; try tauto.
          rewrite H7, pp12; tauto.
  Qed.    
    
  Definition nth (n : nat) (A : Type) (v : Vt A n):= Vector.nth v.

  Lemma step_inv (ks1 ks2 : kstate ngroup) (red_k : (ks1 ==>k* ks2))
        (hs1 : Vector.t pheap ngroup) (ss1 : Vector.t stack ngroup) (c : cmd) :
    (exists ty : type, typing_cmd env c ty) ->
    disj_eq hs1 (htop (snd ks1)) ->
    ss1 = get_ss_k ks1 -> low_eq_l2 env ss1 ->
    (forall tid : Fin.t ngroup, (get_cs_k ks1)[@tid] = c) -> 
    (forall tid : Fin.t ngroup, safe_aux tid c (ss1[@tid]) (hs1[@tid])) ->
    exists (pss' : Vector.t pstate ngroup) (pss2 : Vector.t pstate ngroup) (c' : cmd) 
           (cs : Vector.t cmd ngroup) (h' : pheap), 
      disj_eq (get_hs pss') h' /\  low_eq_l2 env (get_ss pss') /\
      disj_eq (get_hs pss2) (htop (snd ks2)) /\ 
      (exists ty : type, typing_cmd env c' ty) /\
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
      exists pss', pss', c, (Vector.const c ngroup), (htop (snd ks1)).
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
        { unfold get_ss_k, get_ss in Hi2; simpl in Hi2; 
          rewrite !(Vector.nth_map _ _ tid tid), sstid in Hi2; eauto; simpl in Hi2. }
        rewrite <-Hceq,<-Hseq in red'.
        pose proof (safe_inv' Hi3 Hi4) as hsafei.
        destruct (disj_tid tid H3) as [h_ni [eqni [h_ntid hnip]]].
        assert ((get_hs pss2)[@tid] = snd pss2[@tid]) as H'
          by (unfold get_hs; erewrite Vector.nth_map; eauto);
          rewrite H' in h_ntid, hnip; clear H'.
        assert (ptoheap (phplus (snd pss2[@tid]) h_ni) h1) as hto 
          by (rewrite hnip; apply ptoheap_htop).
        destruct (safe_red_p red' eq_refl hsafei h_ntid hto) as [pst2 [seq [tred [tdisj tto]]]].
        destruct (disj_upd eqni tdisj) as [hq [hdeq_q  heq_q]].
        exists pss', (replace pss2 tid pst2), c', (replace cs tid c2), h'.
        repeat split; eauto.
        + rewrite heq_q in tto; simpl in tto.
          assert (get_hs (replace pss2 tid pst2) = replace (get_hs pss2) tid (snd pst2)) as Ht.
          { apply eq_nth_iff; intros p1 p2 peq; rewrite peq. 
            unfold get_hs; erewrite Vector.nth_map; eauto.
            repeat rewrite replace_nth. destruct (fin_eq_dec tid p2); eauto.
            erewrite Vector.nth_map; eauto. }
          rewrite Ht.
          cutrewrite (htop h2 = hq); [eauto | symmetry; apply ptoheap_eq; eauto].
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
          erewrite !(Vector.nth_map) in H1; erewrite !(Vector.nth_map) in H2; eauto;
          destruct ss'[@tid]; f_equal; eauto. }
        assert (forall tid : Fin.t ngroup, wait cs[@tid] = Some (j, fst ss2[@tid])) as cswait.
        { intros tid; destruct (Hbrr tid) as [cp [s [cq' [H1 [H2 H3]]]]]. specialize (heqss' tid).
          rewrite heqss' in H1; destruct ss2[@tid]; inversion H1; inversion H2; inversion H3; 
          subst; eauto. }
        assert (forall tid, exists phP phF : pheap, 
                  pdisj phP phF /\ phplus phP phF = snd pss2[@tid] /\ 
                  sat (fst pss2[@tid], phP) (pre_j tid j)) as hpre.
        { intros tid; specialize (hsafe2 tid); destruct hsafe2 as [q hsafe2];
          specialize (hsafe2 1%nat); destruct hsafe2 as [_ [_ [_ [_ [_ hsafe2]]]]];
          specialize (hsafe2 j (fst ss2[@tid]) (cswait tid));
          destruct hsafe2 as [phP [phF [? [? [? _]]]]]; eexists; eauto. }
        assert (exists (phPs phFs : t pheap ngroup), forall tid : Fin.t ngroup,
                  pdisj phPs[@tid] phFs[@tid] /\
                  phplus phPs[@tid] phFs[@tid] = snd pss2[@tid] /\
                  sat (fst pss2[@tid], phPs[@tid]) (pre_j tid j)) as [phPs [phFs Hpre]].
        { destruct (@vec_exvec pheap ngroup (fun tid phP => exists (phF : pheap), pdisj phP phF /\
           phplus phP phF = snd pss2[@tid] /\
           sat (fst pss2[@tid], phP) (pre_j tid j)) hpre) as [phPs Hp].
          destruct (@vec_exvec pheap ngroup (fun tid phF => pdisj phPs[@tid] phF /\
            phplus phPs[@tid] phF = snd pss2[@tid] /\
            sat (fst pss2[@tid], phPs[@tid]) (pre_j tid j)) Hp) as [phFs Hp'].
          eexists; eauto. }
        assert (forall tid : Fin.t ngroup, 
                  pdisj phPs[@tid] phFs[@tid] /\ phplus phPs[@tid] phFs[@tid] = (get_hs pss2)[@tid]) 
        as H'.
        { intros tid; specialize (Hpre tid); split; try tauto.
          unfold get_hs; erewrite Vector.nth_map; eauto; des; tauto. }
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
        assert (exists phQs : Vector.t pheap ngroup, 
                  disj_eq phQs hP /\ 
                  forall tid : Fin.t ngroup, 
                    pdisj phQs[@tid] phFs[@tid] /\ 
                    sat (fst pss2[@tid], phQs[@tid]) (post_j tid j)) as hq.
        { assert (disj_eq (get_hs psspre) (hP)) as disj1 by
          (cutrewrite (get_hs psspre = phPs); [eauto|
             (apply Vector.eq_nth_iff; intros i1 i2 ?; subst; unfold get_hs, psspre;
              erewrite Vector.nth_map; eauto; erewrite Vector.nth_map2; simpl; eauto)]).
          assert (forall tid : Fin.t ngroup, sat psspre[@tid] (fst (bspec j))[@tid]).
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
        exists pssq, pssq, c'', (Vector.const c'' ngroup), (htop h).
        Hint Unfold low_eq_l2 get_hs get_ss.
        Hint Rewrite map_map2 map2_fst' map2_snd' init_spec.
        unfold pssq, phs.
        repeat split; eauto.
        - autounfold; autorewrite with core; 
          cutrewrite (htop h = phplus_pheap hdispf); [| apply pheap_eq; eauto].
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
        - (* copipe!! *)
          autounfold; autorewrite with core; 
          cutrewrite (htop h = phplus_pheap hdispf); [| apply pheap_eq; eauto].
          apply (disj_eq_sum hdispf hdisq HhF).
          intros i; rewrite init_spec; eauto.
        - (* admitted!!!! *)admit.
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

  Definition bdiv (ks : kstate ngroup) :=
    exists tid1 tid2 : Fin.t ngroup, 
      let c1 := (get_cs_k ks)[@tid1] in
      let c2 := (get_cs_k ks)[@tid2] in
      (exists j1 c1', wait c1 = Some (j1, c1') /\ c2 = Cskip) \/ 
      (exists j2 c2', c1 = Cskip                /\ wait c2 = Some (j2, c2')) \/ 
      diverge (wait c1) (wait c2).

  Theorem barrier_divergence_freedom  (ks1 ks2 : kstate ngroup) (red_k : (ks1 ==>k* ks2))
          (hs1 : Vector.t pheap ngroup) (ss1 : Vector.t stack ngroup) (c : cmd) :
    (exists ty : type, typing_cmd env c ty) ->
    disj_eq hs1 (htop (snd ks1)) ->
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
      + destruct (non_interference_p3 hty' (st_compat_refl hcompat) hred2 hred1 hw1).
      + remember (wait cs[@tid1]) as wc1; remember (wait cs[@tid2]) as wc2.
        destruct wc1 as [[? ?]|], wc2 as [[? ?]|]; try (simpl in hdiv; eauto).
        (destruct (non_interference_p2 hty' hcompat hred1 hred2 (eq_sym Heqwc1) (eq_sym Heqwc2)) 
          as [? [? ?]]; congruence).
  Qed.
End SeqCSL.