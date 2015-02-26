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

Section Assertion.
  Inductive assn : Set := 
    Aemp
  | Apure (b: bexp)
  | Aconj (p1: assn) (p2: assn)
  | Adisj (p1: assn) (p2: assn)
  | Astar (p1: assn) (p2: assn)
  | Apointsto (p : Qc) (e1 e2: exp)
  | Aex (pp: nat -> assn).

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
      Vector.Forall (fun p => low_assn p) (fst (bspec j)) /\
      Vector.Forall (fun p => low_assn p) (snd (bspec j)).

  Import VectorNotations.

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
      (Vector.Forall2 (fun x y => sat (s, x) y) hs assns).
  Proof.
    induction[h] assns; intros h' hsat.
    - exists []; split; simpl in hsat.
      apply emp_is_emp in hsat; rewrite hsat; constructor.
      constructor.
    - simpl in hsat; destruct hsat as [h1 [h2 [H1 [H2 [hdis hplus]]]]].
      apply (IHassns h2) in H2; destruct H2 as [hs1 [heq1 hsat]].
      exists (h1 :: hs1); split.
      + remember (Pheap (pdisj_is_pheap hdis)) as ph2.
        assert (h' = ph2).
        { destruct h' as [h' ph']; simpl in hplus; rewrite Heqph2.
          destruct hplus.
          cutrewrite (ph' = pdisj_is_pheap (h1:=h1) (h2:=h2) hdis);[eauto | apply proof_irrelevance]. }
        rewrite H, Heqph2; econstructor; eauto.
      + constructor; eauto.
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
    disj_eq (get_hs hs) h -> Vector.Forall2 (fun x y => sat (s, snd x) y) hs assns -> 
    sat (s, h) (Aistar_v assns).
  Proof.
    intros heq hsat.
    induction [h heq assns hsat]hs; intros h' heq assns hsat.
    - assert (assns = []) by (apply (case0 (fun (v : t assn 0) => v = [])); eauto).
      simpl in heq; inversion heq.
      rewrite H; simpl; intros; simpl; unfold emp_h; eauto.
    - destruct (vinvS assns) as [a [assns' ha]]; subst.
      inversion hsat; subst. apply inj_pair2 in H1; apply inj_pair2 in H4; subst.
      destruct h; simpl in heq.
      inversion heq; subst; simpl in *; apply inj_pair2 in H2; subst.
      apply (IHhs ph ) in H5.
      repeat eexists; eauto. eauto.
  Qed.

  Lemma sync_barrier (n : nat) (s : stack) (hs : Vector.t pstate n) (h : pheap)
        (prs pss : Vector.t assn n) (bf1 : Vector.Forall (fun p => low_assn p) prs)
        (bf2 : Vector.Forall (fun p => low_assn p) pss) (heq : disj_eq (get_hs hs) h)
        (eq : forall st, sat st (Aistar_v prs) <-> sat st (Aistar_v pss))
        (hp : Vector.Forall2 (fun x y => sat (s, snd x) y) hs prs) :
    exists (hs' : Vector.t pheap n),
      disj_eq hs' h /\ Vector.Forall2 (fun x y => sat (s, x) y) hs' pss.
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
        (bf : Vector.Forall (fun p => low_assn p) ps) :
    Vector.Forall2 (fun st p => sat st p) sts ps <->
    Vector.Forall2 (fun st p => sat st p) (Vector.map (fun st => (s, snd st)) sts) ps.
  Proof.
    clear env_wf bspec.
    induction sts.
    - pose proof (vinv0 ps); subst; split; constructor.
    - pose proof (vinvS ps) as [pr [prs hpr]]; subst.
      split; intros Hsat; inversion Hsat; subst; apply inj_pair2 in H1; apply inj_pair2 in H4; 
      subst; constructor.
      + destruct low_eq as [leq _]; simpl in leq; destruct leq as [leq _].
        inversion bf; subst. apply inj_pair2 in H1; subst.
        unfold low_assn in H2.
        pose proof (H2 (s, snd h) h) as bw'; apply bw'; eauto.
      + apply IHsts; eauto.
        * simpl in low_eq; split; try tauto.
        * inversion bf; subst; eauto. apply inj_pair2 in H1; subst; eauto.
      + destruct low_eq as [leq _]; simpl in leq; destruct leq as [leq _].
        inversion bf; subst; eauto. apply inj_pair2 in H1; subst; eauto.
        pose proof (H2 (s, snd h) h) as bw'; apply bw'; eauto.
      + apply IHsts; eauto.
        * simpl in low_eq; split; try tauto.
        * inversion bf; subst; eauto. apply inj_pair2 in H1; subst; eauto.
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
        (hp : Vector.Forall2 (fun st y => sat st y) sts (fst (bspec j))) :
    exists (sts' : Vector.t pstate ngroup),
      disj_eq (get_hs sts') h /\ 
      get_ss sts' = get_ss sts /\
      Vector.Forall2 (fun st y => sat st y) sts' (snd (bspec j)).
  Proof.
    unfold env_wellformed, bwf in *; destruct env_wf as [bwf H]; clear env_wf.
    unfold jth_pre, jth_post in *; specialize (H j); (specialize (bwf j));
    destruct (bspec j) as [pres posts]; simpl in *.
    remember (get_hs sts) as phs; remember (get_ss sts) as ss.
    generalize dependent ngroup. clear bspec ngroup.
    destruct sts; intros phs phs_eq heq ss ss_eq ss_leq pres posts hsat bwf bwf'; simpl in *; subst.
    - exists [].
      simpl; repeat split; eauto.
      cutrewrite (posts = []); [subst; constructor | 
                                apply (case0 (fun (v : Vector.t assn 0) => v = [])); eauto].
    - pose proof (vinvS pres) as [pr [pres' Hpr]].
      pose proof (vinvS posts) as [ps [posts' Hps]].
      subst; simpl.
      destruct bwf0 as [bwf1 bwf2]; inversion bwf1; subst; inversion bwf2; subst.
      apply inj_pair2 in H1; apply inj_pair2 in H4; subst.
      rename H2 into hpr, H5 into hps, H6 into hposts, H3 into hpres.
      inversion hsat; subst.
      apply inj_pair2 in H1; apply inj_pair2 in H4; subst.
      rename H3 into hsathd, H5 into hsattl.
      remember (Vector.map (fun st => (fst h0, snd st)) (h0 :: sts)) as sts'.
      assert (Vector.Forall2 (fun st pr=> sat st pr) sts' (pr :: pres')).
      { rewrite Heqsts'; simpl; constructor; [destruct h0; eauto | ].
        subst; apply -> loweq_sat; eauto. }
      rewrite Heqsts' in H; apply ->forall2_map in H; simpl in H.
      eapply sync_barrier in H; eauto.
      destruct H as [hs' [heqq hsatq]].
      apply forall2_map in hsatq.
      remember (Vector.map2 (fun st h => (fst st, h)) (h0 :: sts) hs') as stq.
      assert (Vector.Forall2 (fun st ps => sat st ps) stq (ps :: posts')).
      { rewrite Heqstq; apply <-(loweq_sat (n := S n) (s := fst h0)); eauto.
        - rewrite map_map2.
          cutrewrite (Vector.map2 (fun x y => (fst h0, snd (fst x, y))) (h0 :: sts) hs' =
                      Vector.map (pair (fst h0)) hs'); [eauto | ].
          rewrite map2_map; eauto.
        - unfold get_ss; rewrite map_map2.
        rewrite map2_fst.
        simpl in ss_leq.
        simpl; repeat split; try tauto. }
      exists stq; repeat split; eauto.
      rewrite Heqstq; unfold get_hs; rewrite map_map2, map2_snd; eauto.
      rewrite Heqstq; unfold get_ss. rewrite map_map2, map2_fst; simpl; eauto.
  Qed.     
  
  Lemma finvS (n : nat) (i : Fin.t (S n)) : (i = Fin.F1 \/ exists i', i = Fin.FS i').
  Proof.
    apply (Fin.caseS (fun n (i : Fin.t (S n)) =>  i = Fin.F1 \/ (exists i' : Fin.t n, i = Fin.FS i'))).
    - intros n0; tauto.
    - intros n0 p; right; eexists; tauto.
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
End Barrier.

Section SeqCSL.
  Variable ngroup : nat.
  Variable bspec : barrier_spec ngroup.
  Variable env : var -> type.
  Hypothesis env_wf : env_wellformed bspec env.
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
             pdisj phP ph' /\ phplus phP ph' = ph /\ sat (s, ph') (pre_j tid j) /\
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
    clear Heqcps Heqcps' c ps c' ps'; induction hred as [|cps' cps'' hred]; eauto.
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

  Lemma pheap_eq (ph1 ph2 : pheap') (is_p1 : is_pheap ph1) (is_p2 : is_pheap ph2) :
    ph1 = ph2 -> Pheap is_p1 = Pheap is_p2.
  Proof.
    destruct 1.
    cutrewrite (is_p1 = is_p2); [eauto | apply proof_irrelevance ].
  Qed.

  Lemma disj_eq_fun (n : nat) (hs : Vt pheap n) (h h' : pheap) : 
    disj_eq hs h -> disj_eq hs h' -> h = h'.
  Proof.
    clear env_wf env bspec ngroup.
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
    clear env_wf env bspec ngroup; move: hs h h' i; induction n; 
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
    clear env_wf env bspec ngroup.
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
    clear env_wf env bspec ngroup; move: hs h i; induction n; 
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
          
  Definition nth (n : nat) (A : Type) (v : Vt A n):= Vector.nth v.
  Lemma step_inv (ks1 ks2 : kstate ngroup) (red_k : (ks1 ==>k* ks2)) (ph1 ph2 : heap) 
        (hs1 : Vector.t pheap ngroup) (ss1 : Vector.t stack ngroup) (c : cmd) :
    disj_eq hs1 (htop (snd ks1)) ->
    ss1 = get_ss_k ks1 -> low_eq_l2 env ss1 ->
    (forall tid : Fin.t ngroup, (get_cs_k ks1)[@tid] = c) ->
    (forall tid : Fin.t ngroup, safe_aux tid c (ss1[@tid]) (hs1[@tid])) ->
    exists (pss' : Vector.t pstate ngroup) (pss2 : Vector.t pstate ngroup) (c' : cmd) 
           (cs : Vector.t cmd ngroup) (h' : pheap), 
      disj_eq (get_hs pss') h' /\  low_eq_l2 env (get_ss pss') /\
      disj_eq (get_hs pss2) (htop (snd ks2)) /\ 
      (forall tid : Fin.t ngroup, 
         cs[@tid] = (get_cs_k ks2)[@tid] /\
         (get_ss pss2)[@tid] = (get_ss_k ks2)[@tid] /\
         safe_aux tid c' (fst pss'[@tid]) (snd pss'[@tid]) /\
         c' / (pss'[@tid]) ==>p* cs[@tid] / pss2[@tid]).
  Proof.
    intros hdis1 heq hloweq1 hc hsafe.
    apply clos_rt1n_rt, clos_rt_rtn1 in red_k.
    induction red_k as [| ks' ks2]. 
    Hint Unfold low_eq_l2 get_hs get_ss.
    Hint Rewrite map_map2 map2_fst' map2_snd'.
    - remember (Vector.map2 (fun s h => (s, h)) ss1 hs1) as pss'.
      exists pss', pss', c, (Vector.const c ngroup), (htop (snd ks1)).
      subst; repeat split; autounfold; autorewrite with core; eauto.
(*      + cutrewrite (get_hs (Vector.map2 (fun (s : stack) h => (s, h)) (get_ss_k ks1) hs1) = hs1); 
          [eauto | ].
        unfold get_hs; rewrite map_map2, map2_snd'; eauto.
      + autorewrite with core. unfold get_ss; rewrite map_map2, map2_fst'; eauto.
      + unfold get_hs; rewrite map_map2, map2_snd'; eauto. *)
      + rewrite const_nth; pose proof (hc tid); eauto.
(*      + unfold get_ss_k, get_ss; rewrite map_map2, map2_fst'; eauto.*)
      + assert ((Vector.map2 (fun (s : stack) h => (s, h)) (get_ss_k ks1) hs1)[@tid] = 
                ((get_ss_k ks1)[@tid], hs1[@tid])); erewrite nth_map2; eauto.
      + rewrite const_nth; econstructor.
    - generalize dependent ks'. intros ks' H; case H.
      intros ? ss c1 c2 st1 st2 s1 s2 h1 h2 tid ? sstid red' ? ? red_k IHred_k; subst.
      destruct IHred_k as [pss' [pss2 [c' [cs [h' [H1 [H2 [H3 H4]]]]]]]]; simpl in *.
      destruct (H4 tid) as [Hi1 [Hi2 [Hi3 Hi4]]].
      assert (cs[@tid] = c1) as Hceq.
      { unfold get_cs_k in Hi1; simpl in Hi1. rewrite Hi1.
        rewrite (Vector.nth_map _ _ tid tid); eauto; rewrite sstid; eauto. }
      assert (fst pss2[@tid] = s1) as Hseq.
      { unfold get_ss_k, get_ss in Hi2; simpl in Hi2; 
        rewrite !(Vector.nth_map _ _ tid tid), sstid in Hi2; eauto; simpl in Hi2. }
      rewrite <-Hceq,<-Hseq in red'.
      pose proof (safe_inv' Hi3 Hi4) as hsafei.
      remember (replace cs tid c2) as cs'.
      remember (replace pss2 tid (s2 ?)) as pss2'.
End BDF.