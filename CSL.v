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
  Definition pre_j  (j : nat) (tid : Fin.t ngroup) := Vector.nth (fst (bspec j)) tid.
  Definition post_j (j : nat) (tid : Fin.t ngroup) := Vector.nth (snd (bspec j)) tid.

  Definition low_assn (P : assn) : Prop := 
    forall (x : var) (v : Z) (st st' : pstate) , 
      low_eq env (fst st) (fst st') -> (sat st P <-> sat st' P).

  (* fv(bspec) \cup V_hi = \empty *)
  Definition bwf := forall (j : nat) (tid : Fin.t ngroup), 
      low_assn (Vector.nth (fst (bspec j)) tid) /\
      low_assn (Vector.nth (snd (bspec j)) tid).


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
      | x :: xs => low_eq env s x /\ low_eq_l x xs
    end.
  Fixpoint low_eq_l2 (ng : nat) (sts : Vector.t stack ng) :=
    match sts with
      | [] => True
      | x :: xs => low_eq_l x xs /\ low_eq_l2 xs
    end.

  Lemma aistar_eq (n : nat) (s : stack) (assns : Vector.t assn n) (hs : Vector.t pheap n) 
        (h : pheap) :
    disj_eq hs h -> Vector.Forall2 (fun x y => sat (s, x) y) hs assns -> 
    sat (s, h) (Aistar_v assns).
  Proof.
    intros heq hsat.
    induction heq.
    - assert (assns = []) by (apply (case0 (fun (v : t assn 0) => v = [])); eauto).
      rewrite H; simpl.
      intros x; unfold emp_h; simpl; eauto.
    - inversion hsat; subst.
      apply inj_pair2 in H1; apply inj_pair2 in H2.
      rewrite H1 in H4.
      apply (IHheq _) in H4.
      simpl.
      repeat eexists; eauto.
  Qed.

  Lemma sync_barrier (s : stack) (hs : Vector.t pheap ngroup) (j : nat) (h : pheap)
        (heq : disj_eq hs h)
        (hp : Vector.Forall2 (fun x y => sat (s, x) y) hs (fst (bspec j))) :
    exists (hs' : Vector.t pheap ngroup),
      disj_eq hs' h /\ Vector.Forall2 (fun x y => sat (s, x) y) hs' (snd (bspec j)).
  Proof.
    unfold env_wellformed, bwf in *; destruct env_wf as [_ H]; clear env_wf.
    unfold jth_pre, jth_post in *; specialize (H j);
    destruct (bspec j) as [pres posts]; simpl in *.
    eapply (aistar_eq heq) in hp.
    apply H in hp.
    apply aistar_disj in hp.
    des; repeat eexists; eauto.
  Qed.

End Barrier.

Section SeqCSL.
  Fixpoint safe_s (n : nat) (c : cmd) (s : stack) (ph : pheap) (q : assn) :=
    match n with
      | O => True
      | S n => 
        (c = Cskip -> sat (s, ph) q) /\

        (forall (hf : pheap) (h : heap), 
           (pdisj ph hf) -> ptoheap (phplus ph hf) h -> ~aborts c (s, h)) /\

        Lang.PLang.access_ok c s ph /\ write_ok c s ph /\

        (forall (hF : pheap) (h : heap) (c' : cmd) (ss' : state),
           (pdisj ph hF) -> (ptoheap (phplus ph hF) h ->
           (c / (s, h) ==>s c' / ss') ->
           exists h' (ph' : pheap),
             snd ss' = h' /\ pdisj ph' hF /\ ptoheap (phplus ph' hF) h' /\
             safe_s n c' (fst ss') ph' q)) /\
          
        (forall j c', wait c = Some (j, c') ->
           exists (phP ph' : pheap), 
             pdisj phP ph' /\ phplus phP ph' = ph /\ sat (s, ph') pre_j /\
             (forall (phQ : pheap) (H : pdisj phQ ph'), sat (s, phQ) post_j ->
                safe_s n c' s (phplus_pheap H) q))
    end.
  
  Definition CSL (p : assn) (c : cmd) (q : assn) := 
    (exists g, typing_cmd g c Lo) /\ wf_cmd c /\ 
    forall n, (forall s ph, sat (s, ph) p -> safe_s n c s ph q).

End SeqCSL.
