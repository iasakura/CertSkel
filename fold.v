Require Import QArith.
Require Import Qcanon.
Require Import MyVector.
Require Import List.
Require Import ZArith.
Add LoadPath "../../src/cslsound".
Require Import Lang.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import PHeap.
Require Import Bdiv.
Require Import CSL.

Close Scope Qc_scope.
Close Scope Q_scope.

Section Fold.
  Notation tid := (0%Z : var).
  Notation x := (1%Z : var).
  Notation y := (2%Z : var).
  Notation r := (3%Z : var).
  Notation arr := (4%Z : var).

  Variable n : Z.
  Variable ntrd : nat.

  Bind Scope exp_scope with exp.
  Bind Scope bexp_scope with bexp.
  
  Infix "+" := (Eplus) : exp_scope.
  Infix "<" := (Blt) : bexp_scope.
  Infix "==" := (Beq) : bexp_scope.
  Coercion Evar : var >-> exp.
  Coercion Enum : Z >-> exp.
  Open Scope exp_scope.
  Open Scope bexp_scope.

  Fixpoint is_array (e : exp) (n : nat) (f : nat -> Z) :=
    match n with
      | 0 => Aemp
      | S n' => Adisj (Aex (fun v => Apointsto 1%Qc (e + Z.of_nat n) v))
                      (is_array e n' f)
    end.


  Bind Scope assn_scope with assn.
  Notation "P '//\\' Q" := (fun s h => P s h /\ Q s h) (at level 80, right associativity) : assn_scope.
  Notation "x '===' y" := 
    (fun s h => edenot x s = edenot y s) (at level 70, no associativity) 
    : assn_scope.
  Notation "'existS' x .. y , p" := 
    (fun s h => ex (fun x => .. (ex (fun y => p s h)) ..))
      (at level 200, x binder, y binder, right associativity) : assn_scope.
  Notation "e1 '-->p' ( p ,  e2 )" := (Apointsto p e1 e2) (at level 75) : assn_scope.
  Delimit Scope assn_scope with assn.

  Definition nat_of_fin (i : Fin.t ntrd) : nat := projT1 (Fin.to_nat i).
  Definition Z_of_fin (i : Fin.t ntrd) : Z := Z.of_nat (nat_of_fin i).

  Section Rotate.
    Notation ntrdZ := (Z_of_nat ntrd).
    Definition rotate := 
      x ::= [arr + tid] ;;
      Cbarrier 0 ;;
      Cif (r == ntrdZ) (
        y ::= 0%Z
      ) (
        y ::= tid + 1%Z
      ) ;;
      [arr + y] ::= x.
    Definition Pre := is_array arr (ntrd + 1) (fun i => Z.of_nat i).
    Definition Post := is_array arr (ntrd + 1) (fun i : nat => (Z.of_nat i - 1) mod ntrdZ)%Z.
    Definition Pre_i := (arr + tid -->p (1%Qc, tid))%assn.
    Definition Post_i := (arr + ((tid + 1) mod ntrdZ)%Z -->p (1%Qc, tid))%assn.
    
    Definition E (var : var) := 
      if Z.eq_dec var tid then Hi
      else if Z.eq_dec var x then Hi
      else if Z.eq_dec var y then Hi
      else Lo.

    Definition bpre (tid : Fin.t ntrd) := 
      (arr + (Z_of_fin tid) -->p (1%Qc, Z_of_fin tid))%assn.
    Definition bpost (tid : Fin.t ntrd) := 
      (arr + (((Z_of_fin tid) + 1) mod ntrdZ)%Z -->p (1%Qc, Z_of_fin tid))%assn.

    Lemma pre_lassn (tid : Fin.t ntrd) : low_assn E (bpre tid).
    Proof.
      unfold low_assn, Bdiv.low_assn, indeP, bpre, low_eq, E in *; intros s1 s2 h Hleq; simpl.
      cutrewrite (s1 4%Z = s2 4%Z); [| apply Hleq; simpl; eauto].
      split; intros H x; eauto.
    Qed.

    Lemma post_lassn (tid : Fin.t ntrd) : low_assn E (bpost tid).
    Proof.
      unfold low_assn, Bdiv.low_assn, indeP, bpost, low_eq, E in *; intros s1 s2 h Hleq; simpl.
      cutrewrite (s1 4%Z = s2 4%Z); [| apply Hleq; simpl; eauto].
      split; intros H x; eauto.
    Qed.

    Notation FalseP := (fun (_ : stack) (h : pheap) => False).

    Definition default : (Vector.t assn ntrd * Vector.t assn ntrd) := 
      (init (fun _ => FalseP), init (fun _ => FalseP)).

    Lemma FalseP_lassn (E' : env) : low_assn E' FalseP.
    Proof.
      unfold low_assn, Bdiv.low_assn, indeP; intros; tauto.
    Qed.

    Definition bspec (i : nat) :=
      match i with
        | 0 => (init bpre, init bpost)
        | S _ => default
      end.

    Lemma bpre_lassn (i : nat) :
      (forall tid : Fin.t ntrd, low_assn E (Vector.nth (fst (bspec i)) tid)) /\
      (forall tid : Fin.t ntrd, low_assn E (Vector.nth (snd (bspec i)) tid)).
    Proof.
      Hint Resolve FalseP_lassn pre_lassn post_lassn.
      split; intros tid; destruct i; simpl; rewrite init_spec; eauto.
    Qed.

    Lemma default_wf (s : stack) (h : pheap) : 
      Aistar_v (fst default) s h <-> Aistar_v (snd default) s h.
    Proof.
      cutrewrite (fst default = snd default); [tauto | unfold default; eauto].
    Qed.
    Import VectorNotations.
    Lemma swap_wf : 
      forall (m : nat) (s : stack) (h : pheap) (p : assn) (ps : Vector.t assn m) (i : Fin.t m),
        Aistar_v (p :: ps) s h -> Aistar_v (ps[@i] :: (Vector.replace ps i p)) s h.
    Proof.
      induction m; intros s h p ps i; [rewrite (vinv0 ps); inversion i | ].
      destruct (vinvS ps) as (p' & ps' & ?); subst. 
      destruct (finvS i) as [|[i' ?]]; subst; [simpl |].
      - intros (ph1 & ph2 & Hp1 & (ph3 & ph4 & Hp3 & Hp4 & Hd34 & Heq34) & Hdis12 & Heq12).
        assert (pdisj ph1 ph4) as Hdis14.
        { rewrite <-Heq34 in Hdis12; apply pdisjE2 in Hdis12; eauto. }
        exists ph3, (phplus_pheap Hdis14); repeat split; eauto.
        + exists ph1, ph4; repeat split; eauto.
        + simpl; apply pdisj_padd_comm; [rewrite Heq34|]; eauto.
        + simpl; rewrite padd_left_comm, Heq34; eauto.
          apply pdisj_padd_comm; [rewrite Heq34|]; eauto.
      - intros (ph1 & ph2 & Hp1 & (ph3 & ph4 & Hp3 & Hp4 & Hd34 & Heq34) & Hdis12 & Heq12); simpl.
        assert (pdisj ph1 ph4) as Hdis14.
        { rewrite <-Heq34 in Hdis12; apply pdisjE2 in Hdis12; eauto. }
        assert (Aistar_v (p :: ps') s (phplus_pheap Hdis14)) as H14.
        { simpl; repeat eexists; eauto. }
        destruct (IHm _ _ _ _ i' H14) as (ph1' & ph4' & H1' & H4' & Hdis14' & Heq14').
        simpl in Heq14'.
        assert (pdisj ph3 (phplus ph1' ph4')) as Hdis314'.
        { rewrite <-Heq34 in Hdis12. apply pdisj_padd_comm in Hdis12; eauto.
          rewrite <-Heq14' in Hdis12; eauto. }
        assert (pdisj ph3 ph4') as Hdis34'.
        { apply pdisjE2 in Hdis314'; eauto. }
        exists ph1', (phplus_pheap Hdis34'); repeat split; eauto.
        exists ph3, ph4'; repeat split; eauto.
        + simpl; apply pdisj_padd_comm; eauto.
        + simpl. rewrite padd_left_comm, Heq14', padd_left_comm, Heq34; eauto.
          apply pdisj_padd_comm; [rewrite Heq34; eauto | eauto].
    Qed.

    Lemma bijectS : forall (m : nat) (f g : Fin.t (S m) -> Fin.t (S m)),
      (forall i : Fin.t (S m), f (g i) = i) ->
      (forall i : Fin.t (S m), g (f i) = i) ->
      f Fin.F1 = Fin.F1 ->
      exists f' g' : Fin.t m -> Fin.t m,
        (forall i : Fin.t m, f (Fin.FS i) = Fin.FS (f' i)) /\
        (forall i : Fin.t m, g (Fin.FS i) = Fin.FS (g' i)) /\
        (forall i : Fin.t m, f' (g' i) = i) /\
        (forall i : Fin.t m, g' (f' i) = i).
    Proof.
      intros m f g Hfg Hgf H.
      assert (forall i : Fin.t m, exists v, f (Fin.FS i) = Fin.FS v) as HfS.
      { intros i.
        remember (f (Fin.FS i)) as fSi; destruct (finvS (f (Fin.FS i))) as [HfS| [v ?]]; subst;
        [| exists v; congruence].
        pose proof (Hgf Fin.F1) as Hgf1; pose proof (Hgf (Fin.FS i)) as HgfS.
        rewrite H in Hgf1; rewrite HfS in HgfS; rewrite HgfS in Hgf1; inversion Hgf1. }
      apply vec_exvec in HfS as [vf Hvf].
      assert (forall i : Fin.t m, exists v, g (Fin.FS i) = Fin.FS v) as HgS.
      { intros i.
        pose proof (Hgf Fin.F1) as Hg1; rewrite H in Hg1.
        remember (g (Fin.FS i)) as gSi; destruct (finvS (g (Fin.FS i))) as [HgS| [v ?]]; subst;
        [| exists v; congruence].
        pose proof (Hfg Fin.F1) as Hfg1; pose proof (Hfg (Fin.FS i)) as HfgS.
        rewrite Hg1 in Hfg1; rewrite HgS in HfgS; rewrite HfgS in Hfg1; inversion Hfg1. }
      apply vec_exvec in HgS as [vg Hvg].
      exists (fun i => vf[@i]), (fun i => vg[@i]); repeat split; eauto.
      + assert (forall i : Fin.t m, Fin.FS vf[@ vg[@i] ] = Fin.FS i) as HeqS.
        { intros i; rewrite <-Hvf, <-Hvg, <-Hfg; eauto. }
        intros i; specialize (HeqS i); inversion HeqS; apply inj_pair2 in H1; eauto.
      + assert (forall i : Fin.t m, Fin.FS vg[@ vf[@i] ] = Fin.FS i) as HeqS.
        { intros i; rewrite <-Hvg, <-Hvf, <-Hgf; eauto. }
        intros i; specialize (HeqS i); inversion HeqS; apply inj_pair2 in H1; eauto.
    Qed.

    Lemma biject_wf : forall (m : nat) (s : stack) (h : pheap) (ps qs : Vector.t assn m) 
          (f : Fin.t m -> Fin.t m) (g : Fin.t m -> Fin.t m),
      (forall i : Fin.t m, f (g i) = i) ->
      (forall i : Fin.t m, g (f i) = i) ->
      qs = init (fun i : Fin.t m => ps[@(f i)]) ->
      (Aistar_v ps s h -> Aistar_v qs s h).
    Proof.
      induction m; intros s h ps qs f g Hfg Hgf HeqQP; [rewrite (vinv0 ps), (vinv0 qs); simpl; tauto |].
      destruct (vinvS ps) as (p & ps' & ?), (vinvS qs) as (q & qs' & ?); subst; intros Hps.
      assert (init (fun i : Fin.t (S m) => (p :: ps')[@f i]) =
              (p :: ps')[@f Fin.F1] :: init (fun i : Fin.t m => (p :: ps')[@f (Fin.FS i)])) as Heq.
      { apply eq_nth_iff; intros p1 p2 ?; subst; rewrite !init_spec.
        destruct (finvS p2) as [|[p' ?]]; subst; eauto.
        simpl; rewrite init_spec; eauto. }
      rewrite Heq; clear Heq.
      destruct (finvS (f Fin.F1)) as [H1 | [i' H1]].
      - rewrite H1.
        apply (bijectS (g := g)) in H1 as (f' & g' & Hf' & Hg' & Hfg' & Hgf'); eauto.
        cutrewrite (init (fun i : Fin.t m => (p :: ps')[@f (Fin.FS i)]) =
                    init (fun i : Fin.t m => ps'[@f' i])); 
          [| apply Vector.eq_nth_iff; intros p1 p2 ?; subst; rewrite !init_spec; rewrite Hf'; eauto].
        simpl in Hps; simpl; destruct Hps as (ph1 & ph2 & Hsat1 & Hsat2 & Hdis & Heq12).
        exists ph1, ph2; repeat split; eauto.
      - apply (swap_wf i') in Hps; rewrite H1.
        destruct Hps as (ph1 & ph2 & Hsat1 & Hsat2 & Hdis & Heq12).
        exists ph1, ph2; repeat split; eauto.
        set (f' := fun i : Fin.t m =>
               match f (Fin.FS i) in Fin.t k return Fin.t (Peano.pred k) ->Fin.t (Peano.pred k) with 
                 | Fin.F1 _ => fun i' => i'
                 | Fin.FS _ m => fun _ => m
               end i' : Fin.t m).
        assert (init (fun i : Fin.t m => (p :: ps')[@f (Fin.FS i)]) = 
                init (fun i : Fin.t m => (replace ps' i' p)[@i])).
        apply eq_nth_iff; intros ? i ?; subst; rewrite !init_spec, replace_nth.
        destruct (fin_eq_dec i' i); subst.
        apply (IHm _ _ _ _ _ g' _ _ _ Hsat2).

      destruct Hps as (h1 & h2 & Hsat1 & Hsat2 & Hdis12 & Heq12).
      assert (forall i : Fin.t m, exists fSi : Fin.t m,
                f (Fin.FS i) = Fin.FS fSi).
      { intros i; destruct (finvS (f (Fin.FS i))) as [H |]; eauto.
        destruct (Hbi (Fin.FS i)) as [_ Hgf], (Hbi (Fin.F1)) as [_ Hgf1].
        rewrite H in Hgf; rewrite H1 in Hgf1. 
        rewrite Hgf in Hgf1; inversion Hgf1. }
      apply vec_exvec in H as [fSi Hfi].
      assert (forall i : Fin.t m, exists gSi : Fin.t m,
                g (Fin.FS i) = Fin.FS gSi).
      { intros i; destruct (finvS (g (Fin.FS i))) as [H |]; eauto.
        destruct (Hbi Fin.F1) as [_ Hgf1]; rewrite H1 in Hgf1.
        destruct (Hbi (Fin.FS i)) as [Hfg _], (Hbi (Fin.F1)) as [Hfg1 _].
        rewrite H in Hfg; rewrite Hgf1 in Hfg1. 
        rewrite Hfg in Hfg1; inversion Hfg1. }
      apply vec_exvec in H as [gSi Hgi].
      

    Lemma barrier_wf (i : nat) (st : pstate) :
       Aistar_v (fst (bspec i)) (fst st) (snd st) <-> Aistar_v (snd (bspec i)) (fst st) (snd st).
    Proof.
      destruct i; simpl; [|apply default_wf].
      unfold bpre, bpost, Z_of_fin, nat_of_fin. induction ntrd.
      - split; simpl; intros H x; apply H.
      - 
  Section FoldDef.
    Definition fold :=
      r ::= n ;;
      Cwhile (Bnot (r < 1%Z)) (
        Cif (tid < (Ediv2 r)) (
          x ::= [arr + tid + Ediv2 r] ;;
          y ::= [arr + tid] ;;
          [arr + tid] ::= x + y
        ) Cskip
      ) ;;
      Cbarrier 0;;
      r ::= Ediv2 r.
  End FoldDef.
  
  Hypothesis n_pow2 : exists e : Z, n = two_p e.
  


  Definition preP :=
    (tid 
  Definition preP_tid (i : Fin.t ntrd) := 
    (tid === Z_of_fin i //\\
    (arr + Z_of_fin i) -->p (1%Qc, f (nat_of_fin i)))%assn.

End Fold.
