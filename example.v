Require Import QArith.
Require Import Qcanon.
Require Import MyVector.
Require Import List.
Require Import ZArith.

Require Import Lang.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import PHeap.
Require Import Bdiv.
Require Import CSL.

Close Scope Qc_scope.
Close Scope Q_scope.

Section Example.
  Notation TID := (0%Z : var).
  Notation X := (1%Z : var).
  Notation Y := (2%Z : var).
  Notation R := (3%Z : var).
  Notation ARR := (4%Z : var).

  Variable ntrd : nat.

  Bind Scope exp_scope with exp.
  Bind Scope bexp_scope with bexp.
  
  Infix "+" := (Eplus) : exp_scope.
  Infix "<" := (Blt) : bexp_scope.
  Infix "==" := (Beq) : bexp_scope.
  Open Scope exp_scope.
  Open Scope bexp_scope.

  Bind Scope assn_scope with assn.
  Notation "P '//\\' Q" := (fun s h => P s h /\ Q s h) (at level 80, right associativity).
  Notation "P1 ** P2" := (Astar P1 P2) (at level 70, right associativity).
  Notation "x '===' y" := 
    (fun s h => edenot x s = edenot y s) (at level 70, no associativity).
  Notation "'existS' x .. y , p" := 
    (fun s h => ex (fun x => .. (ex (fun y => p s h)) ..))
      (at level 200, x binder, y binder, right associativity).
  Notation "e1 '-->p' ( p ,  e2 )" := (Apointsto p e1 e2) (at level 75).
  Notation Emp := (fun s h => forall x, this h x = None).
  Notation "!( P )" := (Emp //\\ P).
  Delimit Scope assn_scope with assn.

  Fixpoint is_array (e : exp) (n : nat) (f : nat -> Z) :=
    match n with
      | 0 => Aemp
      | S n' => e + Enum (Z.of_nat n') -->p (1%Qc, Enum (f n')) **
                is_array e n' f
    end.

  Definition nat_of_fin (i : Fin.t ntrd) : nat := proj1_sig (Fin.to_nat i).
  Definition Z_of_fin (i : Fin.t ntrd) : Z := Z.of_nat (nat_of_fin i).

  Section Rotate.
    Notation ntrdZ := (Z_of_nat ntrd).

    Definition rotate := 
      X ::= [Evar ARR + Evar TID] ;;
      Cbarrier 0 ;;
      Cif (Evar TID == Enum (ntrdZ - 1)) (
        Y ::= Enum 0%Z
      ) (
        Y ::= Evar TID + Enum 1%Z
      ) ;;
      [Evar ARR + Evar Y] ::= Evar X.

    Definition Pre := is_array (Evar ARR) ntrd (fun i => Z.of_nat i).
    Definition Post := is_array (Evar ARR) ntrd (fun i : nat => (Z.of_nat i - 1) mod ntrdZ)%Z.

    Definition Pre_i (i : Fin.t ntrd) := 
      (Evar ARR + Enum (Z_of_fin i)  -->p (1%Qc, Enum (Z_of_fin i)))%assn.
    Definition Post_i (i : Fin.t ntrd) := 
      (Evar ARR + ((Enum ((Z_of_fin i + 1) mod ntrdZ))%Z)  -->p (1%Qc, Enum (Z_of_fin i)))%assn.

    Definition E (var : var) := 
      if Z.eq_dec var TID then Hi
      else if Z.eq_dec var X then Hi
      else if Z.eq_dec var Y then Hi
      else Lo.

    Definition bpre (tid : Fin.t ntrd) := 
      (Evar ARR + Enum (Z_of_fin tid) -->p (1%Qc, Enum (Z_of_fin tid)))%assn.
    Definition bpost (tid : Fin.t ntrd) := 
      (Evar ARR + Enum ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p (1%Qc, Enum ((Z_of_fin tid + 1) mod ntrdZ)%Z)%assn.

    Lemma pre_lassn (tid : Fin.t ntrd) : low_assn E (bpre tid).
    Proof.
      unfold low_assn, Bdiv.low_assn, indeP, bpre, low_eq, E in *; intros s1 s2 h Hleq; simpl.
      rewrite Hleq; simpl; eauto.
      split; intros x H; eauto.
    Qed.

    Lemma post_lassn (tid : Fin.t ntrd) : low_assn E (bpost tid).
    Proof.
      unfold low_assn, Bdiv.low_assn, indeP, bpost, low_eq, E in *; intros s1 s2 h Hleq; simpl.
      rewrite Hleq; simpl; eauto.
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

    Lemma prei_lassn : forall tid : Fin.t ntrd, low_assn E (Vector.nth (init Pre_i) tid).
    Proof.
      unfold low_assn, Bdiv.low_assn, indeP, E, Pre_i, low_eq; simpl; intros; rewrite init_spec.
      cutrewrite (s1 4%Z = s2 4%Z); [split; intros; eauto|rewrite H; eauto].
    Qed.

    Lemma posti_lassn : forall tid : Fin.t ntrd, low_assn E (Vector.nth (init Post_i) tid).
    Proof.
      unfold low_assn, Bdiv.low_assn, indeP, E, Post_i, low_eq; simpl; intros; rewrite init_spec.
      cutrewrite (s1 4%Z = s2 4%Z); [split; intros; eauto|rewrite H; eauto].
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
                init (fun i : Fin.t m => (replace ps' i' p)[@f' i]))as Heq.
        { apply eq_nth_iff; intros ? i ?; subst; rewrite !init_spec, replace_nth.
          unfold f'.
          destruct (finvS (f (Fin.FS i))) as [Heq | [fi Heq]]; subst; rewrite Heq; simpl.
          + destruct (fin_eq_dec i' i'); congruence.
          + destruct (fin_eq_dec i' fi); try congruence.
            rewrite <-e in Heq.
            pose proof (Hgf (Fin.FS i)) as Hc1;  pose proof (Hgf (Fin.F1)) as Hc2.
            rewrite Heq in Hc1; rewrite H1 in Hc2; rewrite Hc1 in Hc2; inversion Hc2. }
        assert (exists j', g Fin.F1 = Fin.FS j') as [j' Hg1].
        { destruct (finvS (g Fin.F1)) as [Heqg | [j' Heqg']]; [|exists j'; eauto]. 
          specialize (Hfg Fin.F1); rewrite Heqg in Hfg; rewrite H1 in Hfg; inversion Hfg. }
        set (g' := fun i : Fin.t m =>
               match
                 g (Fin.FS i) in (Fin.t k)
                 return (Fin.t (Peano.pred k) -> Fin.t (Peano.pred k))
               with
                 | Fin.F1 n0 => fun i => i
                 | Fin.FS n0 m0 => fun _ : Fin.t (Peano.pred (S n0)) => m0
               end j').
        assert (forall i : Fin.t m, f' (g' i) = i).
        { intros i; unfold f', g'.
          destruct (finvS (g (Fin.FS i))) as [Heq' | [gi Heq']]; rewrite Heq'.
          rewrite <-Hg1, Hfg.
          specialize (Hfg (Fin.FS i)); rewrite Heq', H1 in Hfg; inversion Hfg; apply inj_pair2 in H2;
          congruence.
          rewrite <-Heq'; rewrite Hfg; eauto. }
        assert (forall i : Fin.t m, g' (f' i) = i).
        { intros i; unfold f', g'.
          destruct (finvS (f (Fin.FS i))) as [Heq' | [fi Heq']]; rewrite Heq'.
          rewrite <-H1, Hgf.
          specialize (Hgf (Fin.FS i)); rewrite Heq', Hg1 in Hgf; inversion Hgf; apply inj_pair2 in H3;
          congruence.
          rewrite <-Heq'; rewrite Hgf; eauto. }
        apply (IHm _ _ _ _ f' g' H H2 Heq Hsat2).
    Qed.

    Lemma fin_dec (n : nat) (P : Fin.t n -> Prop) (P_dec : forall i : Fin.t n, {P i} + {~ P i}):
      (forall i : Fin.t n, P i) + ({i : Fin.t n | ~ P i}).
    Proof.
      induction n; [left; intros i; inversion i| ].
      destruct (P_dec Fin.F1) as [Hp1 | Hp1].
      destruct (IHn (fun i : Fin.t n => P (Fin.FS i))) as [Hps1 | Hps1].
      - intros i; apply (P_dec (Fin.FS i)).
      - left; intros i; destruct (finvS i) as [? | [i' ?]]; subst; eauto.
      - right; destruct Hps1 as [i Hc]; exists (Fin.FS i); eauto.
      - right; exists Fin.F1; eauto.
    Qed.

    Lemma fin_dec_ex (n : nat) (P : Fin.t n -> Prop) (P_dec : forall i : Fin.t n, {P i} + {~ P i}):
      (forall i : Fin.t n, ~ P i) + ({i : Fin.t n | P i}).
    Proof.
      destruct (@fin_dec _ (fun i => ~ P i)); firstorder.
    Qed.

    Notation predn := Peano.pred.
(*
    Lemma inject_inverse (n : nat) (f : Fin.t n -> Fin.t n) :
      (forall i j, f i = f j -> i = j) ->
      forall v : Fin.t n, { i : Fin.t n | f i = v }.
    Proof.
      induction n; intros Hinj v; [inversion v | ].
      destruct (@fin_dec_ex _ (fun i => f i = v)).
      - intros i; apply fin_eq_dec.
      - set (f' := fun (i : Fin.t n) => match f i with
                                          | Fin.F1 => f (Fin.F1)*)
    Require Import Coq.Program.Equality.
    Lemma inject_biject (n : nat) (f : Fin.t n -> Fin.t n) :
      (forall i j, f i = f j -> i = j) ->
      exists g : Fin.t n -> Fin.t n,
        (forall i, f (g i) = i) /\
        (forall i, g (f i) = i).
    Proof.
      induction n; intros Heq.
      - exists (fun i : Fin.t 0 => match i with end); split; intros i; inversion i.
      - destruct (finvS (f Fin.F1)) as [Heqf1| [f1' Heqf1]].
        + assert (forall i : Fin.t n, {v| f (Fin.FS i) = Fin.FS v}).
          { intros i. destruct (finvS (f (Fin.FS i))) as [HeqfS|[fS HeqfS]].
            - rewrite <-HeqfS in Heqf1; apply Heq in Heqf1; rewrite Heqf1 in HeqfS; inversion HeqfS.
            - exists fS; eauto. }
          set (f' := fun (i : Fin.t n) => let (fSi, eq) := H i in fSi).
          assert (forall i j : Fin.t n, f' i = f' j -> i = j) as f'inj.
          { unfold f'; intros i j Heqf'ij; destruct (H i) as [f'i Heqi'], (H j) as [f'j Heqj'].
            rewrite Heqf'ij in Heqi'; rewrite <-Heqi' in Heqj'; apply Heq in Heqj'; inversion Heqj'.
            apply inj_pair2 in H1; congruence. }
          apply IHn in f'inj as (g' & HS1 & HS2).
          exists (fun (i : Fin.t (S n)) => match i in Fin.t n' return 
                                                 (Fin.t (predn n') -> Fin.t (predn n')) -> Fin.t n' with
                                             | Fin.F1 _ => fun _ => Fin.F1
                                             | Fin.FS _ i' => fun g' => Fin.FS (g' i')
                                           end g').
          split; intros i; destruct (finvS i) as [? | [i' ?]]; subst; simpl; eauto.
          * specialize (HS1 i').
            unfold f' in HS1, HS2; destruct (H (g' i')) as [v Hveq]; congruence.
          * rewrite Heqf1; eauto. 
          * specialize (HS2 i').
            unfold f' in HS1, HS2; destruct (H i') as [v Hveq]. rewrite Hveq; congruence.
        + set (f' := fun i : Fin.t n => match f (Fin.FS i) in Fin.t n' return 
                                              Fin.t (predn n') ->
                                              Fin.t (predn n') with
                                          | Fin.F1 _ => fun f1' => f1'
                                          | Fin.FS _ j => fun _ => j
                                        end f1').
          assert (forall i j : Fin.t n, f' i = f' j -> i = j).
          { unfold f'; intros i j Heq'.
            remember (f (Fin.FS i)) as fSi; remember (f (Fin.FS j)) as fSj.
            dependent destruction fSi; dependent destruction fSj; eauto.
            rewrite HeqfSi in HeqfSj; apply Heq in HeqfSj; inversion HeqfSj.
            apply inj_pair2; eauto.
            rewrite <-Heq' in HeqfSj; rewrite HeqfSj in Heqf1; apply Heq in Heqf1; inversion Heqf1.
            rewrite Heq' in HeqfSi; rewrite HeqfSi in Heqf1; apply Heq in Heqf1; inversion Heqf1.
            rewrite Heq' in HeqfSi; rewrite HeqfSi in HeqfSj; apply Heq in HeqfSj; inversion HeqfSj.
            apply inj_pair2 in H0; eauto. }
          destruct (IHn _ H) as (g & Hfg & Hgf).
          exists (fun (i : Fin.t (S n)) => 
                    if fin_eq_dec (f Fin.F1) i then Fin.F1
                    else match i in Fin.t n return 
                               (Fin.t (predn n) -> Fin.t (predn n)) -> (Fin.t (predn n)) -> 
                               Fin.t n
                         with
                           | Fin.F1 _ => fun g f1' => Fin.FS (g f1')
                           | Fin.FS _ i' => fun g _ => Fin.FS (g i')
                         end g f1').
          split; intros i; [destruct (fin_eq_dec (f Fin.F1) i); subst; eauto|
                            destruct (fin_eq_dec (f Fin.F1) (f i)) ].
          * destruct (finvS i) as [? | [i' ?]]; subst; eauto.
            { unfold f' in Hfg; specialize (Hfg f1').
              destruct (finvS (f (Fin.FS (g f1')))) as [?| [x Heqx]]; eauto.
              rewrite Heqx in Hfg.
              rewrite Hfg, <-Heqf1 in Heqx; apply Heq in Heqx; inversion Heqx. }
            { specialize (Hfg i'); unfold f' in Hfg.
              destruct (finvS (f (Fin.FS (g i')))) as [Heqx | [x Heqx]]; rewrite Heqx in Hfg.
              rewrite Hfg in Heqf1; congruence.
              rewrite Hfg in Heqx; eauto. }
          * apply Heq; eauto.
          * destruct (finvS (f i)) as [Heqfi | [fi Heqfi]]; rewrite Heqfi.
            { specialize (Hfg f1'); unfold f' in Hfg.
              destruct (finvS (f (Fin.FS (g f1')))) as [Heqx | [x Heqx]]; rewrite Heqx in Hfg.
              - rewrite <-Heqfi in Heqx; apply Heq; eauto.
              - rewrite Hfg,<-Heqf1 in Heqx; apply Heq in Heqx; inversion Heqx.  }
            { specialize (Hfg fi); unfold f' in Hfg.
              destruct (finvS (f (Fin.FS (g fi)))) as [Heqx | [x Heqx]]; rewrite Heqx in Hfg.
              - rewrite <-Hfg,<-Heqf1 in Heqfi; congruence.
              - apply Heq. simpl; rewrite Hfg in Heqx; rewrite Heqx; congruence. }
    Qed.

    Lemma plusn1 (m : nat) : (m + 1 = S m)%nat.
    Proof. omega. Qed.

    Definition vec_n1 (T : Type) (m : nat) (vs : Vector.t T (m + 1)) : Vector.t T (S m) :=
      match plusn1 m in eq _ n return Vector.t T n with
        | eq_refl => vs
      end.

    Definition rotate1 (T : Type) (n : nat) (v : Vector.t T n) : Vector.t T n :=
      match n return Vector.t T n -> Vector.t T n with
        | 0 => fun _ => Vector.nil T
        | S n => fun v => vec_n1 (Vector.append (Vector.tl v) [Vector.hd v])
      end v.

    Import VectorNotations.
    Lemma rotate1_0th (T : Type) (m : nat) (v : Vector.t T m) (x : T) :
      Vector.last (rotate1 (x :: v)) =  x.
    Proof.
      unfold rotate1, vec_n1. remember (plusn1 m) as ef; clear Heqef.
      revert v x. induction m; simpl; dependent destruction v; simpl; intros x.
      - simpl in ef. rewrite (UIP_refl _ _ ef); eauto.
      - simpl in ef. injection ef. intros ef'. generalize (IHm ef' v x). simpl.
        intros Heq; rewrite <- Heq at 2.
        generalize (Vector.append v [x]).
        generalize ef.
        generalize ef'.
        cutrewrite (m + 1 = S m)%nat; [|omega].
        intros.
        rewrite (UIP_refl _ _ ef0), (UIP_refl _ _ ef'0); simpl.
        eauto.
    Qed.

    Fixpoint last_idx (n : nat) : Fin.t (S n) :=
      match n with
        | 0 => Fin.F1
        | S m => Fin.FS (last_idx m)
      end.

    Lemma disj_eq_app (m k : nat) (h1 h2 : pheap) (hs1 : Vector.t pheap m) (hs2 : Vector.t pheap k) 
          (dis12 : pdisj h1 h2) :
      disj_eq hs1 h1 -> disj_eq hs2 h2 -> disj_eq (Vector.append hs1 hs2) (phplus_pheap dis12).
    Proof.
      generalize dependent h1; induction m;
      [intros h1 dis12 Heq1; rewrite (vinv0 hs1) in *; inversion Heq1; subst; intros | ].
      - simpl; cutrewrite (phplus_pheap dis12 = h2); eauto.
        destruct h2; apply pheap_eq; simpl; extensionality x; unfold phplus; simpl; eauto.
      - intros h1 dis12; destruct (vinvS hs1) as [ph1 [hs1' ?]]; subst; simpl.
        intros Heq1 Heq2; inversion Heq1.
        apply inj_pair2 in H2; subst; simpl.
        assert (pdisj ph h2) as Hdisp2.
        { pose proof (pdisjC dis12) as dis12'; simpl in dis12'; apply pdisjE2, pdisjC in dis12'; eauto. }
        assert (pdisj ph1 (phplus_pheap Hdisp2)) as Hdis1p2 by (apply pdisj_padd_expand; eauto).
        cutrewrite (phplus_pheap dis12 = phplus_pheap Hdis1p2); [|apply pheap_eq; simpl; apply padd_assoc; eauto].
        constructor; eauto. 
    Qed.
      
    Lemma singleton_disjeq (h : pheap) : disj_eq [h] h.
    Proof.
      assert (pdisj h emp_ph) by (simpl; apply pdisj_empty2).
      assert (h = phplus_pheap H).
      { destruct h as [h' ?]; apply pheap_eq; rewrite phplus_comm; simpl; eauto. }
      rewrite H0 at 2; repeat constructor.
    Qed.

    Lemma rotate_disjeq (m : nat) (hs : Vector.t pheap m) (h : pheap) :
      disj_eq hs h -> disj_eq (rotate1 hs) h.
    Proof.
      intros H.
      destruct m; [rewrite (vinv0 hs) in *; inversion H; subst; simpl; eauto|].
      destruct (vinvS hs) as [ph [hs' ?]]; subst; simpl.
      inversion H; subst.
      apply inj_pair2 in H3; subst.
      unfold vec_n1; destruct (plusn1 m).
      assert (pdisj ph0 ph) as Hdis0 by (apply pdisjC; eauto).
      assert ({| this := phplus ph ph0; is_p := pdisj_is_pheap hdis |} =
              phplus_pheap Hdis0 ) as Heq by  (apply pheap_eq; apply phplus_comm; eauto); 
        rewrite Heq.
      apply disj_eq_app; eauto.
      apply singleton_disjeq.
    Qed.

    Definition fin_to_nat (n : nat) (i : Fin.t n) := proj1_sig (Fin.to_nat i).

    Lemma fin_nat_inv (n : nat) (i : Fin.t n) :
      let (ni, _) := Fin.to_nat i in
      Fin.of_nat ni n = inleft i.
    Proof.
      induction n; [inversion i| destruct (finvS i) as [|[i' ?]]; subst].
      - simpl; eauto.
      - simpl.
        specialize (IHn i').
        remember (Fin.to_nat i') as i''; destruct i'' as [ni H]; simpl.
        remember (Fin.of_nat ni n) as ni'; destruct ni' as [i''' | (c & Hc)];
        inversion IHn; eauto.
    Qed.
    
    Lemma fin_of_nat_lt_inv1 (n m : nat) (H : (n < m)%nat) :
      proj1_sig (Fin.to_nat (Fin.of_nat_lt H)) = n.
    Proof.
      revert m H; induction n; simpl; intros m H.
      destruct m; simpl; inversion H; eauto.
      destruct m; simpl; eauto; [inversion H|].
      remember (Fin.to_nat (Fin.of_nat_lt (lt_S_n n m H))).
      destruct s; simpl.
      specialize (IHn m (lt_S_n _ _ H)).
      destruct (Fin.to_nat (Fin.of_nat_lt (lt_S_n n m H))).
      simpl in IHn; inversion Heqs; congruence.
    Qed.

    Lemma fin_addmn (n m : nat) (i : Fin.t (m + n)) :
      (exists i' : Fin.t m, fin_to_nat i' = fin_to_nat i) +
      (exists i' : Fin.t n, fin_to_nat i' + m = fin_to_nat i)%nat.
    Proof.
      remember (Fin.of_nat (fin_to_nat i) m).
      destruct s.
      - unfold fin_to_nat in Heqs.
        left; exists t.
        induction m; [inversion t|].
        simpl in i.
        destruct (finvS i) as [|[i' ?]], (finvS t) as [|[t' ?]]; subst; eauto. 
        + inversion Heqs.
        + simpl in Heqs; destruct (Fin.to_nat i'); simpl.
          inversion Heqs.
          destruct (Fin.of_nat x m); inversion H0.
        + simpl in Heqs.
          remember (Fin.to_nat i') as ni'. destruct ni' as [ni' P]; simpl in Heqs.
          specialize (IHm i' t'); rewrite <-Heqni' in IHm; simpl in IHm.
          destruct (Fin.of_nat ni' m); inversion Heqs.
          apply inj_pair2 in H0; subst.
          specialize (IHm eq_refl).
          unfold fin_to_nat in *; simpl.
          destruct (Fin.to_nat i'), (Fin.to_nat t); simpl in *; congruence.
      - right.
        assert (m <= fin_to_nat i).
        { destruct e as [? H]; rewrite H; omega. }
        destruct e as [m' Heq].
        assert (m' < n)%nat.
        { unfold fin_to_nat in Heq.
          clear Heqs.
          destruct (Fin.to_nat i) as [ni Hni].
          simpl in Heq.
          rewrite Heq in Hni.
          apply plus_lt_reg_l in Hni.
          omega. }
        remember (Fin.of_nat_lt H0) as x.
        exists x.
        rewrite Heqx. 
        unfold fin_to_nat at 1.
        rewrite fin_of_nat_lt_inv1.
        omega.
    Qed.

    Lemma append_nth1 (T : Type) (n m : nat) (i : Fin.t (n + m)) (j : Fin.t n) 
          (xs : Vector.t T n) (ys : Vector.t T m) :
      fin_to_nat i = fin_to_nat j -> (Vector.append xs ys)[@i] = xs[@j].
    Proof.
      intros Heq.
      induction n; [inversion j|].
      destruct (vinvS xs) as (x & xs' & ?); subst.
      cutrewrite (Vector.append (x :: xs') ys = x :: (Vector.append xs' ys)); [|simpl; eauto].
      destruct (finvS i) as [? | [i' ?]], (finvS j) as [? | [j' ?]]; subst; simpl; eauto;
      unfold fin_to_nat in Heq; simpl in Heq;
      try now 
          (match goal with [ H : context [Fin.to_nat ?x] |- _] => destruct (Fin.to_nat x) end;
           simpl in Heq; inversion Heq).
      apply IHn.
      unfold fin_to_nat.
      case_eq (Fin.to_nat i'); intros ni Heqni Heqi.
      rewrite Heqi in Heq; simpl in Heq.
      case_eq (Fin.to_nat j'); intros nj Heqnj Heqj.
      rewrite Heqj in Heq; simpl in Heq.
      unfold plus; rewrite Heqi; simpl; congruence.
    Qed.

    Lemma fin_to_nat_eq (n : nat) (i j : Fin.t n) :
      fin_to_nat i = fin_to_nat j -> i = j.
    Proof.
      intros Heq; induction n; [inversion i|].
      destruct (finvS i) as [|[i' ?]], (finvS j) as [|[j' ?]]; subst; eauto;
      unfold fin_to_nat in Heq; simpl in *;
      try now (
            match goal with [ H : context [Fin.to_nat ?x] |- _] => destruct (Fin.to_nat x) end;
            simpl in *; inversion Heq).
      rewrite (IHn i' j'); eauto.
      unfold fin_to_nat in *;
      repeat match goal with [ H : context [Fin.to_nat ?x] |- _] => destruct (Fin.to_nat x) end;
      simpl in *.
      inversion Heq; eauto.
    Qed.

    Lemma append_nth2 (T : Type) (n m : nat) (i : Fin.t (n + m)) (j : Fin.t m) 
          (xs : Vector.t T n) (ys : Vector.t T m) :
      (fin_to_nat j + n = fin_to_nat i)%nat -> (Vector.append xs ys)[@i] = ys[@j].
    Proof.
      intros Heq; induction n as [|n'].
      - rewrite (vinv0 xs); simpl in *; eauto.
        rewrite <-plus_n_O in Heq; rewrite (fin_to_nat_eq Heq); eauto.
      - destruct (vinvS xs) as (x & xs' & ?), (finvS i) as [? | [i' ?]]; subst; simpl.
        + rewrite plus_comm in Heq; unfold fin_to_nat in Heq; simpl in Heq; inversion Heq.
        + apply IHn'; rewrite plus_comm in *.
          unfold fin_to_nat in *; simpl in Heq.
          unfold plus in *. destruct (Fin.to_nat i'); simpl in *; inversion Heq; eauto.
    Qed.

    Lemma tl_nth (T : Type) (n : nat) (xs : Vector.t T (S n)) (i : Fin.t n) :
      (Vector.tl xs)[@i] = xs[@Fin.FS i].
    Proof.
      destruct (vinvS xs) as (x & xs' & ?); subst; simpl; eauto.
    Qed.

    Lemma hd_nth (T : Type) (n : nat) (xs : Vector.t T (S n)) :
      (Vector.hd xs) = xs[@Fin.F1].
    Proof.
      destruct (vinvS xs) as (? & ? & ?); subst; simpl; eauto.
    Qed.

    Lemma barrier_wf (i : nat) (st : pstate) :
       Aistar_v (fst (bspec i)) (fst st) (snd st) -> Aistar_v (snd (bspec i)) (fst st) (snd st).
    Proof.
      destruct i; simpl; [|apply default_wf].
      unfold bpre, bpost, Z_of_fin, nat_of_fin; destruct ntrd as [|n']; [simpl; intros; eauto |].
      intros H. destruct (aistar_disj H) as [hsP [Hdis Hsati]].
      apply (aistar_eq (hs := Vector.map (fun h => (fst st, h)) (rotate1 hsP))).
      unfold get_hs; rewrite MyVector.map_map, (@MyVector.map_ext _ _ _ _ _ (fun x => x));
      [| simpl; eauto]; rewrite (MyVector.map_id).
      - apply rotate_disjeq; eauto.
      - intros tid; rewrite init_spec; intros x. destruct st as [s h]; simpl.
        erewrite Vector.nth_map; eauto; simpl.
        unfold vec_n1. destruct (plusn1 n'); simpl.
        destruct (fin_addmn tid) as [[tid' Htid] | [tid' Htid]].
        + rewrite (append_nth1 (j :=tid')); eauto.
          rewrite tl_nth.
          specialize (Hsati (Fin.FS tid')).
          rewrite init_spec in Hsati; simpl in Hsati.
          unfold fin_to_nat in *; remember (Fin.to_nat tid') as tidn; destruct tidn as [ni ?];
          simpl in *.
          rewrite <-Htid, Hsati; eauto.
          assert (' Pos.of_succ_nat ni = (Z.of_nat ni + 1) mod ' Pos.of_succ_nat n')%Z.
          { assert (' Pos.of_succ_nat n' <> 0)%Z as Hgt.
            rewrite Zpos_P_of_succ_nat; omega.
            rewrite (proj2 (Z.mod_small_iff _ _ Hgt)); rewrite Zpos_P_of_succ_nat; omega. }
          rewrite H0; reflexivity.
        + rewrite (append_nth2 (j := tid')); eauto.
          destruct (finvS tid') as [? | [i' ?]]; subst; [|inversion i']; simpl.
          rewrite hd_nth. specialize (Hsati Fin.F1); rewrite init_spec in Hsati; rewrite Hsati; simpl.
          unfold fin_to_nat in Htid; rewrite <-Htid; simpl.
          assert ((Z.of_nat n' + 1) mod ' Pos.of_succ_nat n' = 0)%Z.
          { rewrite Zpos_P_of_succ_nat; simpl.
            cutrewrite (Z.of_nat n' + 1 = Z.succ (Z.of_nat n'))%Z; [| omega].
            rewrite Z.mod_same; eauto; omega. }
          rewrite H0; eauto.
    Qed.
    
    Lemma presice_bc (i : nat) (tid : Fin.t ntrd) :
      precise (fst (bspec i))[@tid] /\ precise (snd (bspec i))[@tid].
    Proof.
      unfold precise; split; intros h1 h2 h1' h2' s Hsat Hsat' Hdis Hdis' Heq;
      destruct i; simpl in *; rewrite init_spec in *; try tauto;
      unfold bpre, bpost in *; destruct h1 as [h1 ?], h1' as [h1' ?];
      apply pheap_eq; extensionality x; simpl in *;
      rewrite Hsat, Hsat'; eauto.
    Qed.

    Definition fin_rev (n : nat) (i : Fin.t n) : Fin.t n.
      refine
        (let (ni, H) := Fin.to_nat i in
         @Fin.of_nat_lt (n - (ni + 1)) _ _).
      abstract (apply lt_minus; omega).
    Defined.

    Lemma fin_eq_of_nat (n : nat) (i j : Fin.t n) :
      Fin.to_nat i = Fin.to_nat j -> i = j.
    Proof.
      induction n as [|n']; [inversion i|].
      destruct (finvS i) as [|[i' ?]], (finvS j) as [|[j' ?]]; subst; simpl; intros H; eauto;
      try (remember (Fin.to_nat i') as t1; destruct t1);
      try (remember (Fin.to_nat j') as t2; destruct t2);
      try now inversion H.
      rewrite (IHn' i' j'); eauto.
      inversion H; destruct H1.
      rewrite <-Heqt1, <-Heqt2; rewrite (proof_irrelevance _ l l0); eauto.
    Qed.

    Lemma fin_rev_inj (n : nat) (i j : Fin.t n) : fin_rev i = fin_rev j -> i = j.
    Proof.
      intros H; apply fin_eq_of_nat; apply (f_equal Fin.to_nat) in H.
      unfold fin_rev in H.
      destruct (Fin.to_nat i) as [ni Hi], (Fin.to_nat j) as [nj Hj].
      apply (f_equal (@proj1_sig _ _)) in H; rewrite !fin_of_nat_lt_inv1 in H.
      assert (ni = nj) as Hij by omega; destruct Hij.
      rewrite (proof_irrelevance _ Hi Hj); eauto.
    Qed.

    Lemma pre_sat' : (Aistar_v (init (fun i => Pre_i (fin_rev i)))) |= Aistar_v (init Pre_i).
    Proof.
      intros s h. 
      destruct (inject_biject (@fin_rev_inj ntrd)) as (g & Hfg & Hgf).
      apply (biject_wf Hgf Hfg).
      apply eq_nth_iff; intros j i ?; subst; rewrite !init_spec; congruence.
    Qed.

    Lemma pre_sat : (Pre |= Aistar_v (init Pre_i)).
    Proof.
      intros s h H; apply pre_sat'.
      unfold Pre,Pre_i,Z_of_fin,nat_of_fin in *; revert s h H. induction ntrd; [simpl in *; eauto|].
      intros s h H.
      destruct H as (ph1 & ph2 & Hpt & ? & ? & ?); exists ph1, ph2; repeat split; eauto.
      - cutrewrite (proj1_sig (Fin.to_nat (fin_rev (@Fin.F1 n))) = n)%nat; eauto.
        unfold fin_rev. remember (Fin.to_nat Fin.F1) as t; destruct t as [x1 Hx1]; simpl.
        rewrite fin_of_nat_lt_inv1.
        simpl in Heqt; inversion Heqt; simpl; omega.
      - apply IHn in H; simpl in *.
        cutrewrite <-(init
                      (fun (i : Fin.t n) (s0 : stack) (ph : pheap) =>
                         forall x : Z,
                           this ph x =
                           (if Z.eq_dec x (s0 4%Z + Z.of_nat (proj1_sig (Fin.to_nat (fin_rev i))))
                            then Some (1%Qc, Z.of_nat (proj1_sig (Fin.to_nat (fin_rev i))))
                            else None)) = 
                    init
                      (fun (i : Fin.t n) (s0 : stack) (ph : pheap) =>
                         forall x : Z,
                           this ph x =
                           (if Z.eq_dec x (s0 4%Z + Z.of_nat (proj1_sig (Fin.to_nat (fin_rev (Fin.FS i)))))
                            then
                              Some (1%Qc, Z.of_nat (proj1_sig (Fin.to_nat (fin_rev (Fin.FS i)))))
                            else None))); eauto.
        apply eq_nth_iff; intros ? i ?; subst; rewrite !init_spec.
        cutrewrite (proj1_sig (Fin.to_nat (fin_rev i)) = proj1_sig (Fin.to_nat (fin_rev (Fin.FS i))));           eauto.
        unfold fin_rev; simpl. destruct (Fin.to_nat i).
        rewrite !fin_of_nat_lt_inv1.
        rewrite (plus_comm (S x) 1); simpl; omega.
    Qed.

    Definition frotate1 (n : nat) (i : Fin.t n) : Fin.t n.
      refine (let (ni, H) := Fin.to_nat i in 
              @Fin.of_nat_lt (match ni with 0 => n - 1 | S n => n end) n _).
      abstract (destruct ni; omega).
    Defined.

    Lemma frotate1_inj (n : nat) (i j : Fin.t n) : frotate1 i = frotate1 j -> i = j.
    Proof.
      unfold frotate1; intros Heq; 
      apply (f_equal (@fin_to_nat _)) in Heq; apply fin_eq_of_nat.
      destruct (Fin.to_nat i) as [ni Hi], (Fin.to_nat j) as [nj Hj].
      unfold fin_to_nat in Heq; rewrite !fin_of_nat_lt_inv1 in Heq; destruct ni, nj; subst; f_equal;
      try apply proof_irrelevance; try omega.
    Qed.

    Lemma post_sat' : Aistar_v (init Post_i) |= (Aistar_v (init (fun i => Post_i (frotate1 i)))).
    Proof.
      intros s h.
      destruct (inject_biject (@frotate1_inj ntrd)) as (g & Hfg & Hgf).
      apply (biject_wf Hfg Hgf).
      apply eq_nth_iff; intros j i ?; subst; rewrite !init_spec; congruence.
    Qed.

    Lemma post_sat'' : Aistar_v (init Post_i) |= 
                         Aistar_v (init (fun i => Post_i (frotate1 (fin_rev i)))).
    Proof.
      intros s h; destruct (inject_biject (@fin_rev_inj ntrd)) as (g & Hfg & Hgf).
      intros H; apply post_sat' in H; revert H.
      apply (biject_wf Hfg Hgf).
      apply eq_nth_iff; intros ? i ?; subst; rewrite !init_spec; eauto.
    Qed.

    Lemma is_array_eq (n : nat) (f g : nat -> Z) (e : exp) :
      (forall x, (x < n)%nat -> f x = g x) -> (is_array e n f |= is_array e n g).
    Proof.
      induction n; intros H; [simpl; firstorder|].
      simpl; intros s h (ph1 & ph2 & Hpt & Hr & ? & ?).
      exists ph1, ph2; repeat split; eauto.
      intros x; specialize (Hpt x); rewrite <-H; eauto. 
    Qed.
    
    Lemma Aistar_v_append (n m : nat) (assns1 : Vector.t assn n) (assns2 : Vector.t assn m) :
      Aistar_v (Vector.append assns1 assns2) |= Astar (Aistar_v assns1) (Aistar_v assns2).
    Proof.
      revert m assns2; induction n; intros m assns2 s h Hsat.
      - rewrite (vinv0 assns1) in *; simpl in *; exists emp_ph, h; intuition; apply disj_emp2.
      - destruct (vinvS assns1) as (assn1 & assn1' & ?); subst; simpl in *.
        destruct Hsat as (ph1 & ph1' & ? & ? & ? & ?).
        apply IHn in H0 as (ph2 & ph2' & ? & ? & ? & ?).
        assert (pdisj ph1 ph2).
        { rewrite <-H5 in H1. apply pdisjE1 in H1; eauto. }
        exists (phplus_pheap H6), ph2'; repeat split; eauto.
        exists ph1, ph2; repeat split; eauto.
        simpl.
        + apply pdisj_padd_expand; eauto; split; eauto.
          rewrite H5; eauto.
        + simpl. rewrite padd_assoc; try rewrite H5; eauto.
    Qed.
    
    Section VectorNotation.
      Import VectorNotations.
      
      Fixpoint snoc_vec (n : nat) (T : Type) (xs : Vector.t T n) (x : T) : Vector.t T (S n) :=
        match xs with
          | [] => x :: []
          | y :: ys => y :: snoc_vec ys x
        end.

      Lemma snoc_dst (n : nat) (T : Type) (vs : Vector.t T (S n)) :
        exists (x : T) (vs' : Vector.t T n), vs = snoc_vec vs' x.
      Proof.
        induction n; destruct (vinvS vs) as (h & vs' & ?); subst.
        - rewrite (vinv0 vs'); exists h, []; eauto.
        - destruct (vinvS vs') as (h2 & vs'' & ?); subst.
          destruct (IHn (h2 :: vs'')) as (x' & vs''' & H).
          exists x', (h :: vs'''); simpl; congruence.
      Qed.          

      Lemma aistar_v_snoc (n : nat) (assns : Vector.t assn n) (x : assn) :
        Aistar_v (snoc_vec assns x) |= Astar (Aistar_v assns) x.
      Proof.
        induction n; intros s ph Hsat.
        - rewrite (vinv0 assns) in *; simpl in *; exists emp_ph, ph; repeat split; eauto.
          destruct Hsat as (ph1 & ph2 & ? & ? & ? & ?).
          assert (ph = ph1). 
          { destruct ph as [ph ?], ph1 as [ph1 ?]; simpl in *; apply pheap_eq; extensionality y.
            assert (phplus ph1 ph2 y = ph y) by (rewrite H2; eauto).
            unfold phplus in *; destruct (ph1 y) as [[? ?] |], (ph y) as [[? ? ]|]; 
            rewrite (H0 y) in H3; inversion H3; subst; eauto. }
          rewrite H3; eauto.
        - destruct (vinvS assns) as (a1 & assns' & ?); subst; simpl in *.
          destruct Hsat as (ph1 & ph2 & Hsat1 & Hsat2 & ? & ?).
          apply IHn in Hsat2 as (ph0 & ph3 & Hsat0 & Hsat2 & ? & ?).
          assert (pdisj ph1 ph0) by (rewrite <-H2 in H; apply pdisjE1 in H; eauto).
          exists (phplus_pheap H3), ph3; repeat split; eauto.
          exists ph1, ph0; repeat split; eauto.
          simpl; apply pdisj_padd_expand; eauto; split; eauto.
          rewrite H2; eauto.
          simpl; rewrite padd_assoc; eauto.
          + rewrite H2; eauto.
          + rewrite H2; eauto.
      Qed.

      Lemma snoc_last (T : Type) (n : nat) (vs : Vector.t T n) (x : T) :
        (snoc_vec vs x)[@(last_idx n)] = x.
      Proof.
        induction n; dependent destruction vs; simpl; eauto.
      Qed.

      Lemma last_n (n : nat) : proj1_sig (Fin.to_nat (last_idx n)) = n.
      Proof.
        induction n; simpl; eauto.
        destruct (Fin.to_nat (last_idx n)); simpl in *; eauto.
      Qed.

      Lemma nth_L_R (n : nat) (T : Type) (vs : Vector.t T n) (v : T) (i : Fin.t n) : 
        (snoc_vec vs v)[@Fin.L_R 1 i] = vs[@i].
      Proof.
        induction n; dependent destruction vs; dependent destruction i; [simpl; eauto|].
        cutrewrite (snoc_vec (h :: vs) v = h :: snoc_vec vs v); [|eauto].
        simpl; rewrite <-IHn; f_equal.
      Qed.
      
      Lemma L_R_Sn (n m : nat) (i : Fin.t n) :
        proj1_sig (Fin.to_nat (Fin.L_R (S m) i)) = proj1_sig (Fin.to_nat (Fin.L_R m i)).
      Proof.
        simpl.
        generalize (Fin.L_R m i); generalize (m+n)%nat.
        clear i n m. intros m t.
        induction m; dependent destruction t; simpl; eauto.
        remember ((fix LS (k : nat) (p : Fin.t k) {struct p} : 
              Fin.t (S k) :=
                match p in (Fin.t n) return (Fin.t (S n)) with
                | Fin.F1 k' => Fin.F1
                | Fin.FS n0 p' => Fin.FS (LS n0 p')
                end) m t) as t'.
        specialize (IHm t); rewrite <-Heqt' in IHm.
        destruct (Fin.to_nat t'), (Fin.to_nat t); simpl in *; eauto.
      Qed.

      Lemma L_R_n (n m : nat) (i : Fin.t n) : 
        proj1_sig (Fin.to_nat i) =  proj1_sig (Fin.to_nat (Fin.L_R m i)).
      Proof.
        induction m; [simpl; eauto|].
        rewrite L_R_Sn, IHm; eauto.
      Qed.
    End VectorNotation.
 
    Lemma Aistar_v_is_array (n : nat) (assns : Vector.t assn n) (g : nat -> Z) (e : exp) :
      (forall i : Fin.t n, assns[@i] |= 
         (e + Enum (Z.of_nat (proj1_sig (Fin.to_nat i))) -->p 
            (1%Qc, Enum (g (proj1_sig (Fin.to_nat i))))))%assn ->
      (Aistar_v assns |= is_array e n g).
    Proof.
      induction n; [rewrite (vinv0 assns) in *; intros; eauto|].
      destruct (snoc_dst assns) as (assn & vs & Heq); rewrite Heq in *.
      intros H s ph Hsat.
      apply aistar_v_snoc in Hsat as (phvs & phas & Hsat1 & Hsat2 & Hdis & Heq').
      exists phas, phvs; repeat split; eauto.
      - intros x.
        specialize (H (last_idx n) s phas).
        rewrite snoc_last in H; specialize (H Hsat2 x).
        rewrite last_n in *; eauto.
      - apply (IHn vs); eauto.
        intros i s' h' Hsat x.
        remember (proj1_sig (Fin.to_nat i)).
        specialize (H (Fin.L_R 1 i) s' h').
        rewrite nth_L_R in H.
        specialize (H Hsat x).
        rewrite <-(L_R_n 1), <-Heqy in H; eauto.
      - rewrite phplus_comm; eauto.
    Qed.

    Hypothesis ntrd_gt_0 : (0 < ntrd)%nat.

    Lemma post_sat : (Aistar_v (init Post_i) |= Post).
    Proof.
      intros s h H; apply post_sat' in H; clear ntrd_gt_0; revert H.
      apply Aistar_v_is_array; clear s h.
      intros i s h Hsat x.
      rewrite init_spec in Hsat; unfold Post_i,Z_of_fin,nat_of_fin,frotate1 in Hsat.
      destruct (Fin.to_nat i) as [ni Hni]; simpl in *.
      rewrite fin_of_nat_lt_inv1 in Hsat; destruct ni.
      - assert ((Z.of_nat (ntrd - 1) + 1) mod ntrdZ = 0)%Z as Heq; [|rewrite Heq in Hsat; clear Heq].
        { rewrite Nat2Z.inj_sub; [|omega].
          simpl; cutrewrite (ntrdZ - 1 + 1 = ntrdZ)%Z; [|omega].
          rewrite Z.mod_same; omega. }
        assert ((-1 mod ntrdZ)%Z = Z.of_nat (ntrd - 1)) as Heq; [|simpl; rewrite Heq; clear Heq; eauto].
        { rewrite <-(Z_mod_plus _ 1 ntrdZ)%Z; [|omega].
          cutrewrite ((-1 + 1 * ntrdZ) = ntrdZ - 1)%Z; [|omega].
          rewrite Zmod_small; [|omega].
          rewrite Nat2Z.inj_sub; simpl; omega. }
      - rewrite Zmod_small in Hsat; [|omega].
        cutrewrite (Z.of_nat (S ni) = Z.of_nat ni + 1)%Z; [|rewrite Nat2Z.inj_succ; omega ].
        cutrewrite (Z.of_nat ni + 1 - 1 = Z.of_nat ni)%Z; [|omega].
        rewrite Z.mod_small; [auto|omega].
    Qed.

    Lemma typing_rotate : typing_cmd E rotate Lo.
    Proof.
      unfold rotate, E.
      repeat constructor.
      apply (ty_read (ty := Hi)); repeat constructor.
      apply (ty_plus (ty1 := Lo) (ty2 := Hi)); repeat constructor.
      apply (ty_if (ty := Hi)); repeat constructor; simpl.
      apply (ty_eq (ty1 := Hi) (ty2 := Lo)); repeat constructor.
      apply (ty_assign (ty := Lo)); repeat constructor.
      apply (ty_assign (ty := Hi)); repeat constructor.
      apply (ty_plus (ty1 := Hi) (ty2 := Hi)); repeat constructor; simpl.
    Qed.
    Hint Resolve disj_emp1 disj_emp2.

    Lemma phplus_emp2 (h : pheap) : phplus h emp_ph = h.
      destruct h; unfold emp_ph,phplus; simpl; extensionality x; simpl; destruct (this x) as [[? ?]|];auto.
    Qed.

    Lemma phplus_emp1 (h : pheap) : phplus emp_ph h = h.
      destruct h; unfold emp_ph,phplus; simpl; extensionality x; simpl; destruct (this x) as [[? ?]|];auto.
    Qed.
    Hint Resolve phplus_emp1 phplus_emp2.

    Lemma rotate_l1 (tid : Fin.t ntrd) :
      ((init Pre_i)[@tid] //\\ (fun s _ => s TID = Z.of_nat (proj1_sig (Fin.to_nat tid))))%assn |=
      ((Evar ARR + Evar TID -->p (1%Qc, Enum (Z_of_fin tid))) ** 
       !(Evar TID === Enum (Z_of_fin tid))).
    Proof.
      intros s h [H0 H1].
      rewrite init_spec in H0; unfold Pre_i in H0.
      exists h, emp_ph; repeat split; eauto.
      intros x; specialize (H0 x); simpl in *.
      rewrite H1; simpl; apply H0.
    Qed.

    Hint Unfold indeE inde writes_var.
    Lemma rotate_l2 (tid : Fin.t ntrd) :
      CSL bspec tid 
          ((Evar ARR + Evar TID -->p (1%Qc, Enum (Z_of_fin tid))) ** !(Evar TID === Enum (Z_of_fin tid)))
          (X ::= [Evar ARR + Evar TID])
          (((Evar ARR + Evar TID) -->p (1%Qc, Enum (Z_of_fin tid)) //\\
            Apure (Beq (Evar X) (Enum (Z_of_fin tid)))) **
           !(Evar TID === Enum (Z_of_fin tid))).
    Proof.
      apply rule_frame;  [apply rule_read | ]; simpl; eauto.
      split; destruct H; subst; firstorder.
    Qed.
    
    Lemma rotate_l3 (tid : Fin.t ntrd) :
      (((Evar ARR + Evar TID) -->p (1%Qc, Enum (Z_of_fin tid)) //\\
           Apure (Beq (Evar X) (Enum (Z_of_fin tid)))) **
        !(Evar TID === Enum (Z_of_fin tid))) |=
      ((Evar ARR + Enum (Z_of_fin tid)) -->p (1%Qc, Enum (Z_of_fin tid)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid))).
    Proof.
      simpl; intros s h (ph1 & ph2 & H); intuition; repeat eexists; eauto.
      intros x; specialize (H x). rewrite H4 in H; eauto.
      destruct (Z_eq_dec (s 1%Z) (Z_of_fin tid)); try firstorder congruence.
    Qed.

    Lemma rotate_l4 (tid : Fin.t ntrd) :
      CSL bspec tid
      ((Evar ARR + Enum (Z_of_fin tid)) -->p (1%Qc, Enum (Z_of_fin tid)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid)))
      (Cbarrier 0)
      ((Evar ARR + Enum ((Z_of_fin tid + 1) mod ntrdZ)) -->p 
          (1%Qc, Enum ((Z_of_fin tid + 1) mod ntrdZ)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid))).
    Proof.
      apply rule_frame; eauto.
      cutrewrite (Apointsto 1%Qc (Evar 4%Z + Enum (Z_of_fin tid)) (Enum (Z_of_fin tid)) =
                  (fst (bspec 0))[@tid]); [|simpl; rewrite init_spec; eauto].
      cutrewrite (Apointsto 1%Qc (Evar 4%Z + Enum ((Z_of_fin tid + 1) mod ntrdZ)) (Enum ((Z_of_fin tid + 1) mod ntrdZ)) =
                  (snd (bspec 0))[@tid]); [|simpl; rewrite init_spec; eauto].
      apply rule_barrier.
      unfold inde; simpl; firstorder.
    Qed.

    Lemma rule_conseq_pre (tid : Fin.t ntrd) (P : assn) C (Q P' : assn) :
      CSL bspec tid P C Q -> (P' |= P) -> CSL bspec tid P' C Q.
    Proof.
      intros.
      eapply rule_conseq; eauto.
    Qed.

    Lemma rotate_l5 (tid : Fin.t ntrd) :
      CSL bspec tid
      (((Evar ARR + Enum ((Z_of_fin tid + 1) mod ntrdZ)) -->p 
          (1%Qc, Enum ((Z_of_fin tid + 1) mod ntrdZ)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid))) //\\
       (Apure (Evar TID == Enum (ntrdZ - 1))))
      (Y ::= Enum 0)
      (((Evar ARR + Evar Y) -->p 
          (1%Qc, Enum ((Z_of_fin tid + 1) mod ntrdZ)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid) //\\
        Evar Y === Enum ((Z_of_fin tid + 1) mod ntrdZ)))).
    Proof.
      eapply rule_conseq_pre; [ apply rule_assign| ].
      intros s h [(ph1 &ph2 & H1) H2]; intuition.
      exists ph1, ph2; repeat split; eauto.
      intros x; specialize (H x); unfold upd; simpl in *.
      assert ((Z_of_fin tid + 1) mod ntrdZ = 0)%Z as Heq.
      { assert ((s 0%Z) = ntrdZ - 1)%Z by (destruct (Z.eq_dec (s 0%Z) (ntrdZ - 1)); congruence).
        cutrewrite (Z_of_fin tid = ntrdZ - 1)%Z; [|congruence].
        cutrewrite ((ntrdZ - 1 + 1)%Z = ntrdZ); [| omega].
        rewrite Z_mod_same_full; eauto. }
      rewrite Heq in *; eauto.
      simpl in *; unfold upd.
      destruct (Z.eq_dec 2 2); try congruence.
      destruct (Z.eq_dec (s 0%Z) (ntrdZ - 1)); try congruence.    
      rewrite <-H3, e0.
      cutrewrite (ntrdZ - 1 + 1 = ntrdZ)%Z; [|omega].
      rewrite Z_mod_same_full; eauto.
    Qed.

    Lemma rotate_l6 (tid : Fin.t ntrd) :
      CSL bspec tid
      (((Evar ARR + Enum ((Z_of_fin tid + 1) mod ntrdZ)) -->p 
          (1%Qc, Enum ((Z_of_fin tid + 1) mod ntrdZ)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid))) //\\
       Apure (Bnot (Evar TID == Enum (ntrdZ - 1))))
      (Y ::= Evar TID + Enum 1%Z)
      (((Evar ARR + Evar Y) -->p 
          (1%Qc, Enum ((Z_of_fin tid + 1) mod ntrdZ)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid) //\\
        Evar Y === Enum ((Z_of_fin tid + 1) mod ntrdZ)))).
    Proof.
      eapply rule_conseq_pre; [ apply rule_assign| ].
      intros s h [(ph1 &ph2 & H1) H2]; intuition.
      exists ph1, ph2; repeat split; eauto.
      - intros x; specialize (H x); unfold upd; simpl in *.
        rewrite H3.
        assert ((Z_of_fin tid + 1) mod ntrdZ = Z_of_fin tid + 1)%Z as Heq.
        { assert (Z_of_fin tid <> ntrdZ - 1)%Z.
          destruct (Z.eq_dec (s 0%Z) (ntrdZ - 1)); simpl in *; congruence.
          apply Zmod_small; split;
          unfold Z_of_fin, nat_of_fin in *; destruct (Fin.to_nat tid); simpl in *; try omega. }
        rewrite Heq in *; eauto.
      - simpl in *; unfold upd.
        rewrite H3; destruct (Z.eq_dec 2 2); try congruence.
        destruct (Z.eq_dec (s 0%Z) (ntrdZ - 1)); simpl in *; try congruence.
        assert ((Z_of_fin tid + 1) mod ntrdZ = Z_of_fin tid + 1)%Z as Heq.
        { assert (Z_of_fin tid <> ntrdZ - 1)%Z.
          destruct (Z.eq_dec (s 0%Z) (ntrdZ - 1)); simpl in *; congruence.
          apply Zmod_small; split;
          unfold Z_of_fin, nat_of_fin in *; destruct (Fin.to_nat tid); simpl in *; try omega. }
        congruence.
    Qed.

    Lemma rotate_l7 (tid : Fin.t ntrd) :
      CSL bspec tid
      ((Evar ARR + Enum ((Z_of_fin tid + 1) mod ntrdZ)) -->p 
          (1%Qc, Enum ((Z_of_fin tid + 1) mod ntrdZ)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid)))
      (Cif (Evar TID == Enum (ntrdZ - 1)) (
         Y ::= Enum 0%Z
       ) (
         Y ::= Evar TID + Enum 1%Z
       ))
      (((Evar ARR + Evar Y) -->p 
          (1%Qc, Enum ((Z_of_fin tid + 1) mod ntrdZ)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid) //\\
        Evar Y === Enum ((Z_of_fin tid + 1) mod ntrdZ)))).
    Proof.
      apply rule_if; [apply rotate_l5 | apply rotate_l6].
    Qed.

    Lemma rotate_l8 (tid : Fin.t ntrd) :
      CSL bspec tid
      ((Evar ARR + Evar Y) -->p 
          (1%Qc, Enum ((Z_of_fin tid + 1) mod ntrdZ)) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid) //\\
         Evar Y === Enum ((Z_of_fin tid + 1) mod ntrdZ)))
      ([Evar ARR + Evar Y] ::= Evar X)
      ((Evar ARR + Evar Y) -->p (1%Qc, Evar X) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid) //\\
         Evar Y === Enum ((Z_of_fin tid + 1) mod ntrdZ))).
    Proof.
        apply rule_frame; [apply rule_write|]; autounfold; simpl; tauto.
    Qed.

    Lemma rotate_l9 (tid : Fin.t ntrd) :
      ((Evar ARR + Evar Y) -->p (1%Qc, Evar X) **
       !(Evar TID === Enum (Z_of_fin tid) //\\ Evar X === Enum (Z_of_fin tid) //\\
         Evar Y === Enum ((Z_of_fin tid + 1) mod ntrdZ))) |=
      (init Post_i)[@tid].
    Proof.
      rewrite init_spec; unfold Post_i.
      simpl; intros s h (ph1 & ph2 & H); intuition.
      specialize (H0 x).
      rewrite H3, H6 in *; eauto.
      destruct ph1 as [ph1 Hph1], ph2 as [ph2 Hph2]; unfold is_pheap in *; simpl in *;
      rewrite <-H4; specialize (H x); specialize (Hph1 x); specialize (Hph2 x); 
      specialize (H1 x); unfold phplus;
      destruct (ph1 x) as [[? ?] |], (ph2 x) as [[? ?]|]; simpl in *; eauto;
      destruct (Z.eq_dec x (s 4%Z + (Z_of_fin tid + 1) mod ntrdZ)); inversion H0; subst; intuition.
      apply frac_contra1 in H12; tauto.
    Qed.      
      
    Lemma rotate_seq (tid : Fin.t ntrd) : 
      CSL bspec tid
          ((init Pre_i)[@tid] //\\ (fun s _ => s TID = Z.of_nat (proj1_sig (Fin.to_nat tid))))%assn
          rotate (init Post_i)[@tid].
    Proof.
      Ltac crush_rotate := 
        first [apply rotate_l1 | apply rotate_l2 | apply rotate_l3 | apply rotate_l4 | apply rotate_l5 | apply rotate_l6 | apply rotate_l7 |
               apply rotate_l8 | apply rotate_l9].
      eapply rule_conseq; try crush_rotate.
      eapply rule_seq; [crush_rotate | ].
      eapply rule_conseq_pre; [| crush_rotate] .
      eapply rule_seq; [crush_rotate|].
      eapply rule_seq; [crush_rotate|crush_rotate].
    Qed.

    Lemma rotate_par : CSLp ntrd E Pre rotate Post.
    Proof.
      eapply rule_par.
      - destruct ntrd as [|n']; try (exists n'; auto).
        inversion ntrd_gt_0.
      - apply bpre_lassn.
      - apply barrier_wf.
      - apply presice_bc.
      - apply pre_sat.
      - apply post_sat.
      - apply prei_lassn.
      - apply posti_lassn.
      - apply typing_rotate.
      - apply rotate_seq.
    Qed.
  End Rotate.
End Example.
