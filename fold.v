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
      X ::= [ARR + TID] ;;
      Cbarrier 0 ;;
      Cif (R == ntrdZ) (
        Y ::= 0%Z
      ) (
        Y ::= TID + 1%Z
      ) ;;
      [ARR + Y] ::= X.
    Definition Pre := is_array ARR (ntrd + 1) (fun i => Z.of_nat i).
    Definition Post := is_array ARR (ntrd + 1) (fun i : nat => (Z.of_nat i - 1) mod ntrdZ)%Z.
    Definition Pre_i := (ARR + TID -->p (1%Qc, TID))%assn.
    Definition Post_i := (ARR + ((TID + 1) mod ntrdZ)%Z -->p (1%Qc, TID))%assn.
    
    Definition E (var : var) := 
      if Z.eq_dec var TID then Hi
      else if Z.eq_dec var X then Hi
      else if Z.eq_dec var Y then Hi
      else Lo.

    Definition bpre (tid : Fin.t ntrd) := 
      (ARR + (Z_of_fin tid) -->p (1%Qc, Z_of_fin tid))%assn.
    Definition bpost (tid : Fin.t ntrd) := 
      (ARR + (((Z_of_fin tid) + 1) mod ntrdZ)%Z -->p (1%Qc, Z_of_fin tid))%assn.

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
        eapply (IHm _ _ _ _ f' g' H H2 Heq Hsat2).
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

    Require Import Coq.Program.Equality.
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

    Lemma fin_mn (n m : nat) (i : Fin.t (m + n)) :
      (exists i' : Fin.t m, fin_to_nat i' = fin_to_nat i) \/
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
        { destruct e as [? H]; rewrite H. apply len_addr. }
        destruct e as [m' Heq].
        assert (m' < n)%nat.
        { unfold fin_to_nat in Heq.
          destruct (Fin.to_nat i) as [ni Hni].

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
        unfold vec_n1. destruct (plusn1 n'); simpl.
        erewrite Vector.nth_map; eauto; simpl.
        
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
