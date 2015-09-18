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
Require Import assertions.
Close Scope Qc_scope.
Close Scope Q_scope.

Section Example.
  Local Notation TID := (Var 0).
  Local Notation X := (Var 1).
  Local Notation Y := (Var 2).
  Local Notation R := (Var 3).
  Local Notation ARR := (Var 4).

  Variable ntrd : nat.

  Open Scope exp_scope.
  Open Scope bexp_scope.
  Definition nosimpl (T : Type) (P : T) := let tt := tt in P.

(*  Notation "P '//\\' Q" := (fun s h => P s h /\ Q s h) (at level 80, right associativity).
  Notation "P1 ** P2" := (nosimpl (Astar P1 P2)) (at level 70, right associativity).
  Notation "x '===' y" := 
    (fun s h => edenot x s = edenot y s) (at level 70, no associativity).
  Notation "'existS' x .. y , p" := 
    (fun s h => ex (fun x => .. (ex (fun y => p s h)) ..))
      (at level 200, x binder, y binder, right associativity).
  Notation "e1 '-->p' ( p ,  e2 )" := (Apointsto p e1 e2) (at level 75).
  Notation Emp := (fun s h => forall x, this h x = None).
  Notation "!( P )" := (Emp //\\ P).*)
  Delimit Scope assn_scope with assn.
  Delimit Scope exp_scope with exp.

  Fixpoint is_array (e : exp) (n : nat) (f : nat -> Z) :=
    match n with
      | 0 => Aemp
      | S n' => e + Enum (Z.of_nat n') -->p (1%Qc, Enum (f n')) **
                is_array e n' f
    end.

(*  Notation nat_of_fin i := (proj1_sig (Fin.to_nat i)) (at level 10).
  Notation Z_of_fin i := (Z.of_nat (nat_of_fin i)) (at level 10).*)

  Section Rotate.
    Notation ntrdZ := (Z_of_nat ntrd).

    Definition rotate := 
      X ::= [ARR + TID] ;;
      Cbarrier 0 ;;
      Cif (TID == (ntrdZ - 1)%Z) (
        Y ::= 0%Z
      ) (
        Y ::= TID + 1%Z
      ) ;;
      [ ARR +  Y] ::=  X.

    Definition Pre := is_array ARR ntrd (fun i => Z.of_nat i).
    Definition Post := is_array ARR ntrd (fun i : nat => (Z.of_nat i - 1) mod ntrdZ)%Z.

    Definition Pre_i (i : Fin.t ntrd) := 
      (ARR + (Z_of_fin i) -->p (1%Qc, (Z_of_fin i))).
    Definition Post_i (i : Fin.t ntrd) := 
      ( ARR + ((Z_of_fin i + 1) mod ntrdZ)%Z) -->p (1%Qc, (Z_of_fin i)).

    Definition E (var : var) := 
      if var_eq_dec var TID then Hi
      else if var_eq_dec var X then Hi
      else if var_eq_dec var Y then Hi
      else Lo.

    Definition bpre (tid : Fin.t ntrd) := 
      (ARR + (Z_of_fin tid) -->p (1%Qc, (Z_of_fin tid)))%assn.
    Definition bpost (tid : Fin.t ntrd) := 
      (ARR + ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p (1%Qc, ((Z_of_fin tid + 1) mod ntrdZ)%Z).

    Hint Unfold bpre.

    Ltac prove_lassn tac :=
      let Heq := fresh in
      match goal with
        | [ |- low_assn _ _] => intros ? ? ? Heq
      end; autounfold; simpl; 
      tac;
      repeat rewrite Heq; split; eauto.

    Ltac prove_lassn0 := prove_lassn ltac:(idtac).

    Lemma pre_lassn (tid : Fin.t ntrd) : low_assn E (bpre tid).
    Proof. prove_lassn ltac:(unfold_conn_all; simpl in *). Qed.

    Hint Unfold bpost.
    Lemma post_lassn (tid : Fin.t ntrd) : low_assn E (bpost tid).
    Proof. prove_lassn ltac:(unfold_conn_all; simpl in *). Qed.

    Notation FalseP := (fun (_ : stack) (h : pheap) => False).

    Definition default : (Vector.t assn ntrd * Vector.t assn ntrd) := 
      (init (fun _ => FalseP), init (fun _ => FalseP)).

    Hint Unfold default.
    Lemma FalseP_lassn (E' : env) : low_assn E' FalseP.
    Proof. prove_lassn0. Qed.

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

    Hint Unfold Pre_i.
    Lemma prei_lassn : forall tid : Fin.t ntrd, low_assn E (Vector.nth (init Pre_i) tid).
    Proof.
      intros; prove_lassn ltac:(unfold_conn_all; simpl in *; rewrite init_spec).
    Qed.
    
    Hint Unfold Post_i.
    Lemma posti_lassn : forall tid : Fin.t ntrd, low_assn E (Vector.nth (init Post_i) tid).
    Proof. intros; prove_lassn ltac:(unfold_conn_all; simpl in *; rewrite init_spec). Qed.
      
    Lemma default_wf (s : stack) (h : pheap) : 
      Aistar_v (fst default) s h <-> Aistar_v (snd default) s h.
    Proof.
      cutrewrite (fst default = snd default); tauto.
    Qed.

    Import VectorNotations.
    Require Import Program.Equality.

    Lemma swap_wf : 
      forall (m : nat) (p : assn) (ps : Vector.t assn m) (i : Fin.t m),
        Aistar_v (p :: ps) |= Aistar_v (ps[@i] :: (Vector.replace ps i p)).
    Proof.
      induction m; intros p ps i s h H; simpl; [rewrite (vinv0 ps); inversion i | ].
      destruct (vinvS ps) as (p' & ps' & ?); subst. 
      destruct (finvS i) as [|[i' ?]]; subst; [simpl |].
      - simpl in *. repeat sep_cancel.
      - simpl in *; repeat sep_cancel.
        apply IHm; auto.
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
        simpl in *; sep_cancel. eapply IHm; auto.
      - apply (swap_wf i') in Hps; rewrite H1.
        cutrewrite ((p :: ps')[@Fin.FS i']  = ps'[@i']); [|auto].
        cut (Aistar_v (replace ps' i' p) |= 
             Aistar_v (init (fun i : Fin.t m => (p :: ps')[@f (Fin.FS i)])));
          [ intros H'; simpl in *; sep_cancel; apply H'; auto | ].
        clear Hps s h; intros s h Hsat.
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
        apply (IHm _ _ _ _ f' g' H H2 Heq Hsat).
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
                                                 (Fin.t (pred n') -> Fin.t (pred n')) -> Fin.t n' with
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
                                              Fin.t (pred n') ->
                                              Fin.t (pred n') with
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
                               (Fin.t (pred n) -> Fin.t (pred n)) -> (Fin.t (pred n)) -> 
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
      (exists i' : Fin.t m, nat_of_fin i' = nat_of_fin i) +
      (exists i' : Fin.t n, nat_of_fin i' + m = nat_of_fin i)%nat.
    Proof.
      remember (Fin.of_nat (nat_of_fin i) m).
      destruct s.
      - left; exists t.
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
          simpl; destruct (Fin.to_nat i'), (Fin.to_nat t); simpl in *; congruence.
      - right.
        assert (m <= nat_of_fin i).
        { destruct e as [? H]; rewrite H; omega. }
        destruct e as [m' Heq].
        assert (m' < n)%nat.
        { clear Heqs.
          destruct (Fin.to_nat i) as [ni Hni].
          simpl in Heq.
          simpl in *; rewrite Heq in Hni.
          apply plus_lt_reg_l in Hni.
          omega. }
        remember (Fin.of_nat_lt H0) as x.
        exists x.
        rewrite Heqx. 
        rewrite fin_of_nat_lt_inv1.
        omega.
    Qed.

    Lemma append_nth1 (T : Type) (n m : nat) (i : Fin.t (n + m)) (j : Fin.t n) 
          (xs : Vector.t T n) (ys : Vector.t T m) :
      nat_of_fin i = nat_of_fin j -> (Vector.append xs ys)[@i] = xs[@j].
    Proof.
      intros Heq.
      induction n; [inversion j|].
      destruct (vinvS xs) as (x & xs' & ?); subst.
      cutrewrite (Vector.append (x :: xs') ys = x :: (Vector.append xs' ys)); [|simpl; eauto].
      destruct (finvS i) as [? | [i' ?]], (finvS j) as [? | [j' ?]]; subst; simpl; eauto;
      simpl in Heq;
      try now 
          (match goal with [ H : context [Fin.to_nat ?x] |- _] => destruct (Fin.to_nat x) end;
           simpl in Heq; inversion Heq).
      apply IHn.
      case_eq (Fin.to_nat i'); intros ni Heqni Heqi.
      rewrite Heqi in Heq; simpl in Heq.
      case_eq (Fin.to_nat j'); intros nj Heqnj Heqj.
      rewrite Heqj in Heq; simpl in Heq.
      unfold plus; rewrite Heqi; simpl; congruence.
    Qed.

    Lemma fin_to_nat_eq (n : nat) (i j : Fin.t n) :
      nat_of_fin i = nat_of_fin j -> i = j.
    Proof.
      intros Heq; induction n; [inversion i|].
      destruct (finvS i) as [|[i' ?]], (finvS j) as [|[j' ?]]; subst; eauto;
      simpl in *;
      try now (
            match goal with [ H : context [Fin.to_nat ?x] |- _] => destruct (Fin.to_nat x) end;
            simpl in *; inversion Heq).
      rewrite (IHn i' j'); eauto.
      repeat match goal with [ H : context [Fin.to_nat ?x] |- _] => destruct (Fin.to_nat x) end;
      simpl in *.
      inversion Heq; eauto.
    Qed.

    Lemma append_nth2 (T : Type) (n m : nat) (i : Fin.t (n + m)) (j : Fin.t m) 
          (xs : Vector.t T n) (ys : Vector.t T m) :
      (nat_of_fin j + n = nat_of_fin i)%nat -> (Vector.append xs ys)[@i] = ys[@j].
    Proof.
      intros Heq; induction n as [|n'].
      - rewrite (vinv0 xs); simpl in *; eauto.
        rewrite <-plus_n_O in Heq; rewrite (fin_to_nat_eq Heq); eauto.
      - destruct (vinvS xs) as (x & xs' & ?), (finvS i) as [? | [i' ?]]; subst; simpl.
        + rewrite plus_comm in Heq; simpl in Heq; inversion Heq.
        + apply IHn'; rewrite plus_comm in *.
          simpl in Heq.
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

    Require Import NPeano.
    Lemma nat_fin_lt (n : nat) (i : Fin.t n) : (nat_of_fin i < n)%nat.
    Proof.
      intros; destruct (Fin.to_nat i) as [? ?]; simpl; auto.
    Qed.

    Hypothesis ntrd_gt_0 : (0 < ntrd)%nat.

    Program Definition fbr (n : nat) (H : (0 < n)%nat) (i : Fin.t n) : Fin.t n :=
      @Fin.of_nat_lt ((nat_of_fin i + 1) mod n) n _.
    Next Obligation.
    Proof.
      apply Nat.mod_upper_bound; omega.
    Qed.      

    Lemma fbr_inject (n : nat) (H : (0<n)%nat) (i j : Fin.t n) : 
      fbr H i = fbr H j -> i = j.
    Proof.
      unfold fbr. intros H'. apply fin_to_nat_eq. 
      apply (f_equal (fun n => nat_of_fin n)) in H'.
      rewrite !fin_of_nat_lt_inv1 in H'.
      destruct (Fin.to_nat i) as [i' Hi], (Fin.to_nat j) as [j' Hj]; simpl in *.
      assert (Hn : (n - 1 + 1 = n)%nat) by omega.
      assert (i' = n - 1 \/ i' + 1 < n)%nat as [Hi'|Hi'] by omega;
        assert (j' = n - 1 \/ j' + 1 < n)%nat as [Hj'|Hj'] by omega; try omega;
      try rewrite Hi' in *; try rewrite Hj' in *; try rewrite Hn in H';
      try (rewrite !Nat.mod_same in *; try omega); try rewrite !Nat.mod_small in H'; try omega.
    Qed.

    Lemma barrier_wf (i : nat) (st : pstate) :
       Aistar_v (fst (bspec i)) (fst st) (snd st) -> Aistar_v (snd (bspec i)) (fst st) (snd st).
    Proof.
      destruct i; simpl; [|apply default_wf].
      unfold bpre, bpost; intros H.
      destruct (inject_biject (@fbr_inject _ ntrd_gt_0)) as [g [H1 H2]].
      eapply (biject_wf (f:=fbr ntrd_gt_0) (g:=g)); eauto.
      apply eq_nth_iff; intros p1 ? <-; rewrite !init_spec.
      cutrewrite ((Z_of_fin p1 + 1) mod ntrdZ = Z_of_fin (fbr ntrd_gt_0 p1))%Z; auto.
      (* Fin.of_nat (Fin.of_nat_lt p) -> p *)
      unfold fbr; rewrite fin_of_nat_lt_inv1, mod_Zmod, Nat2Z.inj_add; 
      simpl; omega.
    Qed.
    
    Lemma presice_bc (i : nat) (tid : Fin.t ntrd) :
      precise (fst (bspec i))[@tid] /\ precise (snd (bspec i))[@tid].
    Proof.
      unfold precise; split; intros h1 h2 h1' h2' s Hsat Hsat' Hdis Hdis' Heq;
      destruct i; simpl in *; rewrite init_spec in *; try tauto;
      unfold bpre, bpost in *; destruct h1 as [h1 ?], h1' as [h1' ?];
      apply pheap_eq; extensionality x; simpl in *;
      unfold_conn_all; rewrite Hsat, Hsat'; eauto.
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
          sep_normal. sep_cancel. apply IHn; auto.
      Qed.

      Lemma aistar_v_snoc' (n : nat) (assns : Vector.t assn n) (x : assn) :
        Astar (Aistar_v assns) x |= Aistar_v (snoc_vec assns x).
      Proof.
        induction n; intros s ph Hsat; simpl in *.
        - rewrite (vinv0 assns) in *; simpl in *; repeat sep_cancel. 
        - destruct (vinvS assns) as (a1 & assns' & ?); subst; simpl in *.
          sep_normal_in Hsat; sep_cancel; apply IHn; sep_cancel.
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
         (e +  Z_of_fin i) -->p (1%Qc,  (g (nat_of_fin i))))%assn ->
      (Aistar_v assns |= is_array e n g).
    Proof.
      induction n; [rewrite (vinv0 assns) in *; intros; eauto|].
      destruct (snoc_dst assns) as (assn & vs & Heq); rewrite Heq in *.
      intros H s ph Hsat; simpl.
      apply aistar_v_snoc in Hsat. 
      pose proof (H (last_idx n)) as Hlast; rewrite last_n in *.
      eapply scRw; [apply Hlast| apply IHn|].
      - intros i; specialize (H (Fin.L_R 1 i)); repeat rewrite <-(L_R_n 1), (nth_L_R) in H; eauto.
      - rewrite snoc_last; repeat sep_cancel.
    Qed.

    Lemma is_array_Aistar_v (n : nat) (assns : Vector.t assn n) (g : nat -> Z) (e : exp) :
      (forall i : Fin.t n, 
         (e +  Z_of_fin i) -->p (1%Qc,  (g (nat_of_fin i)))%assn |= assns[@i])  ->
      (is_array e n g |= Aistar_v assns).
    Proof.
      induction n; [rewrite (vinv0 assns) in *; intros; eauto|].
      destruct (snoc_dst assns) as (assn & vs & Heq); rewrite Heq in *.
      intros H s ph Hsat; simpl in *.
      apply aistar_v_snoc'. 
      pose proof (H (last_idx n)) as Hlast; rewrite last_n in *.
      eapply scRw; [apply IHn | |].
      - intros i; specialize (H (Fin.L_R 1 i)); repeat rewrite <-(L_R_n 1), (nth_L_R) in H; eauto.
      - rewrite snoc_last in Hlast; eauto.
      - rewrite snoc_last in *; repeat sep_cancel.
    Qed.
    
    Lemma pre_sat : (Pre |= Aistar_v (init Pre_i)).
    Proof.
      apply is_array_Aistar_v; intros; rewrite init_spec; unfold Pre_i; auto.
    Qed.      

    Definition frotate1 (n : nat) (i : Fin.t n) : Fin.t n.
      refine (let (ni, H) := Fin.to_nat i in 
              @Fin.of_nat_lt (match ni with 0 => n - 1 | S n => n end) n _).
      abstract (destruct ni; omega).
    Defined.

    Lemma frotate1_inj (n : nat) (i j : Fin.t n) : frotate1 i = frotate1 j -> i = j.
    Proof.
      unfold frotate1; intros Heq.
      apply fin_eq_of_nat.
      apply (f_equal (fun i => nat_of_fin i)) in Heq.
      destruct (Fin.to_nat i) as [ni Hi], (Fin.to_nat j) as [nj Hj].
      rewrite !fin_of_nat_lt_inv1 in Heq.
      assert (H : ni = nj) by (destruct ni, nj; omega); destruct H.
      f_equal; apply proof_irrelevance.
    Qed.

    Lemma post_sat' : Aistar_v (init Post_i) |= (Aistar_v (init (fun i => Post_i (frotate1 i)))).
    Proof.
      intros s h.
      destruct (inject_biject (@frotate1_inj ntrd)) as (g & Hfg & Hgf).
      apply (biject_wf Hfg Hgf).
      apply eq_nth_iff; intros j i ?; subst; rewrite !init_spec; congruence.
    Qed.

    Lemma post_sat : (Aistar_v (init Post_i) |= Post).
    Proof.
      intros s h H; apply post_sat' in H. revert H.
      apply Aistar_v_is_array; clear s h.
      intros i s h Hsat x.
      rewrite init_spec in Hsat; unfold Post_i,frotate1 in Hsat.
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
      - rewrite (vinv0 assns1) in *; simpl in *.
        sep_normal; auto.
      - destruct (vinvS assns1) as (assn1 & assn1' & ?); subst; simpl in *.
        sep_normal; sep_normal_in Hsat; sep_cancel.
        apply IHn; auto.
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
(*
    Lemma rotate_l1 (tid : Fin.t ntrd) :
      ((init Pre_i)[@tid] ** !(TID === Z_of_fin tid))%assn |=
      (( ARR +  TID -->p (1%Qc,  (Z_of_fin tid))) ** 
       !( TID ===  (Z_of_fin tid))).
    Proof.
      intros.
      sep_normal_in H. sep_normal.
      unfold Pre_i in H; rewrite init_spec in H. 
      intros s h [H0 H1].
      rewrite init_spec in H0; unfold Pre_i in H0.
      exists h, emp_ph; repeat split; eauto.
      intros x; specialize (H0 x); simpl in *.
      rewrite H1; simpl; apply H0.
    Qed.

    Hint Unfold indeE inde writes_var.
    Lemma rotate_l2 (tid : Fin.t ntrd) :
      CSL bspec tid 
          (( ARR +  TID -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
          (X ::= [ ARR +  TID])
          ((( ARR +  TID) -->p (1%Qc,  (Z_of_fin tid)) //\\
            Apure (Beq ( X) ( (Z_of_fin tid)))) **
           !( TID ===  (Z_of_fin tid))).
    Proof.
      apply rule_frame;  [apply rule_read | ]; simpl; eauto.
      split; destruct H; subst; firstorder.
    Qed.
    
    Lemma rotate_l3 (tid : Fin.t ntrd) :
      ((( ARR +  TID) -->p (1%Qc,  (Z_of_fin tid)) //\\
           Apure (Beq ( X) ( (Z_of_fin tid)))) **
        !( TID ===  (Z_of_fin tid))) |=
      (( ARR +  (Z_of_fin tid)) -->p (1%Qc,  (Z_of_fin tid)) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid))).
    Proof.
      simpl; intros s h H.
      
      simpl; intros s h (ph1 & ph2 & H); intuition; repeat eexists; eauto.
      intros x; specialize (H x). rewrite H4 in H; eauto.
      destruct (Z_eq_dec (s X) (Z_of_fin tid)); try firstorder congruence.
    Qed.

    Lemma rotate_l4 (tid : Fin.t ntrd) :
      CSL bspec tid
      (( ARR +  (Z_of_fin tid)) -->p (1%Qc,  (Z_of_fin tid)) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid)))
      (Cbarrier 0)
      (( ARR +  ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid))).
    Proof.
      apply rule_frame; eauto.
      assert (Heq : Apointsto 1%Qc (ARR +  (Z_of_fin tid)) ((Z_of_fin tid)) =
                    (fst (bspec 0))[@tid]) by (simpl; rewrite init_spec; eauto).
      rewrite Heq; clear Heq.
      assert (Heq : (Evar ARR + ((Z_of_fin tid + 1) mod ntrdZ)%Z)%exp -->p 
                      (1%Qc, (((Z_of_fin tid + 1) mod ntrdZ)))%Z =
                    (snd (bspec 0))[@tid]) by (simpl; rewrite init_spec; eauto).
      rewrite Heq; clear Heq.
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
      ((( ARR +  ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid))) //\\
       (Apure ( TID ==  (ntrdZ - 1)%Z)))
      (Y ::=  0%Z)
      ((( ARR +  Y) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid) //\\
         Y ===  ((Z_of_fin tid + 1) mod ntrdZ)%Z))).
    Proof.
      eapply rule_conseq_pre; [ apply rule_assign| ].
      intros s h [(ph1 &ph2 & H1) H2]; intuition.
      exists ph1, ph2; repeat split; eauto.
      intros x; specialize (H x); unfold upd; simpl in *.
      assert ((Z_of_fin tid + 1) mod ntrdZ = 0)%Z as Heq.
      { assert ((s TID) = ntrdZ - 1)%Z by (destruct (Z.eq_dec (s TID) (ntrdZ - 1)); congruence).
        assert (Heq : Z_of_fin tid = (ntrdZ - 1)%Z) by congruence; rewrite Heq; clear Heq.
        assert (Heq : (ntrdZ - 1 + 1)%Z = ntrdZ) by omega; rewrite Heq; clear Heq. 
        rewrite Z_mod_same_full; eauto. }
      rewrite Heq in *; eauto.
      simpl in *; unfold upd.
      destruct (Z.eq_dec 2 2); try congruence.
      destruct (Z.eq_dec (s TID) (ntrdZ - 1)); try congruence.    
      rewrite <-H3, e0.
      cutrewrite (ntrdZ - 1 + 1 = ntrdZ)%Z; [|omega].
      rewrite Z_mod_same_full; eauto.
    Qed.

    Lemma rotate_l6 (tid : Fin.t ntrd) :
      CSL bspec tid
      ((( ARR +  ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid))) //\\
       Apure (Bnot ( TID ==  (ntrdZ - 1)%Z)))
      (Y ::=  TID +  1%Z)
      ((( ARR +  Y) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid) //\\
         Y ===  ((Z_of_fin tid + 1) mod ntrdZ)%Z))).
    Proof.
      eapply rule_conseq_pre; [ apply rule_assign| ].
      intros s h [(ph1 &ph2 & H1) H2]; intuition.
      exists ph1, ph2; repeat split; eauto.
      - intros x; specialize (H x); unfold var_upd; simpl in *.
        rewrite H3.
        assert ((Z_of_fin tid + 1) mod ntrdZ = Z_of_fin tid + 1)%Z as Heq.
        { assert (Z_of_fin tid <> ntrdZ - 1)%Z.
          destruct (Z.eq_dec (s TID) (ntrdZ - 1)); simpl in *; congruence.
          simpl in *; apply Zmod_small; split; destruct (Fin.to_nat tid); simpl in *; try omega. 
        }
        rewrite Heq in *; eauto.
      - simpl in *; unfold var_upd.
        rewrite H3; destruct (var_eq_dec Y Y); try congruence.
        destruct (Z.eq_dec (s TID) (ntrdZ - 1)); simpl in *; try congruence.
        assert ((Z_of_fin tid + 1) mod ntrdZ = Z_of_fin tid + 1)%Z as Heq.
        { assert (Z_of_fin tid <> ntrdZ - 1)%Z.
          destruct (Z.eq_dec (s TID) (ntrdZ - 1)); simpl in *; congruence.
          simpl in *; apply Zmod_small; split;
          destruct (Fin.to_nat tid); simpl in *; try omega. }
        congruence.
    Qed.

    Lemma rotate_l7 (tid : Fin.t ntrd) :
      CSL bspec tid
      (( ARR +  ((Z_of_fin tid + 1) mod ntrdZ))%exp -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ))%Z **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid)))
      (Cif ( TID ==  (ntrdZ - 1)%Z) (
         Y ::=  0%Z
       ) (
         Y ::=  TID +  1%Z
       ))
      ((( ARR +  Y) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid) //\\
         Y ===  ((Z_of_fin tid + 1) mod ntrdZ)%Z))).
    Proof.
      apply rule_if; [apply rotate_l5 | apply rotate_l6].
    Qed.

    Lemma rotate_l8 (tid : Fin.t ntrd) :
      CSL bspec tid
      (( ARR +  Y) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid) //\\
          Y ===  ((Z_of_fin tid + 1) mod ntrdZ)%Z))
      ([ ARR +  Y] ::=  X)
      (( ARR +  Y) -->p (1%Qc,  X) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid) //\\
          Y ===  ((Z_of_fin tid + 1) mod ntrdZ)%Z)).
    Proof.
        apply rule_frame; [apply rule_write|]; autounfold; simpl; tauto.
    Qed.

    Lemma rotate_l9 (tid : Fin.t ntrd) :
      (( ARR +  Y) -->p (1%Qc,  X) **
       !( TID ===  (Z_of_fin tid) //\\  X ===  (Z_of_fin tid) //\\
          Y ===  ((Z_of_fin tid + 1) mod ntrdZ)%Z)) |=
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
      destruct (Z.eq_dec x (s ARR + (Z_of_fin tid + 1) mod ntrdZ)); inversion H0; subst; intuition.
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
*)


    Hint Unfold Pre_i Post_i : sep.
    Hint Unfold bspec bpre bpost.
    Hint Rewrite init_spec : sep.
    Require Import VCG.
    Lemma rotate_seq (tid : Fin.t ntrd) : 
      CSL bspec tid
          ((init Pre_i)[@tid] ** !(TID === Z_of_fin tid))%assn
          rotate (init Post_i)[@tid].
    Proof.
      autounfold; autorewrite with sep.
      eapply rule_seq.
      hoare_forward; intros ? ? H'; exact H'.
      eapply rule_seq.
      hoare_forward; intros. 
      sep_normal; sep_normal_in H; sep_split_in H; sep_cancel; sep_combine_in H; sep_normal_in H; exact H.
      autounfold. simpl in H. rewrite init_spec in H. exact H.
      eapply rule_seq.
      hoare_forward.
      hoare_forward; intros ? ? H'; exact H'.
      hoare_forward; intros ? ? H'; exact H'.
      intros ? ? H'; exact H'.
      intros ? ? H'; exact H'.
      eapply Hforward.
      eapply rule_disj.
      eapply Hbackward.
      Focus 2.
        intros ? ? H.
        destruct H; sep_split_in H; sep_normal_in H.
        subA_normalize_in H. simpl in *. 
        sep_normal_in H. sep_split_in H.
        assert (((Z_of_fin tid + 1) mod ntrdZ === 0)%Z s emp_ph).
        { clear H. unfold_conn_all; simpl in *; unfold bexp_to_assn in HP5; simpl in *.
          destruct (Z.eq_dec (s TID) (ntrdZ - 1)); try congruence.
          assert (Z_of_fin tid + 1 = ntrdZ)%Z by (unfold lt; omega).
          rewrite H. apply Z.mod_same; omega. }
        sep_combine_in H.
        exact H.
      hoare_forward. intros ? ? H; exact H.
      eapply Hbackward.
      Focus 2.
        intros ? ? H.
        destruct H; sep_split_in H.
        subA_normalize_in H. simpl in *. 
        sep_normal_in H. sep_split_in H.
        assert (((Z_of_fin tid + 1) mod ntrdZ === Z_of_fin tid + 1)%Z s emp_ph).
        { clear H. unfold_conn_all; simpl in *.
          destruct (Z.eq_dec (s TID) (ntrdZ - 1)); simpl in *; try congruence.
          assert (Z_of_fin tid + 1 < ntrdZ)%Z by (destruct (Fin.to_nat tid); simpl in *; omega).
          rewrite Z.mod_small_iff; [left; omega | omega]. }
        sep_combine_in H.
        exact H.
        hoare_forward; intros ? ? H; exact H.
      intros ? ? H; destruct H; sep_split_in H.
      sep_cancel.
      sep_cancel.
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


  

