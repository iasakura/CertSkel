Set Implicit Arguments.
Unset Strict Implicit.

Require Import Qcanon.
Require Import assertions.
Require Import Lang.
Require Import CSL.
Require Import PHeap.

Local Notation TID := (Var 0).
Local Notation ARR := (Var 1).
Local Notation X := (Var 2).
Local Notation Y := (Var 3).
Open Scope exp_scope.
Open Scope bexp_scope.

Section independent_prover.
  Ltac inde_simpl :=
    unfold inde in *; simpl in *; intros x s h v Hin.

  Lemma inde_sconj (P Q : assn) (vs : list var) :
    inde P vs -> inde Q vs -> inde (P ** Q) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    unfold_conn; split; intros (ph1 & ph2 & Hp' & Hq' & Hdis' & Heq).
    exists ph1, ph2; repeat split; [apply Hp | apply Hq | idtac..]; auto.
    exists ph1, ph2; repeat split; [apply<-Hp | apply<-Hq | idtac..]; eauto.
  Qed.

  Lemma inde_pure (P : assn) (vs : list var) : inde P vs -> inde !(P) vs.
  Proof.
    intros Hp; inde_simpl.
    unfold_conn; split; intros [H1 H2].
    split; [auto | apply Hp]; auto.
    split; [auto | apply<-Hp]; eauto.
  Qed.

  Lemma inde_conj (P Q : assn) (vs : list var) : inde P vs -> inde Q vs -> inde (P //\\ Q) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    unfold_conn; split; intros [Hp' Hq'].
    split; [apply Hp | apply Hq]; auto.
    split; [apply <-Hp | apply <-Hq]; eauto.
  Qed.

  Lemma inde_disj (P Q : assn) (vs : list var) : inde P vs -> inde Q vs -> inde (P \\// Q) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    unfold_conn; split; intros H.
    destruct H; [left; apply Hp | right; apply Hq]; auto.
    destruct H; [left; apply <-Hp | right; apply <-Hq]; eauto.
  Qed.

  Lemma inde_pointto (E E' : exp) (q : Qc) (vs : list var) :
    List.Forall (indeE E) vs -> List.Forall (indeE E') vs ->
    inde (E -->p (q, E')) vs.
  Proof.
    intros Hp Hq; inde_simpl.
    rewrite List.Forall_forall in *.
    unfold_conn; split; intros H.
    rewrite<-(Hp x Hin s); rewrite<-(Hq x Hin s); auto.
    erewrite (Hp x Hin s); erewrite (Hq x Hin s); eauto.
  Qed.

  Lemma inde_eeq (E E' : exp) (vs : list var) :
    List.Forall (indeE E) vs -> List.Forall (indeE E') vs ->
    inde (E === E') vs.
  Proof.
    intros H H'; inde_simpl.
    rewrite List.Forall_forall in *.
    unfold_conn; split; intros Heq.
    rewrite<-(H x Hin s); rewrite<-(H' x Hin s); auto.
    erewrite (H x Hin s); erewrite (H' x Hin s); eauto.
  Qed.
End independent_prover.

Ltac prove_indeE := unfold indeE, var_upd in *; intros; simpl; auto.

Ltac prove_inde :=
  match goal with
    | [ |- inde (?P ** ?Q) _ ] => apply inde_sconj; prove_inde
    | [ |- inde !(?P) _ ] => apply inde_pure; prove_inde
    | [ |- inde (?P //\\ ?Q) _ ] => apply inde_conj; prove_inde
    | [ |- inde (?P \\// ?Q) _ ] => apply inde_disj; prove_inde
    | [ |- inde (?E -->p (_, ?E')) _ ] => apply inde_pointto; repeat (constructor; prove_indeE)
    | [ |- inde (?E === ?E') _ ] => apply inde_eeq; repeat (constructor; prove_indeE)
    | [ |- _ ] => (unfold inde, var_upd; simpl; try tauto)
  end.

Section subA_simpl.
  Lemma subA_pointto (X : var) (E1 E2 E  : exp) (q : Qc) s h : (subA X E (E1 -->p (q, E2))) s h ->
                                                     (subE X E E1 -->p (q, subE X E E2)) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn.
    repeat rewrite <-subE_assign in *; auto.
  Qed.

  Lemma subA_sconj (P Q : assn) (X : var) (E : exp) s h :
    subA X E (P ** Q) s h -> (subA X E P  ** subA X E Q) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn.
    destruct H as (ph1 & ph2 & ? & ? & ? & ?); eexists; eauto.
  Qed.

  Lemma subA_conj (P Q : assn) (X : var) (E : exp) s h :
    subA X E (P //\\ Q) s h -> (subA X E P //\\ subA X E Q) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn; auto.
  Qed.

  Lemma subA_disj (P Q : assn) (X : var) (E : exp) s h :
    subA X E (P \\// Q) s h -> (subA X E P \\// subA X E Q) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn; auto.
  Qed.

  Lemma subA_pure (P : assn) (X : var) (E : exp) s h :
    subA X E !(P) s h -> !(subA X E P) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn; auto.
  Qed.

  Lemma subA_eeq (X : var) (E E1 E2 : exp) s h :
    subA X E (E1 === E2) s h -> (subE X E E1 === subE X E E2) s h.
  Proof.
    intros; unfold subA' in *; unfold_conn.
    repeat rewrite <-subE_assign in *; auto.
  Qed.
End subA_simpl.

Lemma conj_mono (P Q P' Q' : assn) s h : (P s h -> P' s h) -> (Q s h -> Q' s h) ->
                                         (P //\\ Q) s h -> (P' //\\ Q') s h.
Proof.
  intros ? ? [? ?]; split; auto.
Qed.

Lemma disj_mono (P Q P' Q' : assn) s h : (P s h -> P' s h) -> (Q s h -> Q' s h) ->
                                         (P \\// Q) s h -> (P' \\// Q') s h.
Proof.
  intros ? ? [? | ?]; ((left; tauto) || (right; tauto)).
Qed.

Lemma pure_mono (P P' : assn) s h : (P s h -> P' s h) ->
                                    !(P) s h -> !(P') s h.
Proof.
  intros ? [? ?]; split; auto.
Qed.

Lemma subA_bexp_to_assn (x : var) (e : exp) (b : bexp) :
  subA x e (bexp_to_assn b) |= bexp_to_assn (subB x e b).
Proof.
  intros.
  unfold bexp_to_assn, subA' in *; simpl.
  rewrite <-subB_assign in H; auto.
Qed.

Lemma subA_emp (x : var) (e : exp) : subA x e emp |= emp.
Proof. unfold_conn; auto. Qed.

Ltac subA_normalize_in H :=
  let Hf := fresh in
  match goal with _ => idtac end;
  match type of H with
    | subA _ _ (_ ** _) _ _ =>
      apply subA_sconj in H; eapply scRw in H;
        [ idtac | intros ? ? Hf; subA_normalize_in Hf; exact Hf .. ]
    | subA _ _ (_ //\\ _) _ _ =>
      apply subA_conj in H;  eapply conj_mono in H;
        [ idtac | intros Hf; subA_normalize_in Hf; exact Hf .. ]
    | subA _ _ (_ \\// _) _ _ =>
      apply subA_disj in H;  eapply disj_mono in H;
        [ idtac | intros Hf; subA_normalize_in Hf; exact Hf .. ]
    | subA _ _ (_ -->p (_, _)) _ _ => apply subA_pointto in H
    | subA _ _ !(_) _ _ => eapply subA_pure in H; eapply pure_mono in H;
        [ idtac | intros Hf; subA_normalize_in Hf; exact Hf ]
    | subA _ _ (_ === _) _ _ => apply subA_eeq in H
    | subA _ _ emp _ _ => apply subA_emp in H
    | subA _ _ (bexp_to_assn ?b) _ _ => apply subA_bexp_to_assn in H
    | _ => simpl in H
  end.

Example subA_test6 (E1 E2 : exp) (X : var) (E : exp) s h :
  subA X E (E1 === E2) s h -> (subE X E E1 === subE X E E2) s h.
Proof.
  intros. subA_normalize_in H.
Abort.
Ltac find_addr P E k :=
  idtac "find_addr debug:" P;
  match P with
    | (E -->p (?q, ?E1)) ** ?Q => k (Some 0)
    | _ ** ?Q => find_addr Q E ltac:(fun n =>
        match n with false => k false | Some ?n => k (Some (S n)) end)
    | _ => k false
  end.

Example find_addr_test E E1 P Q s h :(P ** (E -->p (1%Qc, E1)) ** Q) s h.
Proof.
  match goal with [ |- ?H ?s ?h ] => find_addr H E ltac:(fun n => idtac n) end.
  sep_lift 1. 
Abort.

Section hoare_lemmas.
  Variable ntrd : nat.
  Variable bspec : Bdiv.barrier_spec ntrd.
  Variable tid : Fin.t ntrd.
  Lemma Hbackward (P P' Q : assn) (C : cmd) :
    CSL bspec tid P' C Q -> (P |= P') -> CSL bspec tid P C Q.
  Proof.
    intros; eapply rule_conseq; eauto.
  Qed.

  Lemma Hforward (P Q Q' : assn) (C : cmd) :
    CSL bspec tid P C Q' -> (Q' |= Q) -> CSL bspec tid P C Q.
  Proof.
    intros; eapply rule_conseq; eauto.
  Qed.
End hoare_lemmas.

Notation "P <=> Q" := (forall s h, P s h <-> Q s h) (at level 87).

Ltac ltac_bug E H :=
  match type of H with
    | ((_ ** _) _ _) =>
      let Hf := fresh in
      eapply scRw_stack in H; [idtac | intros ? Hf; exact Hf |
                               intros ? Hf; ltac_bug E Hf; exact Hf];
      match goal with _ => idtac  end;
      match type of H with
        | ((_ ** _ ** _) _ _) => apply scCA in H
        | ((_ ** _) _ _) => apply scC in H
      end 
    | _ => idtac
  end.

Example ltac_bug P Q s h n (tid : Fin.t n) :
  (P ** Q ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid))) s h -> False.
Proof.
  intros.
  sep_split_in H.
  ltac_bug (ARR + Z_of_fin tid) H.
Abort.

Example find_test P Q s h n (tid : Fin.t n) :
  (P ** Q ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid))) s h -> False.
Proof.
  intros.
  sep_split_in H.
  find_enough_resource (ARR + Z_of_fin tid) H.
Abort.

Example sep_combine_test P Q R S s h : (P ** Q ** !(R) ** !(S)) s h -> True.
Proof.
  intros H; sep_split_in H.
  sep_combine_in H.
Abort.

Lemma rule_assign_forward (ntrd : nat) (bspec : Bdiv.barrier_spec ntrd) (tid : Fin.t ntrd) (X : var) (E : exp) (P : assn) :
  CSL bspec tid P (X ::= E) (Ex v, subA X v P ** !(X === subE X v E)).
Proof.
  unfold subA'.
  eapply Hbackward.
  apply rule_assign.
  intros s h H; exists (s X).
  sep_split; unfold_conn; simpl.
  rewrite subE_assign; unfold var_upd; simpl.
  destruct (var_eq_dec X X) as [_|]; try congruence.
  f_equal; extensionality x.
  destruct (var_eq_dec _ _); subst; congruence.

  assert (Heq : s = var_upd (var_upd s X (edenot E s)) X (s X)); [|rewrite <-Heq; auto].
  extensionality x; unfold var_upd; destruct (var_eq_dec _ _); subst; congruence.
Qed.

Global Create HintDb sep.

Ltac simplify :=
  autounfold; simpl; autorewrite with sep.

Ltac frame_analysis P :=
  let Pe := fresh in
  evar (Pe : assn);
  let Hf := fresh in
  let s := fresh in
  let h := fresh in
  intros s h Hf;
  let Hf' := fresh in
  assert (Hf' : (P ** Pe) s h);
  [ simplify;
    repeat match goal with
      | [P' := ?ev : assn, H : ?Q ?s ?h |- ?P ?s ?h] => match P with
           | P' => is_evar ev; sep_combine_in H; exact H
        end
      | _ => progress (sep_split_in Hf; unfold lt in *; sep_cancel; sep_combine_in Hf)
    end | exact Hf' ].

Lemma rule_if_disj (ntrd : nat) (bspec : Bdiv.barrier_spec ntrd) (tid : Fin.t ntrd) (P Q1 Q2 : assn)
      (b : bexp) (C1 C2 : cmd) :
  CSL bspec tid (P ** !(b)) C1 Q1 -> CSL bspec tid (P ** !(Bnot b)) C2 Q2 ->
  CSL bspec tid (P) (Cif b C1 C2) (Q1 \\// Q2).
Proof.
  intros.
  eapply rule_if;
  eapply Hforward; unfold Apure; unfold bexp_to_assn in *;
  [eapply Hbackward; [apply H |] | | eapply Hbackward; [apply H0 |] |];
   try (intros; destruct H1; exists h, emp_ph; repeat split; auto); intros; unfold_conn; tauto.
Qed.

Definition WhileI (I : assn) (b : bexp) (c : cmd) := nosimpl (Cwhile b c).

Ltac hoare_forward :=
  match goal with
    | [ |- CSL ?bspec ?tid ?P (?X ::= [?E]) ?Q ] => 
      idtac "case: read";
      let Hf := fresh in
      let s := fresh in
      eapply Hbackward; [idtac |
        intros s ? Hf;
        sep_normal_in Hf;
        sep_split_in Hf;
        find_enough_resource E Hf;
        sep_combine_in Hf;
        exact Hf];
      eapply Hforward; [
        eapply rule_frame;
        [eapply rule_read; idtac "ok!!!"; prove_indeE | prove_inde] | prove_inde ]
    | [ |- CSL ?bspec ?tid ?P ([?E] ::= _) ?Q ] =>
      idtac "case: write";
      let Hf := fresh in
      let s := fresh in
      eapply Hbackward; [idtac |
        intros s ? Hf;
        sep_normal_in Hf;
        sep_split_in Hf;
        find_enough_resource E Hf;
        sep_combine_in Hf;
        exact Hf];
      eapply Hforward; [
        eapply rule_frame;
        [eapply rule_write; idtac "ok!!!" | prove_inde ] | idtac]
    | [ |- CSL ?bspec ?tid ?P (?X ::= _) ?Q] =>
      let Hf := fresh in
      eapply Hforward; [
        apply rule_assign_forward | idtac ]
    | [ |- CSL ?bspec ?tid ?P (Cbarrier ?i) ?Q] =>
      idtac "called";
      eapply Hbackward; [
        eapply Hforward; [
          eapply rule_frame; 
          [eapply rule_barrier | prove_inde] |
           autounfold; simpl; repeat rewrite MyVector.init_spec in *] | 
        frame_analysis (Vector.nth (fst (bspec i)) tid)]
    | [ |- CSL ?bspec ?tid ?P (Cif ?b ?c1 ?c2) ?Q ] =>
      eapply Hforward; [
          eapply rule_if_disj | idtac]
    | [ |- CSL ?bspec ?tid (?P1 \\// ?P2) ?C ?Q ] =>
      eapply rule_disj; hoare_forward
    | [ |- CSL ?bspec ?tid ?P (WhileI ?I ?b ?c) ?Q ] => 
      let Hf := fresh in
      eapply Hbackward; [
        eapply Hforward; [apply (@rule_while _ _ _ I) | idtac] |
        idtac
      ]
  end.

Section pmap.
  Definition ele (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s <= edenot y s)%Z).
  Notation "x '<==' y" := (ele x y) (at level 70, no associativity).
  Definition elt (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s < edenot y s)%Z).
  Notation "x '<<' y" := (elt x y) (at level 70, no associativity).

  Variable ntrd : nat.
  Variable len : nat.
  
  Local Notation I := (Var 4).

  Definition map :=
    I ::= TID%Z;;
    Cwhile (I < Z.of_nat len) (
      X ::= [ARR + I] ;;
      [ARR + I] ::= X + 1%Z ;;
      I ::= I + Z.of_nat ntrd%Z
    ).
  Require Import NPeano.
  Require Import Arith.
  Require Import List.
  Import ListNotations.
  Local Open Scope list_scope.
  Local Close Scope exp_scope.
  Local Open Scope nat_scope.

  Definition modi_filter {A : Type} (l : list A) s i n :=
    map snd (filter (fun x => beq_nat (fst x mod n) i) (combine (seq s (length l)) l)).

  Require Import Omega.

  Lemma seq_add : forall (n1 n2 s : nat), seq s (n1 + n2) = seq s n1 ++ seq (s + n1) n2.
  Proof.
    induction n1; intros n2 s; simpl; eauto.
    rewrite <-plus_n_Sm, IHn1; simpl; eauto.
  Qed.
  
  Lemma combine_app :
    forall (S T : Type) (s1 s2 : list S) (t1 t2 : list T),
      length s1 = length t1 -> combine (s1 ++ s2) (t1 ++ t2) = combine s1 t1 ++ combine s2 t2.
  Proof.
    induction s1; intros s2 t1 t2 Hlen.
    - destruct t1; inversion Hlen; simpl; eauto.
    - destruct t1; inversion Hlen; simpl; rewrite IHs1; eauto.
  Qed.
    
  Lemma filter_app : 
    forall (T : Type) (a : T -> bool) (s1 s2 : list T),
      filter a (s1 ++ s2) = filter a s1 ++ filter a s2.
  Proof.
    induction s1; simpl; eauto.
    intros s2; rewrite IHs1; destruct (a a0); eauto.
  Qed.

  Fixpoint mask {T : Type} (m : list bool) (l : list T) :=
    match m with
      | nil => nil
      | b :: m => 
        match l with
          | nil => nil
          | x :: l => if b then x :: mask m l else mask m l
        end
      end.

  Lemma filter_mask:
    forall (T : Type) (a : T -> bool) (s : list T),
      filter a s = mask (map a s) s.
  Proof.
    induction s; simpl; eauto.
    rewrite IHs; eauto.
  Qed.

  Fixpoint nseq (T : Type) (n : nat) (d : T) : list T :=
    match n with
      | 0 => nil
      | S n => d :: nseq n d
    end.
  
  Lemma eq_from_nth :
    forall (T : Type) (x : T) (s1 s2 : list T),
      length s1 = length s2 ->
      (forall i : nat, i < length s1 -> nth i s1 x = nth i s2 x) -> s1 = s2.
  Proof.
    induction s1; intros [|y s2]; inversion 1; eauto.
    intros Heq; f_equal.
    apply (Heq 0); simpl; omega.
    apply IHs1; eauto.
    intros i H'; pose proof (Heq (S i)); simpl in H0; apply H0; omega.
  Qed.

  Lemma length_nseq : forall (T : Type) (n : nat) (x : T), length (nseq n x) = n.
  Proof.
    intros; induction n; simpl; omega.
  Qed.

  Lemma nth_map :
    forall (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2) 
           (f : T1 -> T2) (n : nat) (s : list T1),
      n < length s -> nth n (map f s) x2 = f (nth n s x1).
  Proof.
    induction n; intros [|y s]; simpl; eauto; try omega.
    intros. firstorder; omega.
  Qed.

  Lemma nth_nseq :
    forall (T : Type) (x0 : T) (m : nat) (x : T) (n : nat),
      nth n (nseq m x) x0 = (if leb m n then x0 else x).
  Proof.
    induction m; intros; simpl; eauto.
    - destruct n; simpl; eauto.
    - destruct n; eauto.
  Qed.

  Lemma mask_cat:
    forall (T : Type) (m1 m2 : list bool) (s1 s2 : list T),
      length m1 = length s1 -> mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
  Proof.
    induction m1; intros; destruct s1; simpl in *; try omega; eauto.
    rewrite IHm1; destruct a; simpl; eauto.
  Qed.

  Lemma mask_false:
    forall (T : Type) (s : list T ) (n : nat), mask (nseq n false) s = nil.
  Proof.
    induction s; destruct n; simpl in *; eauto.
  Qed.

  Lemma skipn_length:
    forall (T : Type) (s : list T) (n0 : nat), length (skipn n0 s) = length s - n0.
  Proof.
    induction s; destruct n0; simpl; eauto.
  Qed.

  Lemma nth_skipn:
    forall (n0 : nat) (T : Type) (x0 : T) (s : list T) (i : nat),
      nth i (skipn n0 s) x0 = nth (n0 + i) s x0.
  Proof.
    induction i; destruct n s.
    
    
  Lemma modi_filter_cons : forall {A : Type} (l : list A) (s i n : nat) (d : A),
    n <> 0 ->
    n <= length l -> i < n ->
    modi_filter l (s * n) i n = nth i l d :: modi_filter (skipn n l) (S s * n) i n.
  Proof.
    unfold modi_filter; intros A l s i n d Hn0 Hnl Hin.
    assert (Heq :combine (seq (s * n) (length l)) l =
                 combine (seq (s * n) n) (firstn n l) ++
                    combine (seq (S s * n) (length l - n)) (skipn n l)).
    { assert (H' : length l = n + (length l - n)) by omega.
      rewrite H' at 1; rewrite seq_add; rewrite <-(firstn_skipn n l) at 2.
      rewrite combine_app; simpl.
      cutrewrite (s * n + n = n + s * n); [|omega]; eauto.
      rewrite seq_length, firstn_length; rewrite Min.min_l; eauto. }
    rewrite Heq, filter_app, map_app; clear Heq.
    match goal with
      | [|- ?X ++ ?Y = ?Z :: ?W] => assert (Heq : X = Z :: nil /\ Y = W)
    end; [|destruct Heq as [Heq1 Heq2]; rewrite Heq1, Heq2; simpl; eauto].
    split.
    - rewrite filter_mask.
      assert (Heq : map (fun x => beq_nat (fst x mod n) i) (combine (seq (s * n) n) (firstn n l)) =
                    nseq i false ++ (true :: nseq (n - i - 1) false)); [|rewrite Heq; clear Heq].
      { apply (@eq_from_nth _ false).
        { rewrite map_length, combine_length, firstn_length, app_length, seq_length; simpl.
          rewrite !length_nseq. 
          repeat rewrite !Min.min_l; eauto; omega. }
        rewrite map_length; intros j Hj; rewrite (nth_map (0, d)); auto.
        rewrite combine_length, seq_length, firstn_length in Hj.
          rewrite Min.min_l in Hj; [|rewrite Min.min_l; auto].
        rewrite combine_nth; [|rewrite seq_length, firstn_length, Min.min_l; omega]; simpl.
        rewrite seq_nth; auto.
        rewrite plus_comm, Nat.add_mod, Nat.mod_mul, <-plus_n_O, Nat.mod_mod, Nat.mod_small; auto.
        assert (j < i \/ j = i \/ i < j) as [H | [H | H]] by omega.
        + rewrite app_nth1; [| rewrite length_nseq; auto].
          rewrite nth_nseq; cutrewrite (leb i j = false); [|apply leb_correct_conv; omega].
          apply beq_nat_false_iff; omega.
        + rewrite app_nth2; rewrite length_nseq; [|omega].
          subst; rewrite minus_diag; simpl.
          apply beq_nat_true_iff; omega.
        + rewrite app_nth2; rewrite length_nseq; try omega.
          case_eq (j - i); intros; try omega; simpl; rewrite nth_nseq.
          destruct (leb (n - i - 1) n0); apply beq_nat_false_iff; omega. }
      rewrite <-(firstn_skipn i (combine _ _)).
      rewrite mask_cat;
        [|rewrite length_nseq, !firstn_length, combine_length, seq_length,
                  firstn_length; repeat rewrite Min.min_l; auto; omega].
      case_eq (skipn i (combine (seq (s * n) n) (firstn n l))); [|intros x ss]; intros H.
      apply (f_equal (@length (nat * A))) in H; simpl in H.
      rewrite skipn_length, combine_length, seq_length, firstn_length in H.
      rewrite Min.min_l in H; [|repeat rewrite Min.min_l; omega]; omega.
      simpl; rewrite !mask_false; simpl; f_equal.
      apply (f_equal (fun x => nth 0 x (0, d))) in H; simpl in H.
      rewrite nth_skipn.

Section map.
  Definition ele (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s <= edenot y s)%Z).
  Notation "x '<==' y" := (ele x y) (at level 70, no associativity).
  Definition elt (x y : exp) := (nosimpl (fun s (h : pheap) => edenot x s < edenot y s)%Z).
  Notation "x '<<' y" := (elt x y) (at level 70, no associativity).
  Local Notation I := (Var 4).
  Variable len : nat.
  Variable ntrd : nat.
  Notation ntrdZ := (Z.of_nat ntrd).
  Variable f : nat -> Z.
  Definition loop_inv : assn :=
    Ex x : nat,
      is_array ARR x (fun i => Z.succ (f i)) **
      is_array (ARR + Z.of_nat x) (len - x) (fun j => f (j + x)) **
      !(I === Z.of_nat x) ** !(pure (x < len))%nat.

  Definition map :=
    I ::= 0%Z;;
    WhileI loop_inv (I < Z.of_nat len) (
      X ::= [ARR + I] ;;
      [ARR + I] ::= X + 1%Z ;;
      I ::= I + 1%Z
    ).

  Lemma is_array_unfold : forall (n : nat) (i : nat) (fi : nat -> Z) (e : exp),
    (i < n)%nat ->
    is_array e n fi |=
      (e + Z.of_nat i) -->p (1, fi i) **
      (is_array e i fi) **
      (is_array (e + Z.succ (Z.of_nat i)) (n - i - 1) (fun j => fi (S (i + j))%nat)).
  Proof.
    induction n; intros; [omega|].
    assert (i < n \/ i = n)%nat as [Hle|] by omega; subst.
    simpl in H0.
    eapply scRw in H0; [|intros ? ? H'; exact H' | intros ? ? H'; apply (IHn i) in H'; [exact H' | auto]].
    do 2 sep_cancel.
    cutrewrite (S n - i - 1 = S (n - i - 1)); [|omega].
    simpl; apply scC; sep_cancel.
    assert (Z.of_nat i + Z.succ (Z.of_nat (n - i - 1)) = Z.of_nat n)%Z.
    (rewrite <-Zplus_succ_r_reverse, <-Znat.Nat2Z.inj_add, <-Znat.Nat2Z.inj_succ; f_equal; omega).
    assert (S (i + (n - i - 1)) = n)%nat by omega.
    sep_cancel.
    simpl in H0.
    sep_cancel.
    cutrewrite (S n - n - 1 = 0); [|omega]; simpl.
    sep_normal; sep_cancel.
  Qed.

  Lemma is_array_S : forall (n : nat) (fi : nat -> Z) (e : exp),
    is_array e (S n) fi |= e -->p (1, fi 0) ** is_array (e + 1%Z) n (fun i => fi (S i)).
  Proof.
    induction n as [|n]; [simpl|]; intros; sep_cancel.
    cutrewrite (is_array e (S (S n)) fi =
                ((e + Z.of_nat (S n)) -->p (1, fi (S n)) ** is_array e (S n) fi)) in H; [|auto].
    cutrewrite (is_array (e + 1%Z) (S n) (fun i : nat => fi (S i)) =
                (e + 1%Z + Z.of_nat n -->p (1, fi (S n)) ** 
                is_array (e + 1%Z) n (fun i : nat => fi (S i)))); [|auto].
    apply scCA. rewrite Znat.Nat2Z.inj_succ in H. sep_cancel.
    apply IHn in H. auto.
  Qed.

  Lemma Ex_intro {T : Type} (P : T -> assn) (x : T) :P x |= (Ex x, P x).
  Proof. intros; exists x; auto. Qed.

  Lemma map_correct (tid : Fin.t ntrd) (bspec : Bdiv.barrier_spec ntrd) :
    CSL bspec tid (is_array ARR len f) map (is_array ARR len (fun i => Z.succ (f i))).
  Proof.
    unfold map.
    eapply rule_seq; [hoare_forward; intros ? ? H; exact H| ].
    hoare_forward.
    eapply Hbackward.
    Focus 2.
    intros ? ? H.
    unfold loop_inv in H; sep_split_in H; destruct H; repeat sep_split_in H.
    cutrewrite (len - x = S (len - x - 1)) in H; [|unfold Apure in HP1; simpl in HP1; omega].
    eapply scRw in H; [idtac | intros ? ? H'; exact H' |
                       intros ? ? H'; apply is_array_S in H'; exact H'].
    sep_lift_in H 1.
    sep_combine_in H.

    
    
 (*Section Hoare_test.
  Variable ntrd : nat.
  Notation ntrdZ := (Z.of_nat ntrd).

  Require Import MyVector.
  Import VectorNotations.

  Definition bpre (tid : Fin.t ntrd) := 
    (ARR + (Z_of_fin tid) -->p (1%Qc, (Z_of_fin tid)))%assn.
  Definition bpost (tid : Fin.t ntrd) := 
    (ARR + ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p (1%Qc, ((Z_of_fin tid + 1) mod ntrdZ)%Z).
  Notation FalseP := (fun (_ : stack) (h : pheap) => False).
  Definition default : (Vector.t assn ntrd * Vector.t assn ntrd) := 
    (init (fun _ => FalseP), init (fun _ => FalseP)).

  Definition bspec (i : nat) :=
    match i with
      | 0 => (init bpre, init bpost)
      | S _ => default
    end.

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
      hoare_forward; [hoare_forward | hoare_forward | idtac].
      intros. simpl in H. sep_split_in H. subA_normalize_in H. simpl in H.
      sep_combine_in H. exact H.
      intros. simpl in H. sep_split_in H. subA_normalize_in H. simpl in H. sep_combine_in H. exact H.
      intros ? ? H.
      destruct H.
      sep_split_in H.
    Abort.


  Hint Unfold bspec bpre bpost.
  Hint Rewrite MyVector.init_spec : sep.
  Lemma rotate_l4 (tid : Fin.t ntrd) :
    CSL bspec tid
      (( ARR +  (Z_of_fin tid)) -->p (1%Qc,  (Z_of_fin tid)) **
                                !( TID ===  (Z_of_fin tid)) ** !(X ===  (Z_of_fin tid)))
      (Cbarrier 0)
      (( ARR +  ((Z_of_fin tid + 1) mod ntrdZ)%Z) -->p 
          (1%Qc,  ((Z_of_fin tid + 1) mod ntrdZ)%Z) **
      !( TID ===  (Z_of_fin tid)) **  !(X ===  (Z_of_fin tid))).
  Proof.
    hoare_forward.
    intros.
    sep_cancel.
  Qed.

  Lemma rotate_l2 (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    (inde P (X :: List.nil)) -> (inde Q (X :: List.nil)) -> (indeE E X) ->
    CSL bspec tid 
      (P ** Q ** (E -->p (1%Qc, 3%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
      (X ::= [ ARR + TID]) 
      (P ** Q ** (ARR + TID -->p (1%Qc, (Z_of_fin tid))) ** !( TID === (Z_of_fin tid)) ** (E -->p (1%Qc, 3%Z))).
    Proof.
      intros. 
      hoare_forward.
      intros; sep_normal_in H2; sep_split_in H2; sep_normal; sep_split; solve [auto | repeat sep_cancel].
    Qed.

  Lemma rotate_l3 (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    (inde P (X :: List.nil)) -> (inde Q (X :: List.nil)) -> (indeE E X) ->
    CSL bspec tid 
      (P ** Q ** (E -->p (full_p%Qc, 2%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
      ([ ARR + TID] ::= 3%Z) 
      (P ** Q ** (ARR + TID -->p (full_p%Qc, 3%Z)) ** !( TID === (Z_of_fin tid)) ** (E -->p (1%Qc, 2%Z))).
  Proof.
    intros. hoare_forward.
    intros; repeat sep_cancel.
  Qed.

  Lemma test_assign (tid : Fin.t ntrd) (P Q : assn) (E : exp) :
    CSL bspec tid 
        (P ** Q ** (E -->p (full_p%Qc, 2%Z)) ** ( (ARR +  Z_of_fin tid) -->p (1%Qc,  (Z_of_fin tid))) ** !( TID ===  (Z_of_fin tid)))
        (X ::= 3%Z) 
        (P ** Q ** (ARR + TID -->p (full_p%Qc, 3%Z)) ** !( TID === (Z_of_fin tid)) ** (E -->p (1%Qc, 2%Z))).
  Proof.
    intros. hoare_forward.
    intros s h H.
    sep_split_in H; simpl in *.
    subA_normalize_in H.
  Abort.
End Hoare_test.*)
