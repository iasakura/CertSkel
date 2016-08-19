Require Import GPUCSL scan_lib LibTactics Psatz CSLLemma SetoidClass.
Require Import CSLLemma CSLTactics.

Section map.
Variable ntrd nblk : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis nblk_neq_0 : nblk <> 0.
Hint Resolve ntrd_neq_0 nblk_neq_0.
Variable tid : Fin.t ntrd.
Variable bid : Fin.t nblk.

Local Notation I := (Var "I").
Local Notation T := (Var "T").
Local Notation L := (Var "L").
Local Notation ARR := (Var "ARR").
Notation OUT := (Var "out").
Notation TID := (Var "tid").
Notation BID := (Var "bid").

Definition map inv :=
  I :T Int ::= TID +C BID *C Zn ntrd;;
  WhileI inv (I <C L) (
    T :T Int ::= [Gl ARR +o I] ;;
    [Gl OUT +o I] ::= T ;;
    I ::= Zn ntrd *C Zn nblk +C I
  ).

Notation arri a := (skip a (ntrd * nblk) (nf tid + nf bid * ntrd)).

Definition inv arr out varr vout :=
  Ex j i, 
    Assn (array' (GLoc arr) (arri varr) 1%Qc ***
          array' (GLoc out) (arri (firstn i varr ++ skipn i vout)) 1%Qc)
          (i = j * (ntrd * nblk) + (nf tid + nf bid * ntrd) /\
           i < length varr + ntrd * nblk /\
          length varr = length vout)
         (ARR |-> arr ::
          OUT |-> out ::
          I   |-> Zn i ::
          L   |-> (Zn (length varr)) :: nil).

Lemma ok1 n m j : n + (j * n + m) = (S j) * n + m. nia. Qed.
Lemma ok2 n m : m = 0 * n + m. nia. Qed.
Lemma tid_bid : nf tid + nf bid * ntrd < ntrd * nblk.
Proof.
  pose proof ntrd_neq_0; pose proof nblk_neq_0.
  assert (nf tid < ntrd) by eauto.
  assert (nf bid < nblk) by eauto.
  forwards*: (id_lt_nt_gr H1 H2).
  lia.
Qed.
Lemma ntrd_nblk_neq_0 : ntrd * nblk <> 0. pose ntrd_neq_0; pose nblk_neq_0; nia. Qed.

Hint Resolve ok1 ok2 tid_bid ntrd_nblk_neq_0 : pure_lemma.

Ltac t :=
  autorewrite with pure; simpl;
  abstract (repeat match goal with
                   | [|- context [if ?b then _ else _]] => destruct b; substs; eauto; try (false; lia); try lia
                   | [H : context [if ?b then _ else _] |- _] => destruct b; substs; eauto; try (false; lia); try lia
                   end;
             do 2 f_equal; lia). 


Lemma loop_inv_ok i j vs (varr vout : list val) :
  i = j * (ntrd * nblk) + (nf tid + nf bid * ntrd) ->
  vs = firstn i varr ++ skipn i vout ->
  (Zn i < Zn (length varr))%Z ->
  length varr = length vout ->
  arri (set_nth i vs (get varr i)) =
  arri (firstn (ntrd * nblk + i) varr ++ skipn (ntrd * nblk + i) vout).
Proof.
  intros; substs.
  applys (>>(@eq_from_nth) (@None Z)).
  { t. }
  { intros i; repeat autorewrite with pure; simpl in *.
    destruct lt_dec; [|false; lia]; intros H.
    assert (i = j * (ntrd * nblk) + (nf tid + nf bid * ntrd) ->
            i mod (ntrd * nblk) = nf tid + nf bid * ntrd) by (intros; substs; prove_mod_eq).
    assert (ntrd * nblk <> 0) by eauto with pure_lemma.
    assert (j * (ntrd * nblk) + (nf tid + nf bid * ntrd) < i < S j * (ntrd * nblk) + (nf tid + nf bid * ntrd) ->
            i mod (ntrd * nblk) <> nf tid + nf bid * ntrd).
    { intros; apply (mod_between j); eauto with pure_lemma. }
    Time t. }
Qed.

Lemma before_loop_ok (varr vout : list val) :
  nf tid < ntrd ->
  nf tid + nf bid * ntrd < ntrd * nblk ->
  length varr = length vout ->
  arri vout =
  arri (firstn (nf tid + nf bid * ntrd) varr ++ skipn (nf tid + nf bid * ntrd) vout).
Proof.
  intros; applys (>>(@eq_from_nth) (@None Z)).
  { t. }
  { intros.
    repeat autorewrite with pure; simpl in *.
    assert (i < nf tid + nf bid * ntrd -> (i mod (ntrd * nblk)) <> nf tid + nf bid * ntrd).
    { intros; rewrite Nat.mod_small; eauto; try lia. }
  Time t. }
Qed.

Lemma after_loop_ok (varr vout : list val) vs i :
  ~(Zn i < Zn (length varr))%Z ->
  length varr = length vout ->
  vs = firstn i varr ++ skipn i vout ->
  arri vs = arri varr.
Proof.
  intros; substs; eapply (@eq_from_nth _ None).
  { t. }
  intros i'; repeat autorewrite with pure; simpl; intros ?.
  Time t.
Qed.

Hint Resolve loop_inv_ok before_loop_ok after_loop_ok : pure_lemma.

Lemma map_ok BS arr out varr vout : 
  CSL BS tid 
      (Assn (array' (GLoc arr) (arri varr) 1%Qc ***
             array' (GLoc out) (arri vout) 1%Qc)
            (length varr = length vout)
            (TID |-> Zn (nf tid) ::
             BID |-> Zn (nf bid) ::
             L   |-> Zn (length varr) :: 
             ARR |-> arr ::
             OUT |-> out :: nil))
      (map (inv arr out varr vout))
      (Assn (array' (GLoc arr) (arri varr) 1%Qc ***
             array' (GLoc out) (arri varr) 1%Qc)
            True
            (L   |-> Zn (length varr) ::
             ARR |-> arr ::
             OUT |-> out :: nil)).
Proof.
  unfold map, inv.
  forwards*: (nf_lt tid).
  forwards*: (tid_bid).
  assert (ntrd <> 0) by eauto.
  hoare_forward.
  hoare_forward.
  hoare_forward.
  hoare_forward.
  hoare_forward.
  prove_imp; eauto with pure_lemma.

  prove_imp; eauto with pure_lemma.

  prove_imp; eauto with pure_lemma.
Qed.

End map.