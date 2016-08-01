Require Import GPUCSL scan_lib LibTactics Psatz CSLLemma SetoidClass.
Require Import CSLLemma CSLTactics.

Section SumOf.

Definition sum_of vs := List.fold_right Z.add 0%Z vs.

Local Notation I := (Var "I").
Local Notation T := (Var "T").
Local Notation L := (Var "L").
Local Notation SUM := (Var "SUM").
Local Notation ARR := (Var "ARR").

Definition sum_of_array inv :=
  I :T Int ::= 0%Z ;;
  SUM :T Int ::= 0%Z ;;
  WhileI inv (I <C L) (
    T :T Int ::= [Gl ARR +o I] ;;
    SUM :T Int ::= SUM +C T ;;
    I ::= 1%Z +C I
  ).

Notation ArrL := (Gl ARR).

Definition inv arr vs :=
  Ex i sum, 
    Assn (array (GLoc arr) vs 1%Qc)
         (i <= length vs /\ sum = sum_of (firstn i vs))
         (Ent SUM sum  ::
          Ent ARR arr ::
          Ent I (Zn i) :: 
          Ent L (Zn (length vs)) :: nil).

Lemma sum_ofS i vs :
  (Zn i < Zn (length vs) ->
   (sum_of (firstn i vs) + nth i vs 0) = sum_of (firstn (1 + i) vs))%Z.
Proof.
  intros H.
  assert (H' : i < length vs) by nia.
  clear H; revert H'.
  revert i; induction vs; intros i ?; simpl; try nia.
  - unfold sum_of in *; destruct i; try (simpl; nia).
  - simpl in *.
    intros; destruct i; simpl; try omega.
    rewrite <-IHvs; omega.
Qed.

Lemma firstn_full i (vs : list Z) :
  i <= length vs ->
  ~ (Zn i < Zn (length vs))%Z ->
  sum_of (firstn i vs) = sum_of vs.
Proof.
  intros; assert (Heq : i = length vs) by nia; substs.
  clear.
  induction vs; simpl; congruence.
Qed.

Hint Resolve sum_ofS firstn_full : pure_lemma.

Lemma sum_of_array_ok ntrd BS (tid : Fin.t ntrd) vs arr :
  CSL BS tid
      (Assn (array (GLoc arr) vs 1%Qc)
            (True)
            (ARR |-> arr :: L |-> (Zn (length vs)) :: nil))
      (sum_of_array (inv arr vs))
      (Ex s, Assn (array (GLoc arr) vs 1%Qc)
                  (s = sum_of vs)
                  (SUM |-> s :: ARR |-> arr :: nil)).
Proof.
  unfold sum_of_array, inv.
  hoare_forward.
  hoare_forward.
  hoare_forward.
  hoare_forward.
  
  hoare_forward.
  hoare_forward.
  prove_imp.
  prove_imp.
  prove_imp. 
Qed.
End SumOf.
