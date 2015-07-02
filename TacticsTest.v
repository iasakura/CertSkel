Require Import PHeap.
Require Import assertions.
Require Import Lang.
Require Qcanon.
Require Import VCG.

Section Sep_normal_test.
  Example normalize_test1 (P Q R S : assn) s h :
    (P ** Q ** R ** S) s h -> ((P ** Q) ** (R ** S)) s h.
  Proof.
    intros H. sep_normal. exact H.
  Qed.
  
  Example normalize_test2 (P Q R S : assn) s h : (P ** Q ** R) s h -> ((P ** Q) ** R) s h.
  Proof.
    intros H. sep_normal. exact H.
  Qed.

  Example normalize_test3 (P Q R S : assn) s h : (P ** Q ** R) s h -> (((P ** emp) ** Q) ** R) s h.
  Proof.
    intros H. sep_normal. exact H.
  Qed.

  Example sep_normal4 (P Q R S : nat -> assn) s h : 
    (Ex x, (P x ** Q x ** R x ** S x)) s h -> (Ex x, ((P x ** Q x) ** (R x ** S x))) s h.
  Proof.
    intros H. sep_normal. exact H.
  Qed.

  Example normalize_test5 (P Q R S : assn) s h : 
    (P ** Q ** !(R)) s h -> ((P ** Q) ** !(R)) s h.
  Proof.
    intros H0. sep_normal. apply H0.
  Qed.
End Sep_normal_test.

Section Last_list_in_test.
  Example last_slist_in_test P Q R s h :
    (P ** Q ** R) s h -> ((P ** Q) ** R) s h.
  Proof. intros H; last_slist_in H; exact H. Qed.
End Last_list_in_test.

Section Sep_normal_in_test.
  Example sep_normal_in_test1 (P Q R S : assn) s h :
    ((P ** Q) ** (R ** S)) s h -> (P ** Q ** R ** S) s h.
  Proof.
    intros H. 
    sep_normal_in H. exact H.
  Qed.

  Example sep_normal_in_test2 (P Q R S : assn) s h : ((P ** Q) ** R) s h ->(P ** Q ** R) s h.
  Proof.
    intros H. sep_normal_in H. exact H.
  Qed.

  Example sep_normal_in_test3 (P Q R S : assn) s h : (((P ** emp) ** Q) ** R) s h ->(P ** Q ** R) s h.
  Proof.
    intros H. sep_normal_in H. exact H.
  Qed.

  Example sep_normal_in_goal4 (P Q R S : nat -> assn) s h : 
    (Ex x, ((P x ** Q x) ** (R x ** S x))) s h -> (Ex x, (P x ** Q x ** R x ** S x)) s h.
  Proof.
    intros H. sep_normal_in H. exact H.
  Qed.

  Example sep_normal_in_test5 (P Q R S : assn) s h :
    (((P ** emp ** Q) ** Q) ** R) s h -> (P ** Q ** Q ** R) s h.
  Proof.
    intros H; sep_normal_in H; exact H.
  Qed.
End Sep_normal_in_test.

Section Sep_lift_in_test.
  Example sep_lift_in_test_example (P0 P1 P2 : assn) s h :
    (P0 ** P1 ** P2) s h -> (P1 ** P0 ** P2) s h.
  Proof. intros H. sep_lift_in H 1. exact H. Qed.

  Example sep_lift_in_test0 (P0 P1 P2 P3 P4 : assn) s h :
    (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
  Proof. intros H. sep_lift_in H 0. exact H. Qed.

  Example sep_lift_in_test1 (P0 P1 P2 P3 P4 : assn) s h :
    (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P1 ** P0 ** P2 ** P3 ** P4) s h.
  Proof. intros H. sep_lift_in H 1. exact H. Qed.

  Example sep_lift_in_test2 (P0 P1 P2 P3 P4 : assn) s h :
    (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P2 ** P0 ** P1 ** P3 ** P4) s h.
  Proof. intros H. sep_lift_in H 2. exact H. Qed.

  Example sep_lift_in_test3 (P0 P1 P2 P3 P4 : assn) s h :
    (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P3 ** P0 ** P1 ** P2 ** P4) s h.
  Proof. intros H. sep_lift_in H 3. exact H. Qed.

  Example sep_lift_in_test4 (P0 P1 P2 P3 P4 : assn) s h :
    (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P4 ** P0 ** P1 ** P2 ** P3) s h.
  Proof. intros H. sep_lift_in H 4. exact H. Qed.

  Example sep_lift_in_testEx0 (P0 P1 P2 : nat -> assn) s h :
    (Ex x, P0 x ** P1 x ** P2 x) s h -> (Ex x, (P1 x ** P0 x ** P2 x)) s h.
  Proof. intros H. sep_lift_in H 2. exact H. Qed.

  Example sep_lift_in_testEx1 (P0 P1 P2 : nat -> assn) s h :
    (Ex x, P0 x ** P1 x ** P2 x) s h -> (Ex x, (P2 x ** P0 x ** P1 x)) s h.
  Proof. intros H. sep_lift_in H 3. exact H. Qed.
End Sep_lift_in_test.

Section Sep_split_in_test.
  Example sep_split_in_test5 (P Q R S : assn) s h :
    (((P ** emp ** !(Q)) ** !(S)) ** R) s h ->(P ** R) s h /\ Q s emp_ph /\ S s emp_ph.
  Proof.
    intros H; sep_normal_in H. sep_split_in H. auto.
  Qed.

  Example sep_split_in_test1 (P Q R S : assn) s h :
    ((P ** !(Q)) ** (R ** S)) s h -> (P ** !(Q) ** R ** S) s h.
  Proof.
    intros H. 
    sep_normal_in H. 
    sep_split_in H.
    sep_split; auto.
  Qed.
  
  Example sep_split_in_test2 (P Q R S : assn) s h : ((P ** Q) ** !(R)) s h ->(P ** Q ** !(R)) s h.
  Proof.
    intros H. sep_normal_in H. sep_split_in H. sep_split; auto.
  Qed.

  Example sep_split_in_test3 (P Q R S : assn) s h : (((P ** emp) ** Q) ** R) s h ->(P ** Q ** R) s h.
  Proof.
    intros H. sep_normal_in H. exact H.
  Qed.

  Example sep_split_in_goal4 (P Q R S : nat -> assn) s h : 
    (Ex x, ((P x ** Q x) ** (!(R x) ** S x))) s h -> (Ex x, (P x ** Q x ** !(R x) ** S x)) s h.
  Proof.
    intros H. sep_normal_in H. sep_split_in H. 
  Abort.
End Sep_split_in_test.

Section Sep_lift_test.
  Example sep_lift_test0 (P0 P1 P2 P3 P4 : assn) s h :
    (P0 ** P1 ** P2 ** P3 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
  Proof. intros H. sep_lift 0. exact H. Qed.

  Example sep_lift_test1 (P0 P1 P2 P3 P4 : assn) s h :
    (P1 ** P0 ** P2 ** P3 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
  Proof. intros H. sep_lift 1. exact H. Qed.

  Example sep_lift_test2 (P0 P1 P2 P3 P4 : assn) s h :
    (P2 ** P0 ** P1 ** P3 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
  Proof. intros H. sep_lift 2. exact H. Qed.

  Example sep_lift_test3 (P0 P1 P2 P3 P4 : assn) s h :
    (P3 ** P0 ** P1 ** P2 ** P4) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
  Proof. intros H. sep_lift 3. exact H. Qed.

  Example sep_lift_test4 (P0 P1 P2 P3 P4 : assn) s h :
    (P4 ** P0 ** P1 ** P2 ** P3) s h -> (P0 ** P1 ** P2 ** P3 ** P4) s h.
  Proof. intros H. sep_lift 4. exact H. Qed.

  Example sep_lift_testEx0 (P0 P1 P2 : nat -> assn) s h :
    (Ex x, P1 x ** P0 x ** P2 x) s h -> (Ex x, (P0 x ** P1 x ** P2 x)) s h.
  Proof. intros H. sep_lift 2. exact H. Qed.

  Example sep_lift_testEx1 (P0 P1 P2 : nat -> assn) s h :
    (Ex x, P2 x ** P0 x ** P1 x) s h -> (Ex x, (P0 x ** P1 x ** P2 x)) s h.
  Proof. intros H. sep_lift 3. exact H. Qed.
End Sep_lift_test.

Section Sep_cancel_test.
  Example sep_cansel_example (P Q R : assn) s h :
    (P ** Q ** R) s h -> (R ** Q ** P) s h.
  Proof.
    intros H.
    repeat sep_cancel. 
  Qed.
End Sep_cancel_test.

Section VCG_test.
  Import Qcanon.
  Example find_test (tx ty : Z) (X Y : exp) s h (H : (X -->p(1%Qc, Enum tx) ** (Y -->p(1%Qc, Enum ty))) s h) : (X -->p(1%Qc, Enum tx) ** (Y -->p(1%Qc, Enum ty))) s h.
  Proof.
    find_enough_resource X H.
    exact H.
  Qed.
  
  Example sep_cancel_test (tx ty : Z) (X Y U V : exp) s h :
    (X -->p(1%Qc, U) ** (Y -->p(1%Qc, V)) ** !(Enum tx === U) ** !(Enum ty === V)) s h ->
    (X -->p(1%Qc, Enum tx) ** (Y -->p(1%Qc, Enum ty))) s h.
  Proof.
    intros.
    sep_split_in H.
    sep_cancel.
    sep_cancel.
  Qed.
  Open Scope exp_scope.
  Open Scope bexp_scope.
  Require Import CSL.
  
  Example for_seminor (P : assn) (i : Z) (x a : var) :
    (a +  x -->p (1%Qc, 3%Z)) ** P ** !(x === i) |=
    P ** (a + i -->p (1%Qc, 3%Z)) ** !(x === i).
  Proof.
    intros ? ? ?.
    sep_split_in H.
    sep_cancel.
    sep_cancel.
    sep_cancel.
  Qed.
End VCG_test.

Section subA_test.
  Import Qcanon.
  Example subA_test1 (P Q R S : assn) (X : var) (E : exp) s h :
    subA X E (P ** Q ** R ** S) s h ->
    ((subA X E P) ** (subA X E Q) ** (subA X E R) ** (subA X E S)) s h.
  Proof.
    intros H; subA_normalize_in H; auto.
  Qed.

  Example subA_test2 (P Q R S : assn) (X : var) (E : exp) s h :
    subA X E (P //\\ Q //\\ R //\\ S) s h ->
    ((subA X E P) //\\ (subA X E Q) //\\ (subA X E R) //\\ (subA X E S)) s h.
  Proof.
    intros H; subA_normalize_in H; auto.
  Qed.

  Example subA_test3 (P Q R S : assn) (X : var) (E : exp) s h :
    subA X E (P \\// Q \\// R \\// S) s h ->
    ((subA X E P) \\// (subA X E Q) \\// (subA X E R) \\// (subA X E S)) s h.
  Proof.
    intros H; subA_normalize_in H; auto.
  Qed.

  Example subA_test4 (P Q : assn) (X : var) (E : exp) s h :
    subA X E !(P //\\ Q) s h ->
    !(subA X E P //\\ subA X E Q) s h.
  Proof.
    intros H; subA_normalize_in H; auto.
  Qed.

  Example subA_test5 (E1 E2 : exp) (q : Qc) (X : var) (E : exp) s h :
    subA X E (E1 -->p (q, E2)) s h -> (subE X E E1 -->p (q, subE X E E2)) s h.
  Proof.
    intros H; subA_normalize_in H; auto.
  Qed.

  Example subA_test6 (E1 E2 : exp) (X : var) (E : exp) s h :
    subA X E (E1 === E2) s h -> (subE X E E1 === subE X E E2) s h.
  Proof.
    intros H; subA_normalize_in H; auto.
  Qed.

  Example subA_test7 (P Q : assn) (X : var) (E : exp) s h :
    subA X E (!(P) ** !(Q)) s h ->
    (!(subA X E P) ** !(subA X E Q)) s h.
  Proof.
    intros H; subA_normalize_in H; auto.
  Qed.
End subA_test.


Section Swap.
  Require Import Qcanon.
  Variable ntrd : nat.
  Variable bspec : Bdiv.barrier_spec ntrd.
  
  Open Scope exp_scope.
  Open Scope bexp_scope.

  Definition X := Var 2.
  Definition Y := Var 3.
  Definition T := Var 4.
  Definition U := Var 5.

  Definition swap :=
    T ::= [X] ;;
    U ::= [Y] ;;
    [X] ::= U ;;
    [Y] ::= T.

  Lemma swap_spec (tid : Fin.t ntrd) (tx ty : Z) : 
    CSL bspec tid
       (X -->p(1%Qc, tx) ** (Y -->p(1%Qc, ty))) 
       swap
       (X -->p(1%Qc, ty) ** (Y -->p(1%Qc, tx))).
  Proof.
    unfold swap.
    repeat (hoare_forward || (eapply rule_seq; [hoare_forward; intros ? ? H'; exact H' |])).
    intros ? ? ?.
    sep_normal_in H. sep_split_in H. sep_normal. sep_split. 
    repeat sep_cancel2.
  Qed.
End Swap.