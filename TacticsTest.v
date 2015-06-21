Require Import PHeap.
Require Import assertions.

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
    (P ** Q) s h -> R s emp_ph -> ((P ** Q) ** !(R)) s h.
  Proof.
    intros H0 H1. sep_normal; [apply H0 | apply H1].
  Qed.
End Sep_normal_test.

Section Last_list_in_test.
  Example last_slist_in_test P Q R s h :
    (P ** Q ** R) s h -> ((P ** Q) ** R) s h.
  Proof. intros H; last_slist_in H; exact H. Qed.
End Last_list_in_test.

Section Sep_normal_in'_test.
  Example sep_normal_in'_test1 (P Q R S : assn) s h :
    ((P ** Q) ** (R ** S)) s h -> (P ** Q ** R ** S) s h.
  Proof.
    intros H. 
    sep_normal_in' H. exact H.
  Qed.

  Example sep_normal_in'_test2 (P Q R S : assn) s h : ((P ** Q) ** R) s h ->(P ** Q ** R) s h.
  Proof.
    intros H. sep_normal_in' H. exact H.
  Qed.

  Example sep_normal_in'_test3 (P Q R S : assn) s h : (((P ** emp) ** Q) ** R) s h ->(P ** Q ** R) s h.
  Proof.
    intros H. sep_normal_in' H. exact H.
  Qed.

  Example sep_normal_in'_goal4 (P Q R S : nat -> assn) s h : 
    (Ex x, ((P x ** Q x) ** (R x ** S x))) s h -> (Ex x, (P x ** Q x ** R x ** S x)) s h.
  Proof.
    intros H. sep_normal_in' H. exact H.
  Qed.

  Example sep_normal_in'_test5 (P Q R S : assn) s h :
    (((P ** emp ** Q) ** Q) ** R) s h -> (P ** Q ** Q ** R) s h.
  Proof.
    intros H; sep_normal_in' H; exact H.
  Qed.
End Sep_normal_in'_test.

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

Section Sep_normal_in_test.
  Example sep_normal_in_test5 (P Q R S : assn) s h :
    (((P ** emp ** !(Q)) ** !(S)) ** R) s h ->(P ** R) s h /\ Q s emp_ph /\ S s emp_ph.
  Proof.
    intros H; sep_normal_in H; auto.
  Qed.

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
End Sep_normal_in_test.

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