Require Export Lang CSL PHeap.
Require Export assertion_lemmas assertions VCG array_dist.
Require Export Qcanon List MyList ZArith NPeano Arith.
Close Scope Qc_scope.
Global Notation TID := (Var 0).

Set Implicit Arguments.
Unset Strict Implicit.

Require Import MyVector.
Notation FalseP := (fun (_ : stack) (h : pheap) => False).
Definition default ntrd : (Vector.t assn ntrd * Vector.t assn ntrd) := 
  (init (fun _ => FalseP), init (fun _ => FalseP)).

Ltac ex_intro x H :=
  let t := fresh in
  let H' := fresh in 
  lazymatch type of H with
    | ?X ?s ?h => pose X as t; pattern x in t;
      match goal with
        | [t' := ?X x : _ |- _] => 
          let v := fresh in
          match t with t' => 
            assert (H' : (Ex v, X v) s h) by (exists x; auto)
          end 
      end;
      clear t; clear H; rename H' into H
  end.

Ltac ex_intros vs H :=
  match vs with
    | tt => idtac
    | (?v, ?vs) => ex_intro v H; ex_intros vs H
  end.

