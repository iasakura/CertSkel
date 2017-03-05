Require Export Lang CSL Grid PHeap.
Require Export assertion_lemmas assertions VCG array_dist sep_tacs.
Require Export Qcanon List MyList ZArith PeanoNat Arith.
Close Scope Qc_scope.

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

Infix "+C" := (Ebinop OP_plus) (at level 50, left associativity).
Infix "*C" := (Ebinop OP_mult) (at level 40, left associativity).
Infix "-C" := (Ebinop OP_sub) (at level 50, left associativity).
Infix "<C" := (Bcomp OP_blt) (at level 55).
Infix "==C" := (Bcomp OP_beq) (at level 55).
Infix "/C" := (Ebinop OP_div) (at level 40, left associativity) : exp_scope.
Infix "%C" := (Ebinop OP_mod) (at level 40, left associativity) : exp_scope.
Infix "&&C" := (Bbool OP_and) (at level 57, left associativity) : exp_scope.
Infix "||C" := (Bbool OP_or) (at level 58, left associativity) : exp_scope.
Notation minC x y := (Ebinop OP_min x y).
Notation Zn := Z.of_nat.
