Require Export PHeap Lang CSLLemma FreeVariables SeqRules Bdiv Grid Host.
Require Export Qcanon List ZArith PeanoNat Arith.
Global Close Scope Qc_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import MyVector.
Definition default ntrd : (Vector.t assn ntrd * Vector.t assn ntrd) := 
  (init (fun _ => Emp_assn), init (fun _ => Emp_assn)).

Infix "+C" := (Ebinop OP_plus) (at level 50, left associativity).
Infix "*C" := (Ebinop OP_mult) (at level 40, left associativity).
Infix "-C" := (Ebinop OP_sub) (at level 50, left associativity).
Infix "<C" := (Bcomp OP_blt) (at level 55).
Infix "==C" := (Bcomp OP_beq) (at level 55).
Infix "/C" := (Ebinop OP_div) (at level 40, left associativity).
Infix "%C" := (Ebinop OP_mod) (at level 40, left associativity).
Infix "&&C" := (Bbool OP_and) (at level 56, left associativity).
Infix "||C" := (Bbool OP_or) (at level 57, left associativity).
Notation minC x y := (Ebinop OP_min x y).
Notation Zn := Z.of_nat.
