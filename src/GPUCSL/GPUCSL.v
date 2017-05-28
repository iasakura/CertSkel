Require Export PHeap Lang CSLLemma FreeVariables SeqRules Bdiv Grid Host.
Require Export Qcanon List ZArith PeanoNat Arith.
Global Close Scope Qc_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import MyVector.
Definition default ntrd : (Vector.t assn ntrd * Vector.t assn ntrd) := 
  (init (fun _ => Emp_assn), init (fun _ => Emp_assn)).
