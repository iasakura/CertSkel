Require Import PHeap List.

Class hasDefval A := HD {default : A}.
Global Instance Z_hasDefval : hasDefval Z := {default := 0%Z}.
Global Instance val_hasDefval : hasDefval val := {default := VZ 0%Z}.
Global Instance listA_hasDefval A : hasDefval (list A) := {default := nil}.
Global Instance option_hasDefval A : hasDefval (option A) := {default := None}.
Notation get ls i := (nth i ls default).
Eval compute in get (1 :: 2 :: 3 :: nil)%Z 2.
Eval compute in get (Some 1 :: Some 2 :: Some 3 :: nil)%Z 4.
