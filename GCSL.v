Require Export CSL.
Import Lang.

Section GlobalCSL.
Variable ntrd : nat.
Variable nblk : nat.

Fixpoint safe_ng (n : nat) (gs : g_state) (Q : assn) :=
  match n with
    | 0 => True
    | S n =>

