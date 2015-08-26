Require Import GPUCSL.
Section Fold.

(* Var *)
Notation I := (Var 1).
Notation St := (Var 2).
Notation T1 := (Var 3).
Notation T2 := (Var 4).
Notation ARR := (Var 5).
Variable len : nat.
Hypothesis len_is_power_of_2 : exists e : nat, len = 2 ^ len.

Notation " p '>>1'" := (Ediv2 p) (at level 40, left associativity) : exp_scope.

Definition If (b : bexp) (c : cmd) := Cif b c.

Variable ntrd : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.

Eval compute in (Z.div2 1).

Variable f : nat -> Z.

Fixpoint sum_of (len : nat) (f : nat -> Z) :=
  match len with
    | O => 0
    | S n => f n + sum_of n f
  end%Z.

Fixpoint sum_of_skip (len s : nat) (f : nat -> Z) :=
  if lt_dec s < len then f

Definition init_compat (s : nat) (f fc : nat -> Z) :=
  if Nat.eq_dec s 0 then
    sum_of s 
  sum_of s fc = sum_of len f.

Definition INV (i : nat) :=
  Ex (s e st : nat) (fc : nat -> Z),
    !(S === Enum' s) **
    !(pure (s = Div2.div2 (2 ^ e))) **
    (if Nat.eq_dec s 0 then
       !(pure (len = s * st)) ** nth i (distribute 1 (ARR + TID) len fc (nt_step 1) 0) emp
     else
       nth i (distribute s (ARR + TID) len fc (nt_step s) 0) emp).

Definition fold_ker :=
  S ::= Enum' len >>1 ;;
  WhileI FalseP ( Enum' 0 < S ) (
    If ( Evar TID < S ) (
      T1 ::= [ ARR + TID ] ;;
      T2 ::= [ ARR + TID + S ] ;;
      [ ARR + TID ] ::= T1 + T2
    ) (SKIP) ;;
    S ::= S >>1 ;;
    Cbarrier 0
  )%exp.           