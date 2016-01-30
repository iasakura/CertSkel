Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics Psatz.

Section Stencil.
Local Notation smem := (Var "smem").
Local Notation arr := (Var "arr").
Local Notation out := (Var "out").
Local Notation t0 := (Var "t0").
Local Notation t1 := (Var "t1").
Local Notation t2 := (Var "t2").
Local Notation tid := (Var "tid").
Local Notation bid := (Var "bid").

Variable ntrd nblk : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis nblk_neq_0 : nblk <> 0.

Local Notation gid := (tid +C bid *C Zn ntrd).

Definition stencil :=
  t0 ::= [Gl arr +o gid] ;;
  [Sh smem +o (tid +C 1%Z)] ::= t0 ;;
  Cif (tid == 0%Z) (
    Cif (bid == 0%Z) ([Sh smem +o 0%Z] ::= 0%Z)
    ( t0 ::= [Gl arr +o (gid -C 1%Z)];; [Sh smem +o 0%Z] ::= t0)
  ) (Cskip
  ) ;;
  Cif (tid == Zn nblk -C 1%Z) (
    Cif (bid == 0%Z) ([Sh smem +o (Zn ntrd +C 1%Z)] ::= 0%Z)
    ( t0 ::= [Gl arr +o (gid +C 1%Z)];; [Sh smem +o (Zn ntrd +C 1%Z)] ::= t0)
  ) (Cskip
  ) ;;
  Cbarrier 0 ;;
  t0 ::= [Sh smem +o tid] ;;
  t1 ::= [Sh smem +o (tid +C 1%Z)] ;;
  t2 ::= [Sh smem +o (tid +C 2%Z)] ;;
  [Gl out +o gid] ::= t0 +C t1 +C t2.

