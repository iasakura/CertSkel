(* 
  parallel prescan algorithm 
  
  loop invariant
  f_c(i) = let 2 ^ k * n := i + 1 in
           let m := max (2 ^ k, offset) in
           sum (i + 1 - m, m, f)
 *)

(* 
original code (from Barrier Invariants: ...) 

// data, out, flag, idx: arrays in shared memory
unsigned offset, d, left, right, temp;
// (i) test each element with predicate p
flag[tid] = p(data[tid]);

// (ii) compute indices for compaction
barrier(); // ϕload

if (tid < n/2) {
  idx[2∗tid] = flag[2∗tid]; idx[2∗tid + 1] = flag[2∗tid + 1];
}
// (ii)(a) upsweep offset = 1;
for (d = n/2; d > 0; d /= 2) {
  barrier(); // ϕus
  if (tid < d) {
    left = offset ∗ (2 ∗ tid + 1) − 1;
    right = offset ∗ (2 ∗ tid + 2) − 1;
    idx[right] += idx[left];
  }
  offset ∗= 2;
}

// (ii)(b) downsweep 
if (tid == 0) idx[n−1] = 0;
for (d = 1; d < n; d ∗= 2) {
  offset /= 2;
  barrier(); // ϕds
  if (tid < d) { 
    left = offset ∗ (2 ∗ tid + 1) − 1;
    right = offset ∗ (2 ∗ tid + 2) − 1;
    temp = idx[left];
    idx[left] = idx[right]; idx[right] += temp;
  }
}
barrier(); // ϕspec
// (iii) compaction if (flag[tid]) out[idx[tid]] = data[tid];
*)

Require Import GPUCSL.

Notation Tid := (Var 0).
Notation In := (Var 1). 
Notation Sum := (Var 2).
Notation Pres := (Var 3).

Notation D := (Var 4).
Notation Offset := (Var 5).
Notation Tmp1 := (Var 6).
Notation Tmp2 := (Var 7).

Infix "+C" := (Eplus) (at level 50).
Infix "*C" := (Emult) (at level 40).
Infix "-C" := (Esub) (at level 50).
Infix "<C" := (Blt) (at level 70).

Notation leftC ARR := (ARR +C Offset *C (Enum 2 *C Tid +C Enum 1) -C Enum 1).
Notation rightC ARR := (ARR +C Offset *C (Enum 2 *C Tid +C Enum 2) -C Enum 1).

Notation "E >>1" := (Ediv2 E) (at level 30).

Coercion Z.of_nat : nat >-> Z.
Variable len : nat.

Definition upsweep :=
  Offset ::= 1 ;;
  D ::= (len / 2) ;;
  WhileI (FalseP) (0 <C D) (
    Cbarrier 0 ;;
    Cif (Tid <C D) (
      Tmp1 ::= [leftC Sum] ;;
      Tmp2 ::= [rightC Sum] ;;
      [rightC Sum] ::= Tmp1 +C Tmp2
    ) (Cskip) ;;
    Offset ::= Offset *C 2
  ).

Definition upInv (i : nat) : 
  is_arrray Sum e 

Definition downsweep :=
  D ::= 1 ;;
  WhileI (FalseP) (D <C len) (
    Offset ::= Offset >>1 ;;
    Cif (Tid <C D) (
      Tmp1 ::= [leftC Sum] ;;
      Tmp2 ::= [rightC Pres] ;;
      [leftC Pres] ::= Tmp2 ;;
      [rightC In] ::= Tmp1 +C Tmp2
    ) (Cskip) ;;
    Cbarrier 1 ;;
   D ::= D *C 2
  ).

