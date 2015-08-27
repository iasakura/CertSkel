Require Import GPUCSL.
Section Fold.

(* Var *)
Notation I := (Var 1).
Notation St := (Var 2).
Notation T1 := (Var 3).
Notation T2 := (Var 4).
Notation ARR := (Var 5).

Fixpoint sum_of (len : nat) (f : nat -> Z) :=
  match len with
    | O => 0
    | S len => f len + sum_of len f
  end%Z.

Definition skip_sum_body (f : nat -> Z)  (skip : nat) (Hskip : skip <> 0)  :
  forall (len : nat)
    (rec : forall len', len' < len -> nat -> Z)
    (s : nat), Z.
  refine (
  fun len rec s => 
    match len as l0 return l0 = len -> Z with
      | O => fun _ => 0
      | _ => fun _ => f s + rec (len - skip)%nat _ (s + skip)%nat
    end eq_refl)%Z.
  abstract omega.
Defined.

Definition skip_sum (skip : nat) (Hskip : skip <> 0) (len s : nat) (f : nat -> Z) : Z :=
  Fix lt_wf (fun _ => nat -> Z) (skip_sum_body f skip Hskip) len s.

Example two_neq_0 : 2 <> 0. now auto. Qed.
Eval compute in skip_sum 2 two_neq_0 10 0 (fun i => Z.of_nat i).

Lemma Fix_eq_ok f skip (Hskip : skip <> 0) :
  forall (len : nat) (F G : forall len' : nat, len' < len -> nat -> Z),
  (forall (len' : nat) (p : len' < len), F len' p = G len' p) ->
  skip_sum_body f skip Hskip len F = skip_sum_body f skip Hskip len G.
Proof.
  intros; unfold skip_sum_body.
  assert (F = G) by (do 2 let x := fresh in extensionality x; auto).
  rewrite !H0; auto.
Qed.

Variable len : nat.
Hypothesis len_is_power_of_2 : exists e : nat, len = 2 ^ len.

Notation " p '>>1'" := (Ediv2 p) (at level 40, left associativity) : exp_scope.

Definition If (b : bexp) (c : cmd) := Cif b c.

Variable ntrd : nat.
Hypothesis ntrd_neq_0 : ntrd <> 0.

Definition arr_val_compat (s : nat) (len : nat) (f fc : nat -> Z) :=
  match s with
    | O => fc 0 = sum_of len f
    | _ => sum_of (len / 2) fc = sum_of len f
  end.

Definition INV (i : nat) :=
  Ex (s e st : nat) (fc : nat -> Z),
    !(St === Enum' s) **
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