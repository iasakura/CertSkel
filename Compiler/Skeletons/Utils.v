Require Import PeanoNat Omega Psatz CSLLemma CSLTactics LibTactics. 

Lemma id_lt_nt_gr i j n m : (i < n -> j < m -> i + j * n < m * n)%nat.
Proof.
  clears_all.
  intros.
  assert (i + j * n < n + j * n) by omega.
  assert (n + j * n <= m * n) by nia.
  omega.
Qed.
Lemma nf_lt : forall n (i : Fin.t n), nf i < n.
Proof.
  clears_all; introv; destruct Fin.to_nat; simpl; omega.
Qed.
Lemma mod_between n m q r :
  (m <> 0 -> r < m -> q * m + r < n < S q * m + r -> n mod m <> r)%nat.
Proof.
  intros Hm Hrm Hbetween; rewrite (Nat.div_mod n m) in Hbetween; auto.
  intros Heq; rewrite Heq in Hbetween; clear Heq.
  assert (q * m < m * (n / m) < S q * m)%nat by omega.
  assert (q < n / m < S q)%nat by nia.
  omega.
Qed.
Hint Resolve id_lt_nt_gr nf_lt Nat.neq_mul_0.

Notation fin_star n f :=
  (istar (ls_init 0 n f)).
