Require Import GPUCSL.
Require Import VCG_refined.
Require Import scan_lib.
Section sum_of_number.
Notation X := (Var "x").
Notation T := (Var "t").
Variable n : nat.

Fixpoint sum n := match n with
  | O => 0
  | S n => Z.succ (Z.of_nat n) + sum n
end%Z.
Require Import Psatz.
Lemma sum_Snn_2 (m : nat) : 
  ((Z.of_nat m * (Z.of_nat m + 1)) / 2 = sum m)%Z.
Proof.
  induction m; [simpl; auto|].
  cutrewrite (Zn (S m) * (Zn (S m) + 1) = Zn m * (Zn m + 1) + ((Zn m) + 1) * 2)%Z; [|nia].
  rewrite Z.div_add; try omega.
  rewrite IHm; simpl; omega.
Qed.

Import ListNotations.
Open Scope list_scope.

Require Import LibTactics.
Program Definition INV :=
  ex_ast _ (fun x : val => ex_ast _ (fun t : val => pure_ast (
    {| Aenv := (X, x) :: (T, t) :: nil;
       Aenv_wf := _;
       Ap := (0 <= x /\ x <= Zn n /\ t = sum (Z.to_nat x))%Z;
       sp := nil
    |}))).
Next Obligation.
repeat split; jauto.
intros [H | H]; jauto.
congruence.
Qed.

Definition SUM :=
  T ::= Enum' 0 ;;
  X ::= Enum' 0 ;;
  while (INV) (X < Enum' n) (
    X ::= X + Enum 1 ;;
    T ::= (T + X))%exp.

Variable ntrd : nat.
Variable tid : Fin.t ntrd.

Lemma nil_wf : env_wf nil.
simpl; eauto.
Qed.

Lemma one_wf x v : env_wf ((x, v) :: nil).
simpl; eauto.
Qed.

Arguments exAst_denote : simpl never.
Arguments Ast_denote : simpl never.

Hint Unfold exAst_denote Ast_denote.

Goal
  CSL (fun _ => default ntrd) tid
  (Ast_denote {| Aenv := nil;
                 Aenv_wf := nil_wf;
                 Ap := True;
                 sp := nil|})
  SUM 
  (Ast_denote {| Aenv := (T, (sum n)) :: nil;
                 Aenv_wf := one_wf _ _;
                 Ap := True;
                 sp := nil|}).
Proof.
  unfold SUM, INV; eapply Hforward.
  repeat (sym_exec; [reflexivity|]).
  sym_exec; [unfold INV; simpl; auto|..].
  { unfold INV; autounfold; simpl; intros s h Hsat.
    exists 0%Z 0%Z.
    sep_split_in Hsat; sep_split; eauto.
    destruct HP as ((? & ? & _) & _); repeat split; eauto; omega. }
  simpl; sym_exec; intros x; sym_exec; intros t.
  sym_exec; [reflexivity|].
  simpl; eapply Hforward; [sym_exec; reflexivity |].
  { autounfold in *; simpl in *; intros s h Hsat.
    exists (x + 1)%Z (t + (x + 1))%Z.
    sep_split; sep_split_in Hsat; eauto.
    destruct HP as ((? & ? & _) & (? & ? & ? & ?)); repeat split; eauto; try omega.
    cutrewrite (Z.to_nat (x + 1) = S (Z.to_nat x)); [|].
    simpl; unfold val in *; rewrite Z2Nat.id; omega.
    unfold val in *; rewrite Z2Nat.inj_add; simpl; nia. }
  intros s h (x & t & Hsat); repeat (autounfold in *; simpl in *).
  sep_split_in Hsat; sep_split; eauto.
  destruct HP as ((? & ? & ?) & (? & ? & ? & ?)); repeat split; eauto; try omega.
  unfold_conn_all; simpl in *; subst.
  cutrewrite (n = Z.to_nat (s X)); eauto.
  cutrewrite (s X = Zn n)%Z; [|omega].
  rewrite Nat2Z.id; eauto.
Qed.

Section sum_of_number.