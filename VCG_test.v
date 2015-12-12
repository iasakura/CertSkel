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
       App := (0 <= x /\ x <= Zn n /\ t = sum (Z.to_nat x))%Z;
       Asp := nil |}))).
Next Obligation.
repeat split; jauto.
intros [H | H]; jauto.
congruence.
Qed.
Next Obligation.
cbv; auto.
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

Lemma nil_sp_wf : sp_wf nil.
cbv; auto.
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
                 App := True;
                 Asp := nil;
                 Aenv_wf := nil_wf; Asp_wf := nil_sp_wf |})
  SUM 
  (Ast_denote {| Aenv := (T, (sum n)) :: nil;
                 App := True;
                 Asp := nil;
                 Aenv_wf := one_wf _ _; Asp_wf := nil_sp_wf |}).
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
End sum_of_number.

Section swap.
Variable ntrd : nat.
Variable tid : Fin.t ntrd.

Notation X := (Var "X").
Notation Y := (Var "Y").

Notation ptrX := (Var "ptrX").
Notation ptrY := (Var "ptrY").

Variable locX : val.
Variable locY : val.

Variable valX : val.
Variable valY : val.

Definition swap :=
  ( X ::= [ Gl ptrX ] ;;
    Y ::= [ Gl ptrY ] ;;
    [ Gl ptrX ] ::= Y ;;
    [ Gl ptrY ] ::= X ).

Definition pre_env : penv := (ptrX, locX) :: (ptrY, locY) :: nil.
Definition post_env : penv := nil.

Definition pre_sp := Spts (GLoc locX) 1 valX :: Spts (GLoc locY) 1 valY :: nil.
Definition post_sp := Spts (GLoc locX) 1 valY :: Spts (GLoc locY) 1 valX :: nil.

Hint Unfold pre_env post_env pre_sp post_sp swap.

Lemma pre_env_wf : env_wf pre_env. 
Proof.
  cbv; repeat split; jauto.
  intros [|]; congruence.
Qed.

Lemma post_env_wf : env_wf post_env.
Proof.
  unfold post_env; simpl; auto.
Qed.

Hypothesis pre_sp_wf : disjoint_list (GLoc locX :: GLoc locY :: nil).

Ltac crush :=
  first [tauto | congruence |  omega | ring | nia].

Lemma swap_correct :
  CSL (fun _ => default ntrd) tid
    (Ast_denote
     {| Aenv := pre_env;
        App := True;
        Asp := Spts (GLoc locX) 1 valX :: Spts (GLoc locY) 1 valY :: nil;
        Aenv_wf := pre_env_wf; Asp_wf := pre_sp_wf
     |})
    swap
    (Ast_denote
     {| Aenv := post_env;
        App := True;
        Asp := Spts (GLoc locX) 1 valY :: Spts (GLoc locY) 1 valX :: nil;
        Aenv_wf := post_env_wf; Asp_wf := pre_sp_wf
     |}).
Proof.
  autounfold.
  sym_exec.
  { simpl; introv [|]; congruence. }
  { unfold exec_read; simpl.
    Ltac resource_dec :=
      lazymatch goal with [|- context [if eq_dec_P ?P ?X ?Y then _ else _] ] =>
        first [assert (P -> X = Y) by (intros; crush); destruct (eq_dec_P P X Y); [|elimtype False; crush]  |
               assert (P -> X <> Y) by (intros; crush); destruct (eq_dec_P P X Y); [elimtype False; crush|]]
      end.
    resource_dec.
    reflexivity. }
  sym_exec.
  { simpl; introv [|]; congruence. }
  { unfold exec_read; simpl.
    unfold sp_wf in *; simpl in *.
    repeat resource_dec.
    reflexivity. }
  sym_exec.
  { unfold exec_write, sp_wf; simpl.
    assert ((True /\ ~ (GLoc locY = GLoc locX \/ False) /\ ~ False /\ True) ->
            (GLoc locX) = (GLoc locX)).
    crush.
    