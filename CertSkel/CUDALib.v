Require Import GPUCSL LibTactics scan_lib TypedTerm.

Fixpoint typ2Coq T ty :=
  match ty with
  | Skel.TBool | Skel.TZ => T
  | Skel.TTup t1 t2 => (typ2Coq T t1 * typ2Coq T t2)
  end%type.

Definition ptrs ty := typ2Coq Z ty.
Definition vars ty := typ2Coq var ty.
Definition vals ty := typ2Coq val ty.
Definition locs ty := typ2Coq loc ty.
Definition ctys ty := typ2Coq (option CTyp) ty.
Definition exps ty := typ2Coq exp ty.
Definition lexps ty := typ2Coq loc_exp ty.

Fixpoint nleaf ty :=
  match ty with
  | Skel.TBool | Skel.TZ => 1
  | Skel.TTup t1 t2 => nleaf t1 + nleaf t2
  end.

Fixpoint foldTup {ty : Skel.Typ} {coqTy A : Type} (sing : coqTy -> A) (f : A -> A -> A) :=
  match ty return typ2Coq coqTy ty -> A with
  | Skel.TBool | Skel.TZ => fun x => sing x
  | Skel.TTup _ _ => fun xs => f (foldTup sing f (fst xs)) (foldTup sing f (snd xs))
  end.

Fixpoint assigns {ty : Skel.Typ} := 
  match ty return vars ty -> ctys ty -> exps ty -> cmd with
  | Skel.TBool | Skel.TZ => fun x ty e => x ::T ty ::= e
  | Skel.TTup t1 t2 => fun xs ctys es => 
    assigns (fst xs) (fst ctys) (fst es) ;;
    assigns (snd xs) (snd ctys) (snd es)
  end.

(* A generating function xs := pl arr + ix. pl denotes array is on shared / global memory *)
Fixpoint reads {ty : Skel.Typ} :=
  match ty return vars ty -> ctys ty -> lexps ty -> cmd with
  | Skel.TBool | Skel.TZ => fun x ty e => x ::T ty ::= [e]
  | Skel.TTup t1 t2 => fun xs ctys es => 
    reads (fst xs) (fst ctys) (fst es) ;; reads (snd xs) (snd ctys) (snd es)
  end.

(* A generating function pl arr + ix := es. pl denotes array is on shared / global memory *)
Fixpoint writes {ty : Skel.Typ} :=
  match ty return lexps ty -> exps ty -> cmd with
  | Skel.TBool | Skel.TZ => fun le e  => [le] ::= e
  | Skel.TTup t1 t2 => fun les es => 
    writes (fst les) (fst es) ;; writes (snd les) (snd es)
  end.

Fixpoint nat_to_string (n : nat) : string :=
  match n with
  | O => "O"
  | S n => "S" ++ nat_to_string n
  end%string.

Lemma nat_to_string_inj n m : nat_to_string n = nat_to_string m -> n = m.
Proof.
  revert m; induction n; simpl in *; intros [|m]; simpl; try congruence.
  inversion 1. eauto.
Qed.

Open Scope string.
Lemma string_inj2 s1 s2 s1' s2' : s1 = s1' -> s1 ++ s2 = s1' ++ s2' -> s2 = s2'.
Proof.
  revert s1'; induction s1; intros [|? s1']; simpl in *; try congruence; intros.
  inverts H; inverts H0; subst; eauto.
Qed.
