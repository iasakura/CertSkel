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
Definition vartys ty := typ2Coq (var * CTyp) ty.

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

Fixpoint nat2str (n : nat) : string :=
  match n with
  | O => "O"
  | S n => "S" ++ nat2str n
  end%string.

Lemma nat_to_string_inj n m : nat2str n = nat2str m -> n = m.
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

Fixpoint locs_offset {ty} :=
  match ty return lexps ty -> exp -> lexps ty with
  | Skel.TBool | Skel.TZ => loc_offset
  | Skel.TTup t1 t2 => fun l off => (locs_offset (fst l) off, locs_offset (snd l) off)
  end.

Infix "+os" := (locs_offset) (at level 50, left associativity).

Fixpoint maptys {ty T1 T2} (f : T1 -> T2) :=
  match ty return typ2Coq T1 ty -> typ2Coq T2 ty with
  | Skel.TBool | Skel.TZ => fun x => f x
  | Skel.TTup t1 t2 => fun xs =>
    (maptys f (fst xs), maptys f (snd xs))
  end.

Definition v2e {ty} := @maptys ty _ _ Evar.
Definition e2sh {ty} := @maptys ty _ _ Sh.
Definition e2gl {ty} := @maptys ty _ _ Gl.
Definition v2sh {ty} (xs : vars ty) := (e2sh (v2e xs)).
Definition v2gl {ty} (xs : vars ty) := (e2sh (v2e xs)).

Fixpoint ty2ctys ty :=
  match ty return ctys ty with
  | Skel.TBool => Some Bool
  | Skel.TZ => Some Int
  | Skel.TTup t1 t2 => (ty2ctys t1, ty2ctys t2)
  end.

Definition names_of_array grp d := ls_init 0 d (fun i => "arr" ++ grp ++ nat2str i)%string.
Definition name_of_len grp := ("sh" ++ grp)%string.
Definition names_of_arg grp d := (name_of_len grp, names_of_array grp d).

Definition grpOfInt n := ("In" ++ nat2str n)%string.

Close Scope string.

Fixpoint flatTup {ty : Skel.Typ} {T : Type} :=
  match ty return typ2Coq T ty -> list T with
  | Skel.TBool | Skel.TZ => fun x => x :: nil
  | Skel.TTup _ _ => fun xs => flatTup (fst xs) ++ flatTup (snd xs)
  end.