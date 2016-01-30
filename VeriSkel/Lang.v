Require Import String.
Require Import Vector.
Require Import List.
Require Import ZArith.

Definition name := string. 
Inductive varE : Set := VarE (name : string).
Inductive varA : Set := VarA (name : string).

Inductive SOp : Set := Eplus | Emax | BEq | Blt.

Inductive SExp :=
| EVar (x : varE)
| ELet (x : varE) (e e' : SExp)
| EBin (op : SOp) (e1 e2 : SExp)
| EA (x : varA) (e : SExp)
| EPrj (e : SExp) (i : nat)
| ECons (es : list SExp)
| EIf (e e' e'' : SExp).

Lemma SExp_ind' : forall P : SExp -> Prop,
    (forall x : varE, P (EVar x)) ->
    (forall (x : varE) (e : SExp), P e -> forall e' : SExp, P e' -> P (ELet x e e')) ->
    (forall (op : SOp) (e1 : SExp), P e1 -> forall e2 : SExp, P e2 -> P (EBin op e1 e2)) ->
    (forall (x : varA) (e : SExp), P e -> P (EA x e)) ->
    (forall e : SExp, P e -> forall i : nat, P (EPrj e i)) ->
    (forall (es : list SExp), List.Forall P es -> P (ECons es)) ->
    (forall e : SExp, P e -> forall e' : SExp, P e' -> forall e'' : SExp, P e'' -> P (EIf e e' e'')) ->
    forall e : SExp, P e.
Proof.
  intros; revert e.
  refine (fix rec (e : SExp) := 
    match e return P e with
    | EVar x => H _
    | ELet x e e' => H0 _ _ (rec _) _ (rec _)
    | EBin op e1 e2 => H1 _ _ (rec _) _ (rec _)
    | EA x e => H2 _ _ (rec _)
    | EPrj e i => H3 _ (rec _) _
    | ECons es => 
      let fix rec2 (es : list SExp) : List.Forall P es :=
          match es return List.Forall P es with
          | nil => List.Forall_nil _
          | (e :: es')%list => List.Forall_cons _ (rec e) (rec2 es')
          end in
      H4 _ (rec2 es)
    | EIf e e' e'' => H5 _ (rec _) _ (rec _) _ (rec _)
    end).
Qed.

Inductive Func := F (params : list varE) (body : SExp).

Inductive AE :=
  ALet (va : varA) (sk : name) (fs : list Func) (vas : list varA) (ea : AE)
| ARet (va : varA).

Inductive SVal : Set :=
| VB (b : bool) | VZ (n : Z) | VTup (vs : list SVal).
Record array :=
  Arr {len : nat; dim : nat; arr : list SVal}.

Definition AEnv := varA -> option array.
Definition SEnv := varE -> option SVal.

Definition svar_eq_dec (x y : varE) : {x = y} + {x <> y}. repeat decide equality. Qed.
Definition avar_eq_dec (x y : varA) : {x = y} + {x <> y}. repeat decide equality. Qed.

Definition updE senv x v : SEnv := fun y => if svar_eq_dec y x then Some v else senv x.
Definition updA senv x v : AEnv := fun y => if avar_eq_dec y x then Some v else senv x.

Definition op_denote (op : SOp) (v1 v2 : SVal) :=
  match op with
  | Emax => match v1, v2 with VZ v1, VZ v2 => Some (VZ (Z.max v1 v2)) | _, _ => None end
  | Eplus => match v1, v2 with VZ v1, VZ v2 => Some (VZ (v1 + v2)) | _, _ => None end
  | BEq => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 =? v2)) | _, _ => None end
  | Blt => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 <? v2)) | _, _ => None end
  end%Z.

Section EvalScalarExpr.
Variable aenv : AEnv.

Inductive abort := AB.

Inductive evalSE : SEnv -> SExp -> SVal + abort -> Prop :=
| EvalSE_var senv sx v :
    senv sx = Some v -> evalSE senv (EVar sx) (inl v)
| EvalSE_elet senv sx e1 e2 v1 v2 :
    evalSE senv e1 (inl v1) ->
    evalSE (updE senv sx v1) e2 v2 ->
    evalSE senv (ELet sx e1 e2) v2
| EvalSE_EBin senv op e1 e2 v1 v2 v :
    evalSE senv e1 (inl v1) ->
    evalSE senv e2 (inl v2) ->
    op_denote op v1 v2 = Some v ->
    evalSE senv (EBin op e1 e2) (inl v)
| EvalSE_EA_safe senv varA va e ix :
    evalSE senv e (inl (VZ ix)) ->
    aenv varA = Some va ->
    (0 <= ix)%Z -> (ix < Z.of_nat (len va))%Z -> 
    evalSE senv (EA varA e) (inl (List.nth (Z.to_nat ix) (arr va) (VZ 0)))
| EvalSE_EA_abort senv varA va e ix :
    evalSE senv e (inl (VZ ix)) ->
    aenv varA = Some va ->
    (ix < 0 \/ Z.of_nat (len va) < ix)%Z ->
    evalSE senv (EA varA e) (inl (List.nth (Z.to_nat ix) (arr va) (VZ 0)))
| EvalSE_EPrj senv e tup i :
    evalSE senv e (inl (VTup tup)) ->
    i < List.length (tup) ->
    evalSE senv (EPrj e i) (inl (List.nth i tup (VZ 0)))
| EvalSE_ECons senv es vs :
    evalTup senv es (inl vs) ->
    evalSE senv (ECons es) (inl (VTup vs))
| EvalSE_Eif_true senv e e' e'' v :
    evalSE senv e (inl (VB true)) ->
    evalSE senv e' v ->
    evalSE senv (EIf e e' e'') v
| EvalSE_Eif_false senv e e' e'' v :
    evalSE senv e (inl (VB false)) ->
    evalSE senv e'' v ->
    evalSE senv (EIf e e' e'') v
with
evalTup : SEnv -> list SExp -> list SVal + abort -> Prop :=
| EvalTup_nil senv : evalTup senv nil (inl nil)
| EvalTup_cons senv e es v vs :
    evalTup senv es (inl vs) ->
    evalSE senv e (inl v) ->
    evalTup senv (e :: es) (inl (v :: vs)).

Definition default_senv : SEnv := fun _ => None.
Definition default_aenv : AEnv := fun _ => None.

Fixpoint bind_vars xs vs :=
  match xs, vs with
  | nil, nil => Some default_senv
  | (x :: xs), (v :: vs) =>
    match bind_vars xs vs with
    | None => None 
    | Some bnd => Some (updE bnd x v)
    end
  | _, _ => None
  end.

Inductive evalFunc : list SVal -> Func -> SVal + abort -> Prop :=
| EvalFunc_app xs vs e v bnd : 
    bind_vars xs vs = Some bnd ->
    evalSE bnd e v ->
    evalFunc vs (F xs e) v.
End EvalScalarExpr.

Variable eval_skel : AEnv -> name -> list Func -> list varA -> array + abort -> Prop.

Inductive evalAE : AEnv -> AE -> array + abort -> Prop :=
| EvalAE_ret aenv ax v :
    aenv ax = Some v -> evalAE aenv (ARet ax) (inl v)
| EvalAE_alet aenv ax skl fs axs e2 v1 v2 :
    eval_skel aenv skl fs axs (inl v1) ->
    evalAE (updA aenv ax v1) e2 v2 ->
    evalAE aenv (ALet ax skl fs axs e2) v2.
