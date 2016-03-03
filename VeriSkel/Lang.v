Require Import String.
Require Import Vector.
Require Import List.
Require Import ZArith.
Require Import GPUCSL.
Definition name := string. 
Inductive varE : Set := VarE (name : string).
Inductive varA : Set := VarA (name : string).

Inductive SOp : Set := Eplus | Emax | BEq | Blt.

Inductive SExp :=
| EVar (x : varE)
| Enum (x : Z)
| ELet (x : varE) (e e' : SExp)
| EBin (op : SOp) (e1 e2 : SExp)
| EA (x : varA) (e : SExp)
| EPrj (e : SExp) (i : nat)
| ECons (es : list SExp)
| EIf (e e' e'' : SExp).

Lemma SExp_ind' : forall P : SExp -> Prop,
    (forall x : varE, P (EVar x)) ->
    (forall x : Z, P (Enum x)) ->
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
    | Enum x => H0 _
    | ELet x e e' => H1 _ _ (rec _) _ (rec _)
    | EBin op e1 e2 => H2 _ _ (rec _) _ (rec _)
    | EA x e => H3 _ _ (rec _)
    | EPrj e i => H4 _ (rec _) _
    | ECons es => 
      let fix rec2 (es : list SExp) : List.Forall P es :=
          match es return List.Forall P es with
          | nil => List.Forall_nil _
          | (e :: es')%list => List.Forall_cons _ (rec e) (rec2 es')
          end in
      H5 _ (rec2 es)
    | EIf e e' e'' => H6 _ (rec _) _ (rec _) _ (rec _)
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

Definition Env (A B : Type) (eqt : eq_type A) := A -> B.

Definition upd {A B eqt} (env : Env A B eqt) x v : Env A B eqt :=
  fun y => if eq_dec x y then v else env y.
Definition upd_opt {A B eqt} (env : Env A (option B) eqt) x v : Env A (option B) eqt :=
  fun y => if eq_dec x y then Some v else env y.
Definition emp_opt {A B eqt} : Env A (option B) eqt := fun (_ : A) => @None B.
Definition emp_def {A B eqt} (d : B) : Env A B eqt := fun (_ : A) => d.

Instance eq_varA : eq_type varA.
Proof.
  constructor.
  repeat decide equality. 
Defined.

Instance eq_varE : eq_type varE.
Proof.
  constructor.
  repeat decide equality. 
Defined.

Definition AEnv (A : Type) := Env varA A _.
Definition SEnv (A : Type) := Env varE A _.

Notation AEnv_eval := (AEnv (option array)).
Notation SEnv_eval := (SEnv (option SVal)).

Definition op_denote (op : SOp) (v1 v2 : SVal) :=
  match op with
  | Emax => match v1, v2 with VZ v1, VZ v2 => Some (VZ (Z.max v1 v2)) | _, _ => None end
  | Eplus => match v1, v2 with VZ v1, VZ v2 => Some (VZ (v1 + v2)) | _, _ => None end
  | BEq => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 =? v2)) | _, _ => None end
  | Blt => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 <? v2)) | _, _ => None end
  end%Z.

Section EvalScalarExpr.
Variable aenv : AEnv_eval.

Inductive abort := AB.

Inductive evalSE : (SEnv_eval) -> SExp -> SVal + abort -> Prop :=
| EvalSE_var senv sx v :
    senv sx = Some v -> evalSE senv (EVar sx) (inl v)
| EvalSE_elet senv sx e1 e2 v1 v2 :
    evalSE senv e1 (inl v1) ->
    evalSE (upd_opt senv sx v1) e2 v2 ->
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
evalTup : (SEnv_eval) -> list SExp -> list SVal + abort -> Prop :=
| EvalTup_nil senv : evalTup senv nil (inl nil)
| EvalTup_cons senv e es v vs :
    evalTup senv es (inl vs) ->
    evalSE senv e (inl v) ->
    evalTup senv (e :: es) (inl (v :: vs)).

Fixpoint bind_vars (xs : list varE) (vs : list SVal) :=
  match xs, vs with
  | nil, nil => Some emp_opt
  | (x :: xs), (v :: vs) =>
    match bind_vars xs vs with
    | None => None 
    | Some bnd => Some (upd_opt bnd x v)
    end
  | _, _ => None
  end.

Inductive evalFunc : list SVal -> Func -> SVal + abort -> Prop :=
| EvalFunc_app xs vs e v bnd : 
    bind_vars xs vs = Some bnd ->
    evalSE bnd e v ->
    evalFunc vs (F xs e) v.
End EvalScalarExpr.

Variable eval_skel : AEnv_eval -> name -> list Func -> list varA -> array + abort -> Prop.

Inductive evalAE : AEnv_eval -> AE -> array + abort -> Prop :=
| EvalAE_ret aenv ax v :
    aenv ax = Some v -> evalAE aenv (ARet ax) (inl v)
| EvalAE_alet (aenv : AEnv_eval) ax skl fs axs e2 v1 v2 :
    eval_skel aenv skl fs axs (inl v1) ->
    evalAE (upd_opt aenv ax v1) e2 v2 ->
    evalAE aenv (ALet ax skl fs axs e2) v2.
Require GPUCSL.
Module G := GPUCSL.
Require Skel_lemma.
Module S := Skel_lemma.

Section compile.
  Import Lang.
  Open Scope string_scope.

  Notation SVEnv := (Env varE (list exp) _).

  Definition M a := nat -> (option a * nat).

  Definition bind_opt A B (e : M A) (f : A -> M B) : M B:=
    fun n => 
      match e n with
      | (None, n) => (None, n)
      | (Some v, n) => f v n
      end.

  Infix ">>=" := (bind_opt _ _) (at level 70).

  Definition ret {A} (x : A) : M A := fun n => (Some x, n).
  Definition fail {A} : M A  := fun n => (None, n).
  
  Definition get : M nat := fun n => (Some n, n).
  Definition set n : M unit := fun _ => (Some tt, n).

Definition freshes dim : M (list var) :=
  let fix f dim n :=
      match dim with
      | O => ret nil
      | S dim =>
        f dim n >>= fun fs =>
        ret (Var ("l" ++ S.nat_to_string n ++ "_" ++ S.nat_to_string dim) :: fs)
      end in
  get >>= fun n =>
  set (n + 1) >>= fun _ =>
  f dim n.
  
  Notation ATyEnv := (Env varA nat _).
  Notation AVarEnv := (Env varA (list var) _).

  Variable atyenv : ATyEnv.
  Variable avarenv : AVarEnv.

  Fixpoint compile_sexp (se : SExp) (env : SVEnv) : M (cmd * list exp) := match se with
    | EVar v => ret (Cskip, env v)
    | Top.Enum z => ret (Cskip, Enum z :: nil)
    | ELet x e1 e2 =>
      compile_sexp e1 env >>= fun ces1 => 
      let (c1, es1) := ces1 in
      let dim := length es1 in
      freshes dim >>= fun xs =>
      compile_sexp e2 (upd env x (S.vars2es xs)) >>= fun ces2 => 
      let (c2, es2) := ces2 in
      ret (c1 ;; S.read_tup xs es1 ;; c2, es2)
    | EBin op e1 e2 => 
      compile_sexp e1 env >>= fun ces1 =>
      let (c1, es1) := ces1 in
      compile_sexp e2 env >>= fun ces2 =>
      let (c2, es2) := ces2 in
      match es1, es2 with
      | e1 :: nil, e2 :: nil => ret (c1 ;; c2, e1 +C e2 :: nil)
      | _, _ => fail
      end
    | EA va e =>
      compile_sexp e env >>= fun ces =>
      let (c, es) := ces in
      let aty := atyenv va in
      let aname := avarenv va in
      freshes aty >>= fun xs =>
      match es with
      | i :: nil => ret (c ;; S.gen_read Gl xs (S.vars2es aname) i, S.vars2es xs)
      | _ => fail
      end
    | EPrj e i =>
      compile_sexp e env >>= fun ces =>
      let (c, es) := ces in
      if lt_dec i (length es) then ret (Cskip, nth i es 0%Z :: nil) else fail
    | ECons es => 
      let fix compile_sexps (es : list SExp) env : M (cmd * list exp) :=
          match es with
          | nil => ret (Cskip, nil)
          | (e :: es)%list =>
            compile_sexp e env >>= fun ces =>
            let (c, ge) := ces in
            compile_sexps es env >>= fun ces' =>
            let (c', ges) := ces' in
            ret (c ;; c', ge ++ ges)
          end in
      compile_sexps es env
    | EIf e1 e2 e3 => 
      compile_sexp e1 env >>= fun ces1 => 
      let (c1, e1) := ces1 in
      compile_sexp e2 env >>= fun ces2 =>
      let (c2, e2) := ces1 in
      compile_sexp e3 env >>= fun ces3 =>
      let (c3, e3) := ces3 in
      let dim := length e2 in
      freshes dim >>= fun xs =>
      match e1 with
      | e :: nil =>
        ret (Cif (e == 0%Z) (c2 ;; S.read_tup xs e2) (c3 ;; S.read_tup xs e3), S.vars2es xs)
      | _ => fail
      end
    end%list.
  
  Coercion VarE : string >-> varE.
  Coercion EVar : varE >-> SExp.
  Coercion Top.Enum : Z >-> SExp.

  Eval cbv in 
      compile_sexp (
        ELet "x" (ECons ((1%Z : SExp)  :: (2%Z : SExp) :: nil)) (
        ELet "y" (ECons ((3%Z : SExp)  :: (4%Z : SExp) :: nil)) (
        ELet "z" (ECons (("x" : SExp) :: ("y" : SExp) :: nil)) (
        EPrj "z" 0)))) (emp_def nil) 0.