Require Import String.
Require Import Vector.
Require Import List.
Require Import ZArith.
Require Import PHeap.
Require Import LibTactics.
Require Import Psatz.
Require Import Monad.
Require Import Env.
Definition name := string. 

(* variables for scalar expressions/arrays *)
Inductive varE : Set := VarE (name : string).

Inductive varA : Set := VarA (name : string).

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

Module Syntax.
  (* scalar operations *)
  Inductive SOp : Set := Eplus | Emin | BEq | Blt.
  
  (* types of scala expressions *)
  Inductive Typ := TBool | TZ | TTup (typs : list Typ).  
  
  Inductive Forall_rect (A : Type) (P : A -> Type) : list A -> Type :=
    Forall_r_nil : Forall_rect A P nil
  | Forall_r_cons : forall (x : A) (l : list A), P x -> Forall_rect A P l -> Forall_rect A P (x :: l).

  Lemma STyp_rect' (P : Typ -> Type) (f : P TBool) (f0 : P TZ)
        (f1 : forall (typs : list Typ), (Forall_rect _ P typs) -> (P (TTup typs))) : forall ty, P ty.
    refine
      (let fix rec ty :=
           match ty as s0 return (P s0) with
           | TBool => f
           | TZ => f0
           | TTup x =>
             let fix rec (tys : list Typ) :=
                 match tys return Forall_rect _ P tys with
                 | nil => Forall_r_nil _ _
                 | ty :: tys => Forall_r_cons _ _ _ _ _ _
                 end in f1 _ (rec x)
           end in rec).
    eauto.
    eauto.
  Qed.

  Lemma STyp_eq_dec (ty1 ty2 : Typ) : {ty1 = ty2} + {ty1 <> ty2}.
  Proof.
    revert ty2 ty1; apply (STyp_rect' (fun ty => forall ty2, {ty2 = ty} + {ty2 <> ty}));
      destruct ty2; try first [left; congruence | right; congruence].
    revert typs0; induction X.
    - destruct typs0; [left | right]; congruence.
    - destruct typs0.
      + right; congruence.
      + lets [?|?]: (IHX typs0).
        * lets [?|?]: (p t).
          inversion e; substs; left; eauto.
          right; congruence.
        * right; congruence.
  Defined.

  (* scalar expressions *)
  Inductive SExp :=
  | EVar (x : varE) (typ : Typ)
  | ENum (x : Z)
  | ELet (x : varE) (e e' : SExp) (typ : Typ)
  | EBin (op : SOp) (e1 e2 : SExp) (typ : Typ)
  | EA (x : varA) (e : SExp) (typ : Typ)
  | ELen (x : varA)
  | EPrj (e : SExp) (i : nat) (typ : Typ)
  | ECons (es : list SExp) (typ : Typ)
  | EIf (e e' e'' : SExp) (typ : Typ).

  (* getter of the type informations *)
  Definition typ_of_sexp e :=
    match e with
    | EVar _ ty => ty
    | ENum _ => TZ
    | ELet _ _ _ ty => ty
    | EBin _ _ _ ty => ty
    | EA _ _ ty => ty
    | ELen _ => TZ
    | EPrj _ _ ty => ty
    | ECons _ ty => ty
    | EIf _ _ _ ty => ty
    end.

  Lemma SExp_ind' : forall P : SExp -> Prop,
      (forall (x : varE) ty, P (EVar x ty)) ->
      (forall (x : Z), P (ENum x)) ->
      (forall (x : varE) (e : SExp) ty, P e -> forall e' : SExp, P e' -> P (ELet x e e' ty)) ->
      (forall (op : SOp) (e1 : SExp) ty, P e1 -> forall e2 : SExp, P e2 -> P (EBin op e1 e2 ty)) ->
      (forall (x : varA) (e : SExp) ty, P e -> P (EA x e ty)) ->
      (forall (x : varA), P (ELen x)) ->
      (forall (e : SExp) ty, P e -> forall i : nat, P (EPrj e i ty)) ->
      (forall (es : list SExp) ty, List.Forall P es -> P (ECons es ty)) ->
      (forall (e : SExp) ty, P e -> forall e' : SExp, P e' -> forall e'' : SExp, P e'' -> P (EIf e e' e'' ty)) ->
      forall e : SExp, P e.
  Proof.
    intros; revert e.
    refine (fix rec (e : SExp) := 
              match e return P e with
              | EVar x ty => _ x ty
              | ENum x => _ x
              | ELet x e e' ty => _ x e ty (rec e) e' (rec e')
              | EBin op e1 e2 ty => _ op e1 ty  (rec e1) e2 (rec e2)
              | EA x e ty => _ x e ty (rec e)
              | ELen x => _ x
              | EPrj e i ty => _ e ty (rec e) i
              | ECons es ty => 
                let fix rec2 (es : list SExp) : List.Forall P es :=
                    match es return List.Forall P es with
                    | nil => List.Forall_nil _
                    | (e :: es')%list => List.Forall_cons e (rec e) (rec2 es')
                    end in
                _ es ty (rec2 es)
              | EIf e e' e'' ty => _ e ty (rec e) e' (rec e') e'' (rec e'')
              end); try clear rec2; clear rec; eauto.
  Qed.

  (* user defined functions *)
  Inductive Func := F (params : list (varE * Typ)) (body : SExp).

  Inductive LExp : Type :=
  | LNum : Z -> LExp
  (* | LBin : (nat -> nat -> nat) -> LExp -> LExp -> LExp *)
  | LLen : varA -> LExp.
  
  Inductive AE :=
  | DArr (f : Func) (len : LExp)
  | VArr (xa : varA).

  (* array expressions *)
  Inductive prog :=
    ALet (va : varA) (ty : Typ) (sk : name) (fs : list Func) (vas : list (AE * Typ)) (ea : prog)
  | ARet (va : varA).
End Syntax.

Section Semantics.
  Import Syntax.
  (* scalar/array values*)
  Inductive SVal : Set :=
  | VB (b : bool) | VZ (n : Z) | VTup (vs : list SVal).
  Definition array := list SVal.

  (* environments for variables *)
  Definition AEnv (A : Type) := Env varA A _.
  Definition SEnv (A : Type) := Env varE A _.

  Definition op_denote (op : SOp) (v1 v2 : SVal) :=
    match op with
    | Emin => match v1, v2 with VZ v1, VZ v2 => Some (VZ (Z.min v1 v2)) | _, _ => None end
    | Eplus => match v1, v2 with VZ v1, VZ v2 => Some (VZ (v1 + v2)) | _, _ => None end
    | BEq => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 =? v2)) | _, _ => None end
    | Blt => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 <? v2)) | _, _ => None end
    end%Z.

  Section evalS.
    Variable aenv : AEnv (option array).

    (* semantics of scalar expressions *)
    Inductive evalSE : Env varE (option SVal) _  -> SExp -> SVal  -> Prop :=
    | EvalSE_var senv sx v ty :
        senv sx = Some v -> evalSE senv (EVar sx ty) v
    | EvalSE_Z senv n :
        evalSE senv (ENum n) (VZ n)
    | EvalSE_elet senv sx e1 e2 v1 v2 ty:
        evalSE senv e1 v1 ->
        evalSE (upd_opt senv sx v1) e2 v2 ->
        evalSE senv (ELet sx e1 e2 ty) v2
    | EvalSE_EBin senv op e1 e2 v1 v2 v ty:
        evalSE senv e1 v1 ->
        evalSE senv e2 v2 ->
        op_denote op v1 v2 = Some v ->
        evalSE senv (EBin op e1 e2 ty) v
    | EvalSE_EA senv varA va e ix ty:
        evalSE senv e (VZ ix) ->
        aenv varA = Some va ->
        (0 <= ix)%Z -> (ix < Z.of_nat (length va))%Z -> 
        evalSE senv (EA varA e ty) (List.nth (Z.to_nat ix) va (VZ 0))
    | EValSE_ELen senv xa va :
        aenv xa = Some va ->
        evalSE senv (ELen xa) (VZ (Z.of_nat (length va)))
    | EvalSE_EPrj senv e tup i ty :
        evalSE senv e (VTup tup) ->
        i < List.length (tup) ->
        evalSE senv (EPrj e i ty) (List.nth i tup (VZ 0))
    | EvalSE_ECons senv es vs ty :
        evalTup senv es vs ->
        evalSE senv (ECons es ty) (VTup vs)
    | EvalSE_Eif_true senv e e' e'' v ty :
        evalSE senv e (VB true) ->
        evalSE senv e' v ->
        evalSE senv (EIf e e' e'' ty) v
    | EvalSE_Eif_false senv e e' e'' v ty :
        evalSE senv e (VB false) ->
        evalSE senv e'' v ->
        evalSE senv (EIf e e' e'' ty) v
    with
    evalTup : Env varE (option SVal) _ -> list SExp -> list SVal  -> Prop :=
    | EvalTup_nil senv : evalTup senv nil nil
    | EvalTup_cons senv e es v vs :
        evalTup senv es vs ->
        evalSE senv e v ->
        evalTup senv (e :: es) (v :: vs).

    (* semantics of functions *)
    Fixpoint bind_vars (xs : list (varE * Typ)) (vs : list SVal) :=
      match xs, vs with
      | nil, nil => Some emp_opt
      | ((x, _) :: xs), (v :: vs) =>
        match bind_vars xs vs with
        | None => None 
        | Some bnd => Some (upd_opt bnd x v)
        end
      | _, _ => None
      end.

    Inductive evalFunc : list SVal -> Func -> SVal -> Prop :=
    | EvalFunc_app xs vs e v bnd : 
        bind_vars xs vs = Some bnd ->
        evalSE bnd e v ->
        evalFunc vs (F xs e) v.
  End evalS.
  
  Open Scope string_scope.
  Require Import scan_lib.

  Definition Z_to_nat (n : Z) : option nat := if Z_le_dec 0 n then Some (Z.to_nat n) else None.

  Fixpoint evalLExp (aenv : Env varA (option nat) _) (le : LExp) : option nat :=
    match le with
    | LNum n => Z_to_nat n
    (* | LBin op le1 le2 => *)
    (*   let! v1 := evalLExp aenv le1 in *)
    (*   let! v2 := evalLExp aenv le2 in *)
    (*   Some (op v1 v2) *)
    | LLen xa => aenv xa
    end.

  Inductive evalAE (aenv : AEnv (option array)) : AE -> array -> Prop :=
  | EvalAE_var xa arr :
      aenv xa = Some arr ->
      evalAE aenv (VArr xa) arr
  | EvalAE_DArr func f e len :
      evalLExp (fun x => option_map (@length _) (aenv x)) e = Some len ->
      (forall i, i < len -> evalFunc aenv (VZ (Z.of_nat i) :: nil) func (f i)) ->
      evalAE aenv (DArr func e) (ls_init 0 len f).
  
  Inductive evalSK : AEnv (option array) -> name -> list Func -> list (AE * Typ) -> array -> Prop :=
  | Eval_map aenv func f ae typ arr len :
      evalAE aenv ae arr ->
      (forall i, i < len -> evalFunc aenv (VZ (Z.of_nat i) :: nil) func (f (VZ (Z.of_nat i)))) ->
      evalSK aenv "map" (func :: nil) ((ae, typ) :: nil) (map f arr).
  
  Inductive evalP : AEnv (option array) -> prog -> array -> Prop :=
  | EvalP_ret aenv ax v :
      aenv ax = Some v -> evalP aenv (ARet ax) v
  | EvalP_alet (aenv : AEnv (option array)) ax ty skl fs ae e2 v1 v2 :
      evalSK aenv skl fs ae v1 ->
      evalP (upd_opt aenv ax v1) e2 v2 ->
      evalP aenv (ALet ax ty skl fs ae e2) v2.
End Semantics.

Section typing_rule.
  Import Syntax.
  Definition ty_of_SOp (op : SOp) : list Typ -> option Typ :=
    match op with
    | Eplus => fun tys =>
                     match tys with
                     | TZ :: TZ :: nil => Some TZ
                     | _ => None
                     end
    | Emin => fun tys =>
                    match tys with
                    | TZ :: TZ :: nil => Some TZ
                    | _ => None
                    end
    | BEq => (fun tys => 
                   match tys with
                   | ty1 :: ty2 :: nil => if STyp_eq_dec ty1 ty2 then Some TBool else None
                   | _ => None
                  end)
    | Blt => fun tys =>
                   match tys with
                   | TZ :: TZ :: nil => Some TBool
                   | _ => None
                   end
    end.

  Fixpoint typing (atyenv : Env varA (option Typ) _) (styenv : Env varE (option Typ) _) (e : SExp) : option (SExp * Typ) :=
    match e with
    | EVar x _ => match styenv x with Some ty => Some (EVar x ty, ty) | None => None end
    | ENum n => Some (ENum n, TZ)
    | ELet x e1 e2 _ =>
      match typing atyenv styenv e1 with
      | Some (e1, tye1) =>
        match typing atyenv (upd_opt styenv x tye1) e2 with
        | Some (e2, tye2) =>
          Some (ELet x e1 e2 tye2, tye2)
        | None => None
        end
      | None => None
      end
    | EBin op e1 e2 _ =>
      match typing atyenv styenv e1 with
      | Some (e1, tye1) =>
        match typing atyenv styenv e2 with
        | Some (e2, tye2) =>
          match ty_of_SOp op (tye1 :: tye2 :: nil) with
          | Some tyres => Some (EBin op e1 e2 tyres, tyres)
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | EA xa i _ =>
      match atyenv xa with
      | Some aty => Some (EA xa i aty, aty)
      | None => None
      end
    | ELen xa =>
      match atyenv xa with
      | Some _ => Some (ELen xa, TZ)
      | None => None
      end
    | EPrj e i _ =>
      match typing atyenv styenv e with
      | Some (e, ty) => 
        match ty with
        | TTup tys => if lt_dec i (length tys) then Some (EPrj e i (nth i tys TZ), nth i tys TZ) else None
        | _ => None
        end
      | None => None
      end
    | ECons es _ =>
      match fold_right (fun e tys => match typing atyenv styenv e with
                               | None => None
                               | Some (e, ty) =>
                                 match tys with
                                 | None => None
                                 | Some (es, tys) => Some (e :: es, ty :: tys)
                                 end
                        end) (Some (nil, nil)) es with
      | None => None
      | Some (es, tys) => Some (ECons es (TTup tys), (TTup tys))
      end
    | EIf e1 e2 e3 _ =>
      match typing atyenv styenv e1,
            typing atyenv styenv e2,
            typing atyenv styenv e3 with
      | Some (e1, TBool), Some (e2, ty2), Some (e3, ty3) =>
        if STyp_eq_dec ty2 ty3 then Some (EIf e1 e2 e3 ty2, ty2)
        else None
      | _, _, _ => None
      end
    end.

  Inductive has_type (atyenv : Env varA (option Typ) _) :
    Env varE (option Typ) _ -> SExp -> Typ -> Prop :=
  | tyEVar : forall env x typ, env x = Some typ -> has_type atyenv env (EVar x typ) typ
  | tyENum : forall env n, has_type atyenv env (ENum n) TZ
  | tyELet : forall env x e1 e2 ty1 ty2,
      has_type atyenv env e1 ty1 ->
      has_type atyenv (upd_opt env x ty1) e2 ty2 ->
      has_type atyenv env (ELet x e1 e2 ty2) ty2
  | tyEBin : forall env e1 e2 op ty1 ty2 ty,
      has_type atyenv env e1 ty1 ->
      has_type atyenv env e2 ty2 ->
      ty_of_SOp op (ty1 :: ty2 :: nil) = Some ty ->
      has_type atyenv env (EBin op e1 e2 ty) ty
  | tyLen : forall env xa ty, 
      atyenv xa = Some ty ->
      has_type atyenv env (ELen xa) TZ
  | tyEA : forall env x e ty,
      has_type atyenv env e TZ ->
      atyenv x = Some ty ->
      has_type atyenv env (EA x e ty) ty
  | tyEPrj : forall env e i tys,
      has_type atyenv env e (TTup tys) ->
      i < length tys ->
      has_type atyenv env (EPrj e i (nth i tys TZ)) (nth i tys TZ)
  | tyECons : forall env es tys,
      has_type_es atyenv env es tys ->
      has_type atyenv env (ECons es (TTup tys)) (TTup tys)
  | tyEIf : forall env e1 e2 e3 ty,
      has_type atyenv env e1 TBool ->
      has_type atyenv env e2 ty ->
      has_type atyenv env e3 ty ->
      has_type atyenv env (EIf e1 e2 e3 ty) ty
  with
  has_type_es (atyenv : Env varA (option Typ) _) :
    Env varE (option Typ) _ -> list SExp -> list Typ -> Prop :=
  | tyNil env : has_type_es atyenv env nil nil
  | tyCons env e ty es tys :
      has_type_es atyenv env es tys ->
      has_type atyenv env e ty ->
      has_type_es atyenv env (e :: es) (ty :: tys).
End typing_rule.