Require Import String.
Require Import Vector.
Require Import List.
Require Import ZArith.
Require Import GPUCSL.
Require Import LibTactics.
Definition name := string. 

(* general enviroment *)
Section Environment.
  Definition Env (A B : Type) (eqt : eq_type A) := A -> B.
  
  Definition upd {A B eqt} (env : Env A B eqt) x v : Env A B eqt :=
    fun y => if eq_dec x y then v else env y.
  Definition upd_opt {A B eqt} (env : Env A (option B) eqt) x v : Env A (option B) eqt :=
    fun y => if eq_dec x y then Some v else env y.
  Definition emp_opt {A B eqt} : Env A (option B) eqt := fun (_ : A) => @None B.
  Definition emp_def {A B eqt} (d : B) : Env A B eqt := fun (_ : A) => d.
End Environment.

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

(* scalar operations *)
Inductive SOp : Set := Eplus | Emax | BEq | Blt.

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
| Enum (x : Z)
| ELet (x : varE) (e e' : SExp) (typ : Typ)
| EBin (op : SOp) (e1 e2 : SExp) (typ : Typ)
| EA (x : varA) (e : SExp) (typ : Typ)
| EPrj (e : SExp) (i : nat) (typ : Typ)
| ECons (es : list SExp) (typ : Typ)
| EIf (e e' e'' : SExp) (typ : Typ).

(* getter of the type informations *)
Definition typ_of e :=
  match e with
  | EVar _ ty => ty
  | Enum _ => TZ
  | ELet _ _ _ ty => ty
  | EBin _ _ _ ty => ty
  | EA _ _ ty => ty
  | EPrj _ _ ty => ty
  | ECons _ ty => ty
  | EIf _ _ _ ty => ty
  end.

Lemma SExp_ind' : forall P : SExp -> Prop,
    (forall (x : varE) ty, P (EVar x ty)) ->
    (forall (x : Z), P (Enum x)) ->
    (forall (x : varE) (e : SExp) ty, P e -> forall e' : SExp, P e' -> P (ELet x e e' ty)) ->
    (forall (op : SOp) (e1 : SExp) ty, P e1 -> forall e2 : SExp, P e2 -> P (EBin op e1 e2 ty)) ->
    (forall (x : varA) (e : SExp) ty, P e -> P (EA x e ty)) ->
    (forall (e : SExp) ty, P e -> forall i : nat, P (EPrj e i ty)) ->
    (forall (es : list SExp) ty, List.Forall P es -> P (ECons es ty)) ->
    (forall (e : SExp) ty, P e -> forall e' : SExp, P e' -> forall e'' : SExp, P e'' -> P (EIf e e' e'' ty)) ->
    forall e : SExp, P e.
Proof.
  intros; revert e.
  refine (fix rec (e : SExp) := 
    match e return P e with
    | EVar x _ => H _ _
    | Enum x => H0 _
    | ELet x e e' _ => H1 _ _ _ (rec _) _ (rec _)
    | EBin op e1 e2 _ => H2 _ _ _ (rec _) _ (rec _)
    | EA x e _ => H3 _ _ _ (rec _)
    | EPrj e i _ => H4 _ _ (rec _) _
    | ECons es _ => 
      let fix rec2 (es : list SExp) : List.Forall P es :=
          match es return List.Forall P es with
          | nil => List.Forall_nil _
          | (e :: es')%list => List.Forall_cons _ (rec e) (rec2 es')
          end in
      H5 _ _ (rec2 es)
    | EIf e e' e'' _ => H6 _ _ (rec _) _ (rec _) _ (rec _)
    end).
Qed.

(* user defined functions *)
Inductive Func := F (params : list varE) (body : SExp).

(* array expressions *)
Inductive AE :=
  ALet (va : varA) (sk : name) (fs : list Func) (vas : list varA) (ea : AE)
| ARet (va : varA).

(* scalar/array values*)
Inductive SVal : Set :=
| VB (b : bool) | VZ (n : Z) | VTup (vs : list SVal).
Record array :=
  Arr {len_of : nat; dim_of : nat; arr_of : list SVal}.

(* environments for variables *)
Definition AEnv (A : Type) := Env varA A _.
Definition SEnv (A : Type) := Env varE A _.

(* eval environment, var -> val *)
Notation AEnv_eval := (AEnv (option array)).
Notation SEnv_eval := (SEnv (option SVal)).

Definition op_denote (op : SOp) (v1 v2 : SVal) :=
  match op with
  | Emax => match v1, v2 with VZ v1, VZ v2 => Some (VZ (Z.max v1 v2)) | _, _ => None end
  | Eplus => match v1, v2 with VZ v1, VZ v2 => Some (VZ (v1 + v2)) | _, _ => None end
  | BEq => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 =? v2)) | _, _ => None end
  | Blt => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 <? v2)) | _, _ => None end
  end%Z.

Section Semantics.
  Variable aenv : AEnv_eval.

  Inductive abort := AB.

  (* semantics of scalar expressions *)
  Inductive evalSE : Env varE (option SVal) _  -> SExp -> SVal + abort -> Prop :=
  | EvalSE_var senv sx v ty :
      senv sx = Some v -> evalSE senv (EVar sx ty) (inl v)
  | EvalSE_Z senv n :
      evalSE senv (Enum n) (inl (VZ n))
  | EvalSE_elet senv sx e1 e2 v1 v2 ty:
      evalSE senv e1 (inl v1) ->
      evalSE (upd_opt senv sx v1) e2 v2 ->
      evalSE senv (ELet sx e1 e2 ty) v2
  | EvalSE_EBin senv op e1 e2 v1 v2 v ty:
      evalSE senv e1 (inl v1) ->
      evalSE senv e2 (inl v2) ->
      op_denote op v1 v2 = Some v ->
      evalSE senv (EBin op e1 e2 ty) (inl v)
  | EvalSE_EA_safe senv varA va e ix ty:
      evalSE senv e (inl (VZ ix)) ->
      aenv varA = Some va ->
      (0 <= ix)%Z -> (ix < Z.of_nat (len_of va))%Z -> 
      evalSE senv (EA varA e ty) (inl (List.nth (Z.to_nat ix) (arr_of va) (VZ 0)))
  | EvalSE_EA_abort senv varA va e ix ty :
      evalSE senv e (inl (VZ ix)) ->
      aenv varA = Some va ->
      (ix < 0 \/ Z.of_nat (len_of va) < ix)%Z ->
      evalSE senv (EA varA e ty) (inl (List.nth (Z.to_nat ix) (arr_of va) (VZ 0)))
  | EvalSE_EPrj senv e tup i ty :
      evalSE senv e (inl (VTup tup)) ->
      i < List.length (tup) ->
      evalSE senv (EPrj e i ty) (inl (List.nth i tup (VZ 0)))
  | EvalSE_ECons senv es vs ty :
      evalTup senv es (inl vs) ->
      evalSE senv (ECons es ty) (inl (VTup vs))
  | EvalSE_Eif_true senv e e' e'' v ty :
      evalSE senv e (inl (VB true)) ->
      evalSE senv e' v ->
      evalSE senv (EIf e e' e'' ty) v
  | EvalSE_Eif_false senv e e' e'' v ty :
      evalSE senv e (inl (VB false)) ->
      evalSE senv e'' v ->
      evalSE senv (EIf e e' e'' ty) v
  with
  evalTup : (SEnv_eval) -> list SExp -> list SVal + abort -> Prop :=
  | EvalTup_nil senv : evalTup senv nil (inl nil)
  | EvalTup_cons senv e es v vs :
      evalTup senv es (inl vs) ->
      evalSE senv e (inl v) ->
      evalTup senv (e :: es) (inl (v :: vs)).

  (* semantics of functions *)
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

  Variable eval_skel : AEnv_eval -> name -> list Func -> list varA -> array + abort -> Prop.
  
  Inductive evalAE : AEnv_eval -> AE -> array + abort -> Prop :=
  | EvalAE_ret aenv ax v :
      aenv ax = Some v -> evalAE aenv (ARet ax) (inl v)
  | EvalAE_alet (aenv : AEnv_eval) ax skl fs axs e2 v1 v2 :
      eval_skel aenv skl fs axs (inl v1) ->
      evalAE (upd_opt aenv ax v1) e2 v2 ->
      evalAE aenv (ALet ax skl fs axs e2) v2.
End Semantics.

Require GPUCSL.
Module G := GPUCSL.
Require Skel_lemma.
Module S := Skel_lemma.

Section typing_rule.
  Definition ty_of_SOp (op : SOp) : list Typ -> option Typ :=
    match op with
    | Top.Eplus => fun tys =>
                     match tys with
                     | TZ :: TZ :: nil => Some TZ
                     | _ => None
                     end
    | Top.Emax => fun tys =>
                    match tys with
                    | TZ :: TZ :: nil => Some TZ
                    | _ => None
                    end
    | Top.BEq => (fun tys => 
                   match tys with
                   | ty1 :: ty2 :: nil => if STyp_eq_dec ty1 ty2 then Some TBool else None
                   | _ => None
                  end)
    | Top.Blt => fun tys =>
                   match tys with
                   | TZ :: TZ :: nil => Some TBool
                   | _ => None
                   end
    end.

  Fixpoint typing (atyenv : Env varA (option Typ) _) (styenv : Env varE (option Typ) _) (e : SExp) : option (SExp * Typ) :=
    match e with
    | EVar x _ => match styenv x with Some ty => Some (EVar x ty, ty) | None => None end
    | Top.Enum n => Some (Top.Enum n, TZ)
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
End typing_rule.

Section codegen.
  Definition M a := nat -> ((a + string) * nat).

  Definition bind_opt A B (e : M A) (f : A -> M B) : M B:=
    fun n => 
      match e n with
      | (inr msg, n) => (inr msg, n)
      | (inl v, n) => f v n
      end.

  Definition ret {A} (x : A) : M A := fun n => (inl x, n).
  Definition fail {A} (msg : string): M A  := fun n => (inr msg, n).
  
  Definition get : M nat := fun n => (inl n, n).
  Definition set n : M unit := fun _ => (inl tt, n).
End codegen.

Infix ">>=" := (bind_opt _ _) (at level 70).

Section compiler.
  (* typing environment of array *)
  Variable atyenv : Env varA Typ _.
  (* environment of variables of array in the generated code *)
  Variable avarenv : Env varA (list var) _.

  Fixpoint string_of_ty ty : string :=
    match ty with
    | TBool => "Bool"
    | TZ => "Z"
    | TTup ls => "(" ++ fold_right (fun x y => string_of_ty x ++ y) ")" ls
    end%string.

  Fixpoint len_of_ty ty : nat :=
    match ty with
    | TBool | TZ => 1
    | TTup ls => fold_right (fun x y => len_of_ty x + y) 0 ls
    end.
  
  Fixpoint len_until_i tys i : nat :=
    fold_right (fun ty n => len_of_ty ty + n) 0 (firstn i tys).
  
  Fixpoint len_at_i (tys : list Typ) i : nat :=
    len_of_ty (nth i tys TZ).
  
  Import Lang.
  Open Scope string_scope.

  Notation SVEnv := (Env varE (list var) _).

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

  (* compiler of scalar expressions *)
  Fixpoint compile_sexp (se : SExp) (env : SVEnv) : M (cmd * list exp) := match se with
    | EVar v _ => ret (Cskip, S.vars2es (env v))
    | Top.Enum z => ret (Cskip, Enum z :: nil)
    | ELet x e1 e2 _ =>
      compile_sexp e1 env >>= fun ces1 => 
      let (c1, es1) := ces1 in
      let dim := length es1 in
      freshes dim >>= fun xs =>
      compile_sexp e2 (upd env x xs) >>= fun ces2 => 
      let (c2, es2) := ces2 in
      ret (c1 ;; S.read_tup xs es1 ;; c2, es2)
    | EBin op e1 e2 _ => 
      compile_sexp e1 env >>= fun ces1 =>
      let (c1, es1) := ces1 in
      compile_sexp e2 env >>= fun ces2 =>
      let (c2, es2) := ces2 in
      match es1, es2 with
      | e1 :: nil, e2 :: nil => ret (c1 ;; c2, e1 +C e2 :: nil)
      | _, _ => fail ""
      end
    | EA va e _ =>
      compile_sexp e env >>= fun ces =>
      let (c, es) := ces in
      let aty := atyenv va in
      let aname := avarenv va in
      freshes (len_of_ty aty) >>= fun xs =>
      match es with
      | i :: nil => ret (c ;; S.gen_read Gl xs (S.vars2es aname) i, S.vars2es xs)
      | _ => fail ""
      end
    | EPrj e i ty =>
      match typ_of e with
      | TBool | TZ => fail ""
      | TTup tys => 
        let off := len_until_i tys i in
        let l := len_at_i tys i in
        compile_sexp e env >>= fun ces =>
        let (c, es) := ces in
        if le_dec (off + l) (len_of_ty (TTup tys)) then
          ret (Cskip, firstn l (skipn off es))
        else fail ("overflow the index " ++ S.nat_to_string i ++ " of tuple:
" ++               "type of tuple: " ++ string_of_ty ty ++

                   "expected length = " ++ S.nat_to_string (len_of_ty ty) ++ "
" ++
                   "actual length = " ++ S.nat_to_string off ++ " + " ++ S.nat_to_string l)
      end
    | ECons es _ => 
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
    | EIf e1 e2 e3 _ => 
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
      | _ => fail ""
      end
    end%list.
End compiler.

Section TestCompiler.
  Definition EVar' (x : varE) := EVar x TZ.
  Definition ELet' (x : varE) (e e' : SExp)  := ELet x e e' TZ.
  Definition EBin' (op : SOp) (e1 e2 : SExp) := EBin op e1 e2 TZ.
  Definition EA' (x : varA) (e : SExp) (typ : Typ) := EA x e TZ.
  Definition EPrj' (e : SExp) (i : nat) := EPrj e i TZ.
  Definition ECons' (es : list SExp) := ECons es TZ.
  Definition EIf' (e e' e'' : SExp) := EIf e e' e'' TZ.
  
  Open Scope string_scope.

  Coercion VarE : string >-> varE.
  Coercion Top.Enum : Z >-> SExp.
  Coercion EVar' : varE >-> SExp.

  Definition test1 :=
    typing emp_opt emp_opt(
             ELet' "x" (ECons' ((1%Z : SExp)  :: (2%Z : SExp) :: nil)) (
                     ELet' "y" (ECons' ((3%Z : SExp)  :: (4%Z : SExp) :: nil)) (
                             ELet' "z" (ECons' (("x" : SExp) :: ("y" : SExp) :: nil)) ( 
                                     EPrj' "z" 0)))).
  
  Eval cbv in test1.
  Eval cbv in (match test1 with Some (t, _) => Some (compile_sexp (emp_def TZ) (emp_def nil) t (emp_def nil) 0) | None => None end).
  
End TestCompiler.

Section CorrectnessProof.
  Import Skel_lemma.
  (* the set of free variables *)
  Variable free_avs : list varA.
  (* the evaluation environment *)
  Variable aeval_env : Env varA (option array) _.
  (* the typing environment *)
  Variable aty_env : Env varA Typ _.
  (* the variable mapping environment between source and dest. *)
  Variable avar_env : Env varA (list var) _ .
  
  (* free variables lists does not have any duplicated variables *)
  Hypothesis nodup_favs : NoDup free_avs.
  
  (* source lang. values -> dest. lang. values *)
  Fixpoint vs_of_sval sval : list Z :=
    match sval with
    | VB b => (if b then 1%Z else 0%Z) :: nil
    | VZ z => z :: nil
    | VTup vs => fold_right (fun v vs => vs_of_sval v ++ vs) nil vs
    end%list.

  (* precondition of free variable arrays *)
  Fixpoint assn_of_avs (favs : list varA) :=
    match favs with
    | nil => emp
    | x_a :: avs =>
      match aeval_env x_a with
      | None => FalseP
      | Some a =>
        S.is_tuple_array_p (S.es2gls (S.vars2es (avar_env x_a))) (len_of a) (fun i => vs_of_sval (nth i (arr_of a) (VZ 0))) 0 1 **
        assn_of_avs avs
      end
    end.

  (* (* the set of free variables of scalar exp *) *)
  (* Variable free_svs : list varE. *)
  (* (* the evaluation environment of scalar exp *) *)
  (* Variable seval_env : Env varE (option SVal) _. *)
  (* (* the typing environment *) *)
  (* Variable sty_env : Env varE Typ _. *)
  (* (* the variable mapping environment between source and dest. *) *)
  (* Variable svar_env : Env varE (list var) _ . *)

  (* preconditions of scalar variables *)
  Fixpoint assn_of_svs (seval_env : Env varE (option SVal) _) (svar_env : Env varE (list var) _)  (fsvs : list varE) :=
    match fsvs with
    | nil => emp
    | x_e :: svs =>
      match seval_env x_e with
      | Some v => !(vars2es (svar_env x_e) ==t vs_of_sval v) ** assn_of_svs seval_env svar_env svs
      | None => FalseP
      end
    end.
  
  Variable ntrd : nat.
  Variable tid : Fin.t ntrd.
  Variable BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd.
  
  Definition equiv_ls {A : Type} (ls1 ls2 : list A) := (incl ls1 ls2) /\ (incl ls2 ls1).

  Require Import Recdef.
  Lemma remove_length {A : Type} {eqt : eq_type A} (xs : list A) x:
    length (remove eq_dec x xs) <= length xs.
  Proof.
    induction xs; simpl; try omega.
    destruct eq_dec; simpl; try omega.
  Qed.
  
  Function uniq {A} {eqt : eq_type A} (xs : list A) {measure length xs} :=
    match xs with
    | nil => nil
    | x :: xs => x :: uniq (remove eq_dec x xs)
    end.
  Proof.
    intros; simpl.
    lets: (>> remove_length xs0 x); simpl in *; try omega.
  Defined.
  Arguments uniq {A eqt} xs : rename.

  Lemma remove_incl {A} {eqt : eq_type A} x (xs : list A) :
    incl (remove eq_dec x xs) xs.
  Proof.
    induction xs; unfold incl in *; simpl; eauto.
    destruct (eq_dec _ _); substs; simpl in *; jauto.
    intros ? [? | ?]; eauto.
  Qed.
  
  Lemma uniq_incl {A} {eqt : eq_type A} (xs : list A) :
    incl (uniq xs) xs.
  Proof.
    functional induction (uniq xs).
    - unfold incl; eauto.
    - unfold incl in *; simpl.
      intros ? [? | ?]; eauto.
      forwards* : IHl.
      forwards* : remove_incl.
  Qed.

  Lemma uniq_no_dup {A} {eqt : eq_type A} (xs : list A) :
    NoDup (uniq xs).
  Proof.
    functional induction (uniq xs).
    - constructor.
    - constructor; eauto.
      intros Hc.
      forwards*: uniq_incl; unfold incl in *; eauto.
      apply H in Hc; forwards*: remove_In; eauto.
  Qed.

  Import scan_lib.

  Fixpoint free_sv' (e : SExp) :=
    match e with
    | EVar v _ => v :: nil
    | Enum _   => nil
    | ELet x e1 e2 _ => 
      free_sv' e1 ++ remove eq_dec x (free_sv' e2)
    | EBin _ e1 e2 _ => free_sv' e1 ++ free_sv' e2
    | EA _ e _ => free_sv' e
    | EPrj e _ _ => free_sv' e
    | ECons es _ => fold_right (fun e xs => free_sv' e ++ xs) nil es
    | EIf e e' e'' _ => free_sv' e ++ free_sv' e' ++ free_sv' e''
    end.

  Fixpoint free_av' (e : SExp) :=
    match e with
    | EVar v _ => nil
    | Enum _   => nil
    | ELet x e1 e2 _ => 
      free_av' e1 ++ free_av' e2
    | EBin _ e1 e2 _ => free_av' e1 ++ free_av' e2
    | EA x e _ => x :: free_av' e
    | EPrj e _ _ => free_av' e
    | ECons es _ => fold_right (fun e xs => free_av' e ++ xs) nil es
    | EIf e e' e'' _ => free_av' e ++ free_av' e' ++ free_av' e''
    end.

  Definition free_sv e := uniq (free_sv' e).
  Definition free_av e := uniq (free_av' e).

  Lemma compile_ok (se : SExp) (seval_env : Env varE (option SVal) _)
        (svar_env : Env varE (list var) _) (n m : nat)
        (sv : SVal) c es :
    evalSE aeval_env seval_env se (inl sv) ->
    compile_sexp aty_env avar_env se svar_env n =  (inl (c, es), m) ->
    CSL BS tid
        (!(assn_of_svs seval_env svar_env (free_sv se)) **
          (assn_of_avs (free_av se)))
        c
        (!(assn_of_svs seval_env svar_env (free_sv se)) **
          (assn_of_avs (free_av se)) ** !(es ==t vs_of_sval sv)).
  Proof.
    revert se seval_env svar_env n m sv c es.
    induction se using SExp_ind'; simpl;
    introv.
    - intros Heval Hcompile.
      unfold ret in Hcompile; inversion Hcompile; substs.
      inversion Heval; substs; simpl in *.
      eapply Hforward; eauto using rule_skip.
      intros; sep_split; sep_split_in H; repeat sep_cancel.
      destruct (seval_env x); sep_split_in H; sep_split; eauto.
      + inverts H1; sep_normal_in HP; sep_split_in HP; eauto.
      + destruct HP.
      (* assert (Hin : In x ) by (destruct Heq1; unfold incl in *; simpl in *; eauto). *)
      
      (* Lemma assn_of_svs_in seval_env svar_env x fv v : *)
      (*   In x fv -> *)
      (*   seval_env x = Some v -> *)
      (*   !(assn_of_svs seval_env svar_env fv) |= !(S.vars2es (svar_env x) ==t vs_of_sval v). *)
      (* Proof. *)
      (*   induction fv; simpl in *; destruct 1; substs; intros Heq. *)
      (*   - rewrite Heq. *)
      (*     intros. *)
      (*     sep_rewrite_in pure_star H; sep_rewrite_in pure_pure H. *)
      (*     sep_split_in H; sep_split; eauto. *)
      (*   - destruct (seval_env a); [|intros ? ? [? []]]. *)
      (*     intros stk h H'. *)
      (*     sep_rewrite_in pure_star H'; sep_rewrite_in pure_pure H'. *)
      (*     sep_split_in H'. *)
      (*     apply IHfv; eauto; sep_split; eauto. *)
      (* Qed. *)

      (* forwards: (>>assn_of_svs_in s (emp_ph loc)); eauto. *)
      (* sep_split; eauto using emp_emp_ph. *)
      (* sep_split_in H0; eauto. *)

    - intros _; introv Heval Hcompile.
      inversion Hcompile; substs.
      eapply Hforward; [apply rule_skip|].
      intros; sep_split; sep_split_in H; eauto.
      inversion Heval; substs.
      simpl; sep_split; eauto using emp_emp_ph; unfold_conn; simpl; auto.
    - introv Heval Hcompile.
      unfold bind_opt in Hcompile.
      destruct (compile_sexp _ _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (freshes (length es1) _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hcompile].
      destruct (compile_sexp _ _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hcompile].
      inverts Hcompile; substs.
      inverts Heval; substs.
      
      forwards*: IHse1.
      