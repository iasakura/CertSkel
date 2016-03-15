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

  Definition str_of_pnat n m :=
    ("l" ++ S.nat_to_string n ++ "_" ++ S.nat_to_string m).

  Definition freshes dim : M (list var) :=
    let fix f dim n :=
        match dim with
        | O => ret nil
        | S dim =>
          f dim n >>= fun fs =>
           ret (Var (str_of_pnat n dim) :: fs)
        end in
    get >>= fun n =>
    set (n + 1) >>= fun _ =>
    f dim n.

  Definition char a := String a EmptyString.
  Definition str_in s c := exists s1 s2, s = s1 ++ char c ++ s2.
  Lemma sep_var_inj s1 s1' c s2 s2' :
    s1 ++ char c ++ s2 = s1' ++ char c ++ s2' ->
    ~str_in s1 c -> ~str_in s1' c ->
    s1 = s1'.
  Proof.
    revert s1' s2 s2'; induction s1; simpl; introv Heq Hin Hin'.
    - destruct s1'; simpl in *; eauto.
      assert (c <> a).
      { intros Hc; substs.
        apply Hin'.
        exists "" (s1'); eauto. }
      inverts Heq; congruence.
    - destruct s1'; simpl in *; inverts Heq.
      { false; apply Hin; exists "" s1; eauto. }
      forwards*: (>>IHs1 s1'); try congruence.
      { intros (t1 & t2 & Heq'); apply Hin; exists (char a0 ++ t1) t2; simpl in *; congruence. }
      { intros (t1 & t2 & Heq'); apply Hin'; exists (char a0 ++ t1) t2; simpl in *; congruence. }
  Qed.

  Definition char_of_string s := match s with
                                 | String c _ => c
                                 | _ => Ascii.zero
                                 end.
  
  Lemma nat_to_str_underbar n :
    ~str_in (S.nat_to_string n) (char_of_string "_").
  Proof.
    induction n; simpl; intros (s1 & s2 & Heq).
    - destruct s1; simpl in *; try congruence.
      inverts Heq.
      destruct s1; simpl in *; try congruence.
    - destruct s1; simpl in *; try congruence.
      inverts Heq.
      apply IHn; exists s1 s2; eauto.
  Qed.

  Lemma str_of_pnat_inj n m n' m' :
    str_of_pnat n m = str_of_pnat n' m' ->
    n = n' /\ m = m'.
  Proof.
    intros H; unfold str_of_pnat in H.
    inverts H as Heq.
    forwards*: (sep_var_inj (S.nat_to_string n) (S.nat_to_string n')); simpl; eauto using nat_to_str_underbar.
    split; apply S.nat_to_string_inj; auto.
    cut (String "_" (S.nat_to_string m) = String "_" (S.nat_to_string m')); [intros H'; inversion H'; auto|].
    eapply S.string_inj2; eauto.
  Qed.
  
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
        else fail ("overflow the index " ++ S.nat_to_string i ++ " of tuple:" ++ "type of tuple: " ++ string_of_ty ty ++
                   "expected length = " ++ S.nat_to_string (len_of_ty ty) ++
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

Require Import MSets.

Module Type DecType <: DecidableType.
  Parameter t : Type.
  Definition eq := @eq t.
  Lemma eq_equiv : Equivalence eq.
    repeat constructor; unfolds; unfold eq; intros; congruence.
  Qed.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End DecType.

Module VarE_eq : DecType with Definition t := varE.
  Definition t := varE.
  Definition eq (x y : t) := x = y.
  Definition eq_equiv : Equivalence eq.
  Proof.
    split; cbv; intros; congruence.
  Qed.
  Definition eq_dec := eq_dec.
End VarE_eq.
Module VarA_eq : DecType with Definition t := varA.
  Definition t := varA.
  Definition eq (x y : t) := x = y.
  Definition eq_equiv : Equivalence eq.
  Proof.
    split; cbv; intros; congruence. 
  Qed.
  Definition eq_dec := @eq_dec t _.
End VarA_eq.

Require Import SetoidClass.

Module VarsProps (D : DecType).
  Module SE := MSetWeakList.Make D.

  Instance eq_type_dt : eq_type D.t := {| eq_dec := D.eq_dec |}.

  Close Scope exp_scope.
  Infix "==" := equiv.

  Instance eqset_setoid : Setoid SE.t :=
    {| equiv := SE.Equal; setoid_equiv := _ |}.

  Lemma eqset_empty s s' : SE.Empty s -> s == s' -> SE.Empty s'.
  Proof.
    unfold not, SE.Empty, "=="; firstorder.
  Qed.

  Lemma choose_remove s x : SE.In x s -> s == SE.add x (SE.remove x s).
  Proof.
    revert s x; clear; intros s x; simpl.
    unfold SE.Equal; intros.
    rewrite SE.add_spec, SE.remove_spec.
    lets [? | ?]: (eq_dec a x); split; intros; substs; intuition.
  Qed.

  Lemma equal_in x s s' : SE.In x s -> s == s' -> SE.In x s'.
  Proof.
    unfold SE.Equal, SE.In; intros.
    apply H0; auto.
  Qed.

  Lemma cardinal0_empty s : SE.cardinal s = 0 <-> SE.Empty s.
  Proof.
    unfold SE.Empty, SE.cardinal; intros; split; intros H.
    - destruct s as [[|? ?] ?]; simpl in *; try congruence.
      cbv; inversion 1.
    - destruct s as [[| ? ? ] ?]; simpl; auto.
      false; lets: (H e); apply H0; left; auto.
  Qed.

  Lemma cardinal_add x s : ~SE.In x s -> SE.cardinal (SE.add x s) = S (SE.cardinal s).
  Proof.
    destruct s as [s ?]; unfold SE.In, SE.add, SE.cardinal; simpl.
    remember (SE.Raw.cardinal s) as car_s eqn:Heqc.
    clear is_ok.
    revert s Heqc; induction car_s using lt_wf_ind; intros s Heqc Hnin.
    destruct car_s.
    - unfold SE.cardinal in *; destruct s as [|? ?]; simpl in *; congruence.
    - unfold SE.cardinal in *; destruct s as [|? ?]; simpl in *; try congruence.
      destruct (D.eq_dec x e); simpl in *; substs.
      + false; unfold SE.Raw.In in Hnin; apply Hnin.
        constructor; auto.
      + forwards* :(>>H car_s s).
        intros Hc; apply Hnin; right; auto.
  Qed.  

  Lemma remove_nin x s : ~SE.In x (SE.remove x s).
  Proof.
    rewrite SE.remove_spec; intros [? ?]; congruence.
  Qed.

  Lemma eqset_cardinal s s' : s == s' -> SE.cardinal s = SE.cardinal s'.
  Proof.
    destruct s as [s oks], s' as [s' oks'].
    simpl; unfold SE.Equal, SE.In, SE.cardinal.
    revert s' oks'; induction s; simpl in *; intros s' oks'.
    - destruct s'; simpl; auto.
      intros H; lets [? ?]: (H e); unfold SE.Raw.In in *; simpl in *.
      false; forwards: H1; [left; auto|inversion H2].
    - intros Heq.
      inverts oks.
      assert (SE.Raw.Ok s) by apply H2.
      cutrewrite (SE.Raw.cardinal s' = S (SE.Raw.cardinal (SE.Raw.remove a s'))).
      erewrite IHs; eauto using SE.Raw.remove_ok.
      { intros b; rewrite SE.Raw.remove_spec; eauto.
        split; intros.
        + split.
          rewrite <-Heq; right; auto.
          intros Hc; substs; unfold SE.Raw.In in *; auto.
        + destruct H0.
          rewrite <-Heq in H0; inverts H0; try congruence.
          unfold SE.Raw.In; auto. }
      { assert (SE.Raw.In a s').
        { rewrite <-Heq; left; auto. }
        revert H0 oks'; clear.
        induction s'; simpl.
        - inversion 1.
        - destruct D.eq_dec as [Heq | Heq]; unfold VarE_eq.eq in Heq; substs; auto.
          simpl.
          intros; rewrite <-IHs'; eauto.
          inversion H0; substs; eauto; congruence.
          inversion oks'; substs; auto. }
  Qed.

  Lemma eqset_remove a s s' : s == s' -> SE.remove a s == SE.remove a s'.
  Proof.
    simpl; unfold SE.Equal; intros; rewrite !SE.remove_spec.
    firstorder.
  Qed.

  Lemma add_eq a s :
    ~In a s ->
    SE.Raw.add a s = s ++ a :: nil.
  Proof.
    induction s; simpl; eauto.
    intros Hc.
    destruct D.eq_dec; simpl.
    - false; apply Hc; left; auto.
    - f_equal; rewrite IHs; auto.
  Qed.

  Lemma set_eq s s' H H' : s = s' -> {| SE.this := s; SE.is_ok := H |} = {| SE.this := s'; SE.is_ok := H' |}.
  Proof.
    intros Heq.
    destruct Heq.
    assert (H = H') by (apply proof_irrelevance); substs; eauto.
  Qed.

  Lemma add_spec' a b s :
    SE.In a (SE.add b s) <-> a = b \/ (a <> b /\ SE.In a s).
  Proof.
    splits; [|rewrite SE.add_spec; intros [?|[? ?]]; eauto].
    destruct s as [s ok]; unfold SE.In, SE.add; simpl.
    induction s; simpl.
    - intros H; inverts H as H; eauto.
      inverts H.
    - destruct D.eq_dec as [Heq | Hneq]; [substs|].
      + destruct (eq_dec a a0); eauto.
      + unfold VarE_eq.eq in Hneq.
        intros H; inverts H; [right; split; eauto|].
        * left; eauto.
        * inverts ok; forwards*: IHs.
          destruct H as [? | [? ?]]; eauto.
          right; split; eauto.
          right; eauto.
  Qed.

  Lemma add_already a s :
    SE.In a s -> SE.add a s = s.
  Proof.
    destruct s as [s ok]; unfold SE.In, SE.add; simpl.
    induction s; simpl.
    - inversion 1.
    - intros H.
      apply set_eq.
      destruct D.eq_dec; eauto.
      inverts H.
      unfold VarE_eq.eq in n; congruence.
      inverts ok.
      forwards * :(IHs H3).
      apply (f_equal SE.this) in H; simpl in *; congruence.
  Qed.
  
  Lemma add_inverts a s s' :
    ~SE.In a s -> ~SE.In a s' ->
    SE.add a s == SE.add a s' -> s == s'.
  Proof.
    unfold "=="; intros ? ? H b.
    lets ? ?: (H b); rewrite !SE.add_spec in *.
    split; intros H';
      [lets [?|?]: (H2 (or_intror H')) | lets [?|?]: (H3 (or_intror H'))]; eauto;
        [assert (a <> b); [intros Hc; substs; eauto|congruence ]..].
  Qed.
  
  Lemma choose_card s :
    0 < SE.cardinal s -> exists v, SE.In v s.
  Proof.
    destruct s as [[|a s] ok].
    - unfold SE.cardinal; simpl; omega.
    - exists a; cbv.
      left; auto.
  Qed.

  Lemma remove_card a s :
    SE.In a s ->
    SE.cardinal (SE.remove a s) = SE.cardinal s - 1.
  Proof.
    intros H; forwards*: (choose_remove s a).
    lets: (>>eqset_cardinal H0).
    rewrite cardinal_add in H1; [|apply remove_nin].
    omega.
  Qed.

  Lemma union_emp_l s : SE.union SE.empty s == s.
  Proof.
    unfold SE.Equal; intros a.
    rewrite SE.union_spec.
    lets: (SE.empty_spec); unfold SE.Empty in H.
    split; [intros [|]|intros]; eauto.
    intros; false; eapply H; eauto.
  Qed.

  Lemma union_emp_r s : SE.union s SE.empty == s.
  Proof.
    unfold SE.Equal; intros a.
    rewrite SE.union_spec.
    lets: (SE.empty_spec); unfold SE.Empty in H.
    split; [intros [|]|intros]; eauto.
    intros; false; eapply H; eauto.
  Qed.

  Lemma cardinal0_empty' s :
    SE.cardinal s = 0 -> s = SE.empty.
  Proof.
    destruct s as [[|a s ] ok]; cbv; try omega.
    intros; apply set_eq; auto.
  Qed.

  Lemma diff_emp_r s : SE.diff s SE.empty == s.
  Proof.
    unfold "=="; intros a; rewrite SE.diff_spec.
    lets: SE.empty_spec; unfold SE.Empty in *; firstorder.
  Qed.

  Instance union_proper_l : Proper (SE.Equal ==> SE.Equal ==> SE.Equal) SE.union.
  Proof.
    unfold SE.Equal; intros s1 s2 Heq s3 s4 Heq' a.
    rewrite !SE.union_spec; firstorder.
  Qed.

  Instance diff_proper_l : Proper (SE.Equal ==> SE.Equal ==> SE.Equal) SE.diff.
  Proof.
    unfold SE.Equal; intros s1 s2 Heq s3 s4 Heq' a.
    rewrite !SE.diff_spec; firstorder.
  Qed.

  Instance add_proper_l a : Proper (SE.Equal ==> SE.Equal) (SE.add a).
  Proof.
    unfold SE.Equal; intros s1 s2 Heq a'.
    rewrite !SE.add_spec; firstorder.
  Qed.

  Section Assns.
  Variable Vals : Type.
  Variable find : D.t -> option Vals.
  Variable den : D.t -> Vals -> assn.

  Definition assn_of_vs s :=
    SE.fold (fun x rec =>
               match find x with
               | Some vs => den x vs ** rec
               | None => FalseP
               end) s emp.
  
  Tactic Notation "simpl_avs" "in" hyp(HP) := unfold assn_of_vs, SE.fold in HP; simpl in HP.
  Tactic Notation "simpl_avs" := unfold assn_of_vs, SE.fold; simpl.
  Tactic Notation "simpl_avs" "in" "*" := unfold assn_of_vs, SE.fold in *; simpl in *.

  Arguments flip / _ _ _ _ _ _.

  Lemma assn_empty s stk : SE.Empty s -> stk ||= assn_of_vs s <=> emp.
  Proof.
    destruct s as [[| ? ?] ?]; rewrite <-SE.is_empty_spec; simpl; 
      simpl_avs; unfold SE.is_empty; simpl; try congruence.
    reflexivity.
  Qed.

  Lemma assn_empty' stk : stk ||= assn_of_vs SE.empty <=> emp.
  Proof.
    cbv; eauto.
  Qed.

  Lemma add_equiv a s stk :
    ~SE.In a s ->
    stk ||= assn_of_vs (SE.add a s) <=>
        match find a with
        | Some v => den a v ** assn_of_vs s
        | None => FalseP 
        end.
  Proof.
    unfold assn_of_vs, SE.add, SE.In; rewrite !SE.fold_spec.
    destruct s as [s oks]; simpl.
    intros; rewrite add_eq; [|intros Hc; eapply In_InA in Hc; eauto using SE.E.eq_equiv].
    rewrite fold_left_app; simpl.
    destruct (find a); [|reflexivity].
    reflexivity.
  Qed.

  Lemma fold_left_assns (s : list D.t) (P : assn) (stk : stack):
    stk ||=
        fold_left (fun rec x => match find x with
                                         | Some v => den x v ** rec
                                         | None => FalseP end) s P <=>
        P ** fold_left (fun rec x => match find x with
                                     | Some v => den x v ** rec
                                     | None => FalseP end) s emp.
  Proof.
    revert P; induction s; simpl; intros P.
    - rewrite emp_unit_r; reflexivity.
    - rewrite IHs.
      destruct (find a); simpl.
      rewrite (IHs (_ ** emp)).
      repeat rewrite <-sep_assoc, emp_unit_r; split; intros; repeat sep_cancel.
      rewrite (IHs FalseP).
      split; intros; destruct H as (? & ? & ? & ? & ?);
        try lazymatch goal with [H : False|- _] => destruct H end.
      destruct H0 as (? & ? & ? & ? & ?);
        try lazymatch goal with [H : False|- _] => destruct H end.
  Qed.

  Lemma add_equiv'   a s stk :
    SE.In a s ->
    stk ||= assn_of_vs s <=>
            assn_of_vs (SE.add a (SE.remove a s)).
  Proof.
    destruct s as [s oks].
    unfold "==", SE.In, SE.cardinal; simpl.
    unfold assn_of_vs, SE.fold, SE.Raw.fold at 1; simpl.
    generalize emp; induction s;  intros P Hin.
    - inversion Hin.
    - inverts Hin.
      + simpl; destruct D.eq_dec as [? | Hneq].
        2: unfold VarE_eq.eq in Hneq; congruence.
        rewrite add_eq; [|inverts oks; rewrite InA_alt in *; eauto].
        unfold SE.Raw.fold; rewrite fold_left_app; simpl.
        destruct (find a0); simpl.
        * rewrite fold_left_assns. rewrites (>>fold_left_assns s P).
          rewrite <-sep_assoc; reflexivity.
        * rewrite fold_left_assns; split; [|destruct 1].
          intros (? & ? & ? & ? & ?); eauto.
      + inverts keep oks.
        forwards*: (>> (IHs H3)).
        simpl; rewrite H.
        assert (a <> a0).
        { intros Hc; substs; eauto. }
        destruct D.eq_dec; try congruence.
        simpl; destruct D.eq_dec; try congruence; simpl.
        destruct (find a0); [|reflexivity].
        reflexivity.
  Qed.

  Lemma eqset_equiv   s s' stk :
    SE.Equal s s' ->
    stk ||= assn_of_vs s <=> assn_of_vs s'.
  Proof.
    remember (SE.cardinal s) as car_s eqn:Heqc.
    revert s s' Heqc; induction car_s using lt_wf_ind; intros s s' Heqc Heqss'.
    destruct car_s.
    - assert (SE.Empty s).
      { unfold SE.Empty; intros.
        rewrite SE.cardinal_spec in Heqc.
        destruct s as [[|? ?] ?]; simpl in *; try congruence.
        cbv; inversion 1. }
      forwards* : (eqset_empty).
      forwards* Heq: (assn_empty s); rewrite Heq.
      forwards* Heq': (assn_empty s'); rewrite Heq'; reflexivity.
    - lets a Ha: (>>choose_card s); try omega.
      assert (SE.In a s') by (applys* Heqss').
      rewrites* (>>add_equiv' a s).
      rewrites* (>>add_equiv' a s').
      rewrites* (>>add_equiv (SE.remove a s)); [apply remove_nin|].
      rewrites* (>>add_equiv (SE.remove a s')); [apply remove_nin|].
      destruct (find a); [|reflexivity].
      rewrites H; try reflexivity.
      forwards*: (remove_card a s); omega.
      apply (add_inverts a); eauto using remove_nin.
      rewrite <-!choose_remove; eauto.
  Qed.          

  Instance eqset_proper stk : Proper (SE.Equal ==> equiv_sep stk) assn_of_vs.
  Proof.
    intros s1 s2 Heq; apply eqset_equiv; auto.
  Qed.

  Lemma union_add_l a s s' : SE.union (SE.add a s) s' == SE.add a (SE.union s s').
  Proof.
    simpl; unfold SE.Equal; intros.
    repeat (try rewrite SE.union_spec; try rewrite SE.add_spec); intuition.
  Qed.

  Lemma union_add_r a s s' : SE.union s (SE.add a s') == SE.add a (SE.union s s').
  Proof.
    simpl; unfold SE.Equal; intros.
    repeat (try rewrite SE.union_spec; try rewrite SE.add_spec); intuition.
  Qed.
  
  Lemma union_assns s s' stk :
    stk ||= 
        assn_of_vs (SE.union s s') <=>
        assn_of_vs s **
        assn_of_vs (SE.diff s' s).
  Proof.
    remember (SE.cardinal s) as car_s eqn:Heqc.
    revert s s' Heqc; induction car_s using lt_wf_ind; intros s s' Heqc.
    destruct car_s.
    - forwards*: cardinal0_empty'; substs.
      rewrites (union_emp_l s').
      rewrite assn_empty'.
      rewrites (diff_emp_r s').
      rewrite emp_unit_l; reflexivity.
    - forwards* (a & Hin): (choose_card s); try omega.
      forwards* Heq: (choose_remove s).
      rewrite Heq at 1 2.
      rewrite union_add_l, <-union_add_r.
      rewrite (H car_s); try omega; try (rewrites* remove_card; omega).
      assert (Heq' : SE.diff (SE.add a s') (SE.remove a s) ==
                     SE.add a (SE.remove a (SE.diff s' s))).
      { simpl; unfold SE.Equal; intros;
        repeat (try rewrite SE.diff_spec;
                try rewrite SE.add_spec;
                try rewrite SE.remove_spec).
        assert (Decidable.decidable (SE.In a0 s)).
        { unfolds; destruct (SE.mem a0 s) eqn:Heq'.
          rewrite SE.mem_spec in *; eauto.
          right; intros Hc; rewrite <-SE.mem_spec in Hc; congruence. }
        clear; intros; intuition.
        destruct (eq_dec a0 a); eauto. }
      rewrite Heq'.
      repeat rewrite add_equiv; [|apply remove_nin..].
      destruct (find a).
      2: split; intros (? & ? & ? & ? & ? & ?); lazymatch goal with [H : False |- _] => destruct H end.
      assert (Heq'' : SE.remove a (SE.diff s' s) == SE.diff s' s).
      { simpl; unfold SE.Equal; intros;
        repeat (try rewrite SE.diff_spec;
                try rewrite SE.add_spec;
                try rewrite SE.remove_spec).
        intuition; subst; eauto. }
      rewrite Heq''.
      rewrite <-!sep_assoc; split; intros; repeat sep_cancel.
  Qed.
  End Assns.
  Include SE.
End VarsProps.

Module SA := VarsProps VarA_eq.
Module SE := VarsProps VarE_eq.

Section CorrectnessProof.
  Import Skel_lemma.
  (* the set of free variables *)
  Variable free_avs : SA.t.
  (* the evaluation environment *)
  Variable aeval_env : Env varA (option array) _.
  (* the typing environment *)
  Variable aty_env : Env varA Typ _.
  (* the variable mapping environment between source and dest. *)
  Variable avar_env : Env varA (list var) _ .
  
  (* source lang. values -> dest. lang. values *)
  Fixpoint vs_of_sval sval : list Z :=
    match sval with
    | VB b => (if b then 1%Z else 0%Z) :: nil
    | VZ z => z :: nil
    | VTup vs => fold_right (fun v vs => vs_of_sval v ++ vs) nil vs
    end%list.

  (* precondition of free variable arrays *)
  Definition assn_of_avs (favs : SA.t) : assn :=
    SA.assn_of_vs array aeval_env (fun x_a a =>
       S.is_tuple_array_p (S.es2gls (S.vars2es (avar_env x_a))) (len_of a)
                          (fun i => vs_of_sval (nth i (arr_of a) (VZ 0))) 0 1) favs.
  
  (* (* the set of free variables of scalar exp *) *)
  (* Variable free_svs : list varE. *)
  (* (* the evaluation environment of scalar exp *) *)
  (* Variable seval_env : Env varE (option SVal) _. *)
  (* (* the typing environment *) *)
  (* Variable sty_env : Env varE Typ _. *)
  (* (* the variable mapping environment between source and dest. *) *)
  (* Variable svar_env : Env varE (list var) _ . *)

  (* preconditions of scalar variables *)
  Definition assn_of_svs (seval_env : Env varE (option SVal) _) (svar_env : Env varE (list var) _)  (fsvs : SE.t) : assn :=
    SE.assn_of_vs SVal seval_env (fun x_e v =>
                !(vars2es (svar_env x_e) ==t vs_of_sval v)) fsvs.
  
  (* Section UniqList. *)
  (*   Variable A : Type. *)
  (*   Variable eqt : eq_type A. *)
  (*   Definition equiv_ls (ls1 ls2 : list A) := (incl ls1 ls2) /\ (incl ls2 ls1). *)
    
  (*   Require Import Recdef. *)
  (*   Lemma remove_length (xs : list A) x: *)
  (*     length (remove eq_dec x xs) <= length xs. *)
  (*   Proof. *)
  (*     induction xs; simpl; try omega. *)
  (*     destruct eq_dec; simpl; try omega. *)
  (*   Qed. *)
  
  (*   Function uniq (xs : list A) {measure length xs} := *)
  (*     match xs with *)
  (*     | nil => nil *)
  (*     | x :: xs => x :: uniq (remove eq_dec x xs) *)
  (*     end. *)
  (*   Proof. *)
  (*     intros; simpl. *)
  (*     lets: (>> remove_length xs0 x); simpl in *; try omega. *)
  (*   Defined. *)

  (*   Lemma remove_incl x (xs : list A) : *)
  (*     incl (remove eq_dec x xs) xs. *)
  (*   Proof. *)
  (*     induction xs; unfold incl in *; simpl; eauto. *)
  (*     destruct (eq_dec _ _); substs; simpl in *; jauto. *)
  (*     intros ? [? | ?]; eauto. *)
  (*   Qed. *)
    
  (*   Lemma uniq_incl (xs : list A) : incl (uniq xs) xs. *)
  (*   Proof. *)
  (*     functional induction (uniq xs). *)
  (*     - unfold incl; eauto. *)
  (*     - unfold incl in *; simpl. *)
  (*       intros ? [? | ?]; eauto. *)
  (*       forwards* : IHl. *)
  (*       forwards* : remove_incl. *)
  (*   Qed. *)

  (*   Lemma remove_neq (x y : A) (xs : list A) : x <> y -> In x xs -> In x (remove eq_dec y xs). *)
  (*   Proof. *)
  (*     revert y; induction xs; simpl; intros y Hneq Hin; auto. *)
  (*     destruct Hin as [Hin | Hin]; substs. *)
  (*     - destruct eq_dec; try congruence. *)
  (*       simpl; eauto. *)
  (*     - destruct eq_dec; substs. *)
  (*       + apply IHxs; eauto. *)
  (*       + simpl; right; eauto. *)
  (*   Qed. *)
        
  (*   Lemma uniq_incl' (xs : list A) : incl xs (uniq xs). *)
  (*   Proof. *)
  (*     functional induction (uniq xs); unfold incl; simpl; eauto. *)
  (*     intros a [Hin|Hin]; substs; eauto. *)
  (*     destruct (eq_dec x a); eauto. *)
  (*     right; apply IHl. *)
  (*     apply remove_neq; eauto. *)
  (*   Qed. *)

  (*   Lemma uniq_no_dup (xs : list A) : NoDup (uniq xs). *)
  (*   Proof. *)
  (*     functional induction (uniq xs). *)
  (*     - constructor. *)
  (*     - constructor; eauto. *)
  (*       intros Hc. *)
  (*       forwards*: uniq_incl; unfold incl in *; eauto. *)
  (*       apply H in Hc; forwards*: remove_In; eauto. *)
  (*   Qed. *)

  (*   Lemma eq_ls_nil_l xs : equiv_ls nil xs -> xs = nil. *)
  (*   Proof. *)
  (*     unfold equiv_ls, incl; simpl; intros [? ?]. *)
  (*     destruct xs; simpl in *; eauto. *)
  (*     lets *: (H0 a). *)
  (*   Qed. *)

  (*   Lemma eq_ls_nil_r xs : equiv_ls xs nil -> xs = nil. *)
  (*   Proof. *)
  (*     unfold equiv_ls, incl; simpl; intros [? ?]. *)
  (*     destruct xs; simpl in *; eauto. *)
  (*     lets *: (H a). *)
  (*   Qed. *)

  (*   Lemma equiv_ls_refl xs : equiv_ls xs xs. *)
  (*   Proof. *)
  (*     unfold equiv_ls; lets: (incl_refl xs); eauto. *)
  (*   Qed. *)

  (*   Lemma equiv_ls_symm xs ys : equiv_ls xs ys -> equiv_ls ys xs. *)
  (*   Proof. *)
  (*     unfold equiv_ls; jauto. *)
  (*   Qed. *)


  (*   Lemma equiv_ls_cons x xs ys : equiv_ls (x :: xs) ys -> *)
  (*                                 exists ys', ys = x :: ys'. *)
  (*   Proof. *)
  (*     revert xs; induction ys; simpl; intros xs. *)
  (*     - intros; forwards*: (eq_ls_nil_r (x :: xs)). *)
  (*     -  *)
      

  (*   Hint Resolve equiv_ls_refl equiv_ls_symm. *)

  (*   Lemma equiv_ls_cons x xs ys : *)
  (*     equiv_ls xs ys -> equiv_ls (x :: xs) (x :: ys). *)
  (*   Proof. *)
  (*     revert ys; induction xs; simpl. *)
  (*     - intros; rewrites* (eq_ls_nil_r ys). *)
  (*     -  *)
      

  (*     Lemma equive_ls_reorder x xs : *)
  (*       In x xs -> *)
  (*       equiv_ls _ xs (x :: (remove eq_dec x xs)). *)
  (*     Proof. *)
  (*       induction xs; simpl; forwards*: tt. *)
  (*       intros [?|Hin]; substs. *)
  (*       destruct eq_dec; try congruence. *)

  (* End UniqList. *)
  
  Import scan_lib.

  Fixpoint free_sv (e : SExp) : SE.t :=
    match e with
    | EVar v _ => SE.singleton v
    | Enum _   => SE.empty
    | ELet x e1 e2 _ => 
      SE.union (free_sv e1) (SE.remove x (free_sv e2))
    | EBin _ e1 e2 _ => SE.union (free_sv e1) (free_sv e2)
    | EA _ e _ => free_sv e
    | EPrj e _ _ => free_sv e
    | ECons es _ => fold_right (fun e xs => SE.union (free_sv e) xs) SE.empty es
    | EIf e e' e'' _ => SE.union (free_sv e) (SE.union (free_sv e') (free_sv e''))
    end.

  Fixpoint free_av (e : SExp) : SA.t :=
    match e with
    | EVar v _ => SA.empty
    | Enum _   => SA.empty
    | ELet x e1 e2 _ => 
      SA.union (free_av e1) (free_av e2)
    | EBin _ e1 e2 _ => SA.union (free_av e1) (free_av e2)
    | EA x e _ => SA.add x (free_av e)
    | EPrj e _ _ => free_av e
    | ECons es _ => fold_right (fun e xs => SA.union (free_av e) xs) SA.empty es
    | EIf e e' e'' _ => SA.union (free_av e) (SA.union (free_av e') (free_av e''))
    end.

  (* Arguments uniq {A} {eqt} x. *)

  (* Definition free_sv e := uniq (free_sv' e). *)
  (* Definition free_av e := uniq (free_av' e). *)

  Variable ntrd : nat.
  Variable tid : Fin.t ntrd.
  Variable BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd.
  Arguments assn_of_svs _ _ _ _ _ : simpl never.
  Arguments assn_of_avs _ _ _ : simpl never.
  Tactic Notation "simpl_avs" "in" hyp(HP) := unfold assn_of_svs, SE.assn_of_vs, SE.fold in HP; simpl in HP.
  Tactic Notation "simpl_avs" := unfold assn_of_svs, SE.assn_of_vs, SE.fold; simpl.
  Tactic Notation "simpl_avs" "in" "*" := unfold assn_of_svs, SE.assn_of_vs, SE.fold in *; simpl in *.
  Arguments flip / _ _ _ _ _ _.
  Instance ban_proper stk : Proper (equiv_sep stk ==> equiv_sep stk) ban.
  Proof.
    intros P1 P2 Heq h; lets:(Heq h).
    unfold ban, Aconj; rewrite H; split; eauto.
  Qed.
    
  Lemma compile_ok (se : SExp) (seval_env : Env varE (option SVal) _)
        (svar_env : Env varE (list var) _) (n m : nat)
        (sv : SVal) c es :
    evalSE aeval_env seval_env se (inl sv) ->
    compile_sexp aty_env avar_env se svar_env n =  (inl (c, es), m) ->
    (forall x, SE.In x (free_sv se) -> 
       forall k l, In (Var (str_of_pnat k l)) (svar_env x) -> k < n) -> (* fvs are not in the future generated vars *)
    (forall x, In x (writes_var c) -> 
       exists k l, (Var (str_of_pnat k l)) = x -> n <= k < m) -> (* written vars are generated with the managed effect *)
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
      simpl_avs in HP.
      destruct (seval_env x); sep_split_in H; sep_split; eauto.
      + inverts H1; sep_normal_in HP; sep_split_in HP; eauto.
      + destruct HP.
    - introv Heval Hcompile.
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
      eapply Hbackward.
      Focus 2. {
        intros.
        unfold assn_of_svs in H0; sep_rewrite_in SE.union_assns H0; sep_rewrite_in pure_star H0.
        unfold assn_of_avs in H0; sep_rewrite_in SA.union_assns H0.
        Lemma fold_assn_svs se sv :
          SE.assn_of_vs SVal se (fun (x_e : VarE_eq.t) (v : SVal) => !(vars2es (sv x_e) ==t vs_of_sval v)) =
          assn_of_svs se sv. auto. Qed.
        Lemma fold_assn_avs :
          SA.assn_of_vs array aeval_env
          (fun (x_a : VarA_eq.t) (a : array) =>
           S.is_tuple_array_p (S.es2gls (S.vars2es (avar_env x_a))) 
             (len_of a) (fun i : nat => vs_of_sval (nth i (arr_of a) (VZ 0))) 0 1) =
          assn_of_avs. auto. Qed.
        rewrite !fold_assn_svs, !fold_assn_avs in H0.
        
        sep_normal_in H0; sep_normal; repeat sep_cancel.
        assert (((!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) **
                 (!(assn_of_svs seval_env svar_env (SE.SE.diff (SE.remove x (free_sv se2)) (free_sv se1))) **
                 assn_of_avs (SA.SE.diff (free_av se2) (free_av se1)))) s h).
        { sep_normal; repeat sep_cancel. }
        exact H1. } Unfocus.
      eapply rule_seq; [eapply rule_frame|].
      apply H.
      { admit. }
      eapply rule_seq.
      
      destruct (compile_sexp _ _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (freshes (length es1) _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hcompile].
      destruct (compile_sexp _ _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hcompile].
      
      
      (* Lemma uniq_subset A (eqt : eq_type A) (xs ys : list A) : *)
      (*   incl xs ys -> incl (uniq xs) (uniq ys). *)
      (* Proof. *)
      (*   revert ys; functional induction (uniq xs); unfold incl; simpl; intros ys Hin z Hinz; *)
      (*     destruct Hinz; substs. *)
      (*   - forwards *: (Hin z). *)
      (*     apply uniq_incl'; eauto. *)
      (*   - apply IHl; eauto. *)
      (*     unfold incl; intros; apply Hin. *)
      (*     right. *)
      (*     lets: remove_incl; unfold incl in *; eauto. *)
      (* Qed. *)

      (* Lemma assn_of_svs_subset xs ys (seval_env : Env varE (option SVal) _) (svar_env : Env varE (list var) _) stk : *)
      (*   incl xs ys -> *)
      (*   exists zs, *)
      (*     stk ||= !(assn_of_svs seval_env svar_env ys) <=> *)
      (*             !(assn_of_svs seval_env svar_env xs) ** !(assn_of_svs seval_env svar_env zs). *)
      (* Proof. *)
      (*   revert xs; induction ys; simpl; unfold incl; intros xs Hin. *)
      (*   - assert (xs = nil); [|substs]. *)
      (*     { destruct xs; eauto; simpl in *. *)
      (*       forwards* : (Hin v). } *)
      (*     exists (@nil varE); simpl. *)
      (*     split; intros; sep_split_in H; sep_split; eauto. *)
      (*   - simpl in Hin. *)
      (*     assert (incl (remove eq_dec a xs) ys). *)
      (*     { unfold incl; intros b Hin'. *)
      (*       destruct (eq_dec a b) as [|Hneq]; substs. *)
      (*       - apply remove_In in Hin' as []. *)
      (*       - forwards* : (Hin b). *)
      (*         Lemma remove_neq' a b xs : *)
      (*           a <> b -> In a (remove eq_dec b xs) -> In a xs. *)
      (*         Proof. *)
      (*           induction xs; simpl; eauto. *)
      (*           destruct eq_dec; eauto. *)
      (*           simpl; intros ? [? | ?]; eauto. *)
      (*         Qed. *)
      (*         eapply remove_neq'; eauto. } *)
      (*     forwards* [zs IH]: (>>IHys H). *)

              

      (*     Lemma assn_of_svs_equiv xs ys (seval_env : Env varE (option SVal) _) (svar_env : Env varE (list var) _) stk : *)
      (*       equiv_ls _ xs ys -> *)
      (*       stk ||= !(assn_of_svs seval_env svar_env xs) <=> !(assn_of_svs seval_env svar_env ys). *)
      (*     Proof. *)
      (*       revert ys; induction xs; simpl; simpl; intros ys Heq. *)
      (*       - assert (ys = nil); [|substs; simpl]. *)
      (*         { unfold equiv_ls, incl in Heq; destruct Heq, ys; simpl in *; eauto. *)
      (*           forwards*: (H0 v). } *)
      (*         reflexivity. *)
      (*       - destruct ys as [|y ys]. *)
      (*         { unfold equiv_ls, incl in Heq; destruct Heq; simpl in *. *)
      (*           forwards*: (H a). } *)
              

      (*     exists zs; simpl. *)
      (*     destruct (seval_env a). *)
      (*     2: split; intros H'; sep_split_in H'; sep_split; try destruct HP; eauto. *)
      (*     rewrite !pure_star, !pure_pure. *)
      (*     rewrite IH. *)
      (*     split; intros; repeat sep_cancel. *)
