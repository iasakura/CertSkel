Require Import String.
Require Import Vector.
Require Import List.
Require Import ZArith.
Require Import GPUCSL.
Require Import LibTactics.
Require Import Psatz.
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
    (forall (e : SExp) ty, P e -> forall i : nat, P (EPrj e i ty)) ->
    (forall (es : list SExp) ty, List.Forall P es -> P (ECons es ty)) ->
    (forall (e : SExp) ty, P e -> forall e' : SExp, P e' -> forall e'' : SExp, P e'' -> P (EIf e e' e'' ty)) ->
    forall e : SExp, P e.
Proof.
  intros; revert e.
  refine (fix rec (e : SExp) := 
    match e return P e with
    | EVar x _ => H _ _
    | ENum x => H0 _
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
  Arr {len_of : nat; arr_of : list SVal}.

(* environments for variables *)
Definition AEnv (A : Type) := Env varA A _.
Definition SEnv (A : Type) := Env varE A _.

(* eval environment, var -> val *)
Notation AEnv_eval := (AEnv (option array)).
Notation SEnv_eval := (SEnv (option SVal)).

Definition op_denote (op : SOp) (v1 v2 : SVal) :=
  match op with
  | Emin => match v1, v2 with VZ v1, VZ v2 => Some (VZ (Z.min v1 v2)) | _, _ => None end
  | Eplus => match v1, v2 with VZ v1, VZ v2 => Some (VZ (v1 + v2)) | _, _ => None end
  | BEq => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 =? v2)) | _, _ => None end
  | Blt => match v1, v2 with VZ v1, VZ v2 => Some (VB (v1 <? v2)) | _, _ => None end
  end%Z.

Section Semantics.
  Variable aenv : AEnv_eval.

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
      (0 <= ix)%Z -> (ix < Z.of_nat (len_of va))%Z -> 
      evalSE senv (EA varA e ty) (List.nth (Z.to_nat ix) (arr_of va) (VZ 0))
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

  Inductive evalFunc : list SVal -> Func -> SVal -> Prop :=
  | EvalFunc_app xs vs e v bnd : 
      bind_vars xs vs = Some bnd ->
      evalSE bnd e v ->
      evalFunc vs (F xs e) v.

  Variable eval_skel : AEnv_eval -> name -> list Func -> list varA -> array -> Prop.
  
  Inductive evalAE : AEnv_eval -> AE -> array -> Prop :=
  | EvalAE_ret aenv ax v :
      aenv ax = Some v -> evalAE aenv (ARet ax) v
  | EvalAE_alet (aenv : AEnv_eval) ax skl fs axs e2 v1 v2 :
      eval_skel aenv skl fs axs v1 ->
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
    | Top.Emin => fun tys =>
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
    | Top.ENum n => Some (Top.ENum n, TZ)
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
  
  Definition len_at_i (tys : list Typ) i : nat :=
    len_of_ty (nth i tys TZ).
  
  Import Lang.
  Open Scope string_scope.

  Notation SVEnv := (Env varE (list var) _).

  Definition str_of_pnat n m :=
    ("l" ++ S.nat_to_string n ++ "_" ++ S.nat_to_string m).

  Definition freshes dim : M (list var) :=
    let fix f dim n :=
        match dim with
        | O => nil
        | S dim =>
          Var (str_of_pnat n dim) :: f dim n
        end in
    get >>= fun n =>
    set (n + 1) >>= fun _ =>
    ret (f dim n).

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

  Definition compile_op (op : SOp) e1 e2 : (cmd * list exp) :=
    match op with
    | Top.Eplus => (Cskip, Lang.Eplus e1 e2 :: nil)
    | Top.Emin => (Cskip, Lang.Emin e1 e2 :: nil)
    | BEq => (Cskip, Lang.Eeq e1 e2 :: nil)
    | Top.Blt => (Cskip, Lang.Elt e1 e2 :: nil)
    end.
  
  (* compiler of scalar expressions *)
  Fixpoint compile_sexp (se : SExp) (env : SVEnv) : M (cmd * list exp) := match se with
    | EVar v _ => ret (Cskip, S.vars2es (env v))
    | Top.ENum z => ret (Cskip, Enum z :: nil)
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
      | e1 :: nil, e2 :: nil =>
        let (c, es) := compile_op op e1 e2 in
        ret (c1;; c2;; c, es)
      | _, _ => fail ""
      end
    | EA va e _ =>
      compile_sexp e env >>= fun ces =>
      let (c, es) := ces in
      let aname := avarenv va in
      freshes (length aname) >>= fun xs =>
      match es with
      | i :: nil => ret (c ;; S.gen_read Gl xs (S.vars2es aname) i, S.vars2es xs)
      | _ => fail ""
      end
    | EPrj e i ty =>
      match typ_of_sexp e with
      | TBool | TZ => fail ""
      | TTup tys => 
        let off := len_until_i tys i in
        let l := len_at_i tys i in
        compile_sexp e env >>= fun ces =>
        let (c, es) := ces in
        if le_dec (off + l) (len_of_ty (TTup tys)) then
          ret (c, firstn l (skipn off es))
        else (* fail ("overflow the index " ++ S.nat_to_string i ++ " of tuple:" ++ "type of tuple: " ++ string_of_ty ty ++ *)
             (*       "expected length = " ++ S.nat_to_string (len_of_ty ty) ++ *)
             (*       "actual length = " ++ S.nat_to_string off ++ " + " ++ S.nat_to_string l) *)
             fail ""
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
      let (c2, e2) := ces2 in
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
  Coercion Top.ENum : Z >-> SExp.
  Coercion EVar' : varE >-> SExp.

  Definition test1 :=
    typing emp_opt emp_opt(
             ELet' "x" (ECons' ((1%Z : SExp)  :: (2%Z : SExp) :: nil)) (
                     ELet' "y" (ECons' ((3%Z : SExp)  :: (4%Z : SExp) :: nil)) (
                             ELet' "z" (ECons' (("x" : SExp) :: ("y" : SExp) :: nil)) ( 
                                     EPrj' "z" 0)))).
  
  Eval cbv in test1.
  Eval cbv in (match test1 with Some (t, _) => Some (compile_sexp (emp_def nil) t (emp_def nil) 0) | None => None end).
  
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

Module VarE_eq : DecType with Definition t := varE with Definition eq_dec := eq_dec.
  Definition t := varE.
  Definition eq (x y : t) := x = y.
  Definition eq_equiv : Equivalence eq.
  Proof.
    split; cbv; intros; congruence.
  Qed.
  Definition eq_dec := eq_dec.
End VarE_eq.
Module VarA_eq : DecType with Definition t := varA with Definition eq_dec := @eq_dec varA _.
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

  Lemma remove_id s x : ~SE.In x s -> s == SE.remove x s.
  Proof.
    simpl; unfold SE.Equal; intros; rewrite SE.remove_spec.
    split; intros; jauto.
    split; eauto; intros Hc; substs*.
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

  Lemma union_comm s1 s2 :
    SE.union s1 s2 == SE.union s2 s1.
  Proof.
    simpl; unfold SE.Equal; intros;
    rewrite !SE.union_spec; split; intros [|]; eauto.
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

  Lemma assn_of_vs_eq Vals find den find' den' s stk :
    (forall x, SE.In x s -> find x = find' x) ->
    (forall x, SE.In x s -> den x = den' x) ->
    stk ||= assn_of_vs Vals find den s <=>
            assn_of_vs Vals find' den' s.
  Proof.
    revert find den find' den' stk.
    destruct s as [s isok]; simpl.
    unfold SE.In, assn_of_vs, SE.fold, SE.Raw.fold, flip; simpl.
    induction s; simpl.
    - reflexivity.
    - introv Hfind Hden.
      rewrite fold_left_assns.
      rewrites (>>fold_left_assns find').
      rewrite Hfind, Hden; destruct (find' a); try (simpl; left; eauto).
      inverts isok.
      rewrite IHs; [reflexivity|..]; eauto.
      intros; apply Hfind; right; eauto.
      intros; apply Hden; right; eauto.
      split; intros (? & ? & [] & ? & ? & ?).
  Qed.

  Lemma in_dec s x : {SE.In x s} + {~SE.In x s}.
  Proof.
    destruct (SE.mem x s) eqn:Heq; [left|right; intros Hc];
      forwards* (? & ?): (SE.mem_spec s x).
    forwards*: H0; congruence.
  Qed.
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
  Variable aty_env : Env varA (option Typ) _.
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
    | ENum _   => SE.empty
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
    | ENum _   => SA.empty
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

  (* some lemma for generetated variables *)
  Lemma freshes_vars d n m xs:
    freshes d n = (inl xs, m) -> 
    m = n + 1 /\
    (forall x, In x xs -> exists l, x = Var (str_of_pnat n l) /\ l < d).
  Proof.
    revert n m xs; induction d; simpl; intros n m xs.
    - unfold get, set, ">>=", ret; simpl; intros H; inverts H.
      split; eauto; destruct 1.
    - unfold freshes, get, set, ">>=", ret in *; simpl.
      lazymatch goal with [|- context [(Var _ :: ?E) ]] => remember E eqn:Heq end.
      intros H; inverts H.
      forwards* (? & ?): IHd.
      split; eauto.
      intros ? H'; apply in_inv in H' as [? | ?]; eauto.
      substs; forwards* (? & ?): H0; eexists; split; eauto.
  Qed.
  
  Lemma freshes_len d n m xs:
    freshes d n = (inl xs, m) -> length xs = d.
  Proof.
    revert n m xs; induction d; unfold freshes, get, set, ">>=", ret in *;
      simpl; inversion 1; simpl in *; try omega.
    forwards * : IHd.
  Qed.

  Lemma var_pnat_inj n m n' m' : Var (str_of_pnat n m) = Var (str_of_pnat n' m') -> n = n' /\ m = m'.
  Proof.
    intros Heq.
    apply str_of_pnat_inj; inversion Heq.
    unfold str_of_pnat; f_equal; eauto.
  Qed.

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

  Lemma compile_don't_decrease se c es (svar_env : Env varE (list var) _) n m :
    compile_sexp avar_env se svar_env n = (inl (c, es), m) ->
    n <= m.
  Proof.
    revert n m svar_env c es; induction se using SExp_ind'; simpl;
      intros n m svar_env c es' Hsuc; eauto; try inverts Hsuc as Hsuc;
    eauto; unfold ">>=" in *;
          (repeat lazymatch type of Hsuc with
             | context [compile_sexp ?X ?Y ?Z ?n] => destruct (compile_sexp X Y Z n) as [[(? & ?) | ?] ?] eqn:?
             | context [freshes ?X ?Y] => destruct (freshes X Y) as ([? | ?] & ?) eqn:?
             end);
    (repeat lazymatch goal with [H : context [match ?E with | _ => _ end]|- _] => destruct E eqn:? end);
          try now (inverts Hsuc; first
            [forwards*: IHse1; forwards*: IHse2; forwards*: freshes_vars; omega |
             forwards*: IHse1; forwards*: IHse2; forwards*: IHse3; forwards*: freshes_vars; omega |
             forwards*: IHse; forwards*: freshes_vars; omega |
             forwards*: IHse; omega]).
    revert n m c es' Hsuc; induction es; introv; intros Hsuc; [inverts Hsuc; eauto|].
    repeat lazymatch type of Hsuc with
      | context [compile_sexp ?X ?Y ?Z ?W ?n] => destruct (compile_sexp X Y Z W n) as [[(? & ?) | ?] ?] eqn:?
      end; try now inverts Hsuc.
    repeat lazymatch type of Hsuc with
      | context [let (_, _) := ?E in _] => destruct E as [[(? & ?)|?] ?] eqn:?
      end; try now inverts Hsuc.
    forwards*: IHes.
    inverts H; eauto.
    inverts Hsuc.
    rewrite Forall_forall in H; forwards*: H; [left; auto|omega].
    Grab Existential Variables.
    apply 1. apply 1.
  Qed.

  Lemma fold_assn_svs se sv :
    SE.assn_of_vs SVal se (fun (x_e : VarE_eq.t) (v : SVal) => !(vars2es (sv x_e) ==t vs_of_sval v)) =
    assn_of_svs se sv. auto. Qed.
  Lemma fold_assn_avs :
    SA.assn_of_vs array aeval_env
      (fun (x_a : VarA_eq.t) (a : array) =>
         S.is_tuple_array_p (S.es2gls (S.vars2es (avar_env x_a))) 
                            (len_of a) (fun i : nat => vs_of_sval (nth i (arr_of a) (VZ 0))) 0 1) =
    assn_of_avs. auto. Qed.

  Lemma inde_equiv P P' xs :
    (forall stk, stk ||= P <=> P') ->
    (inde P xs <-> inde P' xs).
  Proof.
    unfold inde, equiv_sep.
    intros; simpl.
    split; intros; split; intros; intuition;
      try (apply H, H0, H); eauto.
    apply H; apply <-H0; eauto; apply H; eauto.
    apply H; apply <-H0; eauto; apply H; eauto.
  Qed.

  Lemma inde_assn_of_svs seval_env svar_env fvs (xs : list var) :
    (forall x y, In x xs -> SE.In y fvs -> ~In x (svar_env y)) ->
    inde (assn_of_svs seval_env svar_env fvs) xs.
  Proof.
    destruct fvs as [fvs ok]; simpl.
    simpl_avs.
    induction fvs; simpl; repeat prove_inde.
    destruct (seval_env a).
    unfold SE.SE.Raw.fold; simpl.
    intros H.
    rewrites (>>inde_equiv).
    { intros; rewrite SE.fold_left_assns; reflexivity. }
    repeat prove_inde.
    apply inde_eq_tup.
    rewrite Forall_forall; intros; simplify; simpl; eauto.
    apply H in H0; eauto.
    left; auto.
    eauto.
    inverts keep ok as ? Hok; applys* (IHfvs Hok).
    intros; apply H; eauto.
    right; auto.
    simpl_avs. rewrites (>>inde_equiv).
    { intros; unfold SE.SE.Raw.fold; simpl.
      rewrite SE.fold_left_assns.
      instantiate (1 := FalseP).
      split; [intros (? & ? & [] & ? & ? & ?) | destruct 1]. }
    intros; prove_inde.
  Qed.
  
  Lemma inde_assn_of_avs fvs (xs : list var) :
    (forall x y, In x xs -> SA.In y fvs -> ~In x (avar_env y)) ->
    inde (assn_of_avs fvs) xs.
  Proof.
    destruct fvs as [fvs ok]; simpl.
    unfold assn_of_avs, SA.assn_of_vs, SA.SE.fold, SA.SE.Raw.fold; simpl.
    induction fvs; simpl; repeat prove_inde.
    destruct (aeval_env a).
    intros H.
    rewrites (>>inde_equiv).
    { intros; rewrite SA.fold_left_assns; reflexivity. }
    repeat prove_inde.
    apply inde_is_tup_arr.
    intros; simplify.
    unfold S.es2gls in *; simplify.
    apply H in H0; eauto.
    left; auto.
    inverts keep ok as ? Hok; applys* (IHfvs Hok).
    intros; apply H; eauto.
    right; auto.
    simpl_avs. rewrites (>>inde_equiv).
    { intros; unfold SE.SE.Raw.fold; simpl.
      rewrite SA.fold_left_assns.
      instantiate (1 := FalseP).
      split; [intros (? & ? & [] & ? & ? & ?) | destruct 1]. }
    intros; prove_inde.
  Qed.
  
  Scheme evalSE_ind' := Minimality for evalSE Sort Prop with
         evalTup_ind' := Minimality for evalTup Sort Prop.
  Definition evalSE_ind'' :
    forall (aenv : AEnv_eval) (P : Env varE (option SVal) eq_varE -> SExp -> SVal -> Prop),
      (forall (senv : varE -> option SVal) (sx : varE) (v : SVal) (ty : Typ), senv sx = Some v -> P senv (EVar sx ty) v) ->
      (forall (senv : Env varE (option SVal) eq_varE) (n : Z), P senv n (VZ n)) ->
      (forall (senv : Env varE (option SVal) eq_varE) (sx : varE) (e1 e2 : SExp) (v1 v2 : SVal) (ty : Typ),
          evalSE aenv senv e1 v1 ->
          P senv e1 v1 -> evalSE aenv (upd_opt senv sx v1) e2 v2 -> P (upd_opt senv sx v1) e2 v2 -> P senv (ELet sx e1 e2 ty) v2) ->
      (forall (senv : Env varE (option SVal) eq_varE) (op : SOp) (e1 e2 : SExp) (v1 v2 v : SVal) (ty : Typ),
          evalSE aenv senv e1 v1 ->
          P senv e1 v1 -> evalSE aenv senv e2 v2 -> P senv e2 v2 -> op_denote op v1 v2 = Some v -> P senv (EBin op e1 e2 ty) v) ->
      (forall (senv : Env varE (option SVal) eq_varE) (varA : varA) (va : array) (e : SExp) (ix : Z) (ty : Typ),
          evalSE aenv senv e (VZ ix) ->
          P senv e (VZ ix) ->
          aenv varA = Some va -> (0 <= ix)%Z -> (ix < Zn (len_of va))%Z -> P senv (EA varA e ty) (nth (Z.to_nat ix) (arr_of va) (VZ 0))) ->
      (forall (senv : Env varE (option SVal) eq_varE) (e : SExp) (tup : list SVal) (i : nat) (ty : Typ),
          evalSE aenv senv e (VTup tup) -> P senv e (VTup tup) -> i < Datatypes.length tup -> P senv (EPrj e i ty) (nth i tup (VZ 0))) ->
      (forall (senv : Env varE (option SVal) eq_varE) (es : list SExp) (vs : list SVal) (ty : Typ),
          evalTup aenv senv es vs -> List.Forall2 (P senv) es vs -> P senv (ECons es ty) (VTup vs)) ->
      (forall (senv : Env varE (option SVal) eq_varE) (e e' e'' : SExp) (v : SVal) (ty : Typ),
          evalSE aenv senv e (VB true) -> P senv e (VB true) -> evalSE aenv senv e' v -> P senv e' v -> P senv (EIf e e' e'' ty) v) ->
      (forall (senv : Env varE (option SVal) eq_varE) (e e' e'' : SExp) (v : SVal) (ty : Typ),
          evalSE aenv senv e (VB false) -> P senv e (VB false) -> evalSE aenv senv e'' v -> P senv e'' v -> P senv (EIf e e' e'' ty) v) ->
      (forall senv : Env varE (option SVal) eq_varE, List.Forall2 (P senv) Datatypes.nil Datatypes.nil) ->
      (forall (senv : Env varE (option SVal) eq_varE) (e : SExp) (es : list SExp) (v : SVal) (vs : list SVal),
          evalTup aenv senv es vs -> List.Forall2 (P senv) es vs -> evalSE aenv senv e v -> P senv e v ->
          List.Forall2 (P senv) (e :: es) (v :: vs)) ->
      forall e : Env varE (option SVal) eq_varE, evalSE aenv e |= P e.
  Proof.
    introv.
    apply evalSE_ind' with (P0 := fun senv => List.Forall2 (P senv)).
  Qed.
  
  Inductive has_type_val : SVal -> Typ -> Prop :=
  | has_type_bool b : has_type_val (VB b) TBool
  | has_type_z n : has_type_val (VZ n) TZ
  | has_type_tup vs ts :
      List.Forall2 (fun v ty => has_type_val v ty) vs ts ->
      has_type_val (VTup vs) (TTup ts).
  
  Lemma type_preservation (se : SExp) (ty : Typ) (v : SVal)
        (sty_env : Env varE (option Typ) _)
        (seval_env : Env varE (option SVal) _) :
    (forall x v ty, seval_env x = Some v ->
                    sty_env x = Some ty ->
                    has_type_val v ty) ->
    (forall x arr ty d, aeval_env x = Some arr ->
                        aty_env x = Some ty ->
                        forall i, i < len_of arr -> has_type_val (nth i (arr_of arr) d) ty) ->
    has_type aty_env sty_env se ty ->
    evalSE aeval_env seval_env se v ->
    has_type_val v ty.
  Proof.
    Hint Constructors has_type_val.
    intros Hsctx Hactx Hty Heval; revert sty_env ty Hsctx Hactx Hty.
    pattern seval_env, se, v.
    applys (>>evalSE_ind'' aeval_env seval_env Heval); intros; simpl; [hnf|..]; intros;
      try lazymatch goal with
          [ H : has_type _ _ _ _ |- _] => inverts H
      end; eauto.
    - forwards*: H0; forwards*: H2.
      { intros; unfold upd_opt in H4, H5; case_if; inverts H4; inverts H5; eauto. }
    - forwards*: H0; forwards*: H2.
      destruct op; simpl in *; destruct v1, v2, ty1, ty2;
        inverts H3; inverts H12; eauto;
          case_if; inverts H6; eauto.
    - applys* Hactx.
      zify; rewrite Z2Nat.id; eauto.
    - forwards* Htup: H0; inverts Htup.
      Lemma Forall2_nth (A B : Type) i (xs : list A) (ys : list B) P dx dy :
        i < length xs -> 
        Forall2 P xs ys ->
        P (nth i xs dx) (nth i ys dy).
      Proof.
        intros; revert i H;induction H0.
        - intros; simpl in *; omega.
        - intros; simpl; destruct i; eauto.
          apply IHForall2; simpl in *; omega.
      Qed.
      Lemma Forall2_length (A B : Type) (xs : list A) (ys : list B) P :
        Forall2 P xs ys -> length xs = length ys.
      Proof.
        induction 1; simpl in *; congruence.
      Qed.
      forwards*: (>>Forall2_length H4).
      applys* (>>Forall2_nth (VZ 0) TZ); try omega.
    - constructor.
      revert tys H5; induction H0; intros.
      + inverts H5; eauto.
      + inverts H5.
        constructor; eauto.
        apply IHForall2; eauto.
        inverts* H.
  Qed.

  Scheme has_type_ind' := Minimality for evalSE Sort Prop with
         has_type_es_ind' := Minimality for evalTup Sort Prop.

  Lemma has_type_ind'' :
forall (aenv : AEnv_eval) (P : Env varE (option SVal) eq_varE -> SExp -> SVal -> Prop),
(forall (senv : varE -> option SVal) (sx : varE) (v : SVal) (ty : Typ), senv sx = Some v -> P senv (EVar sx ty) v) ->
(forall (senv : Env varE (option SVal) eq_varE) (n : Z), P senv n (VZ n)) ->
(forall (senv : Env varE (option SVal) eq_varE) (sx : varE) (e1 e2 : SExp) (v1 v2 : SVal) (ty : Typ),
 evalSE aenv senv e1 v1 ->
 P senv e1 v1 -> evalSE aenv (upd_opt senv sx v1) e2 v2 -> P (upd_opt senv sx v1) e2 v2 -> P senv (ELet sx e1 e2 ty) v2) ->
(forall (senv : Env varE (option SVal) eq_varE) (op : SOp) (e1 e2 : SExp) (v1 v2 v : SVal) (ty : Typ),
 evalSE aenv senv e1 v1 ->
 P senv e1 v1 -> evalSE aenv senv e2 v2 -> P senv e2 v2 -> op_denote op v1 v2 = Some v -> P senv (EBin op e1 e2 ty) v) ->
(forall (senv : Env varE (option SVal) eq_varE) (varA : varA) (va : array) (e : SExp) (ix : Z) (ty : Typ),
 evalSE aenv senv e (VZ ix) ->
 P senv e (VZ ix) ->
 aenv varA = Some va -> (0 <= ix)%Z -> (ix < Zn (len_of va))%Z -> P senv (EA varA e ty) (nth (Z.to_nat ix) (arr_of va) (VZ 0))) ->
(forall (senv : Env varE (option SVal) eq_varE) (e : SExp) (tup : list SVal) (i : nat) (ty : Typ),
 evalSE aenv senv e (VTup tup) -> P senv e (VTup tup) -> i < Datatypes.length tup -> P senv (EPrj e i ty) (nth i tup (VZ 0))) ->
(forall (senv : Env varE (option SVal) eq_varE) (es : list SExp) (vs : list SVal) (ty : Typ),
 evalTup aenv senv es vs -> Forall2 (P senv) es vs -> P senv (ECons es ty) (VTup vs)) ->
(forall (senv : Env varE (option SVal) eq_varE) (e e' e'' : SExp) (v : SVal) (ty : Typ),
 evalSE aenv senv e (VB true) -> P senv e (VB true) -> evalSE aenv senv e' v -> P senv e' v -> P senv (EIf e e' e'' ty) v) ->
(forall (senv : Env varE (option SVal) eq_varE) (e e' e'' : SExp) (v : SVal) (ty : Typ),
 evalSE aenv senv e (VB false) -> P senv e (VB false) -> evalSE aenv senv e'' v -> P senv e'' v -> P senv (EIf e e' e'' ty) v) ->
(forall senv : Env varE (option SVal) eq_varE, Forall2 (P senv) Datatypes.nil Datatypes.nil) ->
(forall (senv : Env varE (option SVal) eq_varE) (e : SExp) (es : list SExp) (v : SVal) (vs : list SVal),
 evalTup aenv senv es vs -> Forall2 (P senv) es vs -> evalSE aenv senv e v -> P senv e v -> Forall2 (P senv) (e :: es) (v :: vs)) ->
forall e : Env varE (option SVal) eq_varE, evalSE aenv e |= P e.
  Proof.
    introv; 
      apply has_type_ind' with (P0 := fun senv => Forall2 (P senv)).
  Qed.

  Lemma compile_preserve (se : SExp) 
        (sty_env : Env varE (option Typ) _)
        (svar_env : Env varE (list var) _) (n m : nat)
        c es ty :
    (forall x ty, sty_env x = Some ty ->
                  length (svar_env x) = len_of_ty ty) ->
    (forall x ty, aty_env x = Some ty ->
                  length (avar_env x) = len_of_ty ty) ->
    has_type aty_env sty_env se ty ->
    compile_sexp avar_env se svar_env n =  (inl (c, es), m) ->
    length es = len_of_ty ty.
  Proof.
    intros Hsctx Hactx Htyp;
      revert svar_env sty_env n m c es ty Htyp Hsctx.
    induction se using SExp_ind'; simpl; introv Htyp Hsctx Hsucc.
    - inverts Hsucc; inverts Htyp.
      simplify; eauto.
    - inverts Hsucc; inverts* Htyp.
    - unfold ">>=" in Hsucc.
      destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct (freshes (length es1) _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hsucc].
      destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hsucc].
      inverts Htyp as Htyp1 Htyp2.
      forwards*: IHse1; forwards*: IHse2.
      { intros; unfold upd_opt,  upd in *; case_if*.
        forwards*: freshes_len; inverts H0; congruence. }
      inverts* Hsucc.
    - unfold ">>=" in Hsucc.
      destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hsucc].
      inverts Htyp as Htyp1 Htyp2 Hop.
      destruct op, ty1, ty2, es1 as [|? [| ? ?]], es2 as [|? [| ? ?]];
        inverts Hsucc; simpl in *; try congruence; eauto; simpl in *; try case_if; inverts* Hop.
    - unfold ">>=" in Hsucc.
      destruct (compile_sexp _ se _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct (freshes _ _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hsucc].
      destruct es1 as [|i [|? ?]]; inverts Hsucc.
      inverts Htyp as Htyp Havar.
      simplify.
      rewrites* (>>freshes_len Hfeq1).
    - unfold ">>=" in Hsucc.
      Lemma typ_of_sexp_ok sty_env se ty :
        has_type aty_env sty_env se ty ->
        typ_of_sexp se = ty.
      Proof.
        induction 1; simpl; eauto.
      Qed.
      inverts Htyp as Htyp Hidx.
      rewrites* (>>typ_of_sexp_ok Htyp) in Hsucc.
      destruct (compile_sexp _ se _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct le_dec; inverts Hsucc.
      forwards* Hlen: IHse.
      rewrite firstn_length, skipn_length.
      unfold len_at_i in *; rewrite Hlen; simpl.
      rewrite Nat.min_l; omega.
    - revert c es0 n m ty ty0 Htyp Hsucc; induction H; introv Htyp Hsucc; inverts Htyp as Htyp.
      + inverts Hsucc; inverts Htyp; auto.
      + inverts Htyp as Hty Htys.
        unfold ">>=" in *.
        destruct (compile_sexp _ x _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
        lazymatch type of Hsucc with
        | context [let (_, _) := ?X in _]  =>
          destruct X as [[(cs2 & es2) | ?] n''] eqn:Hceq2; [|inversion Hsucc]
        end.
        inverts Hsucc.
        forwards* : (>>IHForall (TTup tys0) (TTup tys0)).
        { constructor; eauto. }
        forwards*: H.
        simpl in *; rewrite app_length; congruence.
    - unfold ">>=" in Hsucc.
      destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc].
      destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n''] eqn:Hceq2; [|inversion Hsucc]. 
      destruct (compile_sexp _ se3 _ _) as [[(cs3 & es3) | ?] n'''] eqn:Hceq3; [|inversion Hsucc]. 
      destruct (freshes (length es2) _) as [[fvs1 | ?] n''''] eqn:Hfeq1; [|inversion Hsucc].
      destruct es1 as [|? [|? ?]]; simpl in *; inverts Hsucc.
      forwards*: freshes_len; simplify.
      rewrites H.
      inverts Htyp.
      forwards*: IHse2.
  Qed.
  
  Lemma has_type_val_len v ty :
    has_type_val v ty ->
    length (vs_of_sval v) = len_of_ty ty.
  Proof.
    revert v; induction ty using STyp_rect'; try now (intros v H; inverts H; simpl; eauto).
    introv Htyp; inverts Htyp as Htyp.
    revert vs Htyp; induction X; introv Htyp.
    - inverts* Htyp.
    - inverts Htyp; simpl in *.
      forwards*: IHX; forwards*: p.
      rewrite app_length; congruence.
  Qed.

  Instance se_eqset_proper e1 e2 stk : Proper (SE.Equal ==> equiv_sep stk) (assn_of_svs e1 e2).
  Proof.
    intros s1 s2 Heq; apply SE.eqset_equiv; auto.
  Qed.
  Instance sa_eqset_proper stk : Proper (SA.Equal ==> equiv_sep stk) (assn_of_avs).
  Proof.
    intros s1 s2 Heq; apply SA.eqset_equiv; auto.
  Qed.
      
  Lemma compile_ok (se : SExp)
        (sty_env : Env varE (option Typ) _)
        (seval_env : Env varE (option SVal) _)
        (svar_env : Env varE (list var) _) (n m : nat) ty
        (sv : SVal) c es :
    has_type aty_env sty_env se ty ->
    evalSE aeval_env seval_env se sv ->
    compile_sexp avar_env se svar_env n =  (inl (c, es), m) ->
    (forall x ty, sty_env x = Some ty -> length (svar_env x) = len_of_ty ty) ->
    (forall x ty, aty_env x = Some ty -> length (avar_env x) = len_of_ty ty) ->
    (forall (x0 : varE) (v : SVal) (ty : Typ), seval_env x0 = Some v -> sty_env x0 = Some ty -> has_type_val v ty) ->
    (forall (x : varA) (arr : array) (ty0 : Typ) (d : SVal),
        aeval_env x = Some arr -> aty_env x = Some ty0 ->
        forall i : nat, i < len_of arr -> has_type_val (nth i (arr_of arr) d) ty0) ->
    (forall x, SE.In x (free_sv se) -> 
       forall k l, In (Var (str_of_pnat k l)) (svar_env x) -> k < n) -> (* fvs are not in the future generated vars *)
    (* fvs are not in the future generated vars *)
    (forall x y, SA.In x (free_av se) -> In y (avar_env x) -> prefix "l" (S.var_of_str y) = false) ->
    (forall x, In x (writes_var c) -> 
       exists k l, (Var (str_of_pnat k l)) = x /\ n <= k < m) /\ (* (ii) written vars are generated with the freshes func.  *)
    (forall e k l , In e es -> In (Var (str_of_pnat k l)) (fv_E e) -> k < m) /\ (* (iii) return exps. don't have future generated vars*)
    CSL BS tid  (* (iii) correctness of gen. code *)
        (!(assn_of_svs seval_env svar_env (free_sv se)) **
          (assn_of_avs (free_av se)))
        c
        (!(assn_of_svs seval_env svar_env (free_sv se)) **
          (assn_of_avs (free_av se)) ** !(es ==t vs_of_sval sv)).
  Proof.
    revert se ty sty_env seval_env svar_env n m sv c es.
    induction se using SExp_ind'; simpl;
    introv Htyp Heval Hcompile Hsvctx Havctx Hsectx Haectx Hsvar Havar.
    - unfold ret in Hcompile; inversion Hcompile; substs.
      inversion Heval; substs; simpl in *.
      splits; (try now destruct 1); eauto.
      { simplify; forwards*: Hsvar; rewrite SE.singleton_spec; auto. }
      { eapply Hforward; eauto using rule_skip.
        intros; sep_split; sep_split_in H; repeat sep_cancel.
        simpl_avs in HP.
        destruct (seval_env x); sep_split_in H; sep_split; eauto.
        + inverts H3; sep_normal_in HP; sep_split_in HP; eauto.
        + destruct HP. }
    - inversion Hcompile; substs.
      splits; (try now destruct 1); eauto.
      { simplify; destruct H. }
      { eapply Hforward; [apply rule_skip|].
        intros; sep_split; sep_split_in H; eauto.
        inversion Heval; substs.
        simpl; sep_split; eauto using emp_emp_ph; unfold_conn; simpl; auto. }
    - unfold bind_opt in Hcompile.
      (* getting compilation/evaluation/typing results of sub-expressions *)
      destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (freshes (length es1) _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hcompile].
      destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hcompile].
      inverts Hcompile; substs.
      
      inverts Heval as Heval1 Heval2; substs.
      inverts Htyp as Htyp1 Htyp2.
      
      (* obtaining induction hypothesis1 *)
      forwards* (Hwr1 & Hres1 & Htri1): IHse1.
      { intros; eapply Hsvar; eauto; rewrite SE.union_spec; eauto. }
      { intros; applys* Havar; rewrite SA.union_spec; eauto. }

      (* freshness of generated variables *)
      forwards* (? & Hfvs): (>>freshes_vars Hfeq1); substs.

      (* obtaining induction hypothesis 2 *)
      forwards* (Hwr2 & Hres2 & Htri2): IHse2.
      { unfold upd_opt, upd; intros; case_if*.
        rewrites* (>>freshes_len Hfeq1).
        inverts H; forwards*: compile_preserve. }
      { unfold upd_opt, upd; intros; case_if*.
        inverts H; inverts H0.
        forwards*: type_preservation. }
      { intros y Hyin k l Hin; unfold upd in Hin.
        destruct (eq_dec x y); substs.
        forwards* (? & ? & ?): Hfvs.
        forwards* (? & ?): (>>var_pnat_inj H); substs.
        omega.
        forwards*: Hsvar; [rewrite SE.union_spec, SE.remove_spec; eauto|].
        forwards*:(>>compile_don't_decrease Hceq1).
        forwards* (? & ?): (>>freshes_vars Hfeq1); omega. }
      { intros; applys* Havar; rewrite SA.union_spec; eauto. }

      (* prove goals *)
      splits; try omega.

      assert (Hlfvs : length fvs1 = length es1).
      { forwards*: freshes_len. }

      (* written vars are generated vars *)
      { forwards*: (>>compile_don't_decrease Hceq1).
        forwards*: (>>compile_don't_decrease Hceq2).
        simpl; intros y; rewrite !in_app_iff; rewrites* S.read_tup_writes; intros  [? | [? | ?]];
          [forwards* (? & ? & ?): Hwr1 |
           forwards* (? & ? & ?): Hfvs |
           forwards* (? & ? & ?): Hwr2 ];
          repeat eexists; jauto; try omega. }
      (* return variables do not conflict with variables generated later *)
      { simplify; forwards*: Hres2; eauto. }
      
      (* 1st commands *)
      eapply Hbackward.
      Focus 2. {
        intros.
        unfold assn_of_svs in H; sep_rewrite_in SE.union_assns H; sep_rewrite_in pure_star H.
        unfold assn_of_avs in H; sep_rewrite_in SA.union_assns H.
        rewrite !fold_assn_svs, !fold_assn_avs in H.
        
        sep_normal_in H.
        assert (((!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) **
                 (!(assn_of_svs seval_env svar_env (SE.SE.diff (SE.remove x (free_sv se2)) (free_sv se1))) **
                 assn_of_avs (SA.SE.diff (free_av se2) (free_av se1)))) s h).
        { sep_normal; repeat sep_cancel. }
        exact H0. } Unfocus.
      eapply rule_seq; [eapply rule_frame|].
      apply Htri1.
      (* side-condition of frame rule *)
      { prove_inde.
        - apply inde_assn_of_svs.
          intros ? ?; rewrite SE.diff_spec, SE.remove_spec; intros ? H ?; simplify.
          destruct H as ((? & ?) & ?).
          forwards* (? & ? & ? & ?): Hwr1; substs.
          forwards*: Hsvar; [rewrite SE.union_spec, SE.remove_spec; eauto|..].
          omega.
        - apply inde_assn_of_avs.
          intros ? ?; rewrite SA.diff_spec; intros ? [? ?]; simplify.
          forwards*: Havar.
          rewrite SA.union_spec; eauto.
          forwards* (? & ? & ? & ?) : Hwr1; substs.
          unfold str_of_pnat in *; simpl in H3; rewrite S.prefix_nil in *; congruence. }

      (* assignment to generated variables *)
      eapply rule_seq.
      eapply Hbackward.
      Focus 2.
      { intros; sep_normal_in H.
        assert ((!(es1 ==t vs_of_sval v1) **
                 !(assn_of_svs seval_env svar_env (free_sv se1)) **
                 assn_of_avs (free_av se1) **
                 !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.remove x (free_sv se2)) (free_sv se1))) **
                 assn_of_avs (SA.SE.diff (free_av se2) (free_av se1))) s h).
        { repeat sep_cancel. }
        apply H0. } Unfocus.
      eapply rule_frame; [applys* read_tup_correct|].
      (* side-conditions of the assignment *)
      { intros.
        forwards* (? & ? & ?): Hfvs; substs.
        intros Hc; forwards*: Hres1; try omega. }
      { admit. }
      { forwards*: (compile_preserve se1).
        forwards*: (type_preservation se1).
        rewrites* (>>has_type_val_len). }
      { rewrites* (>>freshes_len). }
      { rewrite S.read_tup_writes; [|rewrites* (>>freshes_len)].
        Create HintDb setop.
        Hint Rewrite SE.add_spec SE.union_spec SE.remove_spec SE.diff_spec
             SA.add_spec SA.union_spec SA.remove_spec SA.diff_spec : setop.

        forwards* (? & Hvar) : (>>freshes_vars).
        prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs];
          introv; repeat autorewrite with setop;
            intros ? ? ?; forwards* (? & ? & ?): Hvar; substs.
        - forwards*: Hsvar; [repeat autorewrite with setop; eauto|].
          forwards*: (>>compile_don't_decrease Hceq1); omega.
        - forwards*: Havar; [repeat autorewrite with setop; eauto|].
          simpl in H3; rewrite S.prefix_nil in *; congruence.
        - forwards*: Hsvar; [repeat autorewrite with setop; jauto|].
          forwards*: (>>compile_don't_decrease Hceq1); omega.
        - forwards*: Havar; [repeat autorewrite with setop; jauto|].
          simpl in H3; rewrite S.prefix_nil in *; congruence. }
      
      eapply Hbackward.
      Focus 2. {
        intros s h H; sep_normal_in H.
        assert ((!(vars2es fvs1 ==t vs_of_sval v1) **
                 !(assn_of_svs seval_env svar_env (free_sv (ELet x se1 se2 ty0))) **
                 assn_of_avs (free_av (ELet x se1 se2 ty0))) s h).
        { simpl.
          unfold assn_of_svs; sep_rewrite SE.union_assns; sep_rewrite pure_star.
          unfold assn_of_avs; sep_rewrite SA.union_assns.
          rewrite !fold_assn_svs, !fold_assn_avs.
          sep_normal; repeat sep_cancel. }
        simpl in H0.

        sep_rewrite_in SE.union_comm H0.
        sep_rewrite_in SA.union_comm H0.
        unfold assn_of_svs in H0; sep_rewrite_in SE.union_assns H0.
        unfold assn_of_avs in H0; sep_rewrite_in SA.union_assns H0.
        rewrite !fold_assn_svs, !fold_assn_avs in H0.
        assert (((!(assn_of_svs (upd_opt seval_env x v1) (upd svar_env x fvs1) (free_sv se2)) **
                  assn_of_avs (free_av se2)) **
                 (!(assn_of_svs seval_env svar_env (SE.SE.diff (free_sv se1) (SE.remove x (free_sv se2)))) **
                  assn_of_avs (SA.SE.diff (free_av se1) (free_av se2)))) s h).
        { sep_normal; repeat sep_cancel.
          sep_lift 2; sep_cancel.
          sep_rewrite_in pure_star H2.
          sep_lift 1; sep_cancel.
          destruct (SE.in_dec (free_sv se2) x).
          - sep_rewrite (SE.choose_remove _ _ i).
            unfold assn_of_svs.
            sep_rewrite SE.add_equiv; [|autorewrite with setop; intros [Hc Hc']; congruence].
            unfold upd, upd_opt; destruct eq_dec; [|congruence].
            sep_rewrite pure_star; sep_rewrite pure_pure.
            sep_cancel.
            sep_rewrite SE.assn_of_vs_eq;
              [unfold assn_of_svs in *; eauto | introv; autorewrite with setop;
                                                intros [? ?]; try destruct eq_dec; try congruence..].
          - sep_rewrite (SE.remove_id (free_sv se2) x); eauto.
            unfold assn_of_svs in *; sep_rewrite SE.assn_of_vs_eq;
              [ sep_split_in H3; sep_split; eauto |
                introv; autorewrite with setop;
                unfold upd, upd_opt; case_if; intros [? ?]; eauto; congruence..]. }
        exact H1. } Unfocus.
      eapply Hforward; [eapply rule_frame; [apply Htri2|]| ].
      + prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs];
          introv; repeat autorewrite with setop; intros ? (? & ?) ?;
            forwards* (? & ? & ? & ?): Hwr2; substs.
        forwards*: Hsvar; autorewrite with setop; eauto.
        forwards*: (>>compile_don't_decrease se1); omega.
        forwards*: Havar; autorewrite with setop; eauto.
        simpl in *; rewrite prefix_nil in *; congruence.
      + intros s h H; simpl.
        sep_rewrite SE.union_comm; sep_rewrite SA.union_comm.
        unfold assn_of_svs, assn_of_avs.
        sep_rewrite SE.union_assns; sep_rewrite pure_star; 
          sep_rewrite SA.union_assns; sep_normal.
        rewrite !fold_assn_svs, !fold_assn_avs.
        repeat sep_cancel.
        apply scC; sep_cancel.
        destruct (SE.in_dec (free_sv se2) x).
        * sep_rewrite_in (SE.choose_remove _ _ i) H3.
          unfold assn_of_svs in H3.
          sep_rewrite_in SE.add_equiv H3; [|autorewrite with setop; intros [Hc Hc']; congruence].
          unfold upd, upd_opt in H3; destruct (eq_dec x x); [|congruence].
          sep_rewrite_in pure_star H3; sep_split_in H3.
          sep_split; unfold assn_of_svs; eauto.
          sep_rewrite SE.assn_of_vs_eq;
              [unfold assn_of_svs in *; eauto | introv; autorewrite with setop;
                                                intros [? ?]; try destruct eq_dec; try congruence..].
        * sep_rewrite_in (SE.remove_id _ _ n0) H3.
          unfold assn_of_svs in *;
          sep_rewrite SE.assn_of_vs_eq; eauto;
          introv; autorewrite with setop; intros [? ?]; unfold upd, upd_opt;
            destruct eq_dec; substs; eauto; congruence.
    - unfold ">>=" in Hcompile.
      destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hcompile].
      destruct es1 as [|e1 [|? ?]]; try now inverts Hcompile.
      destruct es2 as [|e2 [|? ?]]; inverts Hcompile.

      inverts Heval as Heval1 Heval2; substs.
      inverts Htyp as Htyp1 Htyp2; substs.
      forwards* (Hwr1 & Hres1 & Htri1): IHse1.
      { intros; eapply Hsvar; eauto; autorewrite with setop; eauto. }
      { intros; applys* Havar; rewrite SA.union_spec; eauto. }
      forwards* (Hwr2 & Hres2 & Htri2): IHse2.
      { intros; forwards*: Hsvar; eauto; autorewrite with setop; eauto.
        forwards*: (>>compile_don't_decrease se1); omega. }
      { intros; applys* Havar; rewrite SA.union_spec; eauto. }

      splits; try omega.
      { simpl; destruct op; simpl in *;
        [inverts H0; simpl;
         introv; rewrite !in_app_iff; intros [? | [? | []]];
         [forwards* (? & ? & ? & ?): Hwr1| forwards* (? & ? & ? & ?): Hwr2];
         do 2 eexists; splits; eauto; try omega;
         [forwards*: (>>compile_don't_decrease Hceq2); omega|
          forwards*: (>>compile_don't_decrease Hceq1); omega]..]. }
      { simpl; destruct op; simpl in *;
        [inverts H0; simpl; simplify..];
        lazymatch goal with
        | [H : context [In (Var (str_of_pnat _ _)) (fv_E e1)] |- _] =>
          forwards*: Hres1
        | [H : context [In (Var (str_of_pnat _ _)) (fv_E e2)] |- _] =>
          forwards*: Hres2
        end;
        first [forwards*: (>>compile_don't_decrease Hceq2); omega | forwards*: (>>compile_don't_decrease Hceq1); omega]. }
      eapply Hbackward.
      Focus 2.
      { unfold assn_of_svs, assn_of_avs; intros;
        sep_rewrite_in (SE.union_assns) H; sep_rewrite_in (SA.union_assns) H;
        rewrite !fold_assn_svs, !fold_assn_avs in H;
        sep_rewrite_in pure_star H; sep_normal_in H.
        assert (((!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) **
                 !(assn_of_svs seval_env svar_env (SE.SE.diff (free_sv se2) (free_sv se1))) **
                 assn_of_avs (SA.SE.diff (free_av se2) (free_av se1))) s h).
        { sep_normal; repeat sep_cancel. }
        apply H1. } Unfocus.
      assert (c = (cs1 ;; cs2 ;; fst (compile_op op e1 e2) )); [|substs].
      { destruct op; simpl in *; inverts H0; eauto. }
      eapply rule_seq; [eapply rule_frame; eauto|].
      { prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs];
        introv; repeat autorewrite with setop; intros ? (? & ?) ?;
          forwards* (? & ? & ? & ?): Hwr1; substs.
        forwards*: Hsvar; autorewrite with setop; eauto. omega.
        forwards*: Havar; autorewrite with setop; eauto.
        unfold S.var_of_str in *; simpl in *; rewrite prefix_nil in *; congruence. }
      eapply Hbackward.
      Focus 2. {
        intros s h H.
        assert ((!(e1 :: Datatypes.nil ==t vs_of_sval v1) **
                 !(assn_of_svs seval_env svar_env (SE.union (free_sv se1) (free_sv se2))) **
                 assn_of_avs (SA.union (free_av se1) (free_av se2))) s h).
        { unfold assn_of_svs, assn_of_avs;
          sep_rewrite SE.union_assns; sep_rewrite SA.union_assns;
          sep_rewrite pure_star; sep_normal; sep_normal_in H;
          rewrite !fold_assn_svs, !fold_assn_avs; repeat sep_cancel. }
        sep_rewrite_in SE.union_comm H1; sep_rewrite_in SA.union_comm H1;
          unfold assn_of_svs, assn_of_avs in H1;
          sep_rewrite_in SE.union_assns H1; sep_rewrite_in SA.union_assns H1;
            rewrite !fold_assn_svs, !fold_assn_avs in H1.
        instantiate (1 :=
         (!(assn_of_svs seval_env svar_env (free_sv se2)) ** assn_of_avs (free_av se2)) ** 
         !(e1 :: Datatypes.nil ==t vs_of_sval v1) **
         !(assn_of_svs seval_env svar_env (SE.SE.diff (free_sv se1) (free_sv se2))) **
         assn_of_avs (SA.SE.diff (free_av se1) (free_av se2))).
        sep_normal; sep_rewrite_in pure_star H1; sep_normal_in H1; repeat sep_cancel. } Unfocus.
      eapply rule_seq; [eapply rule_frame; eauto|].
      { prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs | apply inde_eq_tup; rewrite Forall_forall];
        simpl; introv; repeat autorewrite with setop; intros; simplify;
        forwards* (? & ? & ? & ?): Hwr2; substs.
        - forwards*: Hres1; omega.
        - forwards*: Hsvar; autorewrite with setop; jauto.
          forwards*: (>>compile_don't_decrease se1). omega.
        - forwards*: Havar; autorewrite with setop; jauto. 
          unfold S.var_of_str in *; simpl in *; rewrite prefix_nil in *; congruence. }
      (* TODO: modular lemma for compile_op *)
      assert (Heq: fst (compile_op op e1 e2) = Cskip); [|rewrite Heq; clear Heq ].
      { unfold compile_op; destruct op; eauto. }
      eapply Hforward; eauto using rule_skip.
      intros s h H.
      sep_rewrite SE.union_comm; sep_rewrite SA.union_comm;
        unfold assn_of_svs, assn_of_avs;
        sep_rewrite SE.union_assns; sep_rewrite SA.union_assns.
      rewrite !fold_assn_svs, !fold_assn_avs;
        sep_rewrite pure_star; sep_normal; sep_normal_in H;
          sep_split_in H; sep_split; eauto; sep_cancel.
      asserts_rewrite (es = snd (compile_op op e1 e2)).
      { destruct op; simpl in *; inverts* H0. }
      destruct op, v1, v2; simpl in *; inverts H9;
        sep_split_in HP0; sep_split_in HP1; unfold_conn_in (HP3, HP4); simpl in *;
          sep_split; eauto; unfold_conn; simpl; try congruence;
      rewrite HP3, HP4.
      destruct (Z.eqb_spec n0 n1); destruct (eq_dec n0 n1); eauto; congruence.
      destruct (Z.ltb_spec0 n0 n1); destruct (Z_lt_dec n0 n1); eauto; congruence.
    - unfold ">>=" in Hcompile.
      destruct (compile_sexp _ se _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile].
      destruct (freshes (length _) _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hcompile].
      destruct es1 as [|? [|? ?]]; inverts Hcompile.
      inverts Htyp as Htyp Hatyp; inverts Heval as Heval Haeval Hle Hgt.
      forwards* (Hwr & Hres & Htri): IHse.
      { intros; applys* Havar; autorewrite with setop; eauto. }
      assert (Hlenfv : length fvs1 = length (avar_env x)).
      { forwards*: (>>freshes_len Hfeq1); simplify; eauto. }
      splits.
      { introv; simpl; rewrite gen_read_writes.
        2: simplify; eauto.
        rewrite in_app_iff; intros [? | ?].
        - forwards* (? & ? & ? & ?): Hwr; do 2 eexists; splits*; try omega.
          forwards*: (>>freshes_vars Hfeq1); omega.
        - forwards* (? & Hgenv): (>>freshes_vars Hfeq1).
          forwards* (? & ? & ?): Hgenv.
          do 2 eexists; splits*; try omega.
          forwards*: (>>compile_don't_decrease). }
      { intros; simplify;
        forwards* (? & Hgenv): (>>freshes_vars Hfeq1); forwards* (? & ? & ?): Hgenv.
        forwards* (? & ?): (>>var_pnat_inj H1); omega. }
      eapply Hbackward.
      Focus 2. {
        intros s h H.
        unfold assn_of_svs, assn_of_avs in H.
        Hint Rewrite SE.singleton_spec SA.singleton_spec: setop.
        Lemma add_union x s :
          SA.add x s == SA.union (SA.singleton x) s.
        Proof.
          simpl; unfold SA.Equal; introv.
          autorewrite with setop; split; eauto.
        Qed.
        sep_rewrite_in add_union H; sep_rewrite_in SA.union_comm H.
        sep_rewrite_in SA.union_assns H.
        rewrite !fold_assn_svs, !fold_assn_avs in H.
        instantiate (1 :=
          (!(assn_of_svs seval_env svar_env (free_sv se)) **  assn_of_avs (free_av se)) **
            assn_of_avs (SA.SE.diff (SA.singleton x) (free_av se))).
        sep_normal; sep_normal_in H; repeat sep_cancel. } Unfocus.
      eapply rule_seq; [eapply rule_frame; eauto|].
      { prove_inde; apply inde_assn_of_avs; unfold not; intros.
        forwards* (? & ? & ? & ?) : Hwr; substs.
        forwards*: Havar; autorewrite with setop in *; jauto.
        simpl in *; rewrite prefix_nil in *; congruence. }
      eapply Hbackward.
      Focus 2.
      { intros s h H.
        sep_normal_in H; sep_split_in H; simpl in *.
        sep_split_in HP0.
        assert (assn_of_avs (SA.add x (SA.remove x (free_av se))) s h).
        { Lemma add_remove x s :
            SA.add x (SA.remove x s) == SA.add x s.
          Proof.
            simpl; unfold SA.Equal; introv; autorewrite with setop; split;
              intros.
            - destruct H as [? | [? ?]]; eauto.
            - destruct (eq_dec a x); eauto.
              destruct H; eauto.
          Qed.
          sep_rewrite add_remove; sep_rewrite add_union; sep_rewrite SA.union_comm.
          unfold assn_of_avs; sep_rewrite SA.union_assns.
          apply H. }
        unfold assn_of_avs in H0;
          sep_rewrite_in SA.add_equiv H0; [|autorewrite with setop; intros [? ?]; congruence].
        rewrite Haeval in H0.
        sep_rewrite_in (is_array_tup_unfold (S.es2gls (S.vars2es (avar_env x))) (Z.to_nat ix)) H0.
        Focus 2. {
          simpl; intros; unfold S.es2gls; simplify.
          forwards* Htyv: (>> Haectx (VZ 0) i).
          unfold val in *; rewrites* (>>has_type_val_len Htyv).
          rewrites* (>>Havctx). } Unfocus.
        2: zify; rewrite Z2Nat.id; omega.
        simpl in H0.
        assert ((Zn (Z.to_nat ix) === e) s (emp_ph loc)).
        { unfold_conn_in HP1; unfold_conn; simpl in *; rewrite Z2Nat.id; eauto. }
        sep_rewrite_in S.mps_eq1_tup' H0; [|exact H1].
        clear HP0; sep_combine_in H0; sep_normal_in H0.
        sep_lift_in H0 1.
        apply H0. } Unfocus.
      eapply Hforward; [eapply rule_frame; [apply S.gen_read_correct|]; eauto|].
      { simpl; intros.
        forwards* (? & Hgvars): (>>freshes_vars Hfeq1).
        forwards* (? & ? & ?): Hgvars; substs.
        simplify; eauto.
        forwards*: Hres; omega. }
      { unfold not; intros; simplify.
        forwards* (? & Hgvars): (>>freshes_vars Hfeq1).
        forwards* (? & ? & ?): Hgvars; substs.
        forwards*: Havar; autorewrite with setop; eauto.
        simpl in *; rewrite prefix_nil in *; congruence. }
      { admit. }
      { simplify; eauto. }
      { simpl; intros; unfold S.es2gls; simplify.
        forwards* Htyv: (>> Haectx (VZ 0) (Z.to_nat ix)).
        zify; rewrite Z2Nat.id; omega.
        unfold val in *; rewrites* (>>has_type_val_len Htyv).
        unfold val in *; forwards*: Havctx.
        congruence. }
      { rewrites* S.gen_read_writes; [|simplify; eauto].
        unfold S.es2gls; forwards* (? & Hgvars): (>>freshes_vars Hfeq1).
        prove_inde; simplify; eauto;
          try (apply inde_assn_of_svs; unfold not; intros);
          try (apply inde_assn_of_avs; unfold not; intros);
          forwards* (? & ? & ?): Hgvars; substs;
          try now (lazymatch goal with
                   | [H : In _ (avar_env _) |- _] =>
                     forwards*: (Havar); autorewrite with setop; eauto;
                     simpl in *; rewrite prefix_nil in *; congruence
                   | [H : In _ (fv_E e) |- _ ] =>
                     forwards*: Hres; autorewrite with setop; eauto; omega 
                   end).
        forwards*: Hsvar.
        forwards*: (>>compile_don't_decrease Hceq1); omega.
        forwards*: Havar; autorewrite with setop in *; jauto.
        simpl in *; rewrite prefix_nil in *; congruence. }
      intros; sep_normal_in H; sep_split_in H; sep_split; eauto.
      sep_rewrite_r add_remove.
      unfold assn_of_avs; sep_rewrite SA.add_equiv; [|autorewrite with setop; intros [? ?]; congruence].
      rewrite Haeval.
      apply scC; sep_cancel.
      sep_rewrite (is_array_tup_unfold (S.es2gls (S.vars2es (avar_env x))) (Z.to_nat ix)).
      Focus 2. {
        simpl; intros; unfold S.es2gls; simplify.
        forwards* Htyv: (>> Haectx (VZ 0) i).
        unfold val in *; rewrites* (>>has_type_val_len Htyv).
        rewrites* (>>Havctx). } Unfocus.
      2: zify; rewrite Z2Nat.id; omega.
      unfold S.es2gls in *; simpl.
      assert ((Zn (Z.to_nat ix) === e) s (emp_ph loc)).
      { unfold_conn_in HP1; unfold_conn; simpl in *; rewrite Z2Nat.id; eauto. }
      sep_rewrite S.mps_eq1_tup'; [|exact H1].
      sep_normal; repeat sep_cancel. 
    - admit.
    - admit.
    - admit.
  Qed.