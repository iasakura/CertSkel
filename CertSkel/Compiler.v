Require Import String.
Require Import Vector.
Require Import DepList.
Require Import MyList.
Require Import ZArith.
Require Import GPUCSL.
Require Import LibTactics.
Require Import Psatz.
Require Import Monad.
Require Import MyEnv.
Require Import TypedTerm.
Require Import MyMSets.
Require Import CUDALib.

Open Scope string_scope.
Definition name := string. 

Require GPUCSL.
Module G := GPUCSL.
(* Require Skel_lemma. *)
(* Module S := Skel_lemma. *)

Section codegen.
  Definition M a := nat -> (a * nat).

  Definition bind_opt A B (e : M A) (f : A -> M B) : M B:=
    fun n => let (v, n') := e n in f v n'.

  Definition get : M nat := fun n => (n, n).
  Definition set n : M unit := fun _ => (tt, n).
End codegen.

Instance M_monad : Monad M := {ret := fun _ x n => (x, n);
                               bind := bind_opt}.

Module Sx := Syntax.

Section compiler.
  (* environment of variables of array in the generated code *)
  (* Variable avarenv : Env nat (var * list var) _. *)

  Fixpoint string_of_ty ty : string :=
    match ty with
    | Skel.TBool => "Bool"
    | Skel.TZ => "Z"
    | Skel.TTup t1 t2 => "(" ++ string_of_ty t1 ++ ", " ++ string_of_ty t2 ++ ")"
    end%string.

  Fixpoint len_of_ty ty : nat :=
    match ty with
    | Skel.TBool | Skel.TZ => 1
    | Skel.TTup t1 t2 => len_of_ty t1 + len_of_ty t2
    end.
  
  Definition len_until_i tys i : nat :=
    fold_right (fun ty n => len_of_ty ty + n) 0 (firstn i tys).
  
  Definition len_at_i (tys : list Skel.Typ) i : nat :=
    len_of_ty (nth i tys Skel.TZ).
  
  Import Lang.
  Open Scope string_scope.

  Definition str_of_pnat n m :=
    ("l" ++ nat2str n ++ "_" ++ nat2str m).

  Definition lpref n := "l" ++ nat2str n ++ "_". 

  Definition freshes ty : M (vars ty) :=
    get >>= fun n =>
    set (n + 1) >>= fun _ =>
    ret (locals (lpref n) ty 0).

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
    ~str_in (nat2str n) (char_of_string "_").
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
    forwards*: (sep_var_inj (nat2str n) (nat2str n')); simpl; eauto using nat_to_str_underbar.
    split; apply nat_to_string_inj; auto.
    cut (String "_" (nat2str m) = String "_" (nat2str m')); [intros H'; inversion H'; auto|].
    eapply string_inj2; eauto.
  Qed.

  Definition compile_op {t1 t2 t3 : Skel.Typ} (op : Skel.BinOp t1 t2 t3)  :=
    match op in Skel.BinOp t1 t2 t3 return vars t1 -> vars t2 -> M (cmd * vars t3) with
    | Skel.Eplus =>
      fun e1 e2 => do! x := freshes Skel.TZ in ret (assigns x (ty2ctys _) (e1 +C e2), x)
    | Skel.Emult =>
      fun e1 e2 => do! x := freshes Skel.TZ in ret (assigns x (ty2ctys _) (e1 *C e2), x)
    | Skel.Emin =>
      fun e1 e2 => do! x := freshes Skel.TZ in ret (assigns x (ty2ctys _) (Emin e1 e2), x)
    | Skel.BEq =>
      fun e1 e2 => do! x := freshes Skel.TBool in ret (assigns x (ty2ctys _) (Eeq e1 e2), x)
    | Skel.Blt => 
      fun e1 e2 => do! x := freshes Skel.TBool in ret (assigns x (ty2ctys _) (Elt e1 e2), x)
    end.

  Fixpoint ctyps_of_typ (ty : Skel.Typ) :=
    match ty with
    | Skel.TBool => Int :: nil
    | Skel.TZ => Int :: nil
    | Skel.TTup t1 t2 => (ctyps_of_typ t1 ++ ctyps_of_typ t2)%list
    end.
  
  Fixpoint nat_of_member {GS : list Skel.Typ} {ty : Skel.Typ}  (mem : member ty GS) : nat :=
    match mem with
    | HFirst _ => 0
    | HNext _ _ m => S (nat_of_member m)
    end.

  Definition get_env {T : Type} {GS : list Skel.Typ} {ty : Skel.Typ}
             (env : list T) (mem : member ty GS) (d : T) : T :=
    List.nth (nat_of_member mem) env d.

  Definition get_env_opt {T : Type} {GS : list Skel.Typ} {ty : Skel.Typ}
             (env : list T) (mem : member ty GS) (d : T) : option T :=
    nth_error env (nat_of_member mem).

  (* compiler of scalar expressions *)
  Fixpoint compile_sexp {GA GS : list Skel.Typ} {typ : Skel.Typ}
           (se : Skel.SExp GA GS typ) : 
    hlist (fun ty => var * vars ty)%type GA ->
    hlist (fun ty => vars ty) GS -> M (cmd * vars typ) :=
    match se with
    | Skel.EVar _ _ ty v => fun avenv env => 
      do! x := freshes ty in 
      ret (assigns x (ty2ctys _) (v2e (hget env v)), x)
    | Skel.ENum _ _ z => fun avenv env => do! x := freshes Skel.TZ in ret (assigns x (ty2ctys _) (Enum z), x)
    | Skel.ELet _ _ t1 t2 e1 e2 => fun avenv env =>
      compile_sexp e1 avenv env >>= fun ces1 => 
      let (c1, es1) := ces1 in
      (* let dim := length es1 in *)
      freshes t1 >>= fun xs =>
      compile_sexp e2 avenv  (HCons xs env) >>= fun ces2 => 
      let (c2, es2) := ces2 in
      ret (c1 ;; assigns xs (ty2ctys t1) (v2e es1) ;; c2, es2)
    | Skel.EBin _ _ _ _ _ op e1 e2 => fun avenv env =>
      compile_sexp e1 avenv env >>= fun ces1 =>
      let (c1, e1) := ces1 in
      compile_sexp e2 avenv env >>= fun ces2 =>
      let (c2, e2) := ces2 in
      do! ces := compile_op op e1 e2 in
      let (c, es) := ces in
      ret (c1;; c2;; c, es)
    | Skel.EA _ _ typ va e => fun avenv env =>
      compile_sexp e avenv env >>= fun ces =>
      let (c, i) := ces in
      let (_, aname) := hget avenv va in
      freshes typ >>= fun xs =>
      ret (c ;; reads xs (ty2ctys typ) (v2gl aname +os i), xs)
    | Skel.ELen _ _ _ xa => fun avenv env =>
      do! x := freshes Skel.TZ in
      let (l, _) := hget avenv xa in 
      ret (assigns x (ty2ctys _) l, x)
    | Skel.EPrj1 _ _ t1 t2 e => fun avenv env =>
      compile_sexp e avenv env >>= fun ces =>
      let (c, es) := ces in
      ret (c, fst es)
    | Skel.EPrj2 _ _ t1 t2 e => fun avenv env =>
      let off := len_of_ty t1 in
      let l := len_of_ty t2 in
      (* ugly copy and paste !*)
      compile_sexp e avenv env >>= fun ces =>
      let (c, es) := ces in
      ret (c, snd es)
    | Skel.ECons _ _ t1 t2 e1 e2 => fun avenv env =>
      compile_sexp e1 avenv env >>= fun ces =>
      let (c1, ge1) := ces in
      compile_sexp e2 avenv env >>= fun ces =>
      let (c2, ge2) := ces in
      ret (c1 ;; c2, (ge1, ge2))
    | Skel.EIf _ _ ty e1 e2 e3 => fun avenv env =>
      compile_sexp e1 avenv env >>= fun ces1 => 
      let (c1, e1) := ces1 in
      compile_sexp e2 avenv env >>= fun ces2 =>
      let (c2, e2) := ces2 in
      compile_sexp e3 avenv env >>= fun ces3 =>
      let (c3, e3) := ces3 in
      freshes ty >>= fun xs =>
      ret (c1;; Cif (Bnot (Beq e1 0%Z)) (c2 ;; assigns xs (ty2ctys ty) (v2e e2)) (c3 ;; assigns xs (ty2ctys ty) (v2e e3)), xs)
    end%list.
End compiler.

Section TestCompiler.
  Import Skel.

  Arguments EVar {GA GS t} _.
  Arguments ELet {GA GS t1 t2} _ _.
  Arguments EBin {GA GS t1 t2 t3} _ _ _.
  Arguments EA {GA GS t} _ _.
  Arguments EPrj1 {GA GS t1 t2} _.
  Arguments EPrj2 {GA GS t1 t2} _.
  Arguments ECons {GA GS t1 t2} _ _.
  Arguments EIf {GA GS t} _ _ _.
  Arguments ENum {GA GS} _.
  
  Open Scope string_scope.

  Definition test1 : Skel.SExp nil nil (TTup TZ TZ) :=
    ELet (ECons (ENum 1%Z) (ENum 2%Z)) (
    ELet (ECons (ENum 3%Z) (ENum 4%Z)) (
    ELet (ECons (EVar HFirst) (EVar (HNext HFirst))) (
    EPrj1 (EVar HFirst)))).
  
  Eval cbv in (compile_sexp test1 HNil HNil 0).
  
End TestCompiler.

(* TODO: use actual impl. of skeletons *)
(* Require Import pmap_skel. *)
(* Require Import Reduce_opt_skel. *)
Import scan_lib.

(* Module VarE_eq : DecType with Definition t := varE with Definition eq_dec := eq_dec. *)
(*   Definition t := varE. *)
(*   Definition eq (x y : t) := x = y. *)
(*   Definition eq_equiv : Equivalence eq. *)
(*   Proof. *)
(*     split; cbv; intros; congruence. *)
(*   Qed. *)
(*   Definition eq_dec := eq_dec. *)
(* End VarE_eq. *)

(* Module VarA_eq : DecType with Definition t := varA with Definition eq_dec := @eq_dec varA _. *)
(*   Definition t := varA. *)
(*   Definition eq (x y : t) := x = y. *)
(*   Definition eq_equiv : Equivalence eq. *)
(*   Proof. *)
(*     split; cbv; intros; congruence.  *)
(*   Qed. *)
(*   Definition eq_dec := @eq_dec t _. *)
(* End VarA_eq. *)

(* Instance eq_type_pair A B `{eq_type A} `{eq_type B} : eq_type (A * B) := { *)
(*   eq_dec := _ *)
(* }. *)
(* Proof. *)
(*   intros; destruct H, H0; repeat decide equality. *)
(* Qed. *)

(* Instance eq_type_STyp : eq_type Sx.Typ := { *)
(*   eq_dec := Sx.STyp_eq_dec *)
(* }. *)

(* Module VarATy_eq : DecType with Definition t := (varA * Sx.Typ)%type with Definition eq_dec := @eq_dec (varA * Sx.Typ) _. *)
(*   Definition t := (varA * Sx.Typ)%type. *)
(*   Definition eq (x y : t) := x = y. *)
(*   Definition eq_equiv : Equivalence eq. *)
(*   Proof. *)
(*     split; cbv; intros; congruence.  *)
(*   Qed. *)
(*   Definition eq_dec := @eq_dec t _. *)
(* End VarATy_eq. *)

(* Module SA := MSets VarA_eq. *)
(* Module SATy := MSets VarATy_eq. *)
(* Module SE := MSets VarE_eq. *)

Instance eq_type_nat : eq_type nat := {eq_dec := eq_nat_dec}.

Module Nat_eq : DecType with Definition t := nat with Definition eq_dec := eq_dec.
  Definition t := nat.
  Definition eq (x y : t) := x = y.
  Definition eq_equiv : Equivalence eq.
  Proof.
    split; cbv; intros; congruence.
  Qed.
  Definition eq_dec := @eq_dec t _.
End Nat_eq.
Module NatSet := MSets Nat_eq.

Require Import Host.
(* Instance CUDA_monad : Monad CUDA := {| ret := @ret; bind := bind |}. *)

Section Compiler.
  (* Fixpoint free_sv {GA GS ty} (e : Skel.SExp GA GS ty) : NatSet.t := *)
  (*   match e with *)
  (*   | Skel.EVar _ _ _ v => NatSet.singleton (nat_of_member v) *)
  (*   | Skel.ENum _ _ _ => NatSet.empty *)
  (*   | Skel.ELet _ _ _ e1 e2 => *)
  (*     NatSet.union (free_sv e1) (NatSet.remove (nat_of_member x) (free_sv e2)) *)
  (*   | Skel.EBin _ _ _ _ _ _ e1 e2 => NatSet.union (free_sv e1) (free_sv e2) *)
  (*   | Skel.EA _ _ _ _ e => free_sv e *)
  (*   | Skel.ELen _ _ _ _ => NatSet.empty *)
  (*   | Skel.EPrj1 _ _ _ _ e => free_sv e *)
  (*   | Skel.EPrj2 _ _ _ _ e => free_sv e *)
  (*   | Skel.ECons _ _ _ _ e1 e2 => NatSet.union (free_sv e1) (free_sv e2) *)
  (*   | Skel.EIf _ _ _  e e' e'' => NatSet.union (free_sv e) (NatSet.union (free_sv e') (free_sv e'')) *)
  (*   end. *)

  Fixpoint free_av {GA GS ty} (e : Skel.SExp GA GS ty) : NatSet.t :=
    match e with
    | Skel.EVar _ _ _ _ => NatSet.empty
    | Skel.ENum _ _ _ => NatSet.empty
    | Skel.ELet _ _ _ _ e1 e2 =>
      NatSet.union (free_av e1) (free_av e2)
    | Skel.EBin _ _ _ _ _ _ e1 e2 => NatSet.union (free_av e1) (free_av e2)
    | Skel.EA _ _ _ x e => NatSet.add (nat_of_member x) (free_av e)
    | Skel.ELen _ _ _ x => NatSet.singleton (nat_of_member x)
    | Skel.EPrj1 _ _ _ _ e => free_av e
    | Skel.EPrj2 _ _ _ _ e => free_av e
    | Skel.ECons _ _ _ _  e1 e2 => NatSet.union (free_av e1) (free_av e2)
    | Skel.EIf _ _ _  e e' e'' => NatSet.union (free_av e) (NatSet.union (free_av e') (free_av e''))
    end.

  Definition free_av_func {GA fty} (f : Skel.Func GA fty) :=
    match f with
    | Skel.F1 _ _ _ body => free_av body
    | Skel.F2 _ _ _ _ body => free_av body
    end.

  Fixpoint free_av_lexp {GA ty} (e : Skel.LExp GA ty) : NatSet.t :=
    match e with
    | Skel.LNum _ _ => NatSet.empty
    | Skel.LLen _ _ x => NatSet.singleton (nat_of_member x)
    | Skel.LMin _ le1 le2 => NatSet.union (free_av_lexp le1) (free_av_lexp le2) 
    end.

  Definition free_av_AE {GA ty} (ae : Skel.AE GA ty) :=
    match ae with
    | Skel.DArr _ _ f len =>
      NatSet.union (free_av_func f) (free_av_lexp len)
    | Skel.VArr _ _ xa => NatSet.singleton (nat_of_member xa)
    end.

  Fixpoint map_opt {A B : Type} (f : A -> option B) (xs : list A) : option (list B) :=
    sequence (map f xs).

  Definition opt_def {A : Type} (o : option A) d :=
    match o with
    | Some x => x
    | None => d
    end.

  (* Definition idxEnv_of_sa (xas : SA.t) : Env varA nat _ := *)
  (*   snd (SA.fold (fun xa (n_aenv : nat * Env varA nat _)  => *)
  (*              let (n, aenv) := n_aenv in *)
  (*              (n + 1, upd aenv xa n)) xas (0, emp_def 0)). *)

  Fixpoint arr_params pref ty i := 
    match ty return vartys ty with
    | Skel.TBool => (Var (pref ++ nat2str i), Ptr Bool)
    | Skel.TZ => (Var (pref ++ nat2str i), Ptr Int)
    | Skel.TTup t1 t2 => (arr_params pref t1 i, arr_params pref t2 (nleaf t1 + i))
    end.

  Definition arr_name n (ty : Skel.Typ) :=
    arr_params ("arrIn" ++ nat2str n) ty 0.

  Definition len_name n := Var (name_of_len (grpOfInt n)).
  Definition out_name (ty : Skel.Typ) :=
    arr_params "arrOut" ty 0.
  Definition out_len_name := Var (name_of_len "Out").

  (* Definition env_of_sa (aty_env : Env varA (option Sx.Typ) _)  (xas : SA.t) : *)
  (*   (Env varA (var * list (var * CTyp)) _) := *)
  (*   let idxEnv := idxEnv_of_sa xas in *)
  (*   fun xa => *)
  (*     let ctys := (ctyps_of_typ (opt_def (aty_env xa) Sx.TZ)) in *)
  (*     (len_name (idxEnv xa), arr_name (idxEnv xa) ctys). *)

  Definition zipWith {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B) :=
    map (fun xy => f (fst xy) (snd xy)) (combine xs ys).

  Fixpoint type_of_func (n : nat) :=
    match n with
    | O => (cmd * list exp)%type
    | S n => list var -> type_of_func n
    end.

  Definition evalM {a : Type} (m : M a) (n : nat) : a :=
    match m n with
    | (x, _) => x
    end.

  Fixpoint dumy_fun_n n x :=
    match n return type_of_func n with
    | O => x
    | S n => fun y => dumy_fun_n n x
    end.

  Definition type_of_ftyp (fty : Skel.FTyp) :=
    match fty with
    | Skel.Fun1 dom cod => vars dom -> (cmd * vars cod)
    | Skel.Fun2 dom1 dom2 cod => vars dom1 -> vars dom2 -> (cmd * vars cod)
    end.

  Definition compile_func {GA fty} (body : Skel.Func GA fty) :
    hlist (fun ty => (var * vars ty))%type GA ->
    type_of_ftyp fty :=
    match body in Skel.Func _ fty' return _ -> type_of_ftyp fty' with
    | Skel.F1 _ _ _ body => fun av xs => evalM (compile_sexp body av (HCons xs HNil)) 0
    | Skel.F2 _ _ _ _ body => fun av xs ys => evalM (compile_sexp body av (HCons ys (HCons xs HNil))) 0
    end.

  Fixpoint compile_lexp {GA ty} (aenv : list (hostVar * list hostVar)) (le : Skel.LExp GA ty) : expr :=
    match le with
    | Skel.LNum _ n => Const n
    | Skel.LLen _ _ a => VarE (fst (get_env aenv a (0, nil)))
    | Skel.LMin _ e1 e2 => Min (compile_lexp aenv e1) (compile_lexp aenv e2) 
    end.

  Definition accessor_of_array {GA tyxa} aenv (arr : member tyxa GA) x :=
    compile_func (Skel.F1 _ Skel.TZ _ (Skel.EA _ _ _ arr (Skel.EVar _ _ _ HFirst))) aenv x.

  Definition compile_AE {GA ty} (ae : Skel.AE GA ty) :
    hlist (fun ty => (var * vars ty))%type GA ->
    ((var -> (cmd * vars ty))) :=
    match ae with
    | Skel.DArr _ _ f len => fun avar_env =>
      let f' := compile_func f avar_env in
      fun x => f' x
    | Skel.VArr _ _ xa => fun avar_env =>
      let get := accessor_of_array avar_env xa in
      get
    end.

  Definition compile_AE_len {GA ty}
    (var_ptr_env : list (hostVar * list hostVar)) (ae : Skel.AE GA ty) : expr :=
    match ae with
    | Skel.DArr _ _ f len =>
      let len' := compile_lexp var_ptr_env len in
      len'
    | Skel.VArr _ _ xa => 
      (VarE (fst (get_env var_ptr_env xa (0, nil))))
    end.

  (* Definition Z_of_val (v : SVal) := *)
  (*   match v with *)
  (*   | VB _ | VTup _ => 0%Z *)
  (*   | VZ n => n *)
  (*   end. *)
  
  Open Scope string_scope.

  Fixpoint concat {A : Type} (l : list (list A)) :=
    match l with
    | nil => nil
    | xs :: xss => (xs ++ concat xss)%list
    end.

  (* Definition shiftn n (var_host_env : list (hostVar * list hostVar)) := *)
  (*   map (fun xs => (n + (fst xs), List.map (fun x => n + x) (snd xs))) var_host_env. *)

  Instance eq_kerID : eq_type kerID := {
    eq_dec := Nat.eq_dec
  }.

  (* Eval compute in accessor_of_array (emp_def (Var "len", Var "a" :: nil)) (VarA "a") Sx.TZ (Var "i" :: nil). *)

  Fixpoint alloc_tup_arr v n len :=
    match n with
    | O => nil
    | S n => alloc v len :: alloc_tup_arr (S v) n len
    end.

  (* TODO: should be moved to Monad.v *)
  Definition state s a := s -> (a * s).
  Instance state_Monad s : Monad (state s) := {
     ret A x := fun n => (x, n);
     bind A B x f := fun n => let (y, n) := x n in f y n
  }.
  Definition getS {s} : state s s := fun x => (x, x).
  Definition setS {s} x : state s unit := fun _ => (tt, x).

  Open Scope list_scope.

  Definition CUDAM := state (nat * (list instr * list kernel)).
  Definition fresh : CUDAM hostVar := 
    do! st := getS in
    let (n, x) := st : (nat * _) in
    do! _ := setS (S n, x) in
    ret n.

  Definition setI (i : instr) : CUDAM unit :=
    do! st := getS in
    let '(n, (is_, kers)) := st in
    setS (n, (is_ ++ (i :: nil), kers)).

  Definition fLet e : CUDAM hostVar :=
    do! x := fresh in
    do! _ := setI (iLet x e) in
    ret x.

  Definition fAlloc e : CUDAM hostVar :=
    do! x := fresh in
    do! _ := setI (alloc x e) in
    ret x.

  Definition gen_kernel ker : CUDAM kerID :=
    do! x := getS in
    let '(n, (is_, kers)) := x in
    let newID := length kers in
    do! _ := setS (n, (is_, kers ++ (ker :: nil))) in
    ret newID.

  Definition mapM {B A M} `{Monad M} (f : A -> M B) (xs : list A) : M (list B) :=
    sequence (map f xs).

  Definition fAllocs (ctys : list CTyp) e : CUDAM (list hostVar) :=
    mapM (fun cty => fAlloc e) ctys.

  Definition getLen {GA typ} (x : member typ GA) (env : list (hostVar * list hostVar)) : Host.expr :=
    Host.VarE (fst (get_env env x (0, nil))).

  Fixpoint with_idx' {A : Type} {B : A -> Type} {ls : list A}
           (start : nat) (xs : hlist B ls) : hlist (fun x => nat * B x)%type ls :=
    match xs with
    | HNil => HNil
    | HCons _ _ x xs => 
      (start, x) ::: with_idx' (S start) xs
    end.

  Definition with_idx A B ls := @with_idx' A B ls 0.

  Fixpoint hmake_idx {A : Type} {B : A -> Type} (s : nat) (f : nat -> forall x : A, B x) (ls : list A) : hlist B ls :=
    match ls with
    | Datatypes.nil => HNil
    | x :: ls' => f s x ::: hmake_idx (S s) f ls'
    end.

  Definition gen_params (GA : list Skel.Typ) : hlist (fun ty => var * CTyp * vartys ty)%type GA :=
    let f (i : nat) (ty : Skel.Typ) :=
        (len_name i, Int, arr_name i ty) in
    hmake_idx 0 f GA.

  Definition remove_typeinfo : forall {GA : list Skel.Typ},
    hlist (fun ty => var * CTyp * vartys ty)%type GA ->
    hlist (fun ty => var * vars ty)%type GA :=
    hmap (fun ty (x : var * CTyp * vartys ty) => let (len, arr) := x in (fst len, maptys fst arr)).

  Definition invokeKernel kerID ntrd nblk (args : list Host.expr) :=
    setI (invoke kerID ntrd nblk args).

  (* Definition collect_args (host_var_env : list (hostVar * list hostVar)) (GA : list Skel.CTyp) := *)
  (*   let f i := *)
  (*       let (len, arrs) := nth i host_var_env (0, nil) in *)
  (*       (len :: arrs) in *)
  (*   concat (List.map f fv). *)

  Definition filter_idx {T : Type} (xs : list T) s : list T :=
    let f (x : nat * T) :=
        let (i, x) := x in
        NatSet.mem i s in
    map snd (filter f (combine (seq 0 (length xs)) xs)).

  Definition flatten_param {A : Type} (x : (A * list A)) := fst x :: snd x.
  Definition flatten_params {A : Type} (xs : list (A * list A)) := concat (List.map flatten_param xs).

  Fixpoint flatten_avars {GA : list Skel.Typ}
             (xs : hlist (fun ty => (var * CTyp * vartys ty)%type) GA) :=
    match xs with
    | HNil => nil
    | HCons _ _ x xs => 
      let '(x, ty, ls) := x in
      ((x, ty) :: flatTup ls) ++ flatten_avars xs
    end.

  Parameter mkMap' :
    forall dom cod,
      nat
      -> nat
      -> (var -> cmd * vars dom)
      -> (vars dom -> cmd * vars cod)
      -> cmd.

  Definition mkMap GA dom cod ntrd nblk
             (g : var -> cmd * vars dom)
             (f : vars dom -> cmd * vars cod)
             : kernel :=
    let arr_vars := gen_params GA in
    let params_in := flatten_avars arr_vars in
    let params_out := (out_len_name, Int) :: flatTup (out_name cod) in
    {| params_of := params_out ++ params_in;
       body_of := Pr nil (mkMap' _ _ ntrd nblk g f) |} .

  Definition compile_map {GA dom cod} ntrd nblk
             (host_var_env : list (hostVar * list hostVar))
             (f : Skel.Func GA (Skel.Fun1 dom cod))
             (arr : Skel.AE GA dom)
    : CUDAM (hostVar * list hostVar) :=
    let fvs := NatSet.union (free_av_func f) (free_av_AE arr) in
    
    let arr_vars := gen_params GA in

    let g := compile_AE arr (remove_typeinfo arr_vars) in
    let outlen := compile_AE_len host_var_env arr in
    let f := compile_func f (remove_typeinfo arr_vars) in
    
    do! kerID := gen_kernel (mkMap GA dom cod ntrd nblk g f)  in
    do! outlenVar := fLet outlen in
    let outDim := ctyps_of_typ cod in
    do! outArr := fAllocs outDim outlen in
    let args_in := concat (List.map (fun x => (fst x :: snd x)) (filter_idx host_var_env fvs)) in
    let args_out := outlenVar :: outArr in
    do! t := invokeKernel kerID ntrd nblk (List.map VarE (args_out ++ args_in)) in
    ret (outlenVar, outArr).

  Fixpoint shift_sexp_GA {GA GE typ}
    (newTy : Skel.Typ) (e : Skel.SExp GA GE typ) : Skel.SExp (newTy :: GA) GE typ :=
    match e with
    | Skel.EVar _ _ _ m => Skel.EVar _ _ _ m
    | Skel.ENum _ _ n => Skel.ENum _ _ n
    | Skel.EBin _ _ _ _ _ op e1 e2 => Skel.EBin _ _ _ _ _ op (shift_sexp_GA newTy e1) (shift_sexp_GA newTy e2)
    | Skel.EA _ _ _ m i => Skel.EA _ _ _ (HNext m) (shift_sexp_GA newTy i)
    | Skel.ELen _ _ _ m => Skel.ELen _ _ _ (HNext m)
    | Skel.EIf _ _ _ b th el => Skel.EIf _ _ _ (shift_sexp_GA newTy b) (shift_sexp_GA newTy th) (shift_sexp_GA newTy el)
    | Skel.ECons _ _ _ _ e1 e2 => Skel.ECons _ _ _ _ (shift_sexp_GA newTy e1) (shift_sexp_GA newTy e2)
    | Skel.EPrj1 _ _ _ _ e => Skel.EPrj1 _ _ _ _ (shift_sexp_GA newTy e)
    | Skel.EPrj2 _ _ _ _ e => Skel.EPrj2 _ _ _ _ (shift_sexp_GA newTy e)
    | Skel.ELet _ _ _ _ e e' => Skel.ELet _ _ _ _ (shift_sexp_GA newTy e) (shift_sexp_GA newTy e')
    end.

  Definition shift_func_GA {GA fty}
    (newTy : Skel.Typ) (f : Skel.Func GA fty) : Skel.Func (newTy :: GA) fty :=
    match f with
    | Skel.F1 _ _ _ body => Skel.F1 _ _ _ (shift_sexp_GA newTy body)
    | Skel.F2 _ _ _ _ body => Skel.F2 _ _ _ _ (shift_sexp_GA newTy body)
    end.

  Parameter mkFoldAll' : forall typ,
      nat
      -> nat
      -> nat (* # of unrolling *)
      -> (var -> (cmd * vars typ))
      -> (vars typ -> vars typ -> cmd * vars typ)
      -> cmd.

  Fixpoint addTyp {ty} :=
    match ty return vars ty -> vartys ty with 
    | Skel.TBool => fun x => (x, Bool)
    | Skel.TZ => fun x => (x, Int)
    | Skel.TTup t1 t2 => fun xs => (addTyp (fst xs), addTyp (snd xs))
    end.

  Definition sh_decl len typ :=
    flatTup (
        maptys (fun sv => SD (fst sv) (snd sv) len)
               (addTyp (locals "sdata" typ 0))).

  Definition mkFoldAll GA typ ntrd nblk g f : kernel :=
    let arr_vars := gen_params GA in
    let params_in := flatten_avars arr_vars in
    let params_out := (out_len_name, Int) :: flatTup (out_name typ) in
    {| params_of := params_out ++ params_in;
       body_of := Pr (sh_decl ntrd typ)
                     (mkFoldAll' typ ntrd nblk (S (log2 ntrd)) g f) |}.

  Definition compile_reduce {GA typ} ntrd nblk
             (host_var_env : list (hostVar * list hostVar))
             (f : Skel.Func GA (Skel.Fun2 typ typ typ))
             (arr : Skel.AE GA typ) : CUDAM (hostVar * list hostVar) :=
    let fvs_f := free_av_func f in
    let fvs := NatSet.union fvs_f (free_av_AE arr) in
    let dim := ctyps_of_typ typ in
    
    let arr_vars := gen_params GA in

    let get := compile_AE arr (remove_typeinfo arr_vars) in
    let outlen := compile_AE_len host_var_env arr in
    let func := compile_func f (remove_typeinfo arr_vars) in
    
    do! kerID1 := gen_kernel (mkFoldAll GA typ ntrd nblk get func) in
    do! lenVar := fLet outlen in
    do! tempArr := fAllocs dim (Const (Z.of_nat nblk)) in
    let args_in := concat (List.map (fun x => (fst x :: snd x)) host_var_env) in
    let args_out := lenVar :: tempArr in
    do! t := invokeKernel kerID1 ntrd nblk (List.map VarE (args_out ++ args_in)) in

    let GA := typ :: GA in
    let arr_vars := gen_params GA in
    (* let params_temp := *)
    (*   let grp := NatSet.cardinal fvs_f in *)
    (*   ((len_name grp, Int), (arr_name grp dim)) in *)
    let get := @accessor_of_array GA typ (remove_typeinfo arr_vars) HFirst in
    let func := compile_func (shift_func_GA typ f) (remove_typeinfo arr_vars) in
    do! kerID2 := gen_kernel (mkFoldAll GA typ nblk 1 get func) in
    (* (Nat.min ((l + ntrd - 1) / ntrd) nblk ) *)
    do! lenVar := fLet (Min (Div (Add outlen (Const (Z.of_nat ntrd - 1)%Z)) (Const (Z.of_nat ntrd)))
                            (Const (Z.of_nat nblk))) in
    (* do! lenVar := fLet (Const (Z.of_nat nblk)) in *)
    do! outlenVar := fLet (Const 1) in
    do! outArr := fAllocs dim (Const 1%Z) in
    let args_temp := lenVar :: tempArr in
    let args_in := concat (List.map (fun x => (fst x :: snd x)) host_var_env) in
    let args_out := lenVar :: outArr in
    do! t := invokeKernel kerID2 nblk 1 (List.map VarE (args_out ++ args_temp ++ args_in)) in
    ret (outlenVar, outArr).

  Definition darr_of_arr {GA typ} (arr : Skel.AE GA typ) : 
    Skel.SExp GA (Skel.TZ :: nil) typ * Skel.LExp GA Skel.TZ :=
    match arr with
    | Skel.DArr _ _ f len => (fun f =>
      match f in Skel.Func GA' ftyp return Skel.LExp GA' Skel.TZ -> match ftyp with 
        | Skel.Fun1 dom cod => Skel.SExp GA' (dom :: nil) cod * Skel.LExp GA' Skel.TZ
        | Skel.Fun2 _ _ _ => unit 
        end with
      | Skel.F1 _ _ _ f => fun len => (f, len)
      | Skel.F2 _ _ _ _ _ => fun len => tt 
      end) f len
    | Skel.VArr _ _ arr => 
      (Skel.EA _ _ _ arr (Skel.EVar _ _ _ HFirst), Skel.LLen _ _ arr)
    end.

  Definition zip_AE {GA typ1 typ2} (arr1 : Skel.AE GA typ1) (arr2 : Skel.AE GA typ2) :
    Skel.AE GA (Skel.TTup typ1 typ2) :=
    let (body1, len1) := darr_of_arr arr1 in
    let (body2, len2) := darr_of_arr arr2 in
    Skel.DArr _ _ (Skel.F1 _ _ _ (Skel.ECons _ _ _ _ body1 body2)) (Skel.LMin _ len1 len2).
  Variable sorry : forall T, T.
  Arguments sorry {T}.

  Definition compile_Skel {GA typ} ntrd nblk (host_var_env : list (hostVar * list hostVar))
             (skel : Skel.SkelE GA typ) : CUDAM (hostVar * list hostVar) :=
    match skel with
    | Skel.Map _ dom cod f arr =>
      compile_map ntrd nblk host_var_env f arr
    | Skel.Reduce _ typ f arr => 
      compile_reduce ntrd nblk host_var_env f arr
    | Skel.Seq GA start len => 
      let f := Skel.F1 GA Skel.TZ Skel.TZ (Skel.EVar _ _ _ HFirst) in
      let g := Skel.DArr GA _ (Skel.F1 GA Skel.TZ Skel.TZ (Skel.EVar _ _ _ HFirst)) len in
      compile_map ntrd nblk host_var_env f g
    | Skel.Zip _ typ1 typ2 arr1 arr2 => 
      let f := Skel.F1 _ (Skel.TTup typ1 typ2) (Skel.TTup typ1 typ2) (Skel.EVar _ _ _ HFirst) in
      let arr := zip_AE arr1 arr2 in
      compile_map ntrd nblk host_var_env f arr
    end.

  Fixpoint compile_AS {GA typ} ntrd nblk (host_var_env : list (hostVar * list hostVar))
           (p : Skel.AS GA typ) : CUDAM (hostVar * list hostVar) :=
    match p with
    | Skel.ALet _ tskel tyres skel res => 
      do! outs := compile_Skel ntrd nblk host_var_env skel in
      compile_AS ntrd nblk (outs :: host_var_env) res 
    | Skel.ARet _ _ x =>
      ret (get_env host_var_env x (0, nil))
    end%list.

  Definition env_of_list {A B : Type} `{eq_type A} (xs : list (A * B)) : Env A (option B) _ :=
    List.fold_right (fun x acc => upd_opt acc (fst x) (snd x)) emp_opt xs.

  Definition hostVars_of_typ (ty : Skel.Typ) (n : nat) :=
    let ctys := ctyps_of_typ ty in
    (n, List.combine ctys (List.seq (S n) (length ctys))).

  (* Sx.prog = (list (varA * Sx.Typ) * Sx.AS)%type *)
  (* : Type *)

  Definition gen_env (GA : list Skel.Typ) : nat * list (hostVar * list (CTyp * hostVar)) :=
    List.fold_right (fun typ (acc : nat * list (hostVar * list (CTyp * hostVar))) =>
      let (n, acc) := acc in
      (n + S (length (ctyps_of_typ typ)), (hostVars_of_typ typ n) :: acc))
    (0, nil) GA.
  
  Definition toPtr : list (CTyp * hostVar) -> list (CTyp * hostVar) :=
    map (fun x => (Ptr (fst x), snd x)).

  Definition compile_prog {GA ty} ntrd nblk (p : Skel.AS GA ty) : Host.Prog :=
    let (n, host_var_env) := gen_env GA in
    let host_var_env' := map (fun x => (fst x, map snd (snd x))) host_var_env in
    let '(res, (_, (instrs, kers))) := compile_AS ntrd nblk host_var_env' p (n, (nil, nil)) in
    let pars := concat (map (fun x => (Int, fst x) :: toPtr (snd x)) host_var_env) in
    Build_Prog pars instrs res kers.
End Compiler.
