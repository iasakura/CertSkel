Require Import String.
Require Import Vector.
Require Import MyList.
Require Import ZArith.
Require Import GPUCSL.
Require Import LibTactics.
Require Import Psatz.
Require Import Monad.
Require Import MyEnv.
Require Import TypedTerm.
Require Import MyMSets.

Open Scope string_scope.
Definition name := string. 

Require GPUCSL.
Module G := GPUCSL.
Require Skel_lemma.
Module S := Skel_lemma.

Section codegen.
  Definition M a := nat -> ((a + string) * nat).

  Definition bind_opt A B (e : M A) (f : A -> M B) : M B:=
    fun n => 
      match e n with
      | (inr msg, n) => (inr msg, n)
      | (inl v, n) => f v n
      end.

  Definition fail {A} (msg : string): M A  := fun n => (inr msg, n).
  
  Definition get : M nat := fun n => (inl n, n).
  Definition set n : M unit := fun _ => (inl tt, n).
End codegen.

Instance M_monad : Monad M := {ret := fun _ x n => (inl x, n);
                               bind := bind_opt}.

Module Sx := Syntax.

Section compiler.
  (* environment of variables of array in the generated code *)
  (* Variable avarenv : Env nat (var * list var) _. *)
  Variable avarenv : list (var * list var).

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

  Definition compile_op {t1 t2 t3 : Skel.Typ} (op : Skel.BinOp t1 t2 t3) e1 e2 : (cmd * list exp) :=
    match op with
    | Skel.Eplus => (Cskip, Lang.Eplus e1 e2 :: nil)
    | Skel.Emult => (Cskip, Lang.Emult e1 e2 :: nil)
    | Skel.Emin => (Cskip, Lang.Emin e1 e2 :: nil)
    | Skel.BEq => (Cskip, Lang.Eeq e1 e2 :: nil)
    | Skel.Blt => (Cskip, Lang.Elt e1 e2 :: nil)
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
           (se : Skel.SExp GA GS typ) (env : list (list var)) : M (cmd * list exp) := match se with
    | Skel.EVar _ _ _ v => ret (Cskip, S.vars2es (get_env env v nil))
    | Skel.ENum _ _ z => ret (Cskip, Enum z :: nil)
    | Skel.ELet _ _ t1 t2 e1 e2 =>
      compile_sexp e1 env >>= fun ces1 => 
      let (c1, es1) := ces1 in
      (* let dim := length es1 in *)
      let dim := ctyps_of_typ t1 in
      freshes (length dim) >>= fun xs =>
      compile_sexp e2 (xs :: env) >>= fun ces2 => 
      let (c2, es2) := ces2 in
      ret (c1 ;; S.read_tup xs dim es1 ;; c2, es2)
    | Skel.EBin _ _ _ _ _ op e1 e2 => 
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
    | Skel.EA _ _ typ va e =>
      let dim := ctyps_of_typ typ in
      compile_sexp e env >>= fun ces =>
      let (c, es) := ces in
      let (_, aname) := get_env avarenv va (Var "", nil) in
      freshes (length dim) >>= fun xs =>
      match es with
      | i :: nil => ret (c ;; S.gen_read Gl xs dim (S.vars2es aname) i, S.vars2es xs)
      | _ => fail ""
      end
    | Skel.ELen _ _ _ xa =>
      let (l, _) := get_env avarenv xa (Var "", nil) in ret (Cskip, (Evar l) :: nil)
    | Skel.EPrj1 _ _ t1 t2 e =>
      let off := 0 in
      let l := len_of_ty t1 in
      compile_sexp e env >>= fun ces =>
      let (c, es) := ces in
      ret (c, firstn l (skipn off es))
    | Skel.EPrj2 _ _ t1 t2 e =>
      let off := len_of_ty t1 in
      let l := len_of_ty t2 in
      (* ugly copy and paste !*)
      compile_sexp e env >>= fun ces =>
      let (c, es) := ces in
      ret (c, firstn l (skipn off es))
    | Skel.ECons _ _ t1 t2 e1 e2 => 
      compile_sexp e1 env >>= fun ces =>
      let (c1, ge1) := ces in
      compile_sexp e2 env >>= fun ces =>
      let (c2, ge2) := ces in
      ret (c1 ;; c2, ge1 ++ ge2)
    | Skel.EIf _ _ ty e1 e2 e3 =>
      let dim := ctyps_of_typ ty in
      compile_sexp e1 env >>= fun ces1 => 
      let (c1, e1) := ces1 in
      compile_sexp e2 env >>= fun ces2 =>
      let (c2, e2) := ces2 in
      compile_sexp e3 env >>= fun ces3 =>
      let (c3, e3) := ces3 in
      freshes (length dim) >>= fun xs =>
      match e1 with
      | e :: nil =>
        ret (c1;; Cif (Bnot (Beq e 0%Z)) (c2 ;; S.read_tup xs dim e2) (c3 ;; S.read_tup xs dim e3), S.vars2es xs)
      | _ => fail ""
      end
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
  
  Eval cbv in (compile_sexp nil test1 nil 0).
  
End TestCompiler.

Require Import pmap_skel.
Require Import Reduce_opt_skel.
Import Skel_lemma scan_lib.

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

Require Import Host.
(* Instance CUDA_monad : Monad CUDA := {| ret := @ret; bind := bind |}. *)

Section Compiler.
  (* Fixpoint free_sv (e : Sx.SExp) : SE.t := *)
  (*   match e with *)
  (*   | Sx.EVar v _ => SE.singleton v *)
  (*   | Sx.ENum _   => SE.empty *)
  (*   | Sx.ELet x e1 e2 _ =>  *)
  (*     SE.union (free_sv e1) (SE.remove x (free_sv e2)) *)
  (*   | Sx.EBin _ e1 e2 _ => SE.union (free_sv e1) (free_sv e2) *)
  (*   | Sx.EA _ e _ => free_sv e *)
  (*   | Sx.ELen _ => SE.empty *)
  (*   | Sx.EPrj e _ _ => free_sv e *)
  (*   | Sx.ECons es _ => fold_right (fun e xs => SE.union (free_sv e) xs) SE.empty es *)
  (*   | Sx.EIf e e' e'' _ => SE.union (free_sv e) (SE.union (free_sv e') (free_sv e'')) *)
  (*   end. *)

  (* Fixpoint free_av (e : Sx.SExp) : SA.t := *)
  (*   match e with *)
  (*   | Sx.EVar v _ => SA.empty *)
  (*   | Sx.ENum _   => SA.empty *)
  (*   | Sx.ELet x e1 e2 _ =>  *)
  (*     SA.union (free_av e1) (free_av e2) *)
  (*   | Sx.EBin _ e1 e2 _ => SA.union (free_av e1) (free_av e2) *)
  (*   | Sx.EA x e _ => SA.add x (free_av e) *)
  (*   | Sx.ELen x => SA.singleton x *)
  (*   | Sx.EPrj e _ _ => free_av e *)
  (*   | Sx.ECons es _ => fold_right (fun e xs => SA.union (free_av e) xs) SA.empty es *)
  (*   | Sx.EIf e e' e'' _ => SA.union (free_av e) (SA.union (free_av e') (free_av e'')) *)
  (*   end. *)

  (* Definition free_av_func (f : Sx.Func) := *)
  (*   match f with *)
  (*   | Sx.F ps body => free_av body *)
  (*   end. *)

  (* Fixpoint free_av_lexp (e : Sx.LExp) : SA.t := *)
  (*   match e with *)
  (*   | Sx.LNum _   => SA.empty *)
  (*   (* | Sx.LBin _ e1 e2 => SA.union (free_av_lexp e1) (free_av_lexp e2) *) *)
  (*   | Sx.LLen x => SA.singleton x  *)
  (*   end. *)

  (* Definition free_av_AE (ae : Sx.AE) := *)
  (*   match ae with *)
  (*   | Sx.DArr f len => *)
  (*     SA.union (free_av_func f) (free_av_lexp len) *)
  (*   | Sx.VArr xa => SA.singleton xa *)
  (*   end. *)

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

  Definition arr_name n (d : list CTyp) :=
    List.combine
      (map Var (names_of_array (grpOfInt n) (length d)))
      (map Ptr d).
  Definition len_name n := Var (name_of_len (grpOfInt n)).
  Definition out_name (d : list CTyp) :=
    List.combine
      (map Var (names_of_array "Out" (length d)))
      (map Ptr d).
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

  Definition evalM {a : Type} (m : M a) (n : nat) d : a :=
    match m n with
    | (inl x, _) => x
    | _ => d
    end.

  Fixpoint dumy_fun_n n x :=
    match n return type_of_func n with
    | O => x
    | S n => fun y => dumy_fun_n n x
    end.

  Definition type_of_ftyp (fty : Skel.FTyp) :=
    match fty with
    | Skel.Fun1 dom cod => list var -> (cmd * list exp)
    | Skel.Fun2 dom1 dom2 cod  => list var -> list var -> (cmd * list exp)
    end.

  Fixpoint compile_func {GA fty} avar_env (body : Skel.Func GA fty) :=
    match body in Skel.Func _ fty' return type_of_ftyp fty' with
    | Skel.F1 _ _ _ body => fun xs => evalM (compile_sexp avar_env body (xs :: nil)) 0 (Cskip, nil)
    | Skel.F2 _ _ _ _ body => fun xs ys => evalM (compile_sexp avar_env body (xs :: ys :: nil)) 0 (Cskip, nil)
    end.

  Definition compile_lexp {GA ty} (aenv : list (hostVar * list hostVar)) (le : Skel.LExp GA ty) : expr :=
    match le with
    | Skel.LNum _ n => Const n
    | Skel.LLen _ _ a => VarE (fst (get_env aenv a (0, nil)))
    end.

  Definition accessor_of_array {GA tyxa} aenv (arr : member tyxa GA) :=
    compile_func aenv (Skel.F1 _ Skel.TZ _ (Skel.EA _ _ _ arr (Skel.EVar _ _ _ HFirst))).

  Definition compile_AE {GA ty}
             avar_env (var_ptr_env : list (hostVar * list hostVar)) (ae : Skel.AE GA ty) :
    ((var -> (cmd * list exp)) * expr) :=
    match ae with
    | Skel.DArr _ _ f len =>
      let f' := compile_func avar_env f in
      let len' := compile_lexp var_ptr_env len in
      (fun x => f' (x :: nil), len')
    | Skel.VArr _ _ xa =>
      let get := accessor_of_array avar_env xa in
      (fun x => get (x :: nil), VarE (fst (get_env var_ptr_env xa (0, nil))))
    end.

  Variable ntrd : nat.
  Variable nblk : nat.

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

  Variable sorry : forall {T : Type}, T.
  Arguments sorry {T}.

  Definition state s a := s -> (a * s).
  Instance state_Monad s : Monad (state s) := {
     ret A x := fun n => (x, n);
     bind A B x f := fun n => let (y, n) := x n in f y n
  }.
  Definition getS {s} : state s s := fun x => (x, x).
  Definition setS {s} x : state s unit := fun _ => (tt, x).

  Open Scope list_scope.

  Definition fLet e : state (nat * list instr) hostVar :=
    do! st := getS in
    let (n, irs) := st : nat * list instr in
    do! _ := setS (S n, irs ++ (iLet n e :: nil)) in
    ret n.

  Definition fAlloc e : state (nat * list instr) hostVar :=
    do! st := getS in
    let (n, irs) := st : nat * list instr in
    do! _ := setS (S n, irs ++ (alloc n e :: nil)) in
    ret n.

  Definition fAllocs ctys e : state (nat * list instr) (list hostVar) :=
    mapM (fun cty => fAlloc e) ctys.

  Definition gen_params (GA : list Skel.Typ) : list (var * list var) :=
    let f typ i :=
        let ctyp := ctyps_of_typ typ in
    zipWith (fun p  => 
      let (typ, i) := p in ) (GA (seq 0 (length GA)))

  Definition compile_Skel {GA typ} (host_var_env : list (hostVar * list hostVar))
             (skel : Skel.SkelE GA typ) : Host.Prog * nat :=
    match skel with
    | Skel.Map _ dom cod f arr =>
      let (g, outlen) := compile_AE _ host_var_env arr in
      do! outlenVar := fLet outLen in
      
    | Skel.Reduce _ typ f arr => sorry
    | Skel.Seq _ start len => sorry
    | Skel.Zip _ typ1 typ2 arr1 arr2 => sorry
    end.

  Fixpoint compile_AS {GA typ} (numVar : nat) (host_var_env : list (hostVar * list hostVar)) (p : Skel.AS GA typ) : Host.Prog :=
    match p with
    | Skel.ALet _ tskel tyres skel res => 
      let '((instrs, outs, kers), n) := compile_Skel host_var_env skel in
      let '(instrs_res, outs_res, kers_res) := compile_AS n (outs :: host_var_env) res in
      (instrs ++ instrs_res, outs_res, kers ++ kers_res)
    | Skel.ARet _ _ x =>
      (nil, get_env host_var_env x (0, nil), nil)
    end%list.

  Fixpoint compile_AS
           (numVar : nat)
           (aty_env : Env varA (option Sx.Typ) _)
           (host_var_env : Env varA (hostVar * list hostVar) _)
           (p : Sx.AS) : Host.Prog :=
    match p with
    | Sx.ALet xa tyxa skelE rest =>
      let fvs_f := List.fold_right (fun f sa => SA.union (free_av_func f) sa) SA.empty fs in
      let fvs_ae := List.fold_right (fun ae sa => SA.union (free_av_AE (fst ae)) sa) SA.empty aes in
      let fvs := SA.union fvs_f fvs_ae in
      
      let fvs' := SA.elements fvs in
      (* from free variables, compute a map from each fv to a kernel parameter *)
      let env := env_of_sa aty_env fvs in

      (* kernel parameters for input arrays *)
      let inParams := concat (map (fun xa =>
        let (len, arr) := env xa in
        (len, Int) :: arr) fvs') in
      (* kernel arguments for input arrays *)
      let inArgs := concat (map (fun xa => fst (host_var_env xa) :: snd (host_var_env xa)) fvs') in

      (* the dimension of the output array *)
      let outDim := ctyps_of_typ tyxa in

      (* the kernel parameter for output array *)
      let outsParam := out_name outDim in
      let outlenParam := out_len_name in

      let env' := env_map (fun x => (fst x, List.map fst (snd x))) env in

      match skelE with 
     | SkelMap f (ae, tyAe) =>
        (* the dimension of the input array *)
        let inDim := ctyps_of_typ tyAe in
        let (get, inlen) := compile_AE aty_env env' host_var_env ae in
        let func : list var -> (cmd * list exp) := compile_func_n 1 env' f in
        (* xs := allocs ...; l := Let inlen; invoke ...*)
        (* shift free vars index by (outDim + 1) *)
        let outAllocs := alloc_tup_arr numVar (length outDim) inlen in
        let outs := seq numVar (length outDim) in
        let numVar := numVar + (length outDim) in
        
        let letLen := iLet numVar inlen in
        let outLen := numVar in
        let numVar := numVar + 1 in
        
        let ker := {| params_of := (outlenParam, Int) :: outsParam ++ inParams;
                      body_of := {| get_sh_decl := nil;
                                    get_cmd := mkMap ntrd nblk inDim outDim get func |} |} in
        let newHEnv := upd host_var_env xa (outLen, outs) in
        let newAtyEnv := upd_opt aty_env xa tyxa in
        let '(instr, res, kenv) := compile_AS numVar newAtyEnv newHEnv rest in
        let newID := List.length kenv in
        (outAllocs ++
         (letLen :: nil) ++
         (invoke newID ntrd nblk (List.map VarE (outLen :: outs ++ inArgs)) :: nil) ++
         instr,
         res,
         kenv ++ (ker :: nil))
      | "reduce", (f :: nil), ((ae, tyAe) :: nil) =>
        let inDim := ctyps_of_typ tyAe in

        (* tmpAllocs. ..; allocs ...; iLet inlen; invoke ...*)
        (* shift free vars index by (2 * outDim + 1) *)
        let func : list var -> list var -> (cmd * list exp) := compile_func_n 2 env' f in
        let (get, inlen) := compile_AE aty_env env' host_var_env ae in
        
        let tmpAllocs := alloc_tup_arr numVar (length outDim) (Const (Z.of_nat nblk)) in
        let tmps := seq numVar (length outDim) in
        let numVar := numVar + (length outDim) in
        let outAllocs := alloc_tup_arr numVar (length outDim) (Const 1%Z) in
        let outs := seq numVar (length outDim) in
        let numVar := numVar + (length outDim) in
        let letLen := iLet numVar (Const 1%Z) in
        let outLen := numVar in
        let numVar := numVar + 1 in
        
        let reduce1 := {|
          params_of := ((outlenParam, Int) :: outsParam ++ inParams);
          body_of := Pr (sh_decl ntrd outDim) (mkFoldAll ntrd nblk inDim func (S (log2 ntrd)) get)
        |} in
        let inArgs := concat (map (fun xa => fst (host_var_env xa) :: snd (host_var_env xa)) fvs') in

        (* generating new parameter diffirent from all existing parameters *)
        let newParID := SA.cardinal fvs in
        let len_var := len_name newParID in
        let arr_vars := arr_name newParID outDim in
        (* generating getter accesing the array (len_var, arr_vars) *)
        let get x := accessor_of_array (emp_def (len_var, List.map fst arr_vars))
                        (VarA "") tyxa (x :: nil) in
        let inParam_f := concat (map (fun xa => (fst (env xa), Int) :: snd (env xa)) (SA.elements fvs_f)) ++
                         ((len_var, Int) :: arr_vars) in
        let inArgs_f := List.map VarE
          (concat (map (fun xa => fst (host_var_env xa) :: snd (host_var_env xa)) (SA.elements fvs_f))) ++ 
          (Const (Z.of_nat nblk) :: List.map VarE tmps)in
        (* (Nat.min ((l + ntrd - 1) / ntrd) nblk ) *)
        let ntrd' :=
            Min (Div (Add inlen (Const (Z.of_nat ntrd - 1)%Z))
                     (Const (Z.of_nat ntrd)))
                (Const (Z.of_nat nblk)) in
        let reduce2 := {|
          params_of := ((outlenParam, Int) :: outsParam ++ inParam_f);
          body_of := Pr (sh_decl nblk outDim) (mkFoldAll nblk 1 inDim func (S (log2 nblk)) get)
        |} in

        let newEnv := upd host_var_env xa (outLen, outs) in
        let newAtyEnv := upd_opt aty_env xa tyxa in
        let '(instr, res, kenv) := compile_AS numVar newAtyEnv newEnv rest in
        let red1 := List.length kenv in
        let red2 := S red1 in

        (tmpAllocs ++ outAllocs ++
         (letLen :: nil) ++
         (invoke red1 ntrd nblk (inlen :: List.map VarE tmps ++ List.map VarE inArgs) :: nil) ++
         (invoke red2 nblk 1    ((ntrd' :: List.map VarE outs) ++ inArgs_f) :: nil) ++
         instr,
         res, 
         kenv ++ (reduce1 :: reduce2 :: nil))
      | _, _, _ => (nil, (0, nil), nil)
      end
    | Sx.ARet xa => (nil, host_var_env xa, nil)
    end%list.

  Definition env_of_list {A B : Type} `{eq_type A} (xs : list (A * B)) : Env A (option B) _ :=
    List.fold_right (fun x acc => upd_opt acc (fst x) (snd x)) emp_opt xs.

  Definition hostVars_of_typ (ty : Sx.Typ) (n : nat) :=
    let ctys := ctyps_of_typ ty in
    (n, List.combine ctys (List.seq (S n) (length ctys))).

  (* Sx.prog = (list (varA * Sx.Typ) * Sx.AS)%type *)
  (* : Type *)
  
  Definition compile_prog (p : Sx.prog) :=
    let (pars, body) := p in
    let tyenv := env_of_list pars : Env varA (option Sx.Typ) eq_varA in
    let (n, hostvarEnv) :=
      List.fold_right (fun (x : varA * Sx.Typ) (acc : nat * Env varA (hostVar * list (CTyp * hostVar)) eq_varA) =>
        let (n, acc) := acc in
        let (x, typ) := x in
        (n + S (length (ctyps_of_typ typ)), upd acc x (hostVars_of_typ typ n)))
     ((0, emp_def (0, nil)) : nat * Env varA (hostVar * list (CTyp * hostVar)) eq_varA) pars in
    let pars : list (CTyp * hostVar) :=
        concat (List.map (fun x => (Int, fst (hostvarEnv (fst x))) ::
                                   List.map (fun x => (Ptr (fst x), (snd x))) (snd (hostvarEnv (fst x)))) pars) in
    let hostvarEnv' := env_map (fun x => (fst x, map snd (snd x))) hostvarEnv in
    (pars, compile_AS n tyenv hostvarEnv' body).
End Compiler.

(* Eval compute in "Finished !". *)

(* Section CorrectnessProof. *)
(*   Import Skel_lemma. *)
(*   (* the set of free variables *) *)
(*   Variable free_avs : SA.t. *)
(*   (* the evaluation environment *) *)
(*   Variable aeval_env : Env varA (option array) _. *)
(*   (* the typing environment *) *)
(*   Variable aty_env : Env varA (option Sx.Typ) _. *)
(*   (* the variable mapping environment between source and dest. *) *)
(*   Variable avar_env : Env varA (var * list var) _ . *)
  
(*   (* source lang. values -> dest. lang. values *) *)
(*   Fixpoint vs_of_sval sval : list Z := *)
(*     match sval with *)
(*     | VB b => (if b then 1%Z else 0%Z) :: nil *)
(*     | VZ z => z :: nil *)
(*     | VTup vs => fold_right (fun v vs => vs_of_sval v ++ vs) nil vs *)
(*     end%list. *)

(*   (* precondition of free variable arrays *) *)
(*   Definition assn_of_avs (favs : SA.t) : assn := *)
(*     SA.assn_of_vs array aeval_env (fun x_a a => *)
(*        !(fst (avar_env x_a) === Z.of_nat (length a)) ** *)
(*        S.is_tuple_array_p (S.es2gls (S.vars2es (snd (avar_env x_a)))) (length a) *)
(*                           (fun i => vs_of_sval (nth i a (VZ 0))) 0 1) favs. *)
  
(*   (* (* the set of free variables of scalar exp *) *) *)
(*   (* Variable free_svs : list varE. *) *)
(*   (* (* the evaluation environment of scalar exp *) *) *)
(*   (* Variable seval_env : Env varE (option SVal) _. *) *)
(*   (* (* the typing environment *) *) *)
(*   (* Variable sty_env : Env varE Typ _. *) *)
(*   (* (* the variable mapping environment between source and dest. *) *) *)
(*   (* Variable svar_env : Env varE (list var) _ . *) *)

(*   (* preconditions of scalar variables *) *)
(*   Definition assn_of_svs (seval_env : Env varE (option SVal) _) (svar_env : Env varE (list var) _)  (fsvs : SE.t) : assn := *)
(*     SE.assn_of_vs SVal seval_env (fun x_e v => *)
(*                 !(vars2es (svar_env x_e) ==t vs_of_sval v)) fsvs. *)
  
(*   (* Section UniqList. *) *)
(*   (*   Variable A : Type. *) *)
(*   (*   Variable eqt : eq_type A. *) *)
(*   (*   Definition equiv_ls (ls1 ls2 : list A) := (incl ls1 ls2) /\ (incl ls2 ls1). *) *)
    
(*   (*   Require Import Recdef. *) *)
(*   (*   Lemma remove_length (xs : list A) x: *) *)
(*   (*     length (remove eq_dec x xs) <= length xs. *) *)
(*   (*   Proof. *) *)
(*   (*     induction xs; simpl; try omega. *) *)
(*   (*     destruct eq_dec; simpl; try omega. *) *)
(*   (*   Qed. *) *)
  
(*   (*   Function uniq (xs : list A) {measure length xs} := *) *)
(*   (*     match xs with *) *)
(*   (*     | nil => nil *) *)
(*   (*     | x :: xs => x :: uniq (remove eq_dec x xs) *) *)
(*   (*     end. *) *)
(*   (*   Proof. *) *)
(*   (*     intros; simpl. *) *)
(*   (*     lets: (>> remove_length xs0 x); simpl in *; try omega. *) *)
(*   (*   Defined. *) *)

(*   (*   Lemma remove_incl x (xs : list A) : *) *)
(*   (*     incl (remove eq_dec x xs) xs. *) *)
(*   (*   Proof. *) *)
(*   (*     induction xs; unfold incl in *; simpl; eauto. *) *)
(*   (*     destruct (eq_dec _ _); substs; simpl in *; jauto. *) *)
(*   (*     intros ? [? | ?]; eauto. *) *)
(*   (*   Qed. *) *)
    
(*   (*   Lemma uniq_incl (xs : list A) : incl (uniq xs) xs. *) *)
(*   (*   Proof. *) *)
(*   (*     functional induction (uniq xs). *) *)
(*   (*     - unfold incl; eauto. *) *)
(*   (*     - unfold incl in *; simpl. *) *)
(*   (*       intros ? [? | ?]; eauto. *) *)
(*   (*       forwards* : IHl. *) *)
(*   (*       forwards* : remove_incl. *) *)
(*   (*   Qed. *) *)

(*   (*   Lemma remove_neq (x y : A) (xs : list A) : x <> y -> In x xs -> In x (remove eq_dec y xs). *) *)
(*   (*   Proof. *) *)
(*   (*     revert y; induction xs; simpl; intros y Hneq Hin; auto. *) *)
(*   (*     destruct Hin as [Hin | Hin]; substs. *) *)
(*   (*     - destruct eq_dec; try congruence. *) *)
(*   (*       simpl; eauto. *) *)
(*   (*     - destruct eq_dec; substs. *) *)
(*   (*       + apply IHxs; eauto. *) *)
(*   (*       + simpl; right; eauto. *) *)
(*   (*   Qed. *) *)
        
(*   (*   Lemma uniq_incl' (xs : list A) : incl xs (uniq xs). *) *)
(*   (*   Proof. *) *)
(*   (*     functional induction (uniq xs); unfold incl; simpl; eauto. *) *)
(*   (*     intros a [Hin|Hin]; substs; eauto. *) *)
(*   (*     destruct (eq_dec x a); eauto. *) *)
(*   (*     right; apply IHl. *) *)
(*   (*     apply remove_neq; eauto. *) *)
(*   (*   Qed. *) *)

(*   (*   Lemma uniq_no_dup (xs : list A) : NoDup (uniq xs). *) *)
(*   (*   Proof. *) *)
(*   (*     functional induction (uniq xs). *) *)
(*   (*     - constructor. *) *)
(*   (*     - constructor; eauto. *) *)
(*   (*       intros Hc. *) *)
(*   (*       forwards*: uniq_incl; unfold incl in *; eauto. *) *)
(*   (*       apply H in Hc; forwards*: remove_In; eauto. *) *)
(*   (*   Qed. *) *)

(*   (*   Lemma eq_ls_nil_l xs : equiv_ls nil xs -> xs = nil. *) *)
(*   (*   Proof. *) *)
(*   (*     unfold equiv_ls, incl; simpl; intros [? ?]. *) *)
(*   (*     destruct xs; simpl in *; eauto. *) *)
(*   (*     lets *: (H0 a). *) *)
(*   (*   Qed. *) *)

(*   (*   Lemma eq_ls_nil_r xs : equiv_ls xs nil -> xs = nil. *) *)
(*   (*   Proof. *) *)
(*   (*     unfold equiv_ls, incl; simpl; intros [? ?]. *) *)
(*   (*     destruct xs; simpl in *; eauto. *) *)
(*   (*     lets *: (H a). *) *)
(*   (*   Qed. *) *)

(*   (*   Lemma equiv_ls_refl xs : equiv_ls xs xs. *) *)
(*   (*   Proof. *) *)
(*   (*     unfold equiv_ls; lets: (incl_refl xs); eauto. *) *)
(*   (*   Qed. *) *)

(*   (*   Lemma equiv_ls_symm xs ys : equiv_ls xs ys -> equiv_ls ys xs. *) *)
(*   (*   Proof. *) *)
(*   (*     unfold equiv_ls; jauto. *) *)
(*   (*   Qed. *) *)


(*   (*   Lemma equiv_ls_cons x xs ys : equiv_ls (x :: xs) ys -> *) *)
(*   (*                                 exists ys', ys = x :: ys'. *) *)
(*   (*   Proof. *) *)
(*   (*     revert xs; induction ys; simpl; intros xs. *) *)
(*   (*     - intros; forwards*: (eq_ls_nil_r (x :: xs)). *) *)
(*   (*     -  *) *)
      

(*   (*   Hint Resolve equiv_ls_refl equiv_ls_symm. *) *)

(*   (*   Lemma equiv_ls_cons x xs ys : *) *)
(*   (*     equiv_ls xs ys -> equiv_ls (x :: xs) (x :: ys). *) *)
(*   (*   Proof. *) *)
(*   (*     revert ys; induction xs; simpl. *) *)
(*   (*     - intros; rewrites* (eq_ls_nil_r ys). *) *)
(*   (*     -  *) *)
      

(*   (*     Lemma equive_ls_reorder x xs : *) *)
(*   (*       In x xs -> *) *)
(*   (*       equiv_ls _ xs (x :: (remove eq_dec x xs)). *) *)
(*   (*     Proof. *) *)
(*   (*       induction xs; simpl; forwards*: tt. *) *)
(*   (*       intros [?|Hin]; substs. *) *)
(*   (*       destruct eq_dec; try congruence. *) *)

(*   (* End UniqList. *) *)
  
(*   Import scan_lib. *)

(*   (* Arguments uniq {A} {eqt} x. *) *)

(*   (* Definition free_sv e := uniq (free_sv' e). *) *)
(*   (* Definition free_av e := uniq (free_av' e). *) *)

(*   Ltac unfoldM := unfold freshes, get, set, ret in *; simpl in *; unfold bind_opt in *. *)
  
(*   Lemma freshes_incr d m n xs : *)
(*     freshes d n = (inl xs, m) ->  *)
(*     m = n + 1. *)
(*   Proof. *)
(*     revert n m xs; induction d; simpl; intros n m xs. *)
(*     - unfoldM; simpl; intros H; inverts H; eauto. *)
(*     - unfoldM. *)
(*       lazymatch goal with [|- context [(Var _ :: ?E) ]] => remember E eqn:Heq end. *)
(*       intros H; inverts H. *)
(*       forwards*: (>>IHd n). *)
(*   Qed. *)
  
(*   (* some lemma for generetated variables *) *)
(*   Lemma freshes_vars d n m xs: *)
(*     freshes d n = (inl xs, m) ->  *)
(*     (forall x, In x xs -> exists l, x = Var (str_of_pnat n l) /\ l < d). *)
(*   Proof. *)
(*     revert n m xs; induction d; simpl; intros n m xs; unfoldM. *)
(*     - intros H; inverts H. *)
(*       destruct 1. *)
(*     - unfoldM. *)
(*       lazymatch goal with [|- context [(Var _ :: ?E) ]] => remember E eqn:Heq end. *)
(*       intros H; inverts H. *)
(*       intros ? H'; apply in_inv in H' as [? | ?]; eauto. *)
(*       forwards* (? & ?): IHd. *)
(*       substs; eauto. *)
(*   Qed. *)
  
(*   Lemma freshes_len d n m xs: *)
(*     freshes d n = (inl xs, m) -> length xs = d. *)
(*   Proof. *)
(*     revert n m xs; induction d; unfoldM;  *)
(*       simpl; inversion 1; simpl in *; try omega. *)
(*     forwards * : IHd. *)
(*   Qed. *)

(*   Lemma var_pnat_inj n m n' m' : Var (str_of_pnat n m) = Var (str_of_pnat n' m') -> n = n' /\ m = m'. *)
(*   Proof. *)
(*     intros Heq. *)
(*     apply str_of_pnat_inj; inversion Heq. *)
(*     unfold str_of_pnat; f_equal; eauto. *)
(*   Qed. *)

(*   Variable ntrd : nat. *)
(*   Variable tid : Fin.t ntrd. *)
(*   Variable BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd. *)
(*   Arguments assn_of_svs _ _ _ _ _ : simpl never. *)
(*   Arguments assn_of_avs _ _ _ : simpl never. *)
(*   Tactic Notation "simpl_avs" "in" hyp(HP) := unfold assn_of_svs, SE.assn_of_vs, SE.fold in HP; simpl in HP. *)
(*   Tactic Notation "simpl_avs" := unfold assn_of_svs, SE.assn_of_vs, SE.fold; simpl. *)
(*   Tactic Notation "simpl_avs" "in" "*" := unfold assn_of_svs, SE.assn_of_vs, SE.fold in *; simpl in *. *)
(*   Arguments flip / _ _ _ _ _ _. *)
(*   Instance ban_proper stk : Proper (equiv_sep stk ==> equiv_sep stk) ban. *)
(*   Proof. *)
(*     intros P1 P2 Heq h; lets:(Heq h). *)
(*     unfold ban, Aconj; rewrite H; split; eauto. *)
(*   Qed. *)

(*   Lemma compile_don't_decrease se c es (svar_env : Env varE (list var) _) n m : *)
(*     compile_sexp avar_env se svar_env n = (inl (c, es), m) -> *)
(*     n <= m. *)
(*   Proof. *)
(*     revert n m svar_env c es; induction se using Sx.SExp_ind'; simpl; *)
(*       intros n m svar_env c es' Hsuc; eauto; try inverts Hsuc as Hsuc; *)
(*     eauto; unfoldM; *)
(*           (repeat lazymatch type of Hsuc with *)
(*              | context [compile_sexp ?X ?Y ?Z ?n] => destruct (compile_sexp X Y Z n) as [[(? & ?) | ?] ?] eqn:? *)
(*              | context [freshes ?X ?Y] => destruct (freshes X Y) as ([? | ?] & ?) eqn:? *)
(*              end); *)
(*     (repeat lazymatch goal with [H : context [match ?E with | _ => _ end]|- _] => destruct E eqn:? end); *)
(*           try now (inverts Hsuc; first *)
(*             [now auto| *)
(*              forwards*: IHse1; forwards*: IHse2; omega | *)
(*              forwards*: IHse1; forwards*: IHse2; forwards*: IHse3; omega | *)
(*              forwards*: IHse; omega | *)
(*              forwards*: IHse1; forwards*: IHse2; forwards*: freshes_incr; omega | *)
(*              forwards*: IHse1; forwards*: IHse2; forwards*: IHse3; forwards*: freshes_incr; omega | *)
(*              forwards*: IHse; forwards*: freshes_incr; omega | *)
(*              forwards*: IHse; omega]). *)
(*     revert n m c es' Hsuc; induction es; introv; intros Hsuc; [inverts Hsuc; eauto|]. *)
(*     repeat lazymatch type of Hsuc with *)
(*       | context [compile_sexp ?X ?Y ?Z ?W ?n] => destruct (compile_sexp X Y Z W n) as [[(? & ?) | ?] ?] eqn:? *)
(*       end; try now inverts Hsuc. *)
(*     repeat lazymatch type of Hsuc with *)
(*       | context [let (_, _) := ?E in _] => destruct E as [[(? & ?)|?] ?] eqn:? *)
(*       end; try now inverts Hsuc. *)
(*     forwards*: IHes. *)
(*     inverts H; eauto. *)
(*     inverts Hsuc. *)
(*     rewrite Forall_forall in H; forwards*: H; [left; auto|omega]. *)
(*     Grab Existential Variables. *)
(*   Qed. *)

(*   Lemma fold_assn_svs se sv : *)
(*     SE.assn_of_vs SVal se (fun (x_e : VarE_eq.t) (v : SVal) => !(vars2es (sv x_e) ==t vs_of_sval v)) = *)
(*     assn_of_svs se sv. auto. Qed. *)
(*   Lemma fold_assn_avs : *)
(*     SA.assn_of_vs array aeval_env *)
(*       (fun (x_a : VarA_eq.t) (a : array) => *)
(*          !(fst (avar_env x_a) === Z.of_nat (length a)) ** *)
(*          S.is_tuple_array_p (S.es2gls (S.vars2es (snd (avar_env x_a))))  *)
(*                             (length a) (fun i : nat => vs_of_sval (nth i a (VZ 0))) 0 1) = *)
(*     assn_of_avs. auto. Qed. *)

(*   Lemma inde_equiv P P' xs : *)
(*     (forall stk, stk ||= P <=> P') -> *)
(*     (inde P xs <-> inde P' xs). *)
(*   Proof. *)
(*     unfold inde, equiv_sep. *)
(*     intros; simpl. *)
(*     split; intros; split; intros; intuition; *)
(*       try (apply H, H0, H); eauto. *)
(*     apply H; apply <-H0; eauto; apply H; eauto. *)
(*     apply H; apply <-H0; eauto; apply H; eauto. *)
(*   Qed. *)

(*   Lemma inde_assn_of_svs seval_env svar_env fvs (xs : list var) : *)
(*     (forall x y, In x xs -> SE.In y fvs -> ~In x (svar_env y)) -> *)
(*     inde (assn_of_svs seval_env svar_env fvs) xs. *)
(*   Proof. *)
(*     destruct fvs as [fvs ok]; simpl. *)
(*     simpl_avs. *)
(*     induction fvs; simpl; repeat prove_inde. *)
(*     destruct (seval_env a). *)
(*     unfold SE.SE.Raw.fold; simpl. *)
(*     intros H. *)
(*     rewrites (>>inde_equiv). *)
(*     { intros; rewrite SE.fold_left_assns; reflexivity. } *)
(*     repeat prove_inde. *)
(*     apply inde_eq_tup. *)
(*     rewrite Forall_forall; intros; simplify; simpl; eauto. *)
(*     apply H in H0; eauto. *)
(*     left; auto. *)
(*     eauto. *)
(*     inverts keep ok as ? Hok; applys* (IHfvs Hok). *)
(*     intros; apply H; eauto. *)
(*     right; auto. *)
(*     simpl_avs. rewrites (>>inde_equiv). *)
(*     { intros; unfold SE.SE.Raw.fold; simpl. *)
(*       rewrite SE.fold_left_assns. *)
(*       instantiate (1 := FalseP). *)
(*       split; [intros (? & ? & [] & ? & ? & ?) | destruct 1]. } *)
(*     intros; prove_inde. *)
(*   Qed. *)
  
(*   Lemma inde_assn_of_avs fvs (xs : list var) : *)
(*     (forall x y, In x xs -> SA.In y fvs -> ~In x (snd (avar_env y))) -> *)
(*     (forall x y, In x xs -> SA.In y fvs -> x <> fst (avar_env y)) -> *)
(*     inde (assn_of_avs fvs) xs. *)
(*   Proof. *)
(*     destruct fvs as [fvs ok]; simpl. *)
(*     unfold assn_of_avs, SA.assn_of_vs, SA.SE.fold, SA.SE.Raw.fold; simpl. *)
(*     induction fvs; simpl; repeat prove_inde. *)
(*     destruct (aeval_env a). *)
(*     intros H H'. *)
(*     rewrites (>>inde_equiv). *)
(*     { intros; rewrite SA.fold_left_assns; reflexivity. } *)
(*     repeat prove_inde; try (rewrite Forall_forall; simplify; eauto). *)
(*     forwards*: H'; left; eauto. *)
(*     apply inde_is_tup_arr. *)
(*     intros; simplify. *)
(*     unfold S.es2gls in *; simplify. *)
(*     apply H in H0; eauto. *)
(*     left; auto. *)
(*     inverts keep ok as ? Hok; applys* (IHfvs Hok). *)
(*     intros; apply H; eauto. *)
(*     right; auto. *)
(*     intros; apply H'; eauto; right; eauto. *)
(*     simpl_avs. rewrites (>>inde_equiv). *)
(*     { intros; unfold SE.SE.Raw.fold; simpl. *)
(*       rewrite SA.fold_left_assns. *)
(*       instantiate (1 := FalseP). *)
(*       split; [intros (? & ? & [] & ? & ? & ?) | destruct 1]. } *)
(*     intros; prove_inde. *)
(*   Qed. *)
  
(*   Scheme evalSE_ind' := Minimality for evalSE Sort Prop with *)
(*          evalTup_ind' := Minimality for evalTup Sort Prop. *)
(*   Definition evalSE_ind'' aenv P := evalSE_ind' aenv P (fun senv => List.Forall2 (P senv)). *)
  
(*   Inductive has_type_val : SVal -> Sx.Typ -> Prop := *)
(*   | has_type_bool b : has_type_val (VB b) Sx.TBool *)
(*   | has_type_z n : has_type_val (VZ n) Sx.TZ *)
(*   | has_type_tup vs ts : *)
(*       List.Forall2 (fun v ty => has_type_val v ty) vs ts -> *)
(*       has_type_val (VTup vs) (Sx.TTup ts). *)
  
(*   Lemma type_preservation (se : Sx.SExp) (ty : Sx.Typ) (v : SVal) *)
(*         (sty_env : Env varE (option Sx.Typ) _) *)
(*         (seval_env : Env varE (option SVal) _) : *)
(*     (forall x v ty, seval_env x = Some v -> *)
(*                     sty_env x = Some ty -> *)
(*                     has_type_val v ty) -> *)
(*     (forall x arr ty d, aeval_env x = Some arr -> *)
(*                         aty_env x = Some ty -> *)
(*                         forall i, i < length arr -> has_type_val (nth i arr d) ty) -> *)
(*     has_type aty_env sty_env se ty -> *)
(*     evalSE aeval_env seval_env se v -> *)
(*     has_type_val v ty. *)
(*   Proof. *)
(*     Hint Constructors has_type_val. *)
(*     intros Hsctx Hactx Hty Heval; revert sty_env ty Hsctx Hactx Hty. *)
(*     pattern seval_env, se, v. *)
(*     applys (>>evalSE_ind'' aeval_env seval_env Heval); intros; simpl; [hnf|..]; intros; *)
(*       try lazymatch goal with *)
(*           [ H : has_type _ _ _ _ |- _] => inverts H *)
(*       end; eauto. *)
(*     - forwards*: H0; forwards*: H2. *)
(*       { intros; unfold upd_opt in H4, H5; case_if; inverts H4; inverts H5; eauto. } *)
(*     - forwards*: H0; forwards*: H2. *)
(*       destruct op; simpl in *; destruct v1, v2, ty1, ty2; *)
(*         inverts H3; inverts H12; eauto; *)
(*           case_if; inverts H6; eauto. *)
(*     - applys* Hactx. *)
(*       zify; rewrite Z2Nat.id; eauto. *)
(*     - forwards* Htup: H0; inverts Htup. *)
(*       Lemma Forall2_nth (A B : Type) i (xs : list A) (ys : list B) P dx dy : *)
(*         i < length xs ->  *)
(*         Forall2 P xs ys -> *)
(*         P (nth i xs dx) (nth i ys dy). *)
(*       Proof. *)
(*         intros; revert i H;induction H0. *)
(*         - intros; simpl in *; omega. *)
(*         - intros; simpl; destruct i; eauto. *)
(*           apply IHForall2; simpl in *; omega. *)
(*       Qed. *)
(*       Lemma Forall2_length (A B : Type) (xs : list A) (ys : list B) P : *)
(*         Forall2 P xs ys -> length xs = length ys. *)
(*       Proof. *)
(*         induction 1; simpl in *; congruence. *)
(*       Qed. *)
(*       forwards*: (>>Forall2_length H4). *)
(*       applys* (>>Forall2_nth (VZ 0) Sx.TZ); try omega. *)
(*     - constructor. *)
(*       revert tys H5; induction H0; intros. *)
(*       + inverts H5; eauto. *)
(*       + inverts H5. *)
(*         constructor; eauto. *)
(*         apply IHForall2; eauto. *)
(*         inverts* H. *)
(*   Qed. *)

(*   Scheme has_type_ind' := Minimality for evalSE Sort Prop with *)
(*          has_type_es_ind' := Minimality for evalTup Sort Prop. *)

(*   Definition has_type_ind'' aenv P := has_type_ind' aenv P (fun senv => Forall2 (P senv)). *)

(*   Lemma compile_preserve (se : Sx.SExp)  *)
(*         (sty_env : Env varE (option Sx.Typ) _) *)
(*         (svar_env : Env varE (list var) _) (n m : nat) *)
(*         c es ty : *)
(*     (forall x ty, sty_env x = Some ty -> *)
(*                   length (svar_env x) = len_of_ty ty) -> *)
(*     (forall x ty, aty_env x = Some ty -> *)
(*                   length (snd (avar_env x)) = len_of_ty ty) -> *)
(*     has_type aty_env sty_env se ty -> *)
(*     compile_sexp avar_env se svar_env n =  (inl (c, es), m) -> *)
(*     length es = len_of_ty ty. *)
(*   Proof. *)
(*     intros Hsctx Hactx Htyp; *)
(*       revert svar_env sty_env n m c es ty Htyp Hsctx. *)
(*     induction se using Sx.SExp_ind'; simpl; introv Htyp Hsctx Hsucc. *)
(*     - inverts Hsucc; inverts Htyp. *)
(*       simplify; eauto. *)
(*     - inverts Hsucc; inverts* Htyp. *)
(*     - Ltac unfoldM' := unfold get, set, ret in *; simpl in *; unfold bind_opt in *. *)
(*       unfoldM'. *)
(*       destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc]. *)
(*       destruct (freshes (length es1) _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hsucc]. *)
(*       destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hsucc]. *)
(*       inverts Htyp as Htyp1 Htyp2. *)
(*       forwards*: IHse1; forwards*: IHse2. *)
(*       { intros; unfold upd_opt,  upd in *; case_if*. *)
(*         forwards*: freshes_len; inverts H0; congruence. } *)
(*       inverts* Hsucc. *)
(*     - unfoldM'. *)
(*       destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc]. *)
(*       destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hsucc]. *)
(*       inverts Htyp as Htyp1 Htyp2 Hop. *)
(*       destruct op, ty1, ty2, es1 as [|? [| ? ?]], es2 as [|? [| ? ?]]; *)
(*         inverts Hsucc; simpl in *; try congruence; eauto; simpl in *; try case_if; inverts* Hop. *)
(*     - unfoldM'. *)
(*       destruct (compile_sexp _ se _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc]. *)
(*       destruct (avar_env x) as [? aname] eqn:Heq'. *)
(*       destruct (freshes _ _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hsucc]. *)
(*       destruct es1 as [|i [|? ?]]; inverts Hsucc. *)
(*       inverts Htyp as Htyp Havar. *)
(*       simplify. *)
(*       rewrites* (>>freshes_len Hfeq1). *)
(*       forwards*: Hactx. *)
(*       rewrite Heq' in H; eauto. *)
(*     - destruct (avar_env x) eqn:Heq; simpl in *. *)
(*       inverts Hsucc. *)
(*       inverts Htyp; simpl; auto. *)
(*     - unfoldM'. *)
(*       Lemma typ_of_sexp_ok sty_env se ty : *)
(*         has_type aty_env sty_env se ty -> *)
(*         Sx.typ_of_sexp se = ty. *)
(*       Proof. *)
(*         induction 1; simpl; eauto. *)
(*       Qed. *)
(*       inverts Htyp as Htyp Hidx. *)
(*       rewrites* (>>typ_of_sexp_ok Htyp) in Hsucc. *)
(*       destruct (compile_sexp _ se _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc]. *)
(*       destruct le_dec; inverts Hsucc. *)
(*       forwards* Hlen: IHse. *)
(*       rewrite firstn_length, skipn_length. *)
(*       unfold len_at_i in *; rewrite Hlen; simpl. *)
(*       rewrite Nat.min_l; omega. *)
(*     - revert c es0 n m ty ty0 Htyp Hsucc; induction H; introv Htyp Hsucc; inverts Htyp as Htyp. *)
(*       + inverts Hsucc; inverts Htyp; auto. *)
(*       + inverts Htyp as Hty Htys. *)
(*         unfoldM'. *)
(*         destruct (compile_sexp _ x _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc]. *)
(*         lazymatch type of Hsucc with *)
(*         | context [let (_, _) := ?X in _]  => *)
(*           destruct X as [[(cs2 & es2) | ?] n''] eqn:Hceq2; [|inversion Hsucc] *)
(*         end. *)
(*         inverts Hsucc. *)
(*         forwards* : (>>IHForall (Sx.TTup tys0) (Sx.TTup tys0)). *)
(*         { constructor; eauto. } *)
(*         forwards*: H. *)
(*         simpl in *; rewrite app_length; congruence. *)
(*     - unfoldM'. *)
(*       destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsucc]. *)
(*       destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n''] eqn:Hceq2; [|inversion Hsucc].  *)
(*       destruct (compile_sexp _ se3 _ _) as [[(cs3 & es3) | ?] n'''] eqn:Hceq3; [|inversion Hsucc].  *)
(*       destruct (freshes (length es2) _) as [[fvs1 | ?] n''''] eqn:Hfeq1; [|inversion Hsucc]. *)
(*       destruct es1 as [|? [|? ?]]; simpl in *; inverts Hsucc. *)
(*       forwards*: freshes_len; simplify. *)
(*       rewrites H. *)
(*       inverts Htyp. *)
(*       forwards*: IHse2. *)
(*   Qed. *)
  
(*   Lemma has_type_val_len v ty : *)
(*     has_type_val v ty -> *)
(*     length (vs_of_sval v) = len_of_ty ty. *)
(*   Proof. *)
(*     revert v; induction ty using Sx.STyp_rect'; try now (intros v H; inverts H; simpl; eauto). *)
(*     introv Htyp; inverts Htyp as Htyp. *)
(*     revert vs Htyp; induction X; introv Htyp. *)
(*     - inverts* Htyp. *)
(*     - inverts Htyp; simpl in *. *)
(*       forwards*: IHX; forwards*: p. *)
(*       rewrite app_length; congruence. *)
(*   Qed. *)

(*   Instance se_eqset_proper e1 e2 stk : Proper (SE.Equal ==> equiv_sep stk) (assn_of_svs e1 e2). *)
(*   Proof. *)
(*     intros s1 s2 Heq; apply SE.eqset_equiv; auto. *)
(*   Qed. *)
(*   Instance sa_eqset_proper stk : Proper (SA.Equal ==> equiv_sep stk) (assn_of_avs). *)
(*   Proof. *)
(*     intros s1 s2 Heq; apply SA.eqset_equiv; auto. *)
(*   Qed. *)

(*       (* fix compile_sexps (es : list Sx.SExp) (env : Env varE (list var) eq_varE) :  *) *)
(*       (*  M (cmd * list exp) := *) *)
(*       (*  match es with *) *)
(*       (*  | Datatypes.nil => ret (SKIP, Datatypes.nil) *) *)
(*       (*  | e :: es0 => *) *)
(*       (*    fun n0 : nat => *) *)
(*       (*      let (s, n1) := compile_sexp avar_env e env n0 in *) *)
(*       (*      match s with *) *)
(*       (*      | inl v => *) *)
(*       (*        (let (c, ge) := v in *) *)
(*       (*         fun n2 : nat => *) *)
(*       (*           let (s0, n3) := compile_sexps es0 env n2 in *) *)
(*       (*           match s0 with *) *)
(*       (*           | inl v0 => (let (c', ges) := v0 in ret (c;; c', ge ++ ges)) n3 *) *)
(*       (*           | inr msg => (inr msg, n3) *) *)
(*       (*           end) n1 *) *)
(*       (*      | inr msg => (inr msg, n1) *) *)
(*       (*      end *) *)
(*       (*  end *) *)

(*   Lemma compile_sexps_don't_decrease svar_env cs2 es2 n' m l: *)
(*     (fix compile_sexps (es0 : list Sx.SExp) (env0 : Env varE (list var) eq_varE) {struct es0} :  *)
(*           M (cmd * list exp) := *)
(*             match es0 with *)
(*             | Datatypes.nil => ret (SKIP, Datatypes.nil) *)
(*             | e :: es1 => *)
(*                 compile_sexp avar_env e env0 >>= *)
(*                 (fun ces : cmd * list exp => *)
(*                  let (c, ge) := ces in *)
(*                  compile_sexps es1 env0 >>= (fun ces' : cmd * list exp => let (c', ges) := ces' in ret (c;; c', ge ++ ges))) *)
(*             end) l svar_env n' = (inl (cs2, es2), m) -> *)
(*     n' <= m. *)
(*   Proof. *)
(*     revert cs2 es2 n' m; induction l; simpl; introv Hsuc. *)
(*     - inverts Hsuc; eauto. *)
(*     - unfoldM. *)
(*       destruct (compile_sexp _ _ _ _) as [[(cs1 & es1) | ?]  n''] eqn:Hceq1; [|inversion Hsuc]. *)
(*       lazymatch type of Hsuc with *)
(*       | context [let (_, _) := ?X in _]  => *)
(*         destruct X as [[(? & ?) | ?] ?] eqn:Hceq2; [|inversion Hsuc] *)
(*       end. *)
(*       forwards*: IHl. *)
(*       forwards*: compile_don't_decrease. *)
(*       inverts Hsuc. *)
(*       omega. *)
(*   Qed. *)

(*   Lemma compile_wr_vars (se : Sx.SExp) *)
(*         (svar_env : Env varE (list var) _) (n m : nat) c es : *)
(*     compile_sexp avar_env se svar_env n =  (inl (c, es), m) -> *)
(*     (forall x, In x (writes_var c) ->  *)
(*        exists k l, (Var (str_of_pnat k l)) = x /\ n <= k < m). *)
(*   Proof. *)
(*     Lemma id_mark A (x : A) : *)
(*       x = id x. eauto. Qed. *)
(*     Ltac t := do 2 eexists; splits*; omega. *)
(*     Ltac fwd H := first [forwards* (? & ? & ? & ?): H | forwards* (? & ? & ?): H ]. *)
(*     revert n m svar_env c es; induction se using Sx.SExp_ind'; simpl; *)
(*       intros n m svar_env c es' Hsuc; eauto; try inverts Hsuc as Hsuc; *)
(*     eauto; unfoldM'; *)
(*           (repeat lazymatch type of Hsuc with *)
(*              | context [compile_sexp ?X ?Y ?Z ?n] => destruct (compile_sexp X Y Z n) as [[(? & ?) | ?] ?] eqn:? *)
(*              | context [freshes ?X ?Y] => destruct (freshes X Y) as ([? | ?] & ?) eqn:? *)
(*              end);  *)
(*     (repeat lazymatch goal with [H : context [match ?E with | _ => _ end]|- _] => destruct E eqn:? end); *)
(*     (try inverts Hsuc); simpl; *)
(*       introv; try rewrite !in_app_iff; intros; *)
(*         repeat lazymatch goal with *)
(*         | [H : False |- _] => destruct H *)
(*         | [H : _ \/ _ |- _] => destruct H *)
(*         end; *)
(*     repeat lazymatch goal with *)
(*       | [H : compile_sexp ?A ?B ?C ?D = ?E |- _] => *)
(*           forwards*: (>>compile_don't_decrease H); *)
(*             rewrite (id_mark _ (compile_sexp A B C D = E)) in H *)
(*       | [H : freshes ?A ?B = ?C |- _] => *)
(*         forwards*: (>>freshes_incr H); *)
(*             rewrite (id_mark _ (freshes A B = C)) in H *)
(*       end; unfold id in *. *)
(*     - forwards* (? & ? & ? & ?): (>>IHse1 H); t. *)
(*     - rewrite read_tup_writes in *; [|forwards*: (>>freshes_len Heqp0)]. *)
(*       forwards* (? & ? & ?): freshes_vars; t. *)
(*     - forwards* (? & ? & ? & ?): (>>IHse2 Heqp1). t. *)
(*     - forwards* (? & ? & ? & ?): (>>IHse1 Heqp). t. *)
(*     - forwards* (? & ? & ? & ?): (>>IHse2 Heqp0). t. *)
(*     - destruct op; simpl in *; inverts Heqp1; substs; simpl in *; destruct H. *)
(*     - forwards* (? & ? & ? & ?): (>>IHse Heqp). t. *)
(*     - rewrite gen_read_writes in *; [|simplify; forwards*: (>>freshes_len Heqp1)]. *)
(*       forwards* (? & ? & ?): freshes_vars; t. *)
(*     - revert n c es' H1 H0; induction H; *)
(*       introv Hsuc Hin; [inverts Hsuc; simpl in *|]. *)
(*       + destruct Hin. *)
(*       + unfold ">>=" in *. *)
(*         destruct (compile_sexp _ x0 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hsuc]. *)
(*         lazymatch type of Hsuc with *)
(*         | context [let (_, _) := ?X in _]  => *)
(*           destruct X as [[(cs2 & es2) | ?] n''] eqn:Hceq2; [|inversion Hsuc] *)
(*         end. *)
(*         inverts Hsuc. *)
(*         forwards*: compile_sexps_don't_decrease. *)
(*         simpl in Hin; rewrite in_app_iff in *. *)
(*         destruct Hin as [Hin | Hin]. *)
(*         * forwards* (? & ? & ? & ?): H. *)
(*           t. *)
(*         * forwards* (? & ? & ? & ?): IHForall; substs. *)
(*           forwards*: compile_don't_decrease. *)
(*           t. *)
(*     - substs. *)
(*       forwards* (? & ? & ? & ?): (>>IHse1 Heqp). t. *)
(*     - forwards* (? & ? & ? & ?): (>>IHse2 Heqp0). t. *)
(*     - rewrite S.read_tup_writes in *; [|forwards*: freshes_len]. *)
(*       forwards* (? & ? & ?) : freshes_vars. *)
(*       t. *)
(*     - forwards* (? & ? & ? & ?): (>>IHse3). *)
(*       t. *)
(*     - Lemma read_tup_writes' (vs : list var) (es : list exp) : *)
(*         forall x,  In x (writes_var (read_tup vs es)) -> In x vs. *)
(*       Proof. *)
(*         revert es; induction vs; simpl in *; introv; eauto. *)
(*         destruct es; simpl. *)
(*         - destruct 1. *)
(*         - simpl in *; intros [? | ?]; eauto. *)
(*       Qed. *)
(*       apply read_tup_writes' in H. *)
(*       forwards* (? & ? & ?) : freshes_vars; t. *)
(*   Qed. *)

(*   Lemma compile_sexps_wr_vars svar_env cs es n m l: *)
(*     (fix compile_sexps (es0 : list Sx.SExp) (env0 : Env varE (list var) eq_varE) {struct es0} :  *)
(*        M (cmd * list exp) := *)
(*        match es0 with *)
(*        | Datatypes.nil => ret (SKIP, Datatypes.nil) *)
(*        | e :: es1 => *)
(*          compile_sexp avar_env e env0 >>= *)
(*                 (fun ces : cmd * list exp => *)
(*                  let (c, ge) := ces in *)
(*                  compile_sexps es1 env0 >>= (fun ces' : cmd * list exp => let (c', ges) := ces' in ret (c;; c', ge ++ ges))) *)
(*             end) l svar_env n  = (inl (cs, es), m) -> *)
(*     (forall x, In x (writes_var cs) ->  *)
(*        exists k l, (Var (str_of_pnat k l)) = x /\ n <= k < m). *)
(*   Proof. *)
(*     revert cs es n m; induction l; simpl; introv Hsuc. *)
(*     - unfoldM; inverts Hsuc; simpl; eauto. *)
(*       destruct 1. *)
(*     - unfoldM; destruct (compile_sexp _ _ _ _) as [[(cs1 & es1) | ?]  n''] eqn:Hceq1; [|inversion Hsuc]. *)
(*       lazymatch type of Hsuc with *)
(*       | context [let (_, _) := ?X in _]  => *)
(*         destruct X as [[(? & ?) | ?] ?] eqn:Hceq2; [|inversion Hsuc] *)
(*       end. *)
(*       inverts Hsuc; simpl; introv; rewrite in_app_iff; intros [? | ?]. *)
(*       forwards*: compile_sexps_don't_decrease. *)
(*       forwards* (? & ? & ? & ?) : (compile_wr_vars). t. *)
(*       forwards*: compile_don't_decrease. *)
(*       forwards* (? & ? & ? & ?) : (IHl). t. *)
(*   Qed. *)
  
(*   Lemma freshes_disjoint d n m xs : *)
(*     freshes d n = (inl xs, m) -> *)
(*     disjoint_list xs. *)
(*   Proof. *)
(*     revert n m xs; induction d; simpl; introv. *)
(*     - intros H; inverts H; simpl; eauto. *)
(*     - unfoldM. *)
(*       intros H; inverts H; simpl. *)
(*       split; eauto. *)
(*       intros Hin; clear IHd. *)
(*       assert (forall k, In (Var (str_of_pnat n k)) ((fix f (dim n : nat) := *)
(*                                                        match dim with *)
(*                                                        | 0 => nil *)
(*                                                        | S d => Var (str_of_pnat n d) :: f d n *)
(*                                                        end) d n) -> *)
(*                         k < d). *)
(*       { clear Hin; induction d; simpl. *)
(*         - destruct 1. *)
(*         - intros k [H1 | H2]. *)
(*           + lets* [? ?]: (>>var_pnat_inj H1); omega. *)
(*           + forwards*: IHd. } *)
(*       forwards*: H; omega. *)
(*   Qed. *)

(*   Create HintDb setop. *)
(*   Hint Rewrite SE.add_spec SE.union_spec SE.remove_spec SE.diff_spec *)
(*        SA.add_spec SA.union_spec SA.remove_spec SA.diff_spec : setop. *)
  
(*   Lemma compile_ok (se : Sx.SExp) *)
(*         (sty_env : Env varE (option Sx.Typ) _) *)
(*         (seval_env : Env varE (option SVal) _) *)
(*         (svar_env : Env varE (list var) _) (n m : nat) ty *)
(*         (sv : SVal) c es : *)
(*     has_type aty_env sty_env se ty -> *)
(*     evalSE aeval_env seval_env se sv -> *)
(*     compile_sexp avar_env se svar_env n =  (inl (c, es), m) -> *)
(*     (forall x ty, sty_env x = Some ty -> length (svar_env x) = len_of_ty ty) -> *)
(*     (forall x ty, aty_env x = Some ty -> length (snd (avar_env x)) = len_of_ty ty) -> *)
(*     (forall (x0 : varE) (v : SVal) (ty : Sx.Typ), seval_env x0 = Some v -> sty_env x0 = Some ty -> has_type_val v ty) -> *)
(*     (forall (x : varA) (arr : array) (ty0 : Sx.Typ) (d : SVal), *)
(*         aeval_env x = Some arr -> aty_env x = Some ty0 -> *)
(*         forall i : nat, i < length arr -> has_type_val (nth i arr d) ty0) -> *)
(*     (forall x, SE.In x (free_sv se) ->  *)
(*        forall k l, In (Var (str_of_pnat k l)) (svar_env x) -> k < n) -> (* fvs are not in the future generated vars *) *)
(*     (* fvs are not in the future generated vars *) *)
(*     (forall x y, SA.In x (free_av se) -> In y (snd (avar_env x)) -> prefix "l" (S.var_of_str y) = false) -> *)
(*     (forall x, SA.In x (free_av se) -> prefix "l" (S.var_of_str (fst (avar_env x))) = false) -> *)
(*     (forall e k l , In e es -> In (Var (str_of_pnat k l)) (fv_E e) -> k < m) /\ (* (iii) return exps. don't have future generated vars*) *)
(*     CSL BS tid  (* (iii) correctness of gen. code *) *)
(*         (!(assn_of_svs seval_env svar_env (free_sv se)) ** *)
(*           (assn_of_avs (free_av se))) *)
(*         c *)
(*         (!(assn_of_svs seval_env svar_env (free_sv se)) ** *)
(*           (assn_of_avs (free_av se)) ** !(es ==t vs_of_sval sv)). *)
(*   Proof. *)
(*     revert se ty sty_env seval_env svar_env n m sv c es. *)
(*     induction se using Sx.SExp_ind'; simpl; *)
(*     introv Htyp Heval Hcompile Hsvctx Havctx Hsectx Haectx Hsvar Havar1 Havar2. *)
(*     - unfold ret in Hcompile; inversion Hcompile; substs. *)
(*       inversion Heval; substs; simpl in *. *)
(*       splits; (try now destruct 1); eauto. *)
(*       { simplify; forwards*: Hsvar; rewrite SE.singleton_spec; auto. } *)
(*       { eapply Hforward; eauto using rule_skip. *)
(*         intros; sep_split; sep_split_in H; repeat sep_cancel. *)
(*         simpl_avs in HP. *)
(*         destruct (seval_env x); sep_split_in H; sep_split; eauto. *)
(*         + inverts H3; sep_normal_in HP; sep_split_in HP; eauto. *)
(*         + destruct HP. } *)
(*     - inversion Hcompile; substs. *)
(*       splits; (try now destruct 1); eauto. *)
(*       { simplify; destruct H. } *)
(*       { eapply Hforward; [apply rule_skip|]. *)
(*         intros; sep_split; sep_split_in H; eauto. *)
(*         inversion Heval; substs. *)
(*         simpl; sep_split; eauto using emp_emp_ph; unfold_conn; simpl; auto. } *)
(*     - unfold bind_opt in Hcompile. *)
(*       (* getting compilation/evaluation/typing results of sub-expressions *) *)
(*       destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile]. *)
(*       destruct (freshes (length es1) _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hcompile]. *)
(*       destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hcompile]. *)
(*       inverts Hcompile; substs. *)
      
(*       inverts Heval as Heval1 Heval2; substs. *)
(*       inverts Htyp as Htyp1 Htyp2. *)
      
(*       (* obtaining induction hypothesis1 *) *)
(*       forwards* (Hres1 & Htri1): IHse1; [..|clear IHse1]. *)
(*       { intros; eapply Hsvar; eauto; rewrite SE.union_spec; eauto. } *)
(*       { intros; applys* Havar1; rewrite SA.union_spec; eauto. } *)
(*       { intros; applys* Havar2; rewrite SA.union_spec; eauto. } *)

(*       (* freshness of generated variables *) *)
(*       forwards* : (>>freshes_incr Hfeq1); substs. *)

(*       (* obtaining induction hypothesis 2 *) *)
(*       forwards* (Hres2 & Htri2): IHse2; [..|clear IHse2]. *)
(*       { unfold upd_opt, upd; intros; case_if*. *)
(*         rewrites* (>>freshes_len Hfeq1). *)
(*         inverts H; forwards*: compile_preserve. } *)
(*       { unfold upd_opt, upd; intros; case_if*. *)
(*         inverts H; inverts H0. *)
(*         forwards*: type_preservation. } *)
(*       { intros y Hyin k l Hin; unfold upd in Hin. *)
(*         destruct (eq_dec x y); substs. *)
(*         forwards* (? & ? & ?): (>>freshes_vars). *)
(*         forwards* (? & ?): (>>var_pnat_inj H); substs. *)
(*         omega. *)
(*         forwards*: Hsvar; [rewrite SE.union_spec, SE.remove_spec; eauto|]. *)
(*         forwards*:(>>compile_don't_decrease Hceq1); omega. } *)
(*       { intros; applys* Havar1; rewrite SA.union_spec; eauto. } *)
(*       { intros; applys* Havar2; rewrite SA.union_spec; eauto. } *)
      
(*       (* prove goals *) *)
(*       splits; try omega. *)

(*       assert (Hlfvs : length fvs1 = length es1). *)
(*       { forwards*: freshes_len. } *)

(*       (* return variables do not conflict with variables generated later *) *)
(*       { simplify; forwards*: Hres2; eauto. } *)
      
(*       lets* Hwr1: (>>compile_wr_vars Hceq1). *)
(*       lets* Hwr2: (>>compile_wr_vars Hceq2). *)
(*       lets* Hfvs: (>>freshes_vars Hfeq1). *)

(*       (* 1st commands *) *)
(*       eapply Hbackward. *)
(*       Focus 2. { *)
(*         intros. *)
(*         unfold assn_of_svs in H; sep_rewrite_in SE.union_assns H; sep_rewrite_in pure_star H. *)
(*         unfold assn_of_avs in H; sep_rewrite_in SA.union_assns H. *)
(*         rewrite !fold_assn_svs, !fold_assn_avs in H. *)
        
(*         sep_normal_in H. *)
(*         assert (((!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) ** *)
(*                  (!(assn_of_svs seval_env svar_env (SE.SE.diff (SE.remove x (free_sv se2)) (free_sv se1))) ** *)
(*                  assn_of_avs (SA.SE.diff (free_av se2) (free_av se1)))) s h). *)
(*         { sep_normal; repeat sep_cancel. } *)
(*         exact H0. } Unfocus. *)
(*       eapply rule_seq; [eapply rule_frame|]. *)
(*       apply Htri1. *)
(*       (* side-condition of frame rule *) *)
(*       { Ltac des  := *)
(*           repeat match goal with *)
(*           | [H : _ /\ _  |- _] => destruct H as [? ?] *)
(*           end. *)
(*         prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs]; *)
(*           introv; repeat autorewrite with setop; *)
(*           intros ? ? ?; forwards* (? & ? & ?): Hwr1; des; substs*. *)
(*         - forwards*: Hsvar; [autorewrite with setop; eauto|..]. *)
(*           omega. *)
(*         - forwards*: Havar1; [autorewrite with setop; eauto|].  *)
(*           simpl in *; rewrite S.prefix_nil in *; congruence. *)
(*         - forwards*: Havar2; [autorewrite with setop; eauto|]. *)
(*           rewrite <-H2 in *. *)
(*           simpl in *; rewrite S.prefix_nil in *; congruence. } *)

(*       (* assignment to generated variables *) *)
(*       eapply rule_seq. *)
(*       eapply Hbackward. *)
(*       Focus 2. *)
(*       { intros; sep_normal_in H. *)
(*         assert ((!(es1 ==t vs_of_sval v1) ** *)
(*                  !(assn_of_svs seval_env svar_env (free_sv se1)) ** *)
(*                  assn_of_avs (free_av se1) ** *)
(*                  !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.remove x (free_sv se2)) (free_sv se1))) ** *)
(*                  assn_of_avs (SA.SE.diff (free_av se2) (free_av se1))) s h). *)
(*         { repeat sep_cancel. } *)
(*         apply H0. } Unfocus. *)
(*       eapply rule_frame; [applys* read_tup_correct|]. *)
(*       (* side-conditions of the assignment *) *)
(*       { intros. *)
(*         forwards* (? & ? & ?): Hfvs; substs. *)
(*         intros Hc; forwards*: Hres1; try omega. } *)
(*       { forwards*: freshes_disjoint. } *)
(*       { forwards*: (compile_preserve se1). *)
(*         forwards*: (type_preservation se1). *)
(*         rewrites* (>>has_type_val_len). } *)
(*       { rewrites* (>>freshes_len). } *)
(*       { rewrite S.read_tup_writes; [|rewrites* (>>freshes_len)]. *)
(*         prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs]; *)
(*           introv; repeat autorewrite with setop; *)
(*              intros ? ? ?; forwards* (? & ? & ?): Hfvs; des; substs. *)
(*         - forwards*: Hsvar; [repeat autorewrite with setop; eauto|]. *)
(*           forwards*: (>>compile_don't_decrease Hceq1); omega. *)
(*         - forwards*: Havar1; [repeat autorewrite with setop; eauto|]. *)
(*           simpl in *; rewrite S.prefix_nil in *; congruence. *)
(*         - forwards*: Havar2; [repeat autorewrite with setop; eauto|]. *)
(*           rewrite H2 in *. *)
(*           simpl in *; rewrite S.prefix_nil in *; congruence. *)
(*         - forwards*: Hsvar; [repeat autorewrite with setop; jauto|]. *)
(*           forwards*: (>>compile_don't_decrease Hceq1); omega. *)
(*         - forwards*: Havar1; [repeat autorewrite with setop; jauto|]. *)
(*           simpl in *; rewrite S.prefix_nil in *; congruence. *)
(*         - forwards*: Havar2; [repeat autorewrite with setop; jauto|]. *)
(*           rewrite H2 in *. *)
(*           rewrite <-H1 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
      
(*       eapply Hbackward. *)
(*       Focus 2. { *)
(*         intros s h H; sep_normal_in H. *)
(*         assert ((!(vars2es fvs1 ==t vs_of_sval v1) ** *)
(*                  !(assn_of_svs seval_env svar_env (free_sv (Sx.ELet x se1 se2 ty0))) ** *)
(*                  assn_of_avs (free_av (Sx.ELet x se1 se2 ty0))) s h). *)
(*         { simpl. *)
(*           unfold assn_of_svs; sep_rewrite SE.union_assns; sep_rewrite pure_star. *)
(*           unfold assn_of_avs; sep_rewrite SA.union_assns. *)
(*           rewrite !fold_assn_svs, !fold_assn_avs. *)
(*           sep_normal; repeat sep_cancel. } *)
(*         simpl in H0. *)

(*         sep_rewrite_in SE.union_comm H0. *)
(*         sep_rewrite_in SA.union_comm H0. *)
(*         unfold assn_of_svs in H0; sep_rewrite_in SE.union_assns H0. *)
(*         unfold assn_of_avs in H0; sep_rewrite_in SA.union_assns H0. *)
(*         rewrite !fold_assn_svs, !fold_assn_avs in H0. *)
(*         assert (((!(assn_of_svs (upd_opt seval_env x v1) (upd svar_env x fvs1) (free_sv se2)) ** *)
(*                   assn_of_avs (free_av se2)) ** *)
(*                  (!(assn_of_svs seval_env svar_env (SE.SE.diff (free_sv se1) (SE.remove x (free_sv se2)))) ** *)
(*                   assn_of_avs (SA.SE.diff (free_av se1) (free_av se2)))) s h). *)
(*         { sep_normal; repeat sep_cancel. *)
(*           sep_lift 2; sep_cancel. *)
(*           sep_rewrite_in pure_star H2. *)
(*           sep_lift 1; sep_cancel. *)
(*           destruct (SE.in_dec (free_sv se2) x). *)
(*           - sep_rewrite (SE.choose_remove _ _ i). *)
(*             unfold assn_of_svs. *)
(*             sep_rewrite SE.add_equiv; [|autorewrite with setop; intros [Hc Hc']; congruence]. *)
(*             unfold upd, upd_opt; destruct eq_dec; [|congruence]. *)
(*             sep_rewrite pure_star; sep_rewrite pure_pure. *)
(*             sep_cancel. *)
(*             sep_rewrite SE.assn_of_vs_eq; *)
(*               [unfold assn_of_svs in *; eauto | introv; autorewrite with setop; *)
(*                                                 intros [? ?]; try destruct eq_dec; try congruence..]. *)
(*           - sep_rewrite (SE.remove_id (free_sv se2) x); eauto. *)
(*             unfold assn_of_svs in *; sep_rewrite SE.assn_of_vs_eq; *)
(*               [ sep_split_in H3; sep_split; eauto | *)
(*                 introv; autorewrite with setop; *)
(*                 unfold upd, upd_opt; case_if; intros [? ?]; eauto; congruence..]. } *)
(*         exact H1. } Unfocus. *)
(*       eapply Hforward; [eapply rule_frame; [apply Htri2|]| ]. *)
(*       + prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs]; *)
(*           introv; repeat autorewrite with setop; intros ? ? ?; simplify; *)
(*             forwards* (? & ? & ? & ?): Hwr2; des; substs. *)
(*         * forwards*: Hsvar; autorewrite with setop; eauto. *)
(*           forwards*: (>>compile_don't_decrease se1); omega. *)
(*         * forwards*: Havar1; autorewrite with setop; eauto. *)
(*           simpl in *; rewrite prefix_nil in *; congruence. *)
(*         * forwards*: Havar2; autorewrite with setop; eauto. *)
(*           rewrite <-H2 in *; simpl in *; rewrite prefix_nil in *; congruence. *)
(*       + intros s h H; simpl. *)
(*         sep_rewrite SE.union_comm; sep_rewrite SA.union_comm. *)
(*         unfold assn_of_svs, assn_of_avs. *)
(*         sep_rewrite SE.union_assns; sep_rewrite pure_star;  *)
(*           sep_rewrite SA.union_assns; sep_normal. *)
(*         rewrite !fold_assn_svs, !fold_assn_avs. *)
(*         repeat sep_cancel. *)
(*         apply scC; sep_cancel. *)
(*         destruct (SE.in_dec (free_sv se2) x). *)
(*         * sep_rewrite_in (SE.choose_remove _ _ i) H3. *)
(*           unfold assn_of_svs in H3. *)
(*           sep_rewrite_in SE.add_equiv H3; [|autorewrite with setop; intros [Hc Hc']; congruence]. *)
(*           unfold upd, upd_opt in H3; destruct (eq_dec x x); [|congruence]. *)
(*           sep_rewrite_in pure_star H3; sep_split_in H3. *)
(*           sep_split; unfold assn_of_svs; eauto. *)
(*           sep_rewrite SE.assn_of_vs_eq; *)
(*               [unfold assn_of_svs in *; eauto | introv; autorewrite with setop; *)
(*                                                 intros [? ?]; try destruct eq_dec; try congruence..]. *)
(*         * sep_rewrite_in (SE.remove_id _ _ n0) H3. *)
(*           unfold assn_of_svs in *; *)
(*           sep_rewrite SE.assn_of_vs_eq; eauto; *)
(*           introv; autorewrite with setop; intros [? ?]; unfold upd, upd_opt; *)
(*             destruct eq_dec; substs; eauto; congruence. *)
(*     - unfoldM'. *)
(*       destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile]. *)
(*       destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n'''] eqn:Hceq2; [|inversion Hcompile]. *)
(*       destruct es1 as [|e1 [|? ?]]; try now inverts Hcompile. *)
(*       destruct es2 as [|e2 [|? ?]]; inverts Hcompile. *)

(*       inverts Heval as Heval1 Heval2; substs. *)
(*       inverts Htyp as Htyp1 Htyp2; substs. *)
(*       forwards* (Hres1 & Htri1): IHse1. *)
(*       { intros; eapply Hsvar; eauto; autorewrite with setop; eauto. } *)
(*       { intros; applys* Havar1; rewrite SA.union_spec; eauto. } *)
(*       { intros; applys* Havar2; rewrite SA.union_spec; eauto. } *)
(*       forwards* ( Hres2 & Htri2): IHse2. *)
(*       { intros; forwards*: Hsvar; eauto; autorewrite with setop; eauto. *)
(*         forwards*: (>>compile_don't_decrease se1); omega. } *)
(*       { intros; applys* Havar1; rewrite SA.union_spec; eauto. } *)
(*       { intros; applys* Havar2; rewrite SA.union_spec; eauto. } *)

(*       splits; try omega. *)
(*       (* { simpl; destruct op; simpl in *; *) *)
(*       (*   [inverts H0; simpl; *) *)
(*       (*    introv; rewrite !in_app_iff; intros [? | [? | []]]; *) *)
(*       (*    [forwards* (? & ? & ? & ?): Hwr1| forwards* (? & ? & ? & ?): Hwr2]; *) *)
(*       (*    do 2 eexists; splits; eauto; try omega; *) *)
(*       (*    [forwards*: (>>compile_don't_decrease Hceq2); omega| *) *)
(*       (*     forwards*: (>>compile_don't_decrease Hceq1); omega]..]. } *) *)
(*       { simpl; destruct op; simpl in *; *)
(*         [inverts H0; simpl; simplify..]; *)
(*         lazymatch goal with *)
(*         | [H : context [In (Var (str_of_pnat _ _)) (fv_E e1)] |- _] => *)
(*           forwards*: Hres1 *)
(*         | [H : context [In (Var (str_of_pnat _ _)) (fv_E e2)] |- _] => *)
(*           forwards*: Hres2 *)
(*         end; *)
(*         first [forwards*: (>>compile_don't_decrease Hceq2); omega | forwards*: (>>compile_don't_decrease Hceq1); omega]. } *)
(*       eapply Hbackward. *)
(*       Focus 2. *)
(*       { unfold assn_of_svs, assn_of_avs; intros; *)
(*         sep_rewrite_in (SE.union_assns) H; sep_rewrite_in (SA.union_assns) H; *)
(*         rewrite !fold_assn_svs, !fold_assn_avs in H; *)
(*         sep_rewrite_in pure_star H; sep_normal_in H. *)
(*         assert (((!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) ** *)
(*                  !(assn_of_svs seval_env svar_env (SE.SE.diff (free_sv se2) (free_sv se1))) ** *)
(*                  assn_of_avs (SA.SE.diff (free_av se2) (free_av se1))) s h). *)
(*         { sep_normal; repeat sep_cancel. } *)
(*         apply H1. } Unfocus. *)
(*       assert (c = (cs1 ;; cs2 ;; fst (compile_op op e1 e2) )); [|substs]. *)
(*       { destruct op; simpl in *; inverts H0; eauto. } *)
(*       eapply rule_seq; [eapply rule_frame; eauto|]. *)
(*       { prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs]; *)
(*         introv; repeat autorewrite with setop; intros ? ? ?; *)
(*           forwards* (? & ? & ? & ?): (>> compile_wr_vars Hceq1); des; substs.  *)
(*         - forwards*: Hsvar; autorewrite with setop; eauto. omega. *)
(*         - forwards*: Havar1; autorewrite with setop; eauto. *)
(*           simpl in *; rewrite prefix_nil in *; congruence. *)
(*         - forwards*: Havar2; autorewrite with setop; eauto. *)
(*           rewrite <-H3 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*       eapply Hbackward. *)
(*       Focus 2. { *)
(*         intros s h H. *)
(*         assert ((!(e1 :: Datatypes.nil ==t vs_of_sval v1) ** *)
(*                  !(assn_of_svs seval_env svar_env (SE.union (free_sv se1) (free_sv se2))) ** *)
(*                  assn_of_avs (SA.union (free_av se1) (free_av se2))) s h). *)
(*         { unfold assn_of_svs, assn_of_avs; *)
(*           sep_rewrite SE.union_assns; sep_rewrite SA.union_assns; *)
(*           sep_rewrite pure_star; sep_normal; sep_normal_in H; *)
(*           rewrite !fold_assn_svs, !fold_assn_avs; repeat sep_cancel. } *)
(*         sep_rewrite_in SE.union_comm H1; sep_rewrite_in SA.union_comm H1; *)
(*           unfold assn_of_svs, assn_of_avs in H1; *)
(*           sep_rewrite_in SE.union_assns H1; sep_rewrite_in SA.union_assns H1; *)
(*             rewrite !fold_assn_svs, !fold_assn_avs in H1. *)
(*         instantiate (1 := *)
(*          (!(assn_of_svs seval_env svar_env (free_sv se2)) ** assn_of_avs (free_av se2)) **  *)
(*          !(e1 :: Datatypes.nil ==t vs_of_sval v1) ** *)
(*          !(assn_of_svs seval_env svar_env (SE.SE.diff (free_sv se1) (free_sv se2))) ** *)
(*          assn_of_avs (SA.SE.diff (free_av se1) (free_av se2))). *)
(*         sep_normal; sep_rewrite_in pure_star H1; sep_normal_in H1; repeat sep_cancel. } Unfocus. *)
(*       eapply rule_seq; [eapply rule_frame; eauto|]. *)
(*       { prove_inde; first [apply inde_assn_of_svs | apply inde_assn_of_avs | apply inde_eq_tup; rewrite Forall_forall]; *)
(*         simpl; introv; repeat autorewrite with setop; intros; simplify; *)
(*         forwards* (? & ? & ? & ?): (>>compile_wr_vars Hceq2); substs. *)
(*         - forwards*: Hres1; omega. *)
(*         - forwards*: Hsvar; autorewrite with setop; jauto. *)
(*           forwards*: (>>compile_don't_decrease se1). omega. *)
(*         - forwards*: Havar1; autorewrite with setop; jauto.  *)
(*           simpl in *; rewrite prefix_nil in *; congruence. *)
(*         - forwards*: Havar2; autorewrite with setop; jauto.  *)
(*           rewrite <-H2 in H4; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*       (* TODO: modular lemma for compile_op *) *)
(*       assert (Heq: fst (compile_op op e1 e2) = Cskip); [|rewrite Heq; clear Heq ]. *)
(*       { unfold compile_op; destruct op; eauto. } *)
(*       eapply Hforward; eauto using rule_skip. *)
(*       intros s h H. *)
(*       sep_rewrite SE.union_comm; sep_rewrite SA.union_comm; *)
(*         unfold assn_of_svs, assn_of_avs; *)
(*         sep_rewrite SE.union_assns; sep_rewrite SA.union_assns. *)
(*       rewrite !fold_assn_svs, !fold_assn_avs; *)
(*         sep_rewrite pure_star; sep_normal; sep_normal_in H; *)
(*           sep_split_in H; sep_split; eauto; sep_cancel. *)
(*       asserts_rewrite (es = snd (compile_op op e1 e2)). *)
(*       { destruct op; simpl in *; inverts* H0. } *)
(*       destruct op, v1, v2; simpl in *; inverts H9; *)
(*         sep_split_in HP0; sep_split_in HP1; unfold_conn_in (HP3, HP4); simpl in *; *)
(*           sep_split; eauto; unfold_conn; simpl; try congruence; *)
(*       rewrite HP3, HP4. *)
(*       destruct (Z.eqb_spec n0 n1); destruct (eq_dec n0 n1); eauto; congruence. *)
(*       destruct (Z.ltb_spec0 n0 n1); destruct (Z_lt_dec n0 n1); eauto; congruence. *)
(*     - unfoldM'. *)
(*       Lemma p2 {A B} (x : A * B) : x = (fst x, snd x). destruct x; auto. Qed. *)
(*       destruct (compile_sexp _ se _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile]. *)
(*       rewrite (p2 (avar_env x)) in *. *)
(*       destruct (freshes (length _) _) as [[fvs1 | ?] n''] eqn:Hfeq1; [|inversion Hcompile]. *)
(*       destruct es1 as [|? [|? ?]]; inverts Hcompile. *)
(*       inverts Htyp as Htyp Hatyp; inverts Heval as Heval Haeval Hle Hgt. *)
(*       forwards* (Hres & Htri): IHse. *)
(*       { intros; applys* Havar1; autorewrite with setop; eauto. } *)
(*       { intros; applys* Havar2; autorewrite with setop; eauto. } *)
(*       assert (Hlenfv : length fvs1 = length (snd (avar_env x))). *)
(*       { forwards*: (>>freshes_len Hfeq1); simplify; rewrite Heq in *; eauto. } *)
(*       splits. *)
(*       (* { introv; simpl; rewrite gen_read_writes. *) *)
(*       (*   2: simplify; eauto. *) *)
(*       (*   rewrite in_app_iff; intros [? | ?]. *) *)
(*       (*   - forwards* (? & ? & ? & ?): Hwr; do 2 eexists; splits*; try omega. *) *)
(*       (*     forwards*: (>>freshes_vars Hfeq1); omega. *) *)
(*       (*   - forwards* (? & Hgenv): (>>freshes_vars Hfeq1). *) *)
(*       (*     forwards* (? & ? & ?): Hgenv. *) *)
(*       (*     do 2 eexists; splits*; try omega. *) *)
(*       (*     forwards*: (>>compile_don't_decrease). } *) *)
(*       { intros; simplify; *)
(*         forwards*: (>>freshes_incr Hfeq1). *)
(*         forwards* (? & ? & ?): (>>freshes_vars Hfeq1). *)
(*         forwards* (? & ?): (>>var_pnat_inj H1); omega. } *)
(*       eapply Hbackward. *)
(*       Focus 2. { *)
(*         intros s h H. *)
(*         unfold assn_of_svs, assn_of_avs in H. *)
(*         Hint Rewrite SE.singleton_spec SA.singleton_spec: setop. *)
(*         Lemma add_union x s : *)
(*           SA.add x s == SA.union (SA.singleton x) s. *)
(*         Proof. *)
(*           simpl; unfold SA.Equal; introv. *)
(*           autorewrite with setop; split; eauto. *)
(*         Qed. *)
(*         sep_rewrite_in add_union H; sep_rewrite_in SA.union_comm H. *)
(*         sep_rewrite_in SA.union_assns H. *)
(*         rewrite !fold_assn_svs, !fold_assn_avs in H. *)
(*         instantiate (1 := *)
(*           (!(assn_of_svs seval_env svar_env (free_sv se)) **  assn_of_avs (free_av se)) ** *)
(*             assn_of_avs (SA.SE.diff (SA.singleton x) (free_av se))). *)
(*         sep_normal; sep_normal_in H; repeat sep_cancel. } Unfocus. *)
(*       eapply rule_seq; [eapply rule_frame; eauto|]. *)
(*       { prove_inde; apply inde_assn_of_avs; unfold not; intros; *)
(*         forwards* (? & ? & ? & ?) : (>>compile_wr_vars Hceq1); substs; *)
(*         intros; [forwards*: Havar1 | forwards*: Havar2]; autorewrite with setop in *; jauto. *)
(*         simpl in *; rewrite prefix_nil in *; congruence. *)
(*         rewrite <-H2 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*       eapply Hbackward. *)
(*       Focus 2. *)
(*       { intros s h H. *)
(*         sep_normal_in H; sep_split_in H; simpl in *. *)
(*         sep_split_in HP0. *)
(*         assert (assn_of_avs (SA.add x (SA.remove x (free_av se))) s h). *)
(*         { Lemma add_remove x s : *)
(*             SA.add x (SA.remove x s) == SA.add x s. *)
(*           Proof. *)
(*             simpl; unfold SA.Equal; introv; autorewrite with setop; split; *)
(*               intros. *)
(*             - destruct H as [? | [? ?]]; eauto. *)
(*             - destruct (eq_dec a x); eauto. *)
(*               destruct H; eauto. *)
(*           Qed. *)
(*           sep_rewrite add_remove; sep_rewrite add_union; sep_rewrite SA.union_comm. *)
(*           unfold assn_of_avs; sep_rewrite SA.union_assns. *)
(*           apply H. } *)
(*         unfold assn_of_avs in H0; *)
(*           sep_rewrite_in SA.add_equiv H0; [|autorewrite with setop; intros [? ?]; congruence]. *)
(*         rewrite Haeval in H0. *)
(*         sep_rewrite_in (is_array_tup_unfold (S.es2gls (S.vars2es (snd (avar_env x)))) (Z.to_nat ix)) H0. *)
(*         Focus 2. { *)
(*           simpl; intros; unfold S.es2gls; simplify. *)
(*           forwards* Htyv: (>> Haectx (VZ 0) i). *)
(*           unfold val in *; rewrites* (>>has_type_val_len Htyv). *)
(*           rewrites* (>>Havctx). } Unfocus. *)
(*         2: zify; rewrite Z2Nat.id; omega. *)
(*         simpl in H0. *)
(*         assert ((Zn (Z.to_nat ix) === e) s (emp_ph loc)). *)
(*         { unfold_conn_in HP1; unfold_conn; simpl in *; rewrite Z2Nat.id; eauto. } *)
(*         sep_rewrite_in S.mps_eq1_tup' H0; [|exact H1]. *)
(*         clear HP0; sep_combine_in H0; sep_normal_in H0. *)
(*         sep_lift_in H0 2. *)
(*         apply H0. } Unfocus. *)
(*       eapply Hforward; [eapply rule_frame; [apply S.gen_read_correct|]; eauto|]. *)
(*       { simpl; intros. *)
(*         forwards* (? & ? & ?): (>>freshes_vars Hfeq1). *)
(*         simplify; eauto. *)
(*         forwards*: Hres; omega. } *)
(*       { unfold not; intros; simplify. *)
(*         forwards* (? & ? & ?): (>>freshes_vars Hfeq1); substs. *)
(*         forwards*: Havar1; autorewrite with setop; eauto. *)
(*         simpl in *; rewrite prefix_nil in *; congruence. } *)
(*       { forwards*: freshes_disjoint. } *)
(*       { simplify; eauto. } *)
(*       { simpl; intros; unfold S.es2gls; simplify. *)
(*         forwards* Htyv: (>> Haectx (VZ 0) (Z.to_nat ix)). *)
(*         zify; rewrite Z2Nat.id; omega. *)
(*         unfold val in *; rewrites* (>>has_type_val_len Htyv). *)
(*         unfold val in *; forwards*: Havctx. *)
(*         congruence. } *)
(*       { rewrites* S.gen_read_writes; [|simplify; eauto]. *)
(*         unfold S.es2gls. *)
(*         prove_inde; simplify; eauto; *)
(*           try (apply inde_assn_of_svs; unfold not; intros); *)
(*           try (apply inde_assn_of_avs; unfold not; intros); try (split; intros); *)
(*           forwards* (? & ? & ?): (>>freshes_vars Hfeq1); substs; *)
(*         try now (match goal with *)
(*              | [H : In ?y (snd (avar_env x)) |- _] => *)
(*                forwards*: (Havar1 x y); autorewrite with setop; eauto; eauto; *)
(*                simpl in *; rewrite prefix_nil in *; congruence *)
(*              | [Heq : fst (avar_env x) = Var (str_of_pnat _ _) |- _] => *)
(*                forwards*: (Havar2 x); autorewrite with setop; eauto; *)
(*                rewrite Heq in *; simpl in *; rewrite prefix_nil in *; congruence *)
(*              | [H : In _ (fv_E e) |- _ ] => *)
(*                forwards*: Hres; autorewrite with setop; eauto; omega  *)
(*              end). *)
(*         forwards*: Hsvar. *)
(*         forwards*: (>>compile_don't_decrease Hceq1); omega. *)
(*         forwards*: Havar1; autorewrite with setop in *; jauto. *)
(*         simpl in *; rewrite prefix_nil in *; congruence. *)
(*         forwards*: Havar2; autorewrite with setop in *; jauto. *)
(*         rewrite H2 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*       intros; sep_normal_in H; sep_split_in H; sep_split; eauto. *)
(*       sep_rewrite_r add_remove. *)
(*       unfold assn_of_avs; sep_rewrite SA.add_equiv; [|autorewrite with setop; intros [? ?]; congruence]. *)
(*       rewrite Haeval. *)
(*       apply scC; sep_cancel. *)
(*       sep_rewrite (is_array_tup_unfold (S.es2gls (S.vars2es (snd (avar_env x)))) (Z.to_nat ix)). *)
(*       Focus 2. { *)
(*         simpl; intros; unfold S.es2gls; simplify. *)
(*         forwards* Htyv: (>> Haectx (VZ 0) i). *)
(*         unfold val in *; rewrites* (>>has_type_val_len Htyv). *)
(*         rewrites* (>>Havctx). } Unfocus. *)
(*       2: zify; rewrite Z2Nat.id; omega. *)
(*       unfold S.es2gls in *; simpl. *)
(*       assert ((Zn (Z.to_nat ix) === e) s (emp_ph loc)). *)
(*       { unfold_conn_in HP1; unfold_conn; simpl in *; rewrite Z2Nat.id; eauto. } *)
(*       sep_rewrite S.mps_eq1_tup'; [|exact H1]. *)
(*       sep_normal; sep_split; repeat sep_cancel. *)
(*     - rewrite (p2 (avar_env x)) in *. *)
(*       inverts Hcompile. *)
(*       inverts Heval. *)
(*       split. *)
(*       { intros; simplify. *)
(*         forwards*: Havar2; autorewrite with setop; eauto. *)
(*         rewrite H0 in *; simpl in *; rewrite prefix_nil in *; try congruence. } *)
(*       simpl; eapply Hforward; eauto using rule_skip. *)
(*       intros. *)
(*       sep_split; sep_split_in H; intros; repeat sep_cancel. *)
(*       sep_split; eauto using emp_emp_ph. *)
(*       unfold assn_of_avs in *; sep_rewrite_in (SA.add_equiv') H. *)
(*       2: instantiate (1 := x); autorewrite with setop; eauto. *)
(*       sep_rewrite_in (SA.add_equiv) H; [|autorewrite with setop; intros [? ?]; congruence]; try rewrite H1 in H. *)
(*       sep_normal_in H; sep_split_in H; eauto. *)
(*     - unfoldM'. *)
(*       destruct (Sx.typ_of_sexp se) eqn:Heqty; try now inverts Hcompile. *)
(*       destruct (compile_sexp _ se _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile]. *)
(*       destruct (le_dec _ _); inverts Hcompile. *)
(*       inverts Htyp as Htyp Hlt. *)
(*       inverts Heval as Heval Hlt'. *)
(*       forwards* (Hres & Htri): IHse. *)
(*       splits*. *)
(*       Lemma firstn_in (A: Type) n (x : A) xs  : In x (firstn n xs) -> In x xs. *)
(*       Proof. *)
(*         revert xs; induction n; simpl; [destruct 1|]. *)
(*         destruct xs; simpl; eauto. *)
(*         simpl in *; intros [? | ?]; eauto. *)
(*       Qed. *)

(*       Lemma skipn_in (A : Type) n (x : A) xs : In x (skipn n xs) -> In x xs. *)
(*       Proof. *)
(*         revert xs; induction n; simpl; eauto. *)
(*         destruct xs; simpl; eauto. *)
(*       Qed. *)
(*       Hint Resolve firstn_in skipn_in. *)
(*       intros; forwards*: Hres. *)
(*       eapply Hforward; eauto. *)
(*       simpl; intros s h H; sep_split_in H; sep_split; eauto. *)
(*       forwards*: type_preservation. *)
(*       forwards*: compile_preserve. *)
(*       forwards*: (>>has_type_val_len H0). *)
(*       assert (Hlen : length es1 = length (vs_of_sval (VTup tup))) by congruence. *)
(*       inverts H0. *)
(*       rewrites* (>>typ_of_sexp_ok) in Heqty; inverts Heqty. *)
(*       revert H5 Hlt Hlen HP0. *)
(*       clear. *)
(*       intros Hty; revert i es1. *)
(*       induction Hty; simpl; introv Hlt Hlen Heq. *)
(*       + destruct es1; simpl in *; try congruence; intros; omega. *)
(*       + destruct i; simpl. *)
(*         * unfold len_at_i; simpl. *)
(*           forwards*: (>>has_type_val_len H); rewrite <-H0. *)
(*           revert Heq; clear; revert es1; induction (vs_of_sval x); introv. *)
(*           { intros; simpl; apply emp_emp_ph. } *)
(*           { destruct es1; simpl; eauto. *)
(*             intros H; sep_split_in H; sep_split; eauto. } *)
(*         * unfold len_at_i; simpl. *)
(*           forwards*: (>>has_type_val_len H). *)
(*           assert (exists es es1', es1 = es ++ es1' /\ length es = len_of_ty y) as *)
(*               (es & es1' & ? & Hlen'); [|substs]. *)
(*           { exists (firstn (len_of_ty y) es1) (skipn (len_of_ty y) es1). *)
(*             split; eauto using firstn_skipn. *)
(*             rewrite firstn_length, Nat.min_l; eauto. *)
(*             rewrite app_length in *; omega. } *)
(*           Lemma eq_tup_app es1 es2 es1' es2' stk : *)
(*             length es1 = length es1' -> *)
(*             (es1 ++ es2 ==t es1' ++ es2') stk (emp_ph loc) -> *)
(*             (es1 ==t es1') stk (emp_ph loc) /\ *)
(*             (es2 ==t es2') stk (emp_ph loc). *)
(*           Proof. *)
(*             revert es2 es1' es2'; induction es1; introv Hlen Heq. *)
(*             - destruct es1'; simpl in *; try congruence. *)
(*               split; eauto using emp_emp_ph. *)
(*             - destruct es1'; simpl in *; try congruence. *)
(*               sep_split_in Heq. *)
(*               forwards*: IHes1. *)
(*               split; sep_split; jauto. *)
(*           Qed. *)
(*           forwards* (? & ?): (>>eq_tup_app Heq). *)
(*           { unfold val; rewrite H0; eauto. } *)
(*           forwards*: (>>IHHty i); try omega. *)
(*           { simpl; rewrite !app_length in Hlen; omega. } *)
(*           Lemma skipn_app (A : Type) n (xs ys : list A) : *)
(*             skipn n (xs ++ ys) = if lt_dec n (length xs) then (skipn n xs) ++ ys else skipn (n - length xs) ys. *)
(*           Proof. *)
(*             revert xs ys; induction n; simpl; introv. *)
(*             - destruct lt_dec; eauto. *)
(*               destruct xs; simpl in *; try omega; eauto. *)
(*             - introv; destruct xs; simpl; eauto. *)
(*               rewrite IHn; repeat destruct lt_dec; try omega; eauto. *)
(*           Qed. *)
(*           unfold val, len_until_i in *; simpl in *; rewrite skipn_app; destruct lt_dec; try omega. *)
(*           unfold val in *; rewrite Hlen', <-H0, minus_plus. *)
(*           eauto. *)
(*     - assert (ty = ty0); [|substs]. *)
(*       { forwards*: typ_of_sexp_ok. } *)
(*       revert n m c es0 sv ty0 Hsvar Htyp Heval Hcompile; induction H; introv Hsvar Htyp Heval Hcompile. *)
(*       + inverts Hcompile; simpl. *)
(*         inverts Htyp as Htyp; inverts Htyp. *)
(*         inverts Heval as Heval; inverts Heval. *)
(*         splits; try now destruct 1. *)
(*         eapply Hforward; eauto using rule_skip. *)
(*         simpl; intros; sep_split_in H; sep_split; repeat sep_cancel. *)
(*       + inverts Heval as Heval; inverts Heval as Heval0 Heval. *)
(*         inverts Htyp as Htyp; inverts Htyp as Htyp0 Htyp. *)
(*         unfoldM'. *)
(*         destruct (compile_sexp _ x _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile]. *)
(*         lazymatch type of Hcompile with *)
(*         | context [let (_, _) := ?X in _] => *)
(*           destruct X as [[(cs' & es') | ?] n''] eqn:Hceq2; inversion Hcompile *)
(*         end; substs. *)
(*         assert (Hnn' : n <= n'). *)
(*         { forwards*: compile_don't_decrease. } *)
(*         assert (Hn'm : n' <= m). *)
(*         { revert Hceq2; clear; intros Hceq2. *)
(*           revert es' cs' n' m Hceq2; induction l; introv Hceq. *)
(*           - inverts Hceq; eauto. *)
(*           - unfoldM'. *)
(*             destruct (compile_sexp _ _ _ _)  as [[(cs1 & es1) | ?] k] eqn:Hceq1; [|inversion Hceq]. *)
(*             lazymatch type of Hceq with *)
(*               | context [let (_, _) := ?X in _] => *)
(*                 destruct X as [[(cs'' & es'') | ?] n'''] eqn:Hceq2; inversion Hceq *)
(*             end; substs. *)
(*             forwards*: compile_don't_decrease. *)
(*             forwards*: IHl. *)
(*             omega. } *)
(*         forwards* (Hres & Htri): IHForall; try now constructor; eauto. *)
(*         { intros. *)
(*           forwards*: Havar1; simpl; autorewrite with setop; eauto. } *)
(*         { intros. *)
(*           forwards*: Havar2; simpl; autorewrite with setop; eauto. } *)
(*         { intros. *)
(*           forwards*: Hsvar; simpl; autorewrite with setop; eauto. *)
(*           forwards*: compile_don't_decrease; omega. } *)
(*         forwards* (Hres0 & Htri0): H. *)
(*         { intros. *)
(*           forwards*: Hsvar; simpl; autorewrite with setop; eauto. } *)
(*         { intros. *)
(*           forwards*: Havar1; simpl; autorewrite with setop; eauto. } *)
(*         { intros. *)
(*           forwards*: Havar2; simpl; autorewrite with setop; eauto. } *)
(*         splits. *)
(*         (* { introv; simpl; rewrite in_app_iff; intros [? | ?]; *) *)
(*         (*   [ forwards* (? & ? & ? & ?): Hwr0 | forwards*(? & ? & ? & ?): Hwr]; do 2 eexists; splits*; *) *)
(*         (*   omega. } *) *)
(*         { introv; rewrite in_app_iff; intros [? | ?] ?; *)
(*           [ forwards*: Hres0 | forwards*: Hres]; try omega. } *)
(*         simpl. *)
(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           unfold assn_of_svs, assn_of_avs; intros s h Hsat. *)
(*           sep_rewrite_in SE.union_assns Hsat; sep_rewrite_in pure_star Hsat. *)
(*           sep_rewrite_in SA.union_assns Hsat. *)
(*           rewrite !fold_assn_svs, !fold_assn_avs in Hsat. *)
(*           instantiate (1 := *)
(*             ((!(assn_of_svs seval_env svar_env (free_sv x)) ** assn_of_avs (free_av x)) ** *)
(*              !(assn_of_svs seval_env svar_env *)
(*                (SE.SE.diff (fold_right (fun (e : Sx.SExp) (xs : SE.t) => SE.union (free_sv e) xs) SE.empty l) (free_sv x))) ** *)
(*           assn_of_avs (SA.SE.diff (fold_right (fun (e : Sx.SExp) (xs : SA.t) => SA.union (free_av e) xs) SA.empty l) (free_av x)))). *)
(*           sep_normal; sep_normal_in Hsat; repeat sep_cancel. } Unfocus. *)
(*         eapply rule_seq; [eapply rule_frame; eauto|]. *)
(*         { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs]; *)
(*           introv; autorewrite with setop; intros ? ? ?; *)
(*           forwards* (? & ? & ? & ?): (>>compile_wr_vars Hceq1); des; substs. *)
(*           - forwards*: Hsvar; simpl; autorewrite with setop; eauto; omega. *)
(*           - forwards*: Havar1; simpl; autorewrite with setop; eauto. *)
(*             simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - forwards*: Havar2; simpl; autorewrite with setop; eauto. *)
(*             rewrite <-H4 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           intros s h Hsat. *)
(*           assert (Hsat' : (!(es1 ==t vs_of_sval v) ** *)
(*                    !(assn_of_svs seval_env svar_env *)
(*                      (SE.union (free_sv x) (fold_right (fun (e : Sx.SExp) (xs : SE.t) => SE.union (free_sv e) xs) SE.empty l))) ** *)
(*                     assn_of_avs (SA.union (free_av x) (fold_right (fun (e : Sx.SExp) (xs : SA.t) => SA.union (free_av e) xs) SA.empty l))) *)
(*                     s h). *)
(*           { unfold assn_of_svs, assn_of_avs in *. *)
(*             sep_rewrite SE.union_assns; sep_rewrite SA.union_assns; sep_rewrite pure_star. *)
(*             sep_normal_in Hsat; sep_normal; repeat sep_cancel. } *)
(*           sep_rewrite_in SE.union_comm Hsat'; sep_rewrite_in SA.union_comm Hsat'. *)
(*           unfold assn_of_svs, assn_of_avs in *. *)
(*           sep_rewrite_in SE.union_assns Hsat'; *)
(*           sep_rewrite_in SA.union_assns Hsat'; sep_rewrite_in pure_star Hsat'. *)
(*           rewrite !fold_assn_svs, !fold_assn_avs in Hsat'. *)
(*           instantiate (1 := *)
(*             ((!(assn_of_svs seval_env svar_env *)
(*                             (fold_right (fun (e : Sx.SExp) (xs : SE.t) => SE.union (free_sv e) xs) SE.empty l)) ** *)
(*               assn_of_avs (fold_right (fun (e : Sx.SExp) (xs : SA.t) => SA.union (free_av e) xs) SA.empty l)) ** *)
(*              !(es1 ==t vs_of_sval v) ** *)
(*              !(assn_of_svs seval_env svar_env *)
(*                   (SE.SE.diff (free_sv x) (fold_right (fun (e : Sx.SExp) (xs : SE.t) => SE.union (free_sv e) xs) SE.empty l))) ** *)
(*              assn_of_avs (SA.SE.diff (free_av x) *)
(*                                      (fold_right (fun (e : Sx.SExp) (xs : SA.t) => SA.union (free_av e) xs) SA.empty l)))). *)
(*          sep_normal; sep_normal_in Hsat'; repeat sep_cancel. } Unfocus. *)
(*         eapply Hforward; [eapply rule_frame; eauto|]. *)
(*         { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify]; *)
(*           introv; autorewrite with setop; try intros ? ? ?; *)
(*           forwards* (? & ? & ? & ?): (>> compile_sexps_wr_vars); des; substs. *)
(*           - forwards*: Hres0; omega. *)
(*           - forwards*: Hsvar; simpl; autorewrite with setop; eauto; omega. *)
(*           - forwards*: Havar1; simpl; autorewrite with setop; eauto. *)
(*             simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - forwards*: Havar2; simpl; autorewrite with setop; eauto. *)
(*             rewrite <-H4 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*         intros s h Hsat. *)
(*         sep_rewrite SE.union_comm; sep_rewrite SA.union_comm; *)
(*           unfold assn_of_svs, assn_of_avs in *; *)
(*           sep_rewrite SE.union_assns; *)
(*           sep_rewrite SA.union_assns; sep_rewrite pure_star. *)
(*         sep_normal_in Hsat; sep_normal; repeat sep_cancel. *)
(*         sep_split_in H4; sep_split; eauto; simpl in *. *)
(*         Lemma eq_tup_app' es1 es2 es1' es2' stk : *)
(*           (es1 ==t es1') stk (emp_ph loc) -> *)
(*           (es2 ==t es2') stk (emp_ph loc) -> *)
(*           (es1 ++ es2 ==t es1' ++ es2') stk (emp_ph loc). *)
(*         Proof. *)
(*           revert es2 es1' es2'; induction es1; introv Heq1 Heq2. *)
(*           - destruct es1'; simpl in *; eauto; destruct Heq1. *)
(*           - destruct es1'; simpl in *; [destruct Heq1|]. *)
(*             sep_split_in Heq1. *)
(*             forwards*: IHes1. *)
(*             sep_split; eauto. *)
(*         Qed. *)
(*         apply eq_tup_app'; eauto. *)
(*     - unfoldM'. *)
(*       destruct (compile_sexp _ se1 _ _) as [[(cs1 & es1) | ?] n'] eqn:Hceq1; [|inversion Hcompile]. *)
(*       destruct (compile_sexp _ se2 _ _) as [[(cs2 & es2) | ?] n''] eqn:Hceq2; [|inversion Hcompile]. *)
(*       destruct (compile_sexp _ se3 _ _) as [[(cs3 & es3) | ?] n'''] eqn:Hceq3; [|inversion Hcompile]. *)
(*       destruct (freshes _ _) as [[fvs1 | ?] n''''] eqn:Hfeq1; [|inversion Hcompile]. *)
(*       destruct es1 as [| e [| ? ?]]; inverts Hcompile. *)
(*       inverts Htyp as Htyp1 Htyp2 Htyp3. *)
(*       splits. *)
(*       { intros; simplify. *)
(*         forwards* (? & ? & ?): (>>freshes_vars Hfeq1). *)
(*         apply var_pnat_inj in H0 as (? & ?); substs. *)
(*         forwards*: (>>freshes_incr); omega. } *)
(*       assert (n <= n' /\ n' <= n'' /\ n'' <= n''' /\ n''' + 1 = m). *)
(*       { splits; [forwards*: (>>compile_don't_decrease Hceq1) | *)
(*                  forwards*: (>>compile_don't_decrease Hceq2) | *)
(*                  forwards*: (>>compile_don't_decrease Hceq3) | *)
(*                  forwards*: (>>freshes_incr Hfeq1) ]. } *)
(*       inverts Heval as Heval1 Heval2. *)
(*       + forwards* (Hres1 & Htri1): IHse1. *)
(*         { intros; forwards*: Hsvar; autorewrite with setop; eauto. } *)
(*         { intros; forwards*: Havar1; autorewrite with setop; eauto. } *)
(*         { intros; forwards*: Havar2; autorewrite with setop; eauto. } *)
(*         forwards* (Hres2 & Htri2): IHse2. *)
(*         { intros; forwards*: Hsvar; autorewrite with setop; eauto; omega. } *)
(*         { intros; forwards*: Havar1; autorewrite with setop; eauto. } *)
(*         { intros; forwards*: Havar2; autorewrite with setop; eauto. } *)
        
(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           intros s h Hsat. *)
(*           unfold assn_of_svs, assn_of_avs in Hsat. *)
(*           sep_rewrite_in SE.union_assns Hsat. *)
(*           sep_rewrite_in SA.union_assns Hsat. *)
(*           sep_rewrite_in pure_star Hsat. *)
(*           rewrite !fold_assn_avs, !fold_assn_svs in Hsat. *)
(*           instantiate (1 := ( *)
(*              (!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) **  *)
(*              !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se2) (free_sv se3)) (free_sv se1))) ** *)
(*              assn_of_avs (SA.SE.diff (SA.union (free_av se2) (free_av se3)) (free_av se1)))). *)
(*           sep_normal; sep_normal_in Hsat; repeat sep_cancel. } Unfocus. *)
(*         eapply rule_seq; [eapply rule_frame; eauto|]. *)
(*         { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify]; *)
(*           introv; autorewrite with setop; intros ? ? ?; des. *)
(*           - destruct H1; *)
(*               forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*                 forwards*: Hsvar; autorewrite with setop; eauto; omega. *)
(*           - destruct H1; *)
(*               forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*                 forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - destruct H1; forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; forwards*: Havar2;  *)
(*               autorewrite with setop in *; eauto. *)
(*             rewrite <- H7 in *; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence. *)
(*             substs; rewrite <- H7 in *; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*         eapply Hforward; [eapply rule_if_disj|]; simpl in *. *)
(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           intros s h Hsat. *)
(*           assert ((!(assn_of_svs seval_env svar_env (SE.union (free_sv se1) (SE.union (free_sv se2) (free_sv se3)))) ** *)
(*                     assn_of_avs (SA.union (free_av se1) (SA.union (free_av se2) (free_av se3)))) s h). *)
(*           { unfold assn_of_svs, assn_of_avs in *. *)
(*             sep_rewrite SE.union_assns; sep_rewrite pure_star. *)
(*             sep_rewrite SA.union_assns. *)
(*             sep_normal_in Hsat; sep_normal; sep_split_in Hsat; sep_split; repeat sep_cancel. } *)
(*           Lemma se_union_assoc s1 s2 s3 : *)
(*             SE.union (SE.union s1 s2) s3 == SE.union s1 (SE.union s2 s3). *)
(*           Proof. *)
(*             simpl; unfold SE.Equal; introv; autorewrite with setop. *)
(*             split; intros; eauto. *)
(*             destruct H as [[? | ?] | ?]; eauto. *)
(*             destruct H as [? | [? | ?]]; eauto. *)
(*           Qed. *)
(*           Lemma sa_union_assoc s1 s2 s3 : *)
(*             SA.union (SA.union s1 s2) s3 == SA.union s1 (SA.union s2 s3). *)
(*           Proof. *)
(*             simpl; unfold SA.Equal; introv; autorewrite with setop. *)
(*             split; intros; eauto. *)
(*             destruct H as [[? | ?] | ?]; eauto. *)
(*             destruct H as [? | [? | ?]]; eauto. *)
(*           Qed. *)
(*           sep_rewrite_in (SE.union_comm (free_sv se1)) H0. *)
(*           sep_rewrite_in se_union_assoc H0. *)
(*           sep_rewrite_in (SA.union_comm (free_av se1)) H0. *)
(*           sep_rewrite_in sa_union_assoc H0. *)
(*           unfold assn_of_svs, assn_of_avs in H0. *)
(*           sep_rewrite_in SE.union_assns H0; sep_rewrite_in pure_star H0. *)
(*           sep_rewrite_in SA.union_assns H0. *)
(*           rewrite !fold_assn_svs, !fold_assn_avs in H0. *)
(*           instantiate (1 := *)
(*             ((!(assn_of_svs seval_env svar_env (free_sv se2)) ** assn_of_avs (free_av se2)) ** *)
(*             !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se3) (free_sv se1)) (free_sv se2))) ** *)
(*             assn_of_avs (SA.SE.diff (SA.union (free_av se3) (free_av se1)) (free_av se2)))). *)
(*           sep_normal; sep_normal_in H0; repeat sep_cancel. } Unfocus. *)
(*         eapply rule_seq; [eapply rule_frame; eauto|]. *)
(*         { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify]; *)
(*           introv; autorewrite with setop; try intros ? [? ?]; try split; try intros ?. *)
(*           - destruct H1; *)
(*               forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*                 forwards*: Hsvar; autorewrite with setop; eauto; omega. *)
(*           - destruct H1; *)
(*               forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*                 forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - destruct H1; *)
(*               forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*             forwards*: Havar2; autorewrite with setop; eauto. *)
(*             rewrite <-H4 in *; simpl in *; rewrite prefix_nil in *; congruence. *)
(*             rewrite <-H4 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           intros s h Hsat. *)
(*           instantiate (1 := *)
(*             !(es2 ==t vs_of_sval sv) ** *)
(*             !(assn_of_svs seval_env svar_env (free_sv se2)) ** assn_of_avs (free_av se2) ** *)
(*             !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se3) (free_sv se1)) (free_sv se2))) ** *)
(*             assn_of_avs (SA.SE.diff (SA.union (free_av se3) (free_av se1)) (free_av se2))). *)
(*           sep_normal_in Hsat; sep_normal; repeat sep_cancel. } Unfocus. *)
(*         eapply rule_frame; [apply read_tup_correct|]. *)
(*         { unfold not; intros. *)
(*           forwards* (? & ? & ?): freshes_vars; substs. *)
(*           forwards*: (Hres2); omega. } *)
(*         { forwards*: freshes_disjoint. } *)
(*         { forwards*: (>>type_preservation Htyp2). *)
(*           unfold val in * ; rewrites* (>> has_type_val_len H0). *)
(*           forwards*: (>>compile_preserve Hceq2). } *)
(*         { forwards*: (>>freshes_len Hfeq1). } *)
(*         { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs]; *)
(*           introv; autorewrite with setop; unfold not; intros; forwards*: (read_tup_writes'); *)
(*           forwards* (? & ? & ?): (>>freshes_vars Hfeq1); substs. *)
(*           - forwards*: Hsvar; autorewrite with setop; eauto; omega. *)
(*           - forwards*: Havar1; autorewrite with setop; eauto. *)
(*             simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - forwards*: Havar2; autorewrite with setop; eauto. *)
(*             rewrite H4 in *; simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - forwards*: Hsvar; autorewrite with setop. *)
(*             destruct H1 as ([? | ?] & _); eauto. *)
(*             omega. *)
(*           - forwards*: Havar1; autorewrite with setop. *)
(*             destruct H1 as ([? | ?] & _); eauto. *)
(*             simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - forwards*: Havar2; autorewrite with setop. *)
(*             destruct H1 as ([? | ?] & _); eauto. *)
(*             rewrite H4 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           intros s h Hsat. *)
(*           sep_normal_in Hsat; sep_split_in Hsat. *)
(*           sep_split_in HP0. *)
(*           unfold_pures. *)
(*           instantiate (1 := FalseP). *)
(*           congruence. } Unfocus. *)
(*         instantiate (1 := FalseP). *)
(*         intros x; destruct 1. *)
(*         intros s h [Hsat | []]. *)
(*         sep_rewrite (SE.union_comm (free_sv se1)). *)
(*         sep_rewrite se_union_assoc. *)
(*         sep_rewrite (SA.union_comm (free_av se1)). *)
(*         sep_rewrite sa_union_assoc. *)
(*         unfold assn_of_svs, assn_of_avs in *; sep_rewrite SE.union_assns; sep_rewrite SA.union_assns; sep_rewrite pure_star. *)
(*         sep_normal_in Hsat; sep_normal; repeat sep_cancel. *)
(*       + forwards* (Hres1 & Htri1): IHse1. *)
(*         { intros; forwards*: Hsvar; autorewrite with setop; eauto. } *)
(*         { intros; forwards*: Havar1; autorewrite with setop; eauto. } *)
(*         { intros; forwards*: Havar2; autorewrite with setop; eauto. } *)
(*         forwards* (Hres3 & Htri3): IHse3. *)
(*         { intros; forwards*: Hsvar; autorewrite with setop; eauto; omega. } *)
(*         { intros; forwards*: Havar1; autorewrite with setop; eauto. } *)
(*         { intros; forwards*: Havar2; autorewrite with setop; eauto. } *)
        
(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           intros s h Hsat. *)
(*           unfold assn_of_svs, assn_of_avs in Hsat. *)
(*           sep_rewrite_in SE.union_assns Hsat. *)
(*           sep_rewrite_in SA.union_assns Hsat. *)
(*           sep_rewrite_in pure_star Hsat. *)
(*           rewrite !fold_assn_avs, !fold_assn_svs in Hsat. *)
(*           instantiate (1 := ( *)
(*              (!(assn_of_svs seval_env svar_env (free_sv se1)) ** assn_of_avs (free_av se1)) **  *)
(*              !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se2) (free_sv se3)) (free_sv se1))) ** *)
(*              assn_of_avs (SA.SE.diff (SA.union (free_av se2) (free_av se3)) (free_av se1)))). *)
(*           sep_normal; sep_normal_in Hsat; repeat sep_cancel. } Unfocus. *)
(*         eapply rule_seq; [eapply rule_frame; eauto|]. *)
(*         { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify]; *)
(*           introv; autorewrite with setop; try intros ? [? ?] ?. *)
(*           - destruct H1; *)
(*               forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*                 forwards*: Hsvar; autorewrite with setop; eauto; omega. *)
(*           - destruct H1; *)
(*               forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*                 forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - destruct H1; forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*             forwards*: Havar2; autorewrite with setop; eauto; simpl in *. *)
(*             rewrite <- H4 in *; simpl in *; rewrite prefix_nil in *; congruence. *)
(*             rewrite <- H4 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*         eapply Hforward; [eapply rule_if_disj|]; simpl in *. *)
(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           intros s h Hsat. *)
(*           sep_normal_in Hsat; sep_split_in Hsat. *)
(*           sep_split_in HP0. *)
(*           unfold_pures. *)
(*           instantiate (1 := FalseP). *)
(*           congruence. } Unfocus. *)
(*         instantiate (1 := FalseP). *)
(*         intros x; destruct 1. *)

(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           intros s h Hsat. *)
(*           assert ((!(assn_of_svs seval_env svar_env (SE.union (free_sv se1) (SE.union (free_sv se2) (free_sv se3)))) ** *)
(*                     assn_of_avs (SA.union (free_av se1) (SA.union (free_av se2) (free_av se3)))) s h). *)
(*           { unfold assn_of_svs, assn_of_avs in *. *)
(*             sep_rewrite SE.union_assns; sep_rewrite pure_star. *)
(*             sep_rewrite SA.union_assns. *)
(*             sep_normal_in Hsat; sep_normal; sep_split_in Hsat; sep_split; repeat sep_cancel. } *)
(*           sep_rewrite_in (SE.union_comm (free_sv se2)) H0. *)
(*           sep_rewrite_in (SE.union_comm (free_sv se1)) H0. *)
(*           sep_rewrite_in se_union_assoc H0. *)
(*           sep_rewrite_in (SA.union_comm (free_av se2)) H0. *)
(*           sep_rewrite_in (SA.union_comm (free_av se1)) H0. *)
(*           sep_rewrite_in sa_union_assoc H0. *)
(*           unfold assn_of_svs, assn_of_avs in H0. *)
(*           sep_rewrite_in SE.union_assns H0; sep_rewrite_in pure_star H0. *)
(*           sep_rewrite_in SA.union_assns H0. *)
(*           rewrite !fold_assn_svs, !fold_assn_avs in H0. *)
(*           instantiate (1 := *)
(*             ((!(assn_of_svs seval_env svar_env (free_sv se3)) ** assn_of_avs (free_av se3)) ** *)
(*             !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se2) (free_sv se1)) (free_sv se3))) ** *)
(*             assn_of_avs (SA.SE.diff (SA.union (free_av se2) (free_av se1)) (free_av se3)))). *)
(*           sep_normal; sep_normal_in H0; repeat sep_cancel. } Unfocus. *)
(*         eapply rule_seq; [eapply rule_frame; eauto|]. *)
(*         { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs | apply inde_eq_tup; simplify]; *)
(*           introv; autorewrite with setop; try intros ? [? ?] ?. *)
(*           - destruct H1; *)
(*               forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*                 forwards*: Hsvar; autorewrite with setop; eauto; omega. *)
(*           - destruct H1; *)
(*               forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*                 forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - substs; destruct H1; forwards*(? & ? & ? & ?): (>>compile_wr_vars H0); substs; *)
(*               forwards*: Havar2; autorewrite with setop; eauto. *)
(*             rewrite <-H3 in *; simpl in *; rewrite prefix_nil in *; congruence. *)
(*             rewrite <-H3 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*         eapply Hbackward. *)
(*         Focus 2. { *)
(*           intros s h Hsat. *)
(*           instantiate (1 := *)
(*             !(es3 ==t vs_of_sval sv) ** *)
(*             !(assn_of_svs seval_env svar_env (free_sv se3)) ** assn_of_avs (free_av se3) ** *)
(*             !(assn_of_svs seval_env svar_env (SE.SE.diff (SE.union (free_sv se2) (free_sv se1)) (free_sv se3))) ** *)
(*             assn_of_avs (SA.SE.diff (SA.union (free_av se2) (free_av se1)) (free_av se3))). *)
(*           sep_normal_in Hsat; sep_normal; repeat sep_cancel. } Unfocus. *)
(*         eapply rule_frame; [apply read_tup_correct|]. *)
(*         { unfold not; intros. *)
(*           forwards* (? & ? & ?): freshes_vars; substs. *)
(*           forwards*: (Hres3); omega. } *)
(*         { forwards*: freshes_disjoint. } *)
(*         { forwards*: (>>type_preservation Htyp3). *)
(*           unfold val in * ; rewrites* (>> has_type_val_len H0). *)
(*           forwards*: (>>compile_preserve Hceq3). } *)
(*         { forwards*: (>>freshes_len Hfeq1). *)
(*           forwards*: (>>compile_preserve Hceq3). *)
(*           forwards*: (>>compile_preserve Hceq2). *)
(*           congruence. } *)
(*         { prove_inde; first [apply inde_assn_of_avs | apply inde_assn_of_svs]; *)
(*           introv; autorewrite with setop; unfold not; intros; forwards*: (read_tup_writes'); *)
(*           forwards* (? & ? & ?): (>>freshes_vars Hfeq1); substs. *)
(*           - forwards*: Hsvar; autorewrite with setop; eauto; omega. *)
(*           - forwards*: Havar1; autorewrite with setop; eauto; simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - forwards*: Havar2; autorewrite with setop; eauto; simpl in *. *)
(*             rewrite H4 in *; simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - forwards*: Hsvar; autorewrite with setop. *)
(*             destruct H1 as ([? | ?] & _); eauto. *)
(*             omega. *)
(*           - forwards*: Havar1; autorewrite with setop. *)
(*             destruct H1 as ([? | ?] & _); eauto. *)
(*             simpl in *; rewrite prefix_nil in *; congruence. *)
(*           - forwards*: Havar2; autorewrite with setop; eauto; simpl in *. *)
(*             destruct H1 as ([? | ?] & _); eauto. *)
(*             rewrite H4 in *; simpl in *; rewrite prefix_nil in *; congruence. } *)
(*         intros s h [[] | Hsat]. *)
(*         sep_rewrite (SE.union_comm (free_sv se2)). *)
(*         sep_rewrite (SE.union_comm (free_sv se1)). *)
(*         sep_rewrite se_union_assoc. *)
(*         sep_rewrite (SA.union_comm (free_av se2)). *)
(*         sep_rewrite (SA.union_comm (free_av se1)). *)
(*         sep_rewrite sa_union_assoc. *)
(*         unfold assn_of_svs, assn_of_avs in *; sep_rewrite SE.union_assns; sep_rewrite SA.union_assns; sep_rewrite pure_star. *)
(*         sep_normal_in Hsat; sep_normal; repeat sep_cancel.  *)
(*   Qed. *)
(* End CorrectnessProof. *)