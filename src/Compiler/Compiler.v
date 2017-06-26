Require Import String.
Require Import Vector.
Require Import DepList.
Require Import ZArith.
Require Import GPUCSL.
Require Import LibTactics.
Require Import Psatz.
Require Import Monad.
Require Import TypedTerm.
Require Import CUDALib.
Require Import Correctness.
Require Import mkMap.
Require Import mkReduce.
Require Import SeqCompiler.

Open Scope string_scope.
Definition name := string. 

Require GPUCSL.
Module G := GPUCSL.
(* Require Skel_lemma. *)
(* Module S := Skel_lemma. *)

Instance eq_type_nat : eq_type nat := {eq_dec := eq_nat_dec}.

Require Import Host.

Section Compiler.

  Fixpoint alloc_tup_arr {ty : Skel.Typ} : vars ty -> exp -> stmt :=
    match ty return vars ty -> exp -> stmt with
    | Skel.TBool | Skel.TZ => fun x len => host_alloc x len
    | Skel.TTup t1 t2 => fun xs len =>
      host_seq (alloc_tup_arr (fst xs) len) (alloc_tup_arr (snd xs) len)
    end.

  (* TODO: should be moved to Monad.v *)
  Definition state s a := s -> (a * s).
  Instance state_Monad s : Monad (state s) := {
     ret A x := fun n => (x, n);
     bind A B x f := fun n => let (y, n) := x n in f y n
  }.

  Open Scope list_scope.

  Definition hseq st st' := match st' with
                            | host_skip => st
                            | _ => host_seq st st'
                            end.
  
  Definition CUDAM A := nat -> nat -> (A * (nat * nat * list stmt * GModule)).
  Global Instance CUDAM_Monad : Monad CUDAM := {
    ret A x := fun n m => (x, (n, m, nil, nil));
    bind A B x f := fun n m =>
                      let '(y, (n', m', st, gm)) := x n m in
                      let '(z, (n'',m'', st', gm')) := f y n' m' in
                      (z, (n'', m'', app st st', gm ++ gm'))
  }.
  Definition getPn : CUDAM nat := fun n m => (n, (n, m, nil, nil)).
  Definition getFn : CUDAM nat := fun n m => (m, (n, m, nil, nil)).
  Definition setPn x : CUDAM unit := fun n m => (tt, (x, m, nil, nil)).
  Definition setFn x : CUDAM unit := fun n m => (tt, (n, x, nil, nil)).
  Definition setGM gm : CUDAM unit := fun n m => (tt, (n, m, nil, gm)).
  Definition setI (i : stmt) : CUDAM unit := fun n m => (tt, (n, m, i :: nil, nil)).

  Definition freshP : CUDAM var := 
    do! n <- getPn in
    do! _ <- setPn (S n) in
    ret (Var ("h" ++ nat2str n))%string.

  Definition freshF : CUDAM string := 
    do! n <- getFn in
    do! _ <- setFn (S n) in
    let newID := ("_ker" ++ nat2str n)%string in
    ret newID.

  Definition fLet e : CUDAM var :=
    do! x <- freshP in
    do! _ <- setI (host_iLet x e) in
    ret x.

  Definition fAlloc e : CUDAM var :=
    do! x <- freshP in
    do! _ <- setI (host_alloc x e) in
    ret x.

  Definition gen_kernel (ker : kernel) : CUDAM string :=
    do! id <- freshF in
    do! _ <- setGM ((id, Kern ker) :: nil) in
    ret id.

  Fixpoint mapMtyp {typ B A M} `{Monad M} (f : A -> M B) : typ2Coq A typ -> M (typ2Coq B typ) :=
    match typ return typ2Coq A typ -> M (typ2Coq B typ) with
    | Skel.TZ | Skel.TBool => fun x => f x
    | Skel.TTup t1 t2 => fun xs => 
      do! xs1 <- mapMtyp f (fst xs) in
      do! xs2 <- mapMtyp f (snd xs) in
      ret (xs1, xs2)
    end.

  Fixpoint fAllocs' (typ : Skel.Typ) (size : var) : CUDAM (vars typ) :=
    match typ return CUDAM (vars typ) with
    | Skel.TZ | Skel.TBool => fAlloc size
    | Skel.TTup t1 t2 => 
      do! xs1 <- fAllocs' t1 size in
      do! xs2 <- fAllocs' t2 size in
      ret (xs1, xs2)
    end.

  Definition fAllocs typ e := do! size <- fLet e in fAllocs' typ size.

  Definition getLen {GA typ} (x : member typ GA) (env : AVarEnv GA) : exp :=
    (fst (hget env x)).

  Fixpoint with_idx' {A : Type} {B : A -> Type} {ls : list A}
           (start : nat) (xs : hlist B ls) : hlist (fun x => nat * B x)%type ls :=
    match xs with
    | HNil => HNil
    | HCons x xs => 
      (start, x) ::: with_idx' (S start) xs
    end.

  Definition with_idx A B ls := @with_idx' A B ls 0.

  Definition invokeKernel kerID ntrd nblk (args : list exp) :=
    setI (host_invoke kerID ntrd nblk args).

  (* Definition collect_args (host_var_env : list (hostVar * list hostVar)) (GA : list Skel.CTyp) := *)
  (*   let f i := *)
  (*       let (len, arrs) := nth i host_var_env (0, nil) in *)
  (*       (len :: arrs) in *)
  (*   concat (List.map f fv). *)

  (* Definition filter_idx {T : Type} (xs : list T) s : list T := *)
  (*   let f (x : nat * T) := *)
  (*       let (i, x) := x in *)
  (*       NatSet.mem i s in *)
  (*   map snd (filter f (combine (seq 0 (length xs)) xs)). *)

  Fixpoint flatten_aenv {GA : list Skel.Typ}
           (xs : hlist (fun ty => (var * vars ty)%type) GA) :=
    match xs with
    | HNil => nil
    | HCons x xs => 
      let '(x, ls) := x in
      (x :: flatTup ls) ++ flatten_aenv xs
    end.

  Definition compile_map {GA dom cod} ntrd nblk
             (host_var_env : AVarEnv GA)
             (f : Skel.Func GA (Skel.Fun1 dom cod))
             (arr : Skel.AE GA dom)
    : CUDAM (var * vars cod) :=
    let arr_vars := gen_params GA in

    let g := compile_AE arr (remove_typeinfo arr_vars) in
    let outlen := compile_AE_len arr host_var_env in
    let f := compile_func f (remove_typeinfo arr_vars) in
    
    do! kerID <- gen_kernel (mkMap GA dom cod g f)  in
    do! outlenVar <- fLet outlen in
    do! outArr <- fAllocs cod outlenVar in
    let args_in := flatten_aenv host_var_env in
    let args_out := outlenVar :: (flatTup outArr) in
    do! t <- invokeKernel kerID (Zn ntrd) (Zn nblk) (List.map Evar (args_out ++ args_in)) in
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

  Fixpoint addTyp {ty} :=
    match ty return vars ty -> vartys ty with 
    | Skel.TBool => fun x => (x, Bool)
    | Skel.TZ => fun x => (x, Int)
    | Skel.TTup t1 t2 => fun xs => (addTyp (fst xs), addTyp (snd xs))
    end.

  Definition sh_decl len typ :=
    flatTup (
        maptys (fun sv => Grid.SD (fst sv) (snd sv) len)
               (addTyp (locals "sdata" typ 0))).

  Definition compile_reduce {GA typ} ntrd nblk
             (host_var_env : AVarEnv GA)
             (f : Skel.Func GA (Skel.Fun2 typ typ typ))
             (arr : Skel.AE GA typ) : CUDAM (var * vars typ) :=
    let dim := ctyps_of_typ typ in
    
    let arr_vars := gen_params GA in

    let get := compile_AE arr (remove_typeinfo arr_vars) in
    let outlen := compile_AE_len arr host_var_env in
    let func := compile_func f (remove_typeinfo arr_vars) in
    
    do! kerID1 <- gen_kernel (mkReduce GA typ ntrd get func) in
    do! lenVar <- fLet outlen in
    do! tempArr <- fAllocs typ (Z.of_nat nblk) in
    let args_in := flatten_aenv host_var_env in
    let args_out := lenVar :: flatTup tempArr in
    do! t <- invokeKernel kerID1 (Zn ntrd) (Zn nblk) (List.map Evar (args_out ++ args_in)) in

    let GA := typ :: GA in
    let arr_vars := gen_params GA in
    (* let params_temp := *)
    (*   let grp := NatSet.cardinal fvs_f in *)
    (*   ((len_name grp, Int), (arr_name grp dim)) in *)
    let get := @accessor_of_array GA typ (remove_typeinfo arr_vars) HFirst in
    let func := compile_func (shift_func_GA typ f) (remove_typeinfo arr_vars) in
    do! kerID2 <- gen_kernel (mkReduce GA typ nblk get func) in
    (* (Nat.min ((l + ntrd - 1) / ntrd) nblk ) *)
    do! lenVar <- fLet (minC ((outlen +C (Z.of_nat ntrd - 1)%Z) /C (Z.of_nat ntrd))
                            (Z.of_nat nblk)) in
    (* do! lenVar <- fLet (Const (Z.of_nat nblk)) in *)
    do! outlenVar <- fLet 1%Z in
    do! outArr <- fAllocs typ 1%Z in
    let args_temp := lenVar :: flatTup tempArr in
    let args_in := flatten_aenv host_var_env in
    let args_out := lenVar :: flatTup outArr in
    do! t <- invokeKernel kerID2 (Zn nblk) (Zn 1) (List.map Evar (args_out ++ args_temp ++ args_in)) in
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

  Fixpoint lexp2sexp GA typ (le : Skel.LExp GA typ) : forall GS, Skel.SExp GA GS typ :=
    match le in Skel.LExp _ typ' return forall GS, Skel.SExp GA GS typ' with
    | Skel.LNum _ n => fun GS => Skel.ENum GA GS n
    | Skel.LLen _ t m => fun GS => Skel.ELen _ _ _ m
    | Skel.LMin _ e1 e2 => fun GS => Skel.EBin _ _ _ _ _ Skel.Emin (lexp2sexp _ _ e1 GS) (lexp2sexp _ _ e2 GS)
    end.

  Definition compile_Skel {GA typ} ntrd nblk 
             (skel : Skel.SkelE GA typ) : AVarEnv GA -> CUDAM (var * vars typ) :=
    match skel in Skel.SkelE GA typ return AVarEnv GA -> _ with
    | Skel.Map _ dom cod f arr => fun aenv =>
      compile_map ntrd nblk aenv f arr
    | Skel.Reduce _ typ f arr => fun aenv =>
      compile_reduce ntrd nblk aenv f arr
    | Skel.Seq GA start len => fun aenv =>
      let f := Skel.F1 GA Skel.TZ Skel.TZ (Skel.EVar _ _ _ HFirst) in
      let g := Skel.DArr GA _ (Skel.F1 GA Skel.TZ Skel.TZ (Skel.EBin GA _ _ _ _ Skel.Eplus
                                                                     (lexp2sexp _ _ start _)
                                                                     (Skel.EVar _ _ _ HFirst))) len in
      compile_map ntrd nblk aenv f g
    | Skel.Zip _ typ1 typ2 arr1 arr2 => fun aenv =>
      let f := Skel.F1 _ (Skel.TTup typ1 typ2) (Skel.TTup typ1 typ2) (Skel.EVar _ _ _ HFirst) in
      let arr := zip_AE arr1 arr2 in
      compile_map ntrd nblk aenv f arr
    end.

  Definition compile_res {GA typ} ntrd nblk
             (host_var_env : AVarEnv GA)
             (arr : Skel.AE GA typ) (outArr : vars typ)
    : CUDAM var :=
    let arr_vars := gen_params GA in

    let g := compile_AE arr (remove_typeinfo arr_vars) in
    let outlen := compile_AE_len arr host_var_env in
    let f := Skel.F1 _ typ typ (Skel.EVar _ _ _ HFirst) in
    let f := compile_func f (remove_typeinfo arr_vars) in
    
    do! kerID <- gen_kernel (mkMap GA typ typ g f)  in
    do! outlenVar <- fLet outlen in
    let args_in := flatten_aenv host_var_env in
    let args_out := outlenVar :: (flatTup outArr) in
    do! t <- invokeKernel kerID (Zn ntrd) (Zn nblk) (List.map Evar (args_out ++ args_in)) in
    ret outlenVar.

  Fixpoint compile_AS {GA typ} ntrd nblk 
           (p : Skel.AS GA typ) : vars typ -> AVarEnv GA -> CUDAM var :=
    match p with
    | Skel.ALet _ tskel tyres skel res => fun outArr aenv => 
      do! outs <- compile_Skel ntrd nblk skel aenv in
      compile_AS ntrd nblk res outArr (outs ::: aenv) 
    | Skel.ARet _ t x => fun outArr aenv =>
      let arr := Skel.VArr _ _ x in
      compile_res ntrd nblk aenv arr outArr
    end%list.

  Definition hostVars_of_typ (ty : Skel.Typ) (n : nat) :=
    let ctys := ctyps_of_typ ty in
    (n, List.combine ctys (List.seq (S n) (length ctys))).

  (* Sx.prog = (list (varA * Sx.Typ) * Sx.AS)%type *)
  (* : Type *)

  (* Definition gen_env (GA : list Skel.Typ) : nat * list (var * list (CTyp * var)) := *)
  (*   List.fold_right (fun typ (acc : nat * list (var * list (CTyp * var))) => *)
  (*     let (n, acc) := acc in *)
  (*     (n + S (length (ctyps_of_typ typ)), (hostVars_of_typ typ n) :: acc)) *)
  (*   (0, nil) GA. *)
  
  Fixpoint toPtr {typ} : vartys typ -> vartys typ :=
    match typ return vartys typ -> vartys typ with
    | Skel.TZ | Skel.TBool => fun x => (fst x, Ptr (snd x))
    | Skel.TTup t1 t2 => fun xs =>
      (toPtr (fst xs), toPtr (snd xs))
    end.

  Definition seqs := List.fold_right host_seq host_skip.

  Definition compile_prog {GA ty} ntrd nblk (p : Skel.AS GA ty) : Host.GModule :=
    let ps := gen_params GA in 
    let aenv := remove_typeinfo ps in
    let outs := outArr ty in
    let '(res, (_, instrs, kers)) := compile_AS ntrd nblk p outs aenv 0 0 in
    let pars := (inp_len_name, Int) :: flatTup (with_PTyp outs) ++ 
                   flatten_avars (gen_params (List.rev GA)) in
    (("__main", Host (Hf pars (seqs instrs) res)) :: kers).
End Compiler.
