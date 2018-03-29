Require Import Monad DepList GPUCSL TypedTerm.
Require Import String List Program.Equality LibTactics.
Require Import CUDALib CSLLemma CodeGen.

Notation SVarEnv GS := (hlist (fun typ : Skel.Typ => vars typ) GS).
Notation SEvalEnv GS := (hlist Skel.typDenote GS).
Notation AVarEnv GA := (hlist (fun typ : Skel.Typ => (var * vars typ)%type) GA).
Notation APtrEnv GA := (hlist (fun typ => vals typ) GA).
Notation AEvalEnv GA := (hlist Skel.aTypDenote GA).

Fixpoint fold_hlist {A B C} (ls : list A) (g : B -> C -> C) (d : C) :=
  match ls return (forall x, member x ls -> B) -> C with
  | nil => fun _ => d
  | x :: ls => fun f => g (f x HFirst) (fold_hlist ls g d (fun x m => f x (HNext m)))
  end.

(* Bad naming: convert TypedIR level value to CUDA level value
 *)
Fixpoint sc2CUDA {ty} : Skel.typDenote ty -> vals ty :=
  match ty return Skel.typDenote ty -> vals ty with
  | Skel.TBool => fun b => if b then 1 else 0
  | Skel.TZ => fun n => n
  | Skel.TTup t1 t2 => fun p => (sc2CUDA (fst p), sc2CUDA (snd p))
  end%Z.

Definition arr2CUDA {ty} : Skel.aTypDenote ty -> list (vals ty) := map sc2CUDA.

Definition arrInvRes {GA} (aPtrEnv : APtrEnv GA) (aEvalEnv : AEvalEnv GA) p : res :=
  fold_hlist GA Star Emp
    (fun x m => arrays (val2gl (hget aPtrEnv m)) (arr2CUDA (hget aEvalEnv m)) p).

Definition arrInvVar {GA} (aVarEnv : AVarEnv GA) (aPtrEnv : APtrEnv GA) (aEvalEnv : AEvalEnv GA) : list entry :=
  fold_hlist GA (@app entry) nil
    (fun x m => let (xlen, xarr) := hget aVarEnv m in
                xlen |-> Zn (length (hget aEvalEnv m)) :: xarr |=> hget aPtrEnv m).

Definition scInv {GS} (sVarEnv : SVarEnv GS) (sEvalEnv : SEvalEnv GS) :=
  fold_hlist GS (@app entry) nil
    (fun x m => (hget sVarEnv m) |=> sc2CUDA (hget sEvalEnv m)). 

Definition sexpInv {GS GA}
           (sVarEnv : SVarEnv GS) (sEvalEnv : SEvalEnv GS)
           (aVarEnv : AVarEnv GA) (aPtrEnv : APtrEnv GA) (aEvalEnv : AEvalEnv GA) R P resEnv p :=
  Assn (arrInvRes aPtrEnv aEvalEnv p *** R)
       P
       (resEnv ++ scInv sVarEnv sEvalEnv ++ arrInvVar aVarEnv aPtrEnv aEvalEnv).

Definition kernelInv {GA} 
           (aVarEnv : AVarEnv GA) (aPtrEnv : APtrEnv GA) (aEvalEnv : AEvalEnv GA) R P resEnv p := 
  Assn (arrInvRes aPtrEnv aEvalEnv p *** R) P (resEnv ++ arrInvVar aVarEnv aPtrEnv aEvalEnv).

Definition kernelInv' {GA} 
           (aPtrEnv : APtrEnv GA) (aEvalEnv : AEvalEnv GA) R P p := 
  Assn (arrInvRes aPtrEnv aEvalEnv p *** R) P nil.

Definition aenv_ok {GA} (avar_env : AVarEnv GA) :=
  (forall ty (m : member ty GA), prefix "_" (str_of_var (fst (hget avar_env m))) = true)
  /\ (forall (ty : Skel.Typ) (m : member ty GA) (y : var),
         In y (flatTup (snd (hget avar_env m)))
         -> prefix "_" (str_of_var y) = true).

Definition senv_ok {GS} (svar_env : SVarEnv GS) n :=
  (forall (ty : Skel.Typ) (m : member ty GS) (k : nat) l,
      In (Var (lpref k ++ l)) (flatTup (hget svar_env m)) -> k < n).

Definition resEnv_ok resEnv n := 
  forall v (k : nat) l,
    In ((lpref k ++ l)%string |-> v) resEnv -> k < n.


Definition is_local (x : var) : Prop := prefix "l" (str_of_var x) = true.
Definition are_local {ty} (xs : vars ty) : Prop :=
  forall x, In x (flatTup xs) -> is_local x.

Definition type_of_ftyp (fty : Skel.FTyp) :=
  match fty with
  | Skel.Fun1 dom cod => vars dom -> (cmd * vars cod)
  | Skel.Fun2 dom1 dom2 cod => vars dom1 -> vars dom2 -> (cmd * vars cod)
  end.

Definition func_ok1 {GA dom cod} (avar_env : AVarEnv GA) 
           (f : Skel.Func GA (Skel.Fun1 dom cod)) (func : type_of_ftyp (Skel.Fun1 dom cod)) :=
  aenv_ok avar_env 
  -> (* func only writes to local variables *)
     (forall x l, In l (writes_var (fst (func x))) -> is_local l) /\
     (* func only returs to local variables or parameter *)
     (forall x l, In l (flatTup (snd (func x))) -> is_local l \/ In l (flatTup x)) /\
     (* functional correctenss *)
     (forall ntrd (tid : Fin.t ntrd) BS xs vs res aptr_env aeval_env R (P : Prop) resEnv p,
         (forall l, In l (flatTup xs) -> ~is_local l)
         -> (forall l v, In (l |-> v) resEnv -> ~is_local l)
         -> evalExps resEnv (v2e xs) (sc2CUDA vs)
         -> (P -> Skel.funcDenote _ _ f aeval_env vs = Some res)
         -> CSL BS tid
                (kernelInv avar_env aptr_env aeval_env R P resEnv p)
                (fst (func xs))
                (kernelInv avar_env aptr_env aeval_env R P
                           (snd (func xs) |=> sc2CUDA res ++ resEnv) p)) /\
     (forall x, barriers (fst (func x)) = nil).

Definition func_ok2 {GA dom1 dom2 cod} (avar_env : AVarEnv GA) 
           (f : Skel.Func GA (Skel.Fun2 dom1 dom2 cod)) (func : type_of_ftyp (Skel.Fun2 dom1 dom2 cod)) :=
  aenv_ok avar_env 
  -> (* func only writes to local variables *)
     (forall x y l, In l (writes_var (fst (func x y))) -> is_local l) /\
     (* func only returs to local variables or parameter *)
     (forall x y l, In l (flatTup (snd (func x y))) -> is_local l \/ In l (flatTup x) \/ In l (flatTup y)) /\
     (* functional correctenss *)
     (forall ntrd (tid : Fin.t ntrd) BS xs ys vs1 vs2 res aptr_env aeval_env R (P : Prop) resEnv p,
         (forall l, In l (flatTup xs) -> ~is_local l)
         -> (forall l, In l (flatTup ys) -> ~is_local l)
         -> (forall l v, In (l |-> v) resEnv -> ~is_local l)
         -> evalExps resEnv (v2e xs) (sc2CUDA vs1)
         -> evalExps resEnv (v2e ys) (sc2CUDA vs2)
         -> (P -> Skel.funcDenote _ _ f aeval_env vs1 vs2 = Some res)
         -> CSL BS tid
                (kernelInv avar_env aptr_env aeval_env R P resEnv p)
                (fst (func xs ys))
                (kernelInv avar_env aptr_env aeval_env R P
                           (snd (func xs ys) |=> sc2CUDA res ++  resEnv) p)) /\
     (forall xs ys, barriers (fst (func xs ys)) = nil).

Definition func_ok {GA fty} (avar_env : AVarEnv GA) :=
  match fty return Skel.Func GA fty -> type_of_ftyp fty -> Prop with
  | Skel.Fun1 dom cod => fun f func => func_ok1 avar_env f func
  | Skel.Fun2 dom1 dom2 cod => fun f func => func_ok2 avar_env f func 
  end.

Fixpoint defval' {ty} : Skel.typDenote ty :=
  match ty return Skel.typDenote ty with
  | Skel.TBool => false
  | Skel.TZ => 0%Z
  | Skel.TTup t1 t2 => (@defval' t1, @defval' t2)
  end.

Lemma defval_sc2CUDA ty : (@defval ty) = sc2CUDA (@defval' ty). 
Proof.
  induction ty; simpl; try congruence.
Qed.

Notation gets' arr i := (nth i arr defval').
Eval simpl in type_of_ftyp (Skel.Fun1 Skel.TZ _).

Definition ae_ok {GA ty} (avar_env : AVarEnv GA) (ae : Skel.AE GA ty) (arr : var -> cmd * vars ty) :=
  aenv_ok avar_env
  -> (* func only writes to local variables *)
     (forall x l, In l (writes_var (fst (arr x))) -> is_local l) /\
     (* func only returs to local variables or parameter *)
     (forall x l, In l (flatTup (snd (arr x))) -> is_local l \/ l = x) /\
     (* functional correctenss *)
     (forall ntrd (tid : Fin.t ntrd) BS ix i res aptr_env aeval_env R (P : Prop) resEnv p,
         ~is_local ix
         -> (forall l v, In (l |-> v) resEnv -> ~is_local l)
         -> evalExp resEnv ix (Zn i)
         -> (Skel.aeDenote _ _ ae aeval_env = Some res)
         -> (P -> i < length res)
         -> CSL BS tid
                (kernelInv avar_env aptr_env aeval_env R P resEnv p)
                (fst (arr ix))
                (kernelInv avar_env aptr_env aeval_env R P
                           ((snd (arr ix)) |=> sc2CUDA (gets' res i) ++ resEnv) p)) /\
     (forall x, barriers (fst (arr x)) = nil).