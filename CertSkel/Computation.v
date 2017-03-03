Require Import DepList.
Require Import GPUCSL.
(* Require Import Host SimplSkel Compiler. *)
Require Import Monad.
Require Import LibTactics.
Require Import TypedTerm.
Require Import Correctness Host.
Open Scope list_scope.

Open Scope Z_scope.

Require Import SkelLib.
(* Notation equiv := equiv1. *)

Lemma change_spec {A : Type} (P Q : A -> Prop) : (forall x, P x -> Q x) -> {x : A | P x} -> {x : A | Q x}.
Proof.
  intros ? [? ?]; eexists; eauto.
Qed.

Lemma let_bind {A B : Type} (t : list A) (f : list A -> comp B) : (let x := t in f x) = (do! x <- ret t in f x).
Proof. eauto. Qed.

Lemma let_lift1 {A B : Type} (f : A -> comp B) (xs : A) : f xs = do! t <- ret xs in f t.
Proof. eauto. Qed.

Definition skels := (tt, @reduceM, @zip, seq).

Ltac in_xs x xs :=
  lazymatch xs with
  | (?rest, x) => idtac
  | (?rest, ?y) => in_xs x rest
  end.

Ltac in_skels skel :=
  let skels := eval unfold skels in skels in
  in_xs skel skels.

Ltac findArgs skel term :=
  match term with
  | context [skel ?a0] => constr:(tt, a0)
  | context [skel ?a0 ?a1] => constr:(tt, a0, a1)
  | context [skel ?a0 ?a1 ?a2] => constr:(tt, a0, a1, a2)
  | context [skel ?a0 ?a1 ?a2 ?a3] => constr:(tt, a0, a1, a2, a3)
  | context [skel ?a0 ?a1 ?a2 ?a3 ?a4] => constr:(a0, a1, a2, a3, a4)
  | context [skel ?a0 ?a1 ?a2 ?a3 ?a4 ?a5] => constr:(a0, a1, a2, a3, a4, a5)
  | context [skel ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6] => constr:(a0, a1, a2, a3, a4, a5, a6)
  end.

Ltac forEach f xs :=
  match xs with
  | tt => idtac
  | (?xs, ?x) => f x; forEach xs f
  end.

Lemma let_lift2 {A B C : Type} (ae : list A) (f : list A -> comp B) (g : B -> comp C) :
  (do! t <- do! u <- ret ae in f u in g t) = (do! u <- ret ae in do! t <- f u in g t).
Proof. eauto. Qed.

Definition myfst {A B} (x : A * B) := match x with (x, y) => x end.
Definition mysnd {A B} (x : A * B) := match x with (x, y) => y end.

Ltac eval_tup t :=
  let t := eval unfold myfst in t in
  let t := eval unfold mysnd in t in
  let t := eval cbv beta in t in
  t.

(* convert last ``skel e1 e2'' to ``do! t <- skel e1 e2 in t'' *)
Ltac bind_last term k :=
  idtac "term = " term;
  lazymatch term with
  | (fun x => do! y <- ?t in @?u x y) =>
    let c := eval cbv beta in (fun t => u (myfst t) (mysnd t)) in
    bind_last c ltac:(fun f =>
    let res := eval cbv beta in (fun x => do! y <- t in f (x, y)) in
    k res)
  | (fun x => @?u x) =>
    let ty := type of u in
    idtac u ":" ty;
    match ty with
    | _ -> comp _ => k (fun x => do! y <- u x in ret y)
    | _ => k term
    end
  end.

Ltac dest :=
  unfold bind, ret; simpl; repeat match goal with
  | [|- context [bind_opt _ _ ?t _]] => destruct t; simpl
  end; eauto.

Open Scope string_scope.

(* Phantom type for tracking generated variable names *)
Definition TyVar {TyV : Type} (x : TyV) (T : Type) := T.

Ltac simplify_type t := 
  lazymatch t with
  | list ?t => simplify_type t
  | comp ?t => simplify_type t
  | TyVar _ ?ty => simplify_type ty
  | ?t => t
  end.

(* Reifying type expressions *)
Ltac reify_type t k :=
  idtac "type_reify t = " t;
  let rec tac t k :=
      lazymatch t with
      | Z => k Skel.TZ
      | bool => k Skel.TBool
      | (?ty1 * ?ty2)%type =>
        tac ty1 ltac:(fun ty1' =>
        tac ty2 ltac:(fun ty2' =>
        k (Skel.TTup ty1' ty2')))
      end in
  let t := simplify_type t in
  tac t k.

Goal False.
  reify_type (list Z) ltac:(fun ty => pose ty).
Abort.

Goal False.
  pose (fun x : nat => 0).
  lazymatch eval cbv in z with
  | (fun (x : ?T) => @?f x) => pose f
  end.
Abort.

(* get variable name information from type of expression fun (x : T1 * T2 * ..) -> ? *)
Notation VarA := id.
Notation VarE := id.
Ltac get_name x k :=
  idtac "get_name x =" x;
  lazymatch type of x with
  | (_ -> TyVar ?name ?ty) =>
    reify_type ty ltac:(fun ty' =>
    idtac "get_name name ty' = " name ty';
    k name ty')
  | _ => k (VarA "error") Skel.TZ
  end.

Ltac collect_params T k :=
  idtac "collect_params T = " T;
  lazymatch T with
  | (unit * ?t)%type => 
    collect_params t k
  | (?t1 * ?t2)%type =>
    collect_params t1 ltac:(fun ps1 =>
    collect_params t2 ltac:(fun ps2 =>
    idtac "collect_params t1 t2 = " t1 t2;
    let t := eval compute in (ps1 ++ ps2)%list in k t))
  | TyVar ?name ?ty =>
    reify_type ty ltac:(fun ty =>
    k ((name, ty) :: nil))
  end.

Goal False.
  let t := constr:(unit * TyVar (VarE "xO") (Z * Z) * TyVar (VarE "xSO") (Z * Z))%type in
  (* let t := constr:(TyVar (VarE "xO") (Z * Z)) in *)
  collect_params t ltac:(fun t =>
  pose t).
Abort.

Goal False.
  let t := lazymatch O with
  | (?t : Z) => t
  end in pose t.
Abort.

Ltac binOp op k :=
  match op with
  | Z.add => k Skel.Eplus
  | Z.mul => k Skel.Emult
  | Z.min => k Skel.Emin
  | Z.ltb => k Skel.Blt
  | Z.eqb => k Skel.BEq
  end.

Ltac traverseTyVar acc k :=
  idtac "traverseTyVar: T acc = " acc;
  let rec tac acc k :=
      idtac "tac in traverseTyVar: acc = " acc;
      lazymatch acc with
      | (fun (x : ?T) => x) => k T
      | (fun (x : ?T) => myfst (@?acc x)) =>
        tac acc ltac:(fun T =>
        idtac "fst case of tac in traverseTyVar: T = " T;
        lazymatch T with
        | (?T * _)%type => k T
        end)
      | (fun (x : ?T) => mysnd (@?acc x)) =>
        tac acc ltac:(fun T =>
        idtac "snd case of tac in traverseTyVar: T = " T;
        lazymatch T with
        | (_ * ?T)%type => k T
        end)
      end in
  tac acc ltac:(fun T =>
  idtac "post processing in traverseTyVar: T = " T;
  lazymatch T with
  | TyVar ?name _ => k name
  end).

Arguments Skel.ENum {GA GS} _.

Ltac searchType GS f :=
  lazymatch f with
  | (fun p => myfst (@?f' p)) =>
    let res := searchType GS f' in
    constr:(fun x : nat => res (S x))
  | (fun p => mysnd (@?f' p)) =>
    let res := searchType GS f' in
    constr:(res 0%nat)
  | (fun p => p) =>
    constr:(fun x : nat => x)
  end.

Ltac proveMember GS n :=
  lazymatch n with
  | O => 
    lazymatch GS with
    | ?t :: ?GS => 
      constr:(@HFirst _ t GS)
    end
  | S ?n => 
    lazymatch GS with
    | ?x :: ?GS => 
      let t := proveMember GS n in
      constr:(@HNext _ _ x GS t)
    end
  end.
      
Ltac member GS f :=
  let t := searchType GS f in
  let t := eval cbv beta in t in
  proveMember GS t.

Goal False.
  let t := member (Z :: Z :: Z :: nil) (fun p : (unit * Z * Z * Z) => mysnd (myfst (myfst p))) in pose t.
Abort.

Ltac scalarExpr GA GS f k :=
  idtac "scalarExpr: f = " f;
  let resTy := match type of f with _ -> _ -> ?Ty => Ty end in
  idtac "scalarExpr: resTy = " resTy;
  reify_type resTy ltac:(fun resTy' =>
  idtac "scalarExpr: resTy' = " resTy';
  match f with
  | (fun a _ => ?c) =>
    idtac "scalarExpr: matched to constant case";
    lazymatch type of c with Z => k (Skel.ENum GA GS c) end
  | (fun a (x : ?T) => let y := @?t1 a x in @?t2 a x y) =>
    idtac "scalarExpr: matched to let case";
    lazymatch type of t1 with
    | _ -> _ -> ?Ty =>
      scalarExpr GA GS t1 ltac:(fun t1' =>
      reify_type Ty ltac:(fun ty1 =>
      let t2 := eval cbv beta in (fun a (p : T * Ty) => t2 a (myfst p) (mysnd p)) in
      scalarExpr GA (ty1 :: GS) t2 ltac:(fun t2' =>
      k (Skel.ELet _ _ _ _ t1' t2'))))
    end
  | (fun a (x : ?T) => do! y <- @?t1 a x in @?t2 a x y) =>
    idtac "scalarExpr: matched to let case";
    lazymatch type of t1 with
    | _ -> _ -> comp ?Ty =>
      scalarExpr GA GS t1 ltac:(fun t1' =>
      reify_type Ty ltac:(fun ty1 =>
      let t2 := eval cbv beta in (fun a (p : T * Ty) => t2 a (myfst p) (mysnd p)) in
      scalarExpr GA (ty1 :: GS) t2 ltac:(fun t2' =>
      k (Skel.ELet _ _ _ _ t1' t2'))))
    end
  | (fun a (x : ?T) => if @?cond a x then @?th a x else @?el a x) =>
    idtac "scalarExpr: matched to if case";
    scalarExpr GA GS cond ltac:(fun cond' =>
    idtac "scalarExpr cond' = " cond';
    scalarExpr GA GS th ltac:(fun th' =>
    idtac "scalarExpr: th' = " th';
    scalarExpr GA GS el ltac:(fun el' =>
    idtac "scalarExpr: el' = " el';
    k (Skel.EIf GA GS resTy' cond' th' el'))))
  | (fun a (x : ?T) => ?op (@?e1 a x) (@?e2 a x)) =>
    idtac "scalarExpr: matched to binop case";
    binOp op ltac:(fun op' =>
    scalarExpr GA GS e1 ltac:(fun e1' =>
    scalarExpr GA GS e2 ltac:(fun e2' =>
    lazymatch type of op' with
    | Skel.BinOp ?t1 ?t2 ?t3 => k (Skel.EBin GA GS t1 t2 t3 op' e1' e2')
    end)))
  | (fun a (x : ?T) => @fst _ _ (@?e a x)) =>
    idtac "scalarExpr: matched to fst case e =" e;
    scalarExpr GA GS e ltac:(fun e' =>
    idtac "scalarExpr: e' = " e';
    k (Skel.EPrj1 GA GS _ _ e'))
  | (fun a (x : ?T) => @snd _ _ (@?e a x)) =>
    idtac "scalarExpr: matched to snd case e =" e;
    scalarExpr GA GS e ltac:(fun e' =>
    k (Skel.EPrj2 GA GS _ _ e'))
  | (fun a (x : ?T) => (@?e1 a x, @?e2 a x)) =>
    idtac "scalarExpr: matched to cons case e1, e2 =" e1 e2;
    scalarExpr GA GS e1 ltac:(fun e1' =>
    scalarExpr GA GS e2 ltac:(fun e2' =>
    k (Skel.ECons GA GS _ _ e1' e2')))
  | (fun a (x : ?T) => ret (@?e a x)) =>
    idtac "scalarExpr: matched ret case e =" e;
    scalarExpr GA GS e k
  | (fun a (x : ?T) => (@?e x)) =>
    idtac "scalarExpr: matched var case e =" e;
    let m := member GS e in
    k (Skel.EVar GA GS _ m)
  | (fun a x => nth_error (@?arr a) (@?idx a x)) =>
    idtac "scalarExpr: matched nth case arr, idx =" arr idx;
    let m := member GA arr in
    scalarExpr GA GS idx ltac:(fun idx' =>
    idtac "scalarExpr: m, idx' = " m idx';
    k (Skel.EA GA GS _ m idx'))
  | (fun a x => len (@?arr a)) =>
    idtac "scalarExpr: matched len case arr =" arr;
    let m := member GA arr in
    k (Skel.ELen GA GS _ m)
  end).

Goal False.
  let t := constr:(fun (a : unit) (p : unit * (Z * Z) * (Z * Z)) => (mysnd (myfst p))) in
  let GS := constr:((Skel.TTup Skel.TZ Skel.TZ) :: (Skel.TTup Skel.TZ Skel.TZ) :: nil) in
  let GA := constr:(@nil Skel.Typ) in
  scalarExpr GA GS t ltac:(fun t => pose t).
  let t := constr:(fun (a : unit * list Z) (p : unit * Z) => nth_error (mysnd a) (mysnd p)) in
  let GS := constr:(Skel.TZ :: nil) in
  let GA := constr:(Skel.TZ :: nil) in
  scalarExpr GA GS t ltac:(fun t => pose t).
  let t := constr:(fun (a : unit * list Z) (p : unit * Z) => len (mysnd a)) in
  let GS := constr:(Skel.TZ :: nil) in
  let GA := constr:(Skel.TZ :: nil) in
  scalarExpr GA GS t ltac:(fun t => pose t).

  Eval simpl in (Skel.sexpDenote _ _ _ s HNil (HCons ((1, 3) : Skel.typDenote (Skel.TTup Skel.TZ Skel.TZ))
                                              (HCons ((4, 5) : Skel.typDenote (Skel.TTup Skel.TZ Skel.TZ)) HNil)))%Z.
Abort.

Ltac scalarFunc GA f k :=
  idtac "scalarFunc f = " f;
  lazymatch f with
  | (fun (a : ?T) (x : ?T1) (y : ?T2) => @?f a x y) =>
    idtac "scalarFunc: matched to inductive case";
    let t := eval cbv beta in (fun a (p : unit * T1 * T2) => f a (mysnd (myfst p)) (mysnd p)) in
    reify_type T1 ltac:(fun ty1 =>
    reify_type T2 ltac:(fun ty2 =>
    scalarExpr GA (ty1 :: ty2 :: nil) t ltac:(fun res =>
    k (Skel.F2 _ _ _ _  res))))
  | (fun (a : ?T) (x : ?T1) => @?f a x) =>
    idtac "scalarFunc: matched to base case";
    idtac "scalarFunc: T = " T1;
    let t := eval cbv beta in (fun a (p : unit * T1) => f a (mysnd p)) in
    reify_type T1 ltac:(fun ty =>
    scalarExpr GA (ty :: nil) t ltac:(fun res =>
    k (Skel.F1 _ _ _  res)))
  end.

Goal False.
  scalarFunc (@nil Skel.Typ) (fun (a : unit) (x y : Z) => Z.min x y) ltac:(fun res => 
  let t := eval simpl in (Skel.funcDenote nil _ res) in pose t).
  scalarFunc (@nil Skel.Typ) (fun (a : unit) (x y : Z) => x + y) ltac:(fun res =>
  let t := eval simpl in (Skel.funcDenote nil _ res) in pose t).
  scalarFunc (@nil Skel.Typ) (fun (a : unit) (x y : Z) => let z := x + y in z) ltac:(fun res => 
  let t := eval simpl in (Skel.funcDenote nil _ res) in pose t).
  scalarFunc (@nil Skel.Typ) 
             (fun (a : unit) (x y : Z * Z) => if (fst x) <? (fst y) then ret x else ret y) ltac:(fun res => 
  let t := eval simpl in (Skel.funcDenote nil _ res) in pose t).
Abort.

Ltac lexpr GA e k :=
  idtac "lexpr e = " e;
  lazymatch e with
  | (fun x => len (@?acc x)) =>
    let m := member GA acc in
    k (Skel.LLen _ _ m)
  | (fun x => ?c) =>
    lazymatch type of c with
    | nat => k (Skel.LNum GA (Z.of_nat c))
    | Z => k (Skel.LNum GA c)
    end
  end.

Goal False.
  lexpr (@nil Skel.Typ) (fun _ : unit => 1) ltac:(fun e => pose e).
  lexpr (Skel.TZ :: nil) (fun x : (unit * list Z) => (len (mysnd x))) ltac:(fun e => pose e).
Abort.

Definition gen {T} (f : Z -> comp T) (len : Z) :=
  mapM f (seq 0 len).

Ltac reifyAE GA f k :=
  idtac "reifyAE f = " f;
  lazymatch f with
  | (fun (x : ?T) => gen (@?f x) (@?len x)) =>
    idtac "match to gen case";
    idtac "reifyAE: f = " f;
    idtac "reifyAE: len = " len;
    scalarFunc GA f ltac:(fun f' =>
    idtac "reifyAE: f' = " f';                            
    lexpr GA len ltac:(fun l =>
    idtac "reifyAE: f' l =" f' l;
    k (Skel.DArr _ _ f' l)))
  | (fun (x : ?T) => (@?acc x)) =>
    idtac "reifyAE: match to length case";
    idtac "reifyAE acc = " acc;
    let m := member GA acc in
    idtac "reifyAE m = " m;
    k (Skel.VArr _ _ m)
  end.

Goal False.
  let t := constr:(fun (_ : unit) => gen (fun x : Z => ret x) 3) in
  reifyAE (@nil Skel.Typ) t ltac:(fun res => pose res).
  let t := constr:(fun (x : unit * list Z) => (mysnd x)) in
  reifyAE (Skel.TZ :: nil) t ltac:(fun res => pose res).
  let t := constr:(fun (x : unit * list Z) =>
                     gen (fun x : Z => ret x) (len (mysnd x))) in
  reifyAE (Skel.TZ :: nil) t ltac:(fun res => pose res).
Abort.

(* ``skelApp'' generate a syntax tree from skeleton application expression.
   ``skelApp'' returns reifyed type of skeleton application and converted syntax tree *)
Ltac skelApp GA f k :=
  idtac "skelApp f = " f;
  lazymatch f with
  | (fun (x : ?T) => ret (seq (@?begin x) (@?len x))) =>
    lexpr GA begin ltac:(fun begin' =>
    lexpr GA len ltac:(fun len' =>
    idtac "match to seq";
    k (Skel.Seq GA begin' len')))
  | (fun (x : ?T) => ret (zip (@?arr1 x) (@?arr2 x))) =>
    idtac "match to zip";
    reifyAE GA arr1 ltac:(fun arr1 =>
    reifyAE GA arr2 ltac:(fun arr2 =>
    idtac arr1 arr2;
    k (Skel.Zip _ _ _ arr1 arr2)))
  | (fun (x : ?T) => do! a1 <- (@?arr1 x) in do! a2 <- (@?arr2 x) in zip a1 a2) =>
    idtac "match to zip";
    reifyAE GA arr1 ltac:(fun arr1 =>
    reifyAE GA arr2 ltac:(fun arr2 =>
    idtac arr1 arr2;
    k (Skel.Zip _ _ _ arr1 arr2)))
  | (fun (x : ?T) => reduceM (@?f x) (@?arr x)) =>
    idtac "match to reduce";
    idtac "skelApp: f, arr = " f arr;
    reifyAE GA arr ltac:(fun arr =>
    scalarFunc GA f ltac:(fun f =>
    k (Skel.Reduce _ _ f arr)))
  | (fun (x : ?T) => do! a <- (@?arr x) in reduceM (@?f x) a) =>
    idtac "match to reduce";
    idtac "skelApp: f, arr = " f arr;
    reifyAE GA arr ltac:(fun arr =>
    scalarFunc GA f ltac:(fun f =>
    k (Skel.Reduce _ _ f arr)))
  | (fun (x : ?T) => mapM (@?f x) (@?arr x)) =>
    idtac "match to map";
    idtac "skelApp: f, arr = " f arr;
    reifyAE GA arr ltac:(fun arr =>
    scalarFunc GA f ltac:(fun f =>
    k (Skel.Map _ _ _ f arr)))
  | (fun (x : ?T) => do! a <- (@?arr x) in mapM (@?f x) a) =>
    idtac "match to map";
    idtac "skelApp: f, arr = " f arr;
    reifyAE GA arr ltac:(fun arr =>
    scalarFunc GA f ltac:(fun f =>
    k (Skel.Map _ _ _ f arr)))
  end.

Goal False.
  let t := constr:(fun p : (unit * list Z) => ret (seq 0 (len (mysnd p)))) in
  skelApp (Skel.TZ :: nil) t ltac:(fun x => pose x as seqex).
  let t := constr:(fun p : (unit * list Z * list Z) => ret (zip (mysnd p) (mysnd (myfst p)))) in
  skelApp (Skel.TZ :: Skel.TZ :: nil) t ltac:(fun x => pose x as zipex).
  let t := constr:(fun (p : unit * list (Z * Z)) =>
                  reduceM (fun x y => if fst x <? fst y then ret x else ret y) (mysnd p)) in
  skelApp (Skel.TTup Skel.TZ Skel.TZ :: Skel.TTup Skel.TZ Skel.TZ :: nil) t ltac:(fun x => pose x as reduceex).
  Eval simpl in (Skel.skelDenote (Skel.TZ :: nil) _ seqex).
  Eval simpl in (Skel.skelDenote (Skel.TZ :: Skel.TZ :: nil) _ zipex).
  Eval simpl in (Skel.skelDenote (Skel.TTup Skel.TZ Skel.TZ :: Skel.TTup Skel.TZ Skel.TZ :: nil) _ reduceex).  
Abort.

Ltac transform' GA prog k :=
  idtac "prog = " prog;
  lazymatch prog with
    (* Note that @?c x t should not be @?c t x, the captured term by c would be malformed *)
  | (fun (x : ?T) => do! t <- @?ae x in @?c x t) =>
    idtac "match do case";
    let T_of_ae := lazymatch type of ae with _ -> comp ?T => T end in
    let c' := eval cbv beta in (fun (x : T * T_of_ae) => c (myfst x) (mysnd x)) in
    reify_type T_of_ae ltac:(fun ty =>
    idtac "transform': ty = " ty;
    skelApp GA ae ltac:(fun sexp => 
    idtac "transform' : sexp = " sexp;
    transform' (ty :: GA) c' ltac:(fun c' => k (Skel.ALet _ _ _ sexp c'))))
  | (fun (x : ?T) => ret (@?c x)) =>
    idtac "match res case";
    let m := member GA c in
    k (Skel.ARet _ _ m)
  end.

Goal False.
  let t := constr:(
  fun (x : unit * list Z) =>
    do! idx <- ret (seq 0 (len (mysnd x))) in
    do! arrIdx <- ret (zip (mysnd x) idx) in
    do! res <- reduceM (fun x y : Z * Z => if fst x <? fst y then ret x else ret y) arrIdx in
    ret res : comp _) in
  transform' (Skel.TZ :: nil) t ltac:(fun res => pose res as prog).
  Eval simpl in Skel.asDenote (Skel.TZ :: nil) _ prog.
Abort.

(* Ltac collect_paramsA T := *)
(*   lazymatch T with *)
(*   | (?t1 * ?t2)%type => *)
(*     let ps1 := collect_paramsA t1 in  *)
(*     let ps2 := collect_paramsA t2 in  *)
(*     eval compute in (ps1 ++ ps2)%list *)
(*   | TyVar ?name _ => constr:((name, Sx.TZ) :: nil) *)
(*   | _ => constr:(@nil (varA * Sx.Typ)) *)
(*   end. *)

Ltac transform0 GA prog k :=
  idtac "transform prog = " prog;
  lazymatch prog with
  | (fun (x : ?T1) (y : ?T2) => @?f x y) =>
    idtac "match inductive";
    let t := eval cbv beta in (fun (p : T1 * T2) => f (myfst p) (mysnd p)) in
    reify_type T2 ltac:(fun ty =>
    idtac ty;
    transform0 (ty :: GA) t k)
  | (fun (x : ?T) => @?f x) =>
    idtac "match base";
    transform' GA f ltac:(fun res => k res)
  end.

Ltac transform prog k :=
  let t := constr:(fun (_ : unit ) => prog) in
  transform0 (@nil Skel.Typ) t ltac:(fun res => k res).

Lemma let_ret T (app : comp T) : (do! x <- app in ret x) = app.
Proof. unfold bind; simpl; unfold bind_opt; destruct app; eauto. Qed.

Ltac let_intro_pure f T ans :=
  lazymatch f with
  | fun x => x => constr:(fun (k : T -> ans) x => k (f x))
  | fun x => seq (@?n x) (@?m x) =>
    constr:(fun (k : list Z -> ans) x => do! t <- ret (seq (n x) (m x)) in k t)
  | fun x => zip (@?arg1 x) (@?arg2 x) =>
    let arg1' := let_intro_pure arg1 T ans in
    let arg2' := let_intro_pure arg2 T ans in
    constr:(fun k x => 
                 arg1' (fun t1 => 
                 arg2' (fun t2 => 
                 do! t3 <- ret (zip t1 t2) in k t3) x) x)
  | fun x => reduceM (@?op x) (@?arg1 x) =>
    let arg1' := let_intro_pure arg1 T ans in
    constr:(fun k x => arg1' (fun t1 => do! t2 <- (reduceM (op x) t1) in k t2) x)
  end.

Ltac let_intro := lazymatch goal with
| [|- forall x, _ x = @?prog x] =>
  let x := fresh "x" in
  idtac prog;
  intros x;
  let T := match type of prog with ?T -> _ => T end in
  let ans := match type of prog with _ -> ?ans => ans end in
  let t := let_intro_pure prog T ans in 
  idtac t;
  let t' := constr:(t ret x) in
  let t' := eval cbv beta in t' in 
  lazymatch goal with
    [|- _ = ?prog] =>
    cutrewrite (prog = t');
      [reflexivity|repeat first [rewrite <-let_lift1 | rewrite let_ret]; eauto]
  end
end.

Lemma if_app (A B : Type) (f : A -> B) (b : bool) x y :
  (f (if b then x else y)) = (if b then f x else f y).
Proof. destruct b; eauto. Qed.

Require Import CUDALib CSLLemma CSLTactics CodeGen.

Definition equivGC1 {dom cod : Skel.Typ}
           (p_g : list (Skel.typDenote dom) -> comp (list (Skel.typDenote cod)))
           (M : GModule) :=
  interp_f M nil "__main"
           {| fs_tag := Hfun;
              fs_params := flatTup (outArr dom) ++ map fst (flatten_avars (gen_params (dom :: nil)));
              fs_tri := 
                All inp apenv outp result vs,
                FDbl (kernelInv
                        (remove_typeinfo (gen_params (dom :: nil))) apenv (inp ::: HNil)
                        (T *** arrays (val2gl outp) vs 1)
                        (p_g inp = Some result /\ length result <= length vs)%nat
                        (outArr cod |=> outp) 1)
                     (fun l => kernelInv'
                                 apenv (inp ::: HNil)
                                 (T *** arrays (val2gl outp) (arr2CUDA result ++ skipn (length result) vs) 1%Qc)
                                 (l = Zn (length result)) 1%Qc) |}.

Definition equivGI1 {T U : Skel.Typ}
           (p_g : list (Skel.typDenote T) -> comp (list (Skel.typDenote U)))
           (p_i : Skel.AS (T :: nil) U) :=
  forall (x : list (Skel.typDenote T)),
    p_g x =  Skel.asDenote _ _ (p_i) (HCons x HNil).

Definition equivIC1 {dom cod : Skel.Typ} (p_i : Skel.AS (dom :: nil) cod) (M : GModule) :=
  interp_f M nil "__main"
           {| fs_tag := Hfun;
              fs_params := flatTup (outArr dom) ++ map fst (flatten_avars (gen_params (dom :: nil)));
              fs_tri := 
                All aeenv apenv outp result vs,
                FDbl (kernelInv
                        (remove_typeinfo (gen_params (dom :: nil))) apenv aeenv
                        (T *** arrays (val2gl outp) vs 1)
                        (Skel.asDenote (dom :: nil) cod p_i aeenv = Some result /\ length result <= length vs)%nat
                        (outArr cod |=> outp) 1)
                     (fun l => kernelInv'
                                 apenv aeenv
                                 (T *** arrays (val2gl outp) (arr2CUDA result ++ skipn (length result) vs) 1%Qc)
                                 (l = Zn (length result)) 1%Qc) |}.

Lemma equiv_trans dom cod
      (p_g : list (Skel.typDenote dom) -> comp (list (Skel.typDenote cod)))
      (p_i : Skel.AS (dom :: nil) cod)
      (M : GModule) :
  equivGI1 p_g p_i -> equivIC1 p_i M -> equivGC1 p_g M .
Proof.
  unfold equivGI1, equivIC1, equivGC1.
  intros Heq1.
  unfold interp_f, with_ctx, interp_f_n, interp_fd_simp, interp_hfun_n_simp, interp_kfun_n_simp.
  destruct func_disp; simpl; eauto.
  intros Hsat ? ?; forwards*Hsat': Hsat.
  destruct f; intros inp apenv outp result vs; forwards* Hsat'': (>>Hsat' (inp ::: HNil) apenv outp result vs);
  rewrite Heq1; eauto.
Qed.  

Lemma ext_fun {T U : Skel.Typ} (p : Skel.AS (T :: nil) U) f g :
  (forall x, f x = g x) -> equivGI1 f p -> equivGI1 g p.
Proof.
  unfold equivGI1; intros Heq; intros; rewrite <-Heq; eauto.
Qed.

Ltac prove_equiv1 :=
  unfold equivGI1; simpl; intros; auto;
  repeat (destruct Z_le_dec; try omega);
  repeat first [rewrite <-let_lift1 | rewrite let_ret];
  repeat
    (match goal with _ => idtac end;
      lazymatch goal with
      | [|- context [do! _ <- ret ?skel in _]] =>  rewrite <-(let_lift1 _ skel)
      | [|- context [do! x <- ?skel in ret x]] =>  rewrite (let_ret _ skel)
      end);
    repeat rewrite let_ret;
  repeat f_equal;
  repeat (let l := fresh in extensionality l; intros);
  repeat (match goal with _ => idtac end;
      lazymatch goal with
      | [|- context [do! _ <- ret ?skel in _]] =>  rewrite <-(let_lift1 _ skel)
      | [|- context [do! x <- ?skel in ret x]] =>  rewrite (let_ret _ skel)
      | [|- context [ret (if _ then _ else _)]] =>  rewrite (if_app _ _ ret)
      end); eauto.

Require Import CompilerProof.

Definition compileOk dom cod (p : Skel.AS (dom :: nil) cod) :
  skel_as_wf _ _ p
  -> equivIC1 p (Compiler.compile_prog 1024 24 p).
Proof.
  unfold equivIC1.
  intros; applys (>>compile_prog_ok (dom :: nil) cod); eauto.
Qed.  

Lemma equiv_trans' (dom cod : Skel.Typ)
  (p_g : list (Skel.typDenote dom) -> comp (list (Skel.typDenote cod))) (p_i : {p_i | equivGI1 p_g p_i}) :
  {M | equivIC1 (proj1_sig p_i) M} ->
  {M | equivGC1 p_g M}.
Proof.
  intros M.
  destruct p_i as [p_i ?]; simpl in *.
  destruct M as [M ?].
  eexists; eapply equiv_trans; eauto.
Qed.

Ltac reifyFunc := 
  eexists;
  eapply equiv_trans;
  [eapply ext_fun;
    [simpl in *; let_intro|
     lazymatch goal with
     | [|- equivGI1 ?prog _ ] =>
       transform prog ltac:(fun res => instantiate (1 := res))
     end]; prove_equiv1|].


Goal False.
  let t := constr:(
  fun (x : list Z) =>
    do! idx <- ret (seq 0 (len x)) in
    do! arrIdx <- ret (zip x idx) in
    do! res <- reduceM (fun x y : Z * Z => if fst x <? fst y then ret x else ret y) arrIdx in
    ret res : comp _) in
  transform t ltac:(fun res => pose res as prog).

  let t := constr:(fun (p : unit * list Z) (i : Z) => do! x1 <- nth_error (mysnd p) i in ret (x1, i)) in
  scalarFunc (Skel.TZ :: nil) t ltac:(fun res => pose res as p).
  let t := constr:(fun (p : unit * list Z) => 
          gen (fun i : Z => do! x1 <- nth_error (mysnd p) i in ret (x1, i))
               (len (mysnd p))) in
  reifyAE (Skel.TZ :: nil) t ltac:(fun res => pose res as p').

  let t := constr:((fun x0 : list Z =>
      do! x1 <- (do! t <- gen (fun i : Z => do! x1 <- nth_error x0 i in ret (x1, i))
               (len x0)
          in reduceM
               (fun x1 y : Z * Z =>
                if fst x1 <? fst y then ret x1 else ret y) t) in 
      ret x1)) in
  transform t ltac:(fun res => pose res as p'').
  Eval simpl in Skel.asDenote (Skel.TZ :: nil) _ prog.
Abort.  

Arguments ret : simpl never.
Arguments bind : simpl never.

