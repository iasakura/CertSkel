Require Import GPUCSL.
Require Import Skel_lemma.
(* Require Import Host SimplSkel Compiler. *)
Require Import Monad.
Require Import LibTactics.
Require Import TypedTerm.
Open Scope list_scope.

Open Scope Z_scope.

Require Import SkelLib.

Definition max_idx (arr : list Z) : comp (list (Z * Z)) :=
  reduceM (fun x y => if (fst x) <? (fst y) then ret x else ret y) (zip arr (seq 0 (length arr))).

(* Notation equiv := equiv1. *)

Lemma change_spec {A : Type} (P Q : A -> Prop) : (forall x, P x -> Q x) -> {x : A | P x} -> {x : A | Q x}.
Proof.
  intros ? [? ?]; eexists; eauto.
Qed.

Lemma let_bind {A B : Type} (t : list A) (f : list A -> comp B) : (let x := t in f x) = (do! x := ret t in f x).
Proof. eauto. Qed.

Lemma let_lift1 {A B : Type} (f : list A -> comp B) (xs : list A) : f xs = do! t := ret xs in f t.
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
  (do! t := do! u := ret ae in f u in g t) = (do! u := ret ae in do! t := f u in g t).
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
  | (fun x => do! y := ?t in @?u x y) =>
    let c := eval cbv beta in (fun t => u (myfst t) (mysnd t)) in
    bind_last c ltac:(fun f =>
    let res := eval cbv beta in (fun x => do! y := t in f (x, y)) in
    k res)
  | (fun x => @?u x) =>
    let ty := type of u in
    idtac u ":" ty;
    match ty with
    | _ -> comp _ => k (fun x => do! y := u x in ret y)
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
  let resTy := match type of f with _ -> ?Ty => Ty end in
  idtac "scalarExpr: resTy = " resTy;
  reify_type resTy ltac:(fun resTy' =>
  idtac "scalarExpr: resTy' = " resTy';
  match f with
  | (fun _ => ?c) =>
    idtac "scalarExpr: matched to constant case";
    lazymatch type of c with Z => k (Skel.ENum GA GS c) end
  | (fun (x : ?T) => let y := @?t1 x in @?t2 x y) =>
    idtac "scalarExpr: matched to let case";
    lazymatch type of t1 with
    | _ -> ?Ty =>
      scalarExpr GA GS t1 ltac:(fun t1' =>
      reify_type Ty ltac:(fun ty1 =>
      let t2 := eval cbv beta in (fun (p : T * Ty) => t2 (myfst p) (mysnd p)) in
      scalarExpr GA (ty1 :: GS) t2 ltac:(fun t2' =>
      k (Skel.ELet _ _ _ _ t1' t2'))))
    end
  | (fun (x : ?T) => if @?cond x then @?th x else @?el x) =>
    idtac "scalarExpr: matched to if case";
    scalarExpr GA GS cond ltac:(fun cond' =>
    idtac "scalarExpr cond' = " cond';
    scalarExpr GA GS th ltac:(fun th' =>
    idtac "scalarExpr: th' = " th';
    scalarExpr GA GS el ltac:(fun el' =>
    idtac "scalarExpr: el' = " el';
    k (Skel.EIf GA GS resTy' cond' th' el'))))
  | (fun (x : ?T) => ?op (@?e1 x) (@?e2 x)) =>
    idtac "scalarExpr: matched to binop case";
    binOp op ltac:(fun op' =>
    scalarExpr GA GS e1 ltac:(fun e1' =>
    scalarExpr GA GS e2 ltac:(fun e2' =>
    lazymatch type of op' with
    | Skel.BinOp ?t1 ?t2 ?t3 => k (Skel.EBin GA GS t1 t2 t3 op' e1' e2')
    end)))
  | (fun (x : ?T) => @fst _ _ (@?e x)) =>
    idtac "scalarExpr: matched to fst case e =" e;
    scalarExpr GA GS e ltac:(fun e' =>
    idtac "scalarExpr: e' = " e';
    k (Skel.EPrj1 GA GS _ _ e'))
  | (fun (x : ?T) => @snd _ _ (@?e x)) =>
    idtac "scalarExpr: matched to snd case e =" e;
    scalarExpr GA GS e ltac:(fun e' =>
    k (Skel.EPrj2 GA GS _ _ e'))
  | (fun (x : ?T) => ret (@?e x)) =>
    idtac "scalarExpr: matched ret case e =" e;
    scalarExpr GA GS e k
  | (fun (x : ?T) => (@?e x)) =>
    idtac "scalarExpr: matched var case e =" e;
    let m := member GS e in
    k (Skel.EVar GA GS _ m)
  end).

Goal False.
  let t := constr:(fun p : unit * (Z * Z) * (Z * Z) => (mysnd (myfst p))) in
  let GS := constr:((Skel.TTup Skel.TZ Skel.TZ) :: (Skel.TTup Skel.TZ Skel.TZ) :: nil) in
  let GA := constr:(@nil Skel.Typ) in
  scalarExpr GA GS t ltac:(fun t => pose t).

  Eval simpl in (Skel.sexpDenote _ _ _ s HNil (HCons ((1, 3) : Skel.typDenote (Skel.TTup Skel.TZ Skel.TZ))
                                              (HCons ((4, 5) : Skel.typDenote (Skel.TTup Skel.TZ Skel.TZ)) HNil)))%Z.
Abort.

Ltac scalarFunc GA f k :=
  idtac "scalarFunc f = " f;
  lazymatch f with
  | (fun (x : ?T1) (y : ?T2) => @?f x y) =>
    idtac "scalarFunc: matched to inductive case";
    let t := eval cbv beta in (fun (p : unit * T1 * T2) => f (mysnd (myfst p)) (mysnd p)) in
    reify_type T1 ltac:(fun ty1 =>
    reify_type T2 ltac:(fun ty2 =>
    scalarExpr GA (ty1 :: ty2 :: nil) t ltac:(fun res =>
    k (Skel.F2 _ _ _ _  res))))
  | (fun (x : ?T) => @?f x) =>
    idtac "scalarFunc: matched to base case";
    idtac "scalarFunc: T = " T;
    let t := eval cbv beta in (fun (p : unit * T) => f (mysnd p)) in
    reify_type T ltac:(fun ty =>
    scalarExpr GA (ty :: nil) t ltac:(fun res =>
    k (Skel.F1 _ _ _  res)))
  end.

Goal False.
  scalarFunc (@nil Skel.Typ) (fun (x y : Z) => Z.min x y) ltac:(fun res => 
  let t := eval simpl in (Skel.funcDenote nil _ res) in pose t).
  scalarFunc (@nil Skel.Typ) (fun (x y : Z) => x + y) ltac:(fun res =>
  let t := eval simpl in (Skel.funcDenote nil _ res) in pose t).
  scalarFunc (@nil Skel.Typ) (fun (x y : Z) => let z := x + y in z) ltac:(fun res => 
  let t := eval simpl in (Skel.funcDenote nil _ res) in pose t).
  scalarFunc (@nil Skel.Typ) 
             (fun (x y : Z * Z) => if (fst x) <? (fst y) then ret x else ret y) ltac:(fun res => 
  let t := eval simpl in (Skel.funcDenote nil _ res) in pose t).
Abort.

Ltac lexpr GA e k :=
  idtac "lexpr e = " e;
  lazymatch e with
  | (fun x => List.length (@?acc x)) =>
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
  lexpr (Skel.TZ :: nil) (fun x : (unit * list Z) => (length (mysnd x))) ltac:(fun e => pose e).
Abort.

Definition gen {T} (f : Z -> comp T) (len : Z) :=
  mapM f (seq 0 (Z.to_nat len)).

Ltac reifyAE GA f k :=
  idtac "reifyAE f = " f;
  lazymatch f with
  | (fun (x : ?T) => gen ?f (@?len x)) =>
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
  | (fun (x : ?T) => reduceM ?f (@?arr x)) =>
    idtac "match to reduce";
    idtac "skelApp: f, arr = " f arr;
    reifyAE GA arr ltac:(fun arr =>
    scalarFunc GA f ltac:(fun f =>
    k (Skel.Reduce _ _ f arr)))
  end.

Goal False.
  let t := constr:(fun p : (unit * list Z) => ret (seq 0 (length (mysnd p)))) in
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
  | (fun (x : ?T) => do! t := @?ae x in @?c x t) =>
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
    do! idx := ret (seq 0 (Datatypes.length (mysnd x))) in
    do! arrIdx := ret (zip (mysnd x) idx) in
    do! res := reduceM (fun x y : Z * Z => if fst x <? fst y then ret x else ret y) arrIdx in
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

Goal False.
  let t := constr:(
  fun (x : list Z) =>
    do! idx := ret (seq 0 (Datatypes.length x)) in
    do! arrIdx := ret (zip x idx) in
    do! res := reduceM (fun x y : Z * Z => if fst x <? fst y then ret x else ret y) arrIdx in
    ret res : comp _) in
  transform t ltac:(fun res => pose res as prog).
  Eval simpl in Skel.asDenote (Skel.TZ :: nil) _ prog.
Abort.  

Arguments ret : simpl never.
Arguments bind : simpl never.

Definition equiv1 {T U : Skel.Typ}
           (p_i : Skel.AS (T :: nil) U)
           (p_g : list (Skel.typDenote T) -> comp (list (Skel.typDenote U))) :=
  forall (x : list (Skel.typDenote T)),
    p_g x =  Skel.asDenote _ _ (p_i) (HCons x HNil).

Lemma ext_fun {T U : Skel.Typ} (p : Skel.AS (T :: nil) U) f g :
  (forall x, f x = g x) -> equiv1 p f -> equiv1 p g.
Proof.
  unfold equiv1; intros Heq; intros; rewrite <-Heq; eauto.
Qed.

Definition max_idx_IR:  {p : Skel.AS (Skel.TZ :: nil) (Skel.TTup Skel.TZ Skel.TZ) |
      equiv1 p (max_idx)}.
Proof.
  unfold max_idx.
  simpl in *.
  eapply change_spec; [intros; eapply ext_fun; [intros|]|].
  simpl in *.
  rewrite (let_lift1 _ (zip _ _)).
  lazymatch goal with
  | [|- _ = do! t := ?ae in @?res t] => pose ae
  end.
  cutrewrite (ret (zip x0 (seq 0 (length x0))) =
              (do! t := ret (seq 0 (length x0)) in ret (zip x0 t) : comp _)); [|eauto].

  repeat lazymatch goal with
  | [|- context [do! t := do! u := ret ?ae in @?f u in @?g t]] => 
    let t := eval cbv beta in (do! t := do! u := ret ae in f u in g t) in 
    cutrewrite (t = (do! u := ret ae in do! t := f u in g t)); [|eauto]
  end.

  lazymatch goal with
  | [|- _ = ?term ] =>
    idtac term;
    bind_last (fun _ : unit => term) ltac:(fun t =>
      let t := eval_tup (t tt) in
      cutrewrite (term = t)); [|dest; eauto]
  end.

  reflexivity.

  apply H.
  cbv beta.
  
  lazymatch goal with
  | [|- { x : Skel.AS _ _  | equiv1 x ?prog } ] =>
    transform prog ltac:(fun res => exists res)
  end.

  unfold equiv1; simpl; intros; auto.
  unfold ret, bind; simpl.
  rewrite Nat2Z.id.
  f_equal. f_equal.
  repeat (let t := fresh "t" in extensionality t).
  destruct (_ <? _); auto.
Defined.

Require Import Compiler Ext Extract.

Definition max_idx_CUDA : Host.Prog :=
  match max_idx_IR with
  | exist ir _ =>
    Compiler.compile_prog 1024 24 ir
  end.


Definition res := save_to_file max_idx_CUDA "max_idx.cu".

Cd "extracted".

Separate Extraction res.