Require Import GPUCSL.
Require Import Monad.
Require Import Skel_lemma.
Require Import SimplSkel.
Require Import LibTactics.
Open Scope list_scope.

Definition comp := option.
Instance Monad_comp : Monad comp := option_monad.
Definition mapM {A B : Type} (f : A -> comp B) (xs : list A) := sequence (List.map f xs).

Definition lift_op {A : Type} (f : A -> A -> comp A) : comp A -> comp A -> comp A :=
  fun x y => match x, y with
             | Some x, Some y => (f x y)
             | Some x, None | None, Some x => Some x
             | None, None => None
             end.

Definition reduceM {A : Type} (f : A -> A -> comp A) (xs : list A) : comp (list A) :=
  match List.fold_right (lift_op f) None (List.map Some xs) with
  | Some x => ret (x :: nil)
  | None => None
  end.

Definition zip {A B : Type} := @List.combine A B.

Fixpoint nth_error {A : Type} (l:list A) (n:nat) : comp A :=
  match n, l with
  | O, x :: _ => Some x
  | S n, _ :: l => nth_error l n
  | _, _ => None
  end.

Definition seq s l := map Z.of_nat (seq s l).

Open Scope Z_scope.

Definition max_idx (arr : list Z) : comp (list (Z * Z)) :=
  reduceM (fun x y => if (fst x) <? (fst y) then ret x else ret y) (zip arr (seq 0 (length arr))).

Module Sx := Syntax.
Definition rel (p : Sx.prog) (f : list Z -> comp (list (Z * Z))) : Prop := True.

Goal {p : Sx.prog | rel p max_idx}.
Proof.
  unfold max_idx.
  
  Lemma ext_fun p f g : (forall x, f x = g x) -> rel p f -> rel p g.
  Proof.
    unfold rel; tauto.
  Qed.
  
  Lemma change_spec {A : Type} (P Q : A -> Prop) : (forall x, P x -> Q x) -> {x : A | P x} -> {x : A | Q x}.
  Proof.
    intros ? [? ?]; eexists; eauto.
  Qed.

  eapply change_spec; intros.
  eapply ext_fun; intros.

  Lemma let_bind {A B : Type} (t : list A) (f : list A -> comp B) : (let x := t in f x) = (do! x := ret t in f x).
  Proof. eauto. Qed.
  
  Lemma let_lift1 {A B : Type} (f : list A -> comp B) (xs : list A) : f xs = do! t := ret xs in f t.
  Proof. eauto. Qed.

  rewrite (let_lift1 _ (zip _ _)).
  cutrewrite (ret (zip x0 (seq 0 (length x0))) = do! t := ret (seq 0 (length x0)) in ret (zip x0 t)); [|eauto].

  Lemma let_lift2 {A B C : Type} (ae : list A) (f : list A -> comp B) (g : B -> comp C) :
    (do! t := do! u := ret ae in f u in g t) = (do! u := ret ae in do! t := f u in g t).
  Proof. eauto. Qed.
  
  repeat lazymatch goal with
  | [|- context [do! t := do! u := ret ?ae in @?f u in @?g t]] => 
    let t := eval cbv beta in (do! t := do! u := ret ae in f u in g t) in 
    cutrewrite (t = (do! u := ret ae in do! t := f u in g t)); [|eauto]
  end.

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
    simpl; repeat match goal with
    | [|- context [bind_opt _ _ ?t _]] => destruct t; simpl
    end; eauto.

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
        | Z => k Sx.TZ
        | bool => k Sx.TBool
        | (?ty1 * ?ty2)%type =>
          tac ty1 ltac:(fun ty1' =>
          tac ty2 ltac:(fun ty2' =>
          k (Sx.TTup (ty1' :: ty2' :: nil))))
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
  Ltac get_name x k :=
    idtac "get_name x =" x;
    lazymatch type of x with
    | (_ -> TyVar ?name ?ty) =>
      reify_type ty ltac:(fun ty' =>
      idtac "get_name name ty' = " name ty';
      k name ty')
    | _ => k (VarA "error") Sx.TZ
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
    | Z.add => k Sx.Eplus
    | Z.mul => k Sx.Emult
    | Z.min => k Sx.Emin
    | Z.ltb => k Sx.Blt
    | Z.eqb => k Sx.BEq
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
  
  Ltac scalarExpr n f k :=
    idtac "scalarExpr: f = " f;
    let resTy := match type of f with _ -> ?Ty => Ty end in
    idtac "scalarExpr: resTy = " resTy;
    reify_type resTy ltac:(fun resTy' =>
    idtac "scalarExpr: resTy' = " resTy';
    match f with
    | (fun _ => ?c) =>
      idtac "scalarExpr: matched to constant case";
      lazymatch type of c with Z => k n (Sx.ENum c) end
    | (fun (x : ?T) => let y := @?t1 x in @?t2 x y) =>
      idtac "scalarExpr: matched to let case";
      lazymatch type of t1 with
      | _ -> ?Ty =>
        scalarExpr n t1 ltac:(fun n t1' =>
        let y' := constr:(VarE ("x" ++ nat_to_string n)) in
        scalarExpr (S n) (fun (p : T * TyVar y' Ty) => t2 (myfst p) (mysnd p)) ltac:(fun n t2' =>
        k n (Sx.ELet y' t1' t2' resTy')))
      end
    | (fun (x : ?T) => if @?cond x then @?th x else @?el x) =>
      idtac "scalarExpr: matched to if case";
      scalarExpr n cond ltac:(fun n cond' =>
      idtac "scalarExpr cond' = " cond';
      scalarExpr n th ltac:(fun n th' =>
      idtac "scalarExpr: th' = " th';
      scalarExpr n el ltac:(fun n el' =>
      idtac "scalarExpr: el' = " el';
      k n (Sx.EIf cond' th' el' resTy'))))
    | (fun (x : ?T) => ?op (@?e1 x) (@?e2 x)) =>
      idtac "scalarExpr: matched to binop case";
      binOp op ltac:(fun op' =>
      scalarExpr n e1 ltac:(fun n e1' =>
      scalarExpr n e2 ltac:(fun n e2' =>
      k n (Sx.EBin op' e1' e2' resTy'))))
    | (fun (x : ?T) => @fst _ _ (@?e x)) =>
      idtac "scalarExpr: matched to fst case e =" e;
      scalarExpr n e ltac:(fun n e' =>
      idtac "scalarExpr: e' = " e';
      k n (Sx.EPrj e' 0%nat resTy'))
    | (fun (x : ?T) => @snd _ _ (@?e x)) =>
      idtac "scalarExpr: matched to snd case e =" e;
      scalarExpr n e ltac:(fun n e' =>
      k n (Sx.EPrj e' 1%nat resTy'))
    | (fun (x : ?T) => ret (@?e x)) =>
      scalarExpr n e k
    | (fun (x : ?T) => (@?e x)) =>
      traverseTyVar e ltac:(fun name => idtac "id case in scalarExpr: name = " name; k n (Sx.EVar name resTy'))
    end).

  Goal False.
    let t := constr:((fun p : unit * TyVar (VarE "xO") (Z * Z) * TyVar (VarE "xSO") (Z * Z) =>  ret (mysnd (myfst p)))) in
    scalarExpr 0%nat t ltac:(fun _ t => pose t).
  Abort.
  
  Ltac scalarFunc f n k :=
    idtac "scalarFunc f = " f;
    lazymatch f with
    | (fun (x : ?T1) (y : ?T2) => @?f x y) =>
      idtac "scalarFunc: matched to inductive case";
      let name := eval cbv in (VarE ("x" ++ nat_to_string n)) in
      let t := eval cbv beta in (fun (p : T1 * TyVar name T2) => f (myfst p) (mysnd p)) in
      scalarFunc t (S n) k
    | (fun (x : ?T) => @?f x) =>
      idtac "scalarFunc: matched to base case";
      idtac "scalarFunc: T = " T;
      collect_params T ltac:(fun ps =>
      idtac "scalarFunc: ps = " ps;
      scalarExpr n f ltac:(fun _ res => k (Sx.F ps res)))
    end.

  Ltac lexpr e k :=
    idtac "lexpr e = " e;
    lazymatch e with
    | (fun x => List.length (@?acc x)) =>
      get_name acc ltac:(fun x _ => k (Sx.LLen x))
    | (fun x => ?c) =>
      lazymatch type of c with
      | nat => k (Sx.LNum (Z.of_nat c))
      | Z => k (Sx.LNum c)
      end
    end.

  Goal False.
    lexpr (fun _ : unit => 1) ltac:(fun e => pose e).
  Abort.
  
  (* ``skelApp'' generate a syntax tree from skeleton application expression.
     ``skelApp'' returns reifyed type of skeleton application and converted syntax tree *)
  Ltac skelApp f k :=
    idtac "skelApp f = " f;
    lazymatch f with
    | (fun (x : ?T) => ret (seq (@?begin x) (@?len x))) =>
      lexpr begin ltac:(fun begin' =>
      lexpr len ltac:(fun len' =>
      idtac "match to seq";
      k Sx.TZ (Sx.Build_SkelExpr "seq" nil nil (begin' :: len' :: nil))))
    | (fun (x : ?T) => ret (zip (@?arr1 x) (@?arr2 x))) =>
      idtac "match to zip";
      get_name arr1 ltac:(fun var1 ty1 =>
      get_name arr2 ltac:(fun var2 ty2 =>
      idtac var1 var2;
      k (Sx.TTup (ty1 :: ty2 :: nil))
        (Sx.Build_SkelExpr "zip" nil ((Sx.VArr var1, ty1) :: (Sx.VArr var2, ty2) :: nil) nil)))
    | (fun (x : ?T) => reduceM ?f (@?arr x)) =>
      idtac "match to reduce";
      get_name arr ltac:(fun arr ty =>
      scalarFunc (fun _ : unit => f) 0%nat ltac:(fun f =>
      k ty (Sx.Build_SkelExpr "reduce" (f :: nil) ((Sx.VArr arr, ty) :: nil) nil)))
    | _ => k Sx.TZ "error" (@nil Sx.Func) (@nil (Sx.AE * Sx.Typ)%type)
    end.
  
  Ltac transform' prog n k :=
    idtac "prog = " prog;
    lazymatch prog with
      (* Note that @?c x t should not be @?c t x, the captured term by c would be malformed *)
    | (fun (x : ?T) => do! t := @?ae x in @?c x t) =>
      idtac "match do case";
      let T_of_ae := lazymatch type of ae with _ -> comp ?T => T end in
      let name := eval cbv in (VarA ("x" ++ nat_to_string n)) in
      let c' := eval cbv beta in (fun (x : T * TyVar name T_of_ae) => c (myfst x) (mysnd x)) in
      skelApp ae ltac:(fun ty sexp => 
      transform' c' (S n) ltac:(fun c' => k (Sx.ALet name ty sexp c')))
    | (fun (x : ?T) => ret (@?c x)) =>
      idtac "match res case";
      get_name c ltac:(fun x ty => k (Sx.ARet x))
    end.

  (* Ltac collect_paramsA T := *)
  (*   lazymatch T with *)
  (*   | (?t1 * ?t2)%type => *)
  (*     let ps1 := collect_paramsA t1 in  *)
  (*     let ps2 := collect_paramsA t2 in  *)
  (*     eval compute in (ps1 ++ ps2)%list *)
  (*   | TyVar ?name _ => constr:((name, Sx.TZ) :: nil) *)
  (*   | _ => constr:(@nil (varA * Sx.Typ)) *)
  (*   end. *)

  Ltac transform prog n k :=
    idtac "transform prog = " prog;
    lazymatch prog with
    | (fun (x : ?T1) (y : ?T2) => @?f x y) =>
      idtac "match inductive";
      let name := eval cbv in (VarA ("x" ++ nat_to_string n)) in
      let t := eval cbv beta in (fun (p : T1 * (TyVar name T2)) => f (myfst p) (mysnd p)) in transform t (S n) k
    | (fun (x : ?T) => @?f x) =>
      idtac "match base";
        collect_params T ltac:(fun ps =>
        pose T;
        transform' prog n ltac:(fun res => k (ps, res)))
    end.
  
  lazymatch goal with
  | [|- { x : Sx.prog  | rel x ?prog } ] =>
    let prog := constr:(fun (_ : unit) => prog) in
    transform prog O ltac:(fun res => pose res)
  end.
  
  exists p.
(* Inductive SOp : Set := *)
(*     Eplus : Sx.SOp *)
(*   | Emult : Sx.SOp *)
(*   | Emin : Sx.SOp *)
(*   | BEq : Sx.SOp *)
(*   | Blt : Sx.SOp *)
