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

  (* Reifying type expressions *)
  Ltac type_reify t k :=
    idtac "type_reify t = " t;
    let t := lazymatch t with list ?t => t end in
    let rec tac t k :=
        lazymatch t with
        | Z => k Sx.TZ
        | bool => k Sx.TBool
        | (?ty1 * ?ty2)%type =>
          tac ty1 ltac:(fun ty1' =>
          tac ty2 ltac:(fun ty2' =>
          k (Sx.TTup (ty1' :: ty2' :: nil))))
        end in
    tac t k.

  Goal False.
    type_reify (list Z) ltac:(fun ty => pose ty).
  Abort.
  
  (* Phantom type for tracking generated variable names *)
  Definition VarA (x : varA) (T : Type) := T.

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
    | (_ -> Var ?name ?ty) =>
      type_reify ty ltac:(fun ty' =>
      k name ty')
    | _ => k (VarA "error") Sx.TZ
    end.

  (* ``skelApp'' generate a syntax tree from skeleton application expression.
     ``skelApp'' returns reifyed type of skeleton application and converted syntax tree *)
  Ltac skelApp f k :=
    idtac "skelApp f = " f;
    lazymatch f with
    | (fun (x : ?T) => ret (seq (@?begin x) (@?len x))) =>
      idtac "match to seq";
      k Sx.TZ (Sx.Build_SkelExpr "seq" nil nil nil)
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
      k ty (Sx.Build_SkelExpr "reduce" (@nil Sx.Func) ((Sx.VArr arr, ty) :: nil) nil))
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
      let c' := eval cbv beta in (fun (x : T * Var name T_of_ae) => c (fst x) (snd x)) in
      skelApp ae ltac:(fun ty sexp => 
      transform' c' (S n) ltac:(fun c' => k (Sx.ALet name ty sexp c')))
    | (fun (x : ?T) => ret (@?c x)) =>
      idtac "match res case";
      get_name c ltac:(fun x ty => k (Sx.ARet x))
    end.

  Ltac collect_params T :=
    lazymatch T with
    | (?t1 * ?t2)%type =>
      let ps1 := collect_params t1 in 
      let ps2 := collect_params t2 in 
      eval compute in (ps1 ++ ps2)%list
    | Var ?name _ => constr:((name, Sx.TZ) :: nil)
    | _ => constr:(@nil (varA * Sx.Typ))
    end.

  Ltac transform prog n k :=
    idtac "transform prog = " prog;
    lazymatch prog with
    | (fun (x : ?T1) (y : ?T2) => @?f x y) =>
      idtac "match inductive";
      let name := eval cbv in (VarA ("x" ++ nat_to_string n)) in
      let t := eval cbv beta in (fun (p : T1 * (Var name T2)) => f (fst p) (snd p)) in transform t (S n) k
    | (fun (x : ?T) => @?f x) =>
      idtac "match base";
        let ps := collect_params T in
        pose T;
        transform' prog n ltac:(fun res => k (ps, res))
    end.
  
  lazymatch goal with
  | [|- { x : Sx.prog  | rel x ?prog } ] =>
    let prog := constr:(fun (_ : unit) => prog) in
    transform prog O ltac:(fun res => pose res)
  end.
  
  exists p.
