Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Open Scope Z_scope.

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

Ltac reifyFunc' :=
  lazymatch goal with
  | [|- { x : Skel.AS _ _  | equiv1 x ?prog } ] =>
    transform prog ltac:(fun res => exists res)
  end.

Lemma let_lift1 {A B : Type} (f : A -> comp B) (xs : A) : f xs = do! t <- ret xs in f t.
Proof. eauto. Qed.
Lemma if_app (A B : Type) (f : A -> B) (b : bool) x y :
  (f (if b then x else y)) = (if b then f x else f y).
Proof. destruct b; eauto. Qed.

Ltac prove_equiv1 :=
  unfold equiv1; simpl; intros; auto;
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

Ltac reifyFunc :=
  let H := fresh in
  lazymatch goal with
  | [|- {_ | equiv1 _ _}] =>
    eapply change_spec;
      [intros ? H; eapply ext_fun;
       [simpl in *; let_intro| apply H]| cbv beta; reifyFunc'; prove_equiv1 ]
  end.

Definition min_idx (arr : list Z) : comp (list (Z * Z))
  := reduceM
       (fun x y => if (fst x) <? (fst y)
                   then ret x else ret y)
       (zip arr (seq 0 (len arr))).

Require Import Compiler Ext Extract.

Definition equivIG {GA T} (f_IR : Skel.AS GA T) (p : Host.GModule) := True.
Definition equivCG {GA T} (f_IR : Skel.AS GA T) (p : Host.GModule) := True.

Definition compileOk GA T (x : Skel.AS GA T) : equivIG x (Compiler.compile_prog 1024 24 x).
Proof.
  unfold equivIG; eauto.
Qed.  

Lemma equiv_trans GA T f' p :
  equiv1 f f'
  -> equivIG f' p
  -> equivCG f p.

Definition min_idx_IR:
  {p : Skel.AS (Skel.TZ :: nil) (Skel.TTup Skel.TZ Skel.TZ) | equiv1 p (min_idx)}.
Proof.
  unfold min_idx.
  reifyFunc.
Defined.

Definition res := save_to_file min_idx_IR "min_idx.cu".

Cd "extracted".

Separate Extraction res.