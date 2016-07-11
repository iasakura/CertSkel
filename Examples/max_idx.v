Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Open Scope Z_scope.

Definition max_idx (arr : list Z) : comp (list (Z * Z))
  := reduceM
       (fun x y => if (fst x) <? (fst y)
                   then ret x else ret y)
       (zip arr (seq 0 (len arr))).c

Definition max_idx_IR:
  {p : Skel.AS (Skel.TZ :: nil) (Skel.TTup Skel.TZ Skel.TZ) | equiv1 p (max_idx)}.
Proof.
  unfold max_idx.
  simpl in *.
  eapply change_spec; [intros; eapply ext_fun; [intros|]|].
  simpl in *.
  rewrite (let_lift1 _ (zip _ _)).
  lazymatch goal with
  | [|- _ = do! t := ?ae in @?res t] => pose ae
  end.
  cutrewrite (ret (zip x0 (seq 0 (len x0))) =
              (do! t := ret (seq 0 (len x0)) in ret (zip x0 t) : comp _)); [|eauto].

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