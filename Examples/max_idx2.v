Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Open Scope Z_scope.

Definition max_idx (arr : list Z) : comp (list (Z * Z))
  :=
  reduceM (fun x y => if (fst x) <? (fst y)
                      then ret x else ret y)
          (zip arr (seq 0 (len arr))).

Lemma zip_seq (arr : list Z) :
  ret (zip arr (seq 0 (len arr))) =
  gen (fun i => do! x := nth_error arr i in ret (x, i)) (len arr).
Admitted.

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
  rewrite (zip_seq x0).
  (* cutrewrite (ret (zip x0 (seq 0 (len x0))) = *)
  (*             (do! t := ret (seq 0 (len x0)) in ret (zip x0 t) : comp _)); [|eauto]. *)

  (* repeat lazymatch goal with *)
  (* | [|- context [do! t := do! u := ret ?ae in @?f u in @?g t]] =>  *)
  (*   let t := eval cbv beta in (do! t := do! u := ret ae in f u in g t) in  *)
  (*   cutrewrite (t = (do! u := ret ae in do! t := f u in g t)); [|eauto] *)
  (* end. *)

  Lemma ret_id (A : Type) (t : comp A) : t = (do! x := t in ret x).
  Proof.
    cbv; destruct t; eauto.
  Qed.

  lazymatch goal with
  | [|- _ = ?term ] =>
    cutrewrite (term = do! x := term in ret x); [|apply ret_id]
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
  f_equal.
  repeat (let t := fresh "t" in extensionality t).
  destruct (_ <? _); auto.
Defined.

Require Import Compiler Ext Extract.

Definition max_idx_CUDA : Host.Prog :=
  match max_idx_IR with
  | exist ir _ =>
    Compiler.compile_prog 1024 24 ir
  end.

Definition res := save_to_file max_idx_CUDA "max_idx_opt.cu".

Cd "extracted".

Separate Extraction res.