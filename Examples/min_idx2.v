Require Import List MyList Monad SkelLib Computation ZArith TypedTerm Program LibTactics Psatz.
Open Scope Z_scope.

Definition min_idx (arr : list Z) : comp (list (Z * Z))
  :=
  reduceM (fun x y => if (fst x) <? (fst y)
                      then ret x else ret y)
          (zip arr (seq 0 (len arr))).

Lemma mapM_evaltoSome A B (f : A -> comp B) (xs : list A) :
  (forall i d, (i < length xs)%nat -> exists v, f (nth i xs d) = Some v) ->
  exists ys, mapM f xs = Some ys.
Proof.
  induction xs; intros H; simpl.
  - exists (@nil B); eauto.
  - forwards* (vs & ?): IHxs.
    intros; forwards* (? & ?): (H (S i) d); eauto; try lia.
    forwards* (v & ?): (H 0)%nat; try lia.
    exists (v :: vs); simpl; eauto.
    unfold mapM in *; simpl.
    rewrite H1, H0; simpl.
    eauto.
Qed.

Lemma zip_seq (arr : list Z) :
  ret (zip arr (seq 0 (len arr))) =
  gen (fun i => do! x := nth_error arr i in ret (x, i)) (len arr).
Proof.
  unfold gen, ret, zip; simpl.
  forwards* (? & ?): (>> mapM_evaltoSome (fun i : Z => do!x := nth_error arr i in Some (x, i)) (seq 0 (len arr))).
  intros; simpl.
  rewrites (>>nth_error_some' d).
  unfold len; rewrite seq_nth, Nat2Z.id; destruct lt_dec.
  lia.
  unfold len in *; rewrite seq_length, Nat2Z.id in *; lia.
  eexists; reflexivity.
  rewrite H; f_equal.
  applys (>>eq_from_nth (0, 0)%Z).
  - forwards*: mapM_length.
    unfold len in *; rewrite combine_length, seq_length, Nat2Z.id, min_l in *; eauto.
  - introv; unfold len in *; rewrite combine_length, seq_length, Nat2Z.id, min_l in *; eauto; intros.
    forwards*: (>>mapM_some i 0 (0,0)%Z).
    rewrite combine_nth, seq_nth in *.
    2: rewrite seq_length, Nat2Z.id; auto.
    rewrite seq_length, Nat2Z.id in *; auto.
    unfold nth_error, Z_to_nat_error in *.
    destruct lt_dec; try lia.
    destruct Z_le_dec; try lia.
    unfold ret, bind in *; simpl in *; unfold bind_opt in *.
    rewrites (>>nth_error_some 0%Z) in H1.
    rewrite Nat2Z.id; lia.
    rewrite Nat2Z.id in *; congruence.
Qed.

Definition min_idx_IR:
  {p : Skel.AS (Skel.TZ :: nil) (Skel.TTup Skel.TZ Skel.TZ) | equiv1 p (min_idx)}.
Proof.
  unfold min_idx.

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

Definition min_idx_CUDA : Host.Prog :=
  match min_idx_IR with
  | exist ir _ =>
    Compiler.compile_prog 1024 24 ir
  end.

Definition res := save_to_file min_idx_CUDA "min_idx_opt.cu".

Cd "extracted".

Separate Extraction res.