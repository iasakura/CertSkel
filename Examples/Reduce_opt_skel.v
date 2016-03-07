Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics Psatz.
Require Import Skel_lemma.

Notation "l '+ol' i" := (tarr_idx l i) (at level 40).
Notation "l '-->l' ( p , e )" := (is_tuple_p l e p) (at level 75, right associativity).

Lemma nseq_in (A : Type) (x : A) y n : In x (nseq n y) -> x = y.
Proof.
  induction n; simpl; try tauto.
  intros [|]; intros; eauto; try congruence.
Qed.

Ltac simplify :=
  unfold vars2es, tarr_idx, vs2es in *;
  repeat (simpl in *; substs; lazymatch goal with
          | [|- In _ (map _ _) -> _] =>
            rewrite in_map_iff; intros [? [? ?]]; substs
          | [H:In _ (map _ _) |-_] =>
            rewrite in_map_iff in H; destruct H as [? [? H]]; substs
          | [|- indeE _ _] => apply indeE_fv
          | [|- indelE _ _] => apply indelE_fv
          | [H : _ \/ False|-_] =>destruct H as [H|[]];substs
          | [H : _ \/ _ |-_] =>destruct H as [?|H]
          | [|- ~(_ \/ _)] => intros [?|?]
          | [|- context [In _ (_ ++ _)]] => rewrite in_app_iff
          | [H : context [In _ (_ ++ _)] |- _] => rewrite in_app_iff in H
          | [|- forall _, _] => intros ?
          | [H : In _ (locals _ _) |- _] => apply locals_pref in H
          | [H : In _ (nseq _ _) |- _] => apply nseq_in in H
          | [H : prefix _ _ = true |- _] => apply prefix_ex in H as [? ?]; substs
          | [|- disjoint_list (locals _ _)] => apply locals_disjoint_ls
          | [|- context [length (locals _ _)]] => rewrite locals_length
          | [H :context [length (locals _ _)]|- _] => rewrite locals_length in H
          | [H :context [length (vars2es _)]|- _] => unfold vars2es in *; rewrite map_length
          | [|- context [length (vars2es _)]] => unfold vars2es; rewrite map_length
          | [H :context [In _ (vars2es _)]|- _] =>
            unfold vars2es in *; rewrite in_map_iff in H;
            destruct H as [? [? H]]; substs
          | [|- context [In _ (vars2es _)]] => unfold vars2es; rewrite in_map_iff
          | [|- Forall _ _] => rewrite Forall_forall; intros
          | [|- indeE _ _] => apply indeE_fv
          | [|- indelE _ _] => apply indelE_fv
          | [|- indeB _ _] => apply indeB_fv
          | [H : context [var_of_str ?x] |- _] => destruct x
          | [|- inde (_ ==t _) _] => apply inde_eq_tup
          | [|- inde (_ -->l (_, _)) _] => apply inde_is_tup
          | [|- inde (is_tuple_array_p _ _ _ _ _) _] => apply inde_is_tup_arr
          | [|- context [length (map _ _)]] => rewrite map_length
          | [H : context [length (map _ _)] |- _] => rewrite map_length in H
          | [|- ~_] => intros ?
          end; simpl in *; try substs).

Section Sum_of.
  Variable T : Type.
  Variable op : T -> T -> T.
  Hypothesis op_assoc : forall x y z, op (op x y) z = op x (op y z).
  Hypothesis op_comm : forall x y, op x y = op y x.
  Variable u : T.
  Definition op' x y : option T :=
    match x, y with
    | None, _ => y
    | _, None => x
    | Some x, Some y => Some (op x y)
    end.
  Notation "a '+++' b" := (op' a b) (at level 40, left associativity).
  
  Lemma opopt_assoc x y z : op' (op' x y) z = op' x (op' y z).
  Proof.
    destruct x, y, z; simpl; eauto.
    rewrite op_assoc; eauto.
  Qed.
  
  Lemma opopt_comm x y : op' x y = op' y x.
  Proof.
    destruct x, y; simpl; eauto.
    rewrite op_comm; eauto.
  Qed.
  
  Arguments op' _ _ : simpl never.
  
  Fixpoint sum_of_f_opt (s len : nat) f : option T :=
    match len with
    | 0 => None
    | S l => Some (f s) +++ sum_of_f_opt (S s) l f
    end.

  Fixpoint skip_sum_of_opt skip (s len : nat) f i : option T :=
    match len with
    | 0 => None
    | S l =>
      if Nat.eq_dec (s mod skip) i 
      then (skip_sum_of_opt skip (S s) l f i +++ Some (f s))%Z
      else skip_sum_of_opt skip (S s) l f i
    end.
  
  Lemma sum_of_eq s len f1 f2: 
    (forall i, s <= i < s + len -> f1 i = f2 i) ->
    sum_of_f_opt s len f1 = sum_of_f_opt s len f2.
  Proof.
    revert s; induction len; simpl; intros s H; eauto. 
    rewrite IHlen; eauto; intros; try omega.
    rewrite H; eauto; omega.
    rewrite H; eauto; try omega.
  Qed.

  Lemma sum_of_f_split s n m f g :
    s <= m -> m < s + n ->
    sum_of_f_opt s n (fun i => if lt_dec i m then f i else g i) = 
    (sum_of_f_opt s (m - s) f +++ sum_of_f_opt m (n - (m - s)) g)%Z.
  Proof.
    revert s m; induction n.
    - intros s m Hsm Hmn; assert (Heq : (m - s) = 0) by omega; rewrite Heq in *; simpl; eauto.
    - intros s m Hsm Hmn; remember (S n - (m - s)); simpl in *.
      assert (s = m \/ s < m) as [Hsm' | Hsm'] by omega; subst.
      + destruct lt_dec; try omega.
        rewrite minus_diag; simpl.
        (* rewrite minus_diag, <-minus_n_O in *; simpl. *)
        erewrite sum_of_eq; unfold op'; simpl; eauto.
        intros i Hi; destruct lt_dec; eauto; try omega.
      + destruct lt_dec; try omega.
        assert (exists ms, m - s = S ms) as [ms Hms]
                                           by (exists (m - s - 1); omega); rewrite Hms.
        simpl.
        rewrite IHn; try omega.
        rewrite opopt_assoc; repeat f_equal; omega.
  Qed.

  Lemma shift_values :
    forall (l1 : nat) (fc : nat -> T) (s sft : nat),
      (sum_of_f_opt s l1 fc +++ sum_of_f_opt (s + sft) l1 fc)%Z =
      sum_of_f_opt s l1 (fun i : nat => (op (fc i) (fc (i + sft)%nat))%Z).
  Proof.
    induction l1; intros fc s sft; simpl; auto.
    cutrewrite (S (s + sft) = S s + sft); [|omega].
    rewrite <-IHl1; simpl.
    rewrite <-!opopt_assoc.
    cutrewrite (Some (op (fc s) (fc (s + sft))) = Some (fc s) +++ Some (fc (s + sft)));
      [|reflexivity].
    f_equal; rewrite !opopt_assoc; f_equal; rewrite opopt_comm; eauto.
  Qed.

  Lemma sum_of_concat :
    forall (l1 : nat) (fc : nat -> T) (s l2 : nat),
      sum_of_f_opt s (l1 + l2) fc = (sum_of_f_opt s l1 fc +++ sum_of_f_opt (l1 + s) l2 fc)%Z.
  Proof.
    induction l1; intros fc s l2; simpl; auto.
    rewrite IHl1, opopt_assoc; do 3 f_equal; omega.
  Qed.
End Sum_of.


Section Reduce.
  Variable ntrd : nat.
  Hypothesis ntrd_neq_0 : ntrd <> 0.
  Variable nblk : nat.
  Hypothesis nblk_neq_0 : nblk <> 0.
  
  (* dimensions of input and output arrays *)
  Variable dim : nat.
  
  (* compiled code of the mapping function *)
  Variable func : list var -> list var -> (cmd * list exp).
  (* code generators filling the function hole *)
  (* func : the argument variable ->
    the command for getting the result and the return expression  *)
  Variable f_den : list val -> list val -> list val -> Prop.
  
  Variable f_fun : list val -> list val -> list val.
  Infix "|+|" := (f_fun) (at level 40).
  Hypothesis f_fun_comm : forall x y, x |+| y = y |+| x.
  Hypothesis f_fun_assoc : forall x y z, (x |+| y) |+| z = x |+| (y |+| z).
  (* f is total *)
  Hypothesis f_fun_den :
    forall vs vs',
      length vs = dim -> length vs' = dim -> f_den vs vs' (f_fun vs vs').
  (* f : Val^dim -> Val^dim -> Val^dim *)
  Hypothesis f_den_wf :
    forall vs vs' rs,
      length vs = dim -> length vs' = dim ->
      f_den vs vs' rs ->
      length rs = dim.
  
  Hypothesis func_local :
    forall x y, forall z, In z (writes_var (fst (func x y))) -> prefix "l" (var_of_str z) = true.
  Hypothesis func_no_bars :
    forall x y, barriers (fst (func x y)) = nil.
  Hypothesis func_res_fv :
    forall x y e u, In e (snd (func x y)) -> In u (fv_E e) ->
                    In u x \/ In u y \/ prefix "l" (var_of_str u) = true.
  
  Hypothesis func_denote : forall (x y : list var) nt (tid : Fin.t nt) (vs us fv : list val) BS,
      f_den vs us fv -> 
      length x = dim ->
      disjoint x (writes_var (fst (func x y))) ->
      disjoint y (writes_var (fst (func x y))) ->
      CSL BS tid
          ( !(vars2es x ==t vs ) ** !(vars2es y ==t us))
          (fst (func x y))
          (!((snd (func x y)) ==t fv)).

  Hypothesis func_wf : forall (x y : list var),
        length (snd (func x y)) = dim.

  (* initial value of the output array *)
  Variable fout : nat -> list val.
  Hypothesis fout_wf : forall i, length (fout i) = dim.
  (* the top address of the output array *)
  Variable out : list Z.
  Hypothesis out_wf : length out = dim.
  Definition Outs := locals "Out" dim.
  Notation Outs' := (vars2es Outs). 
  
  Open Scope string_scope.
  
  Local Notation x := (locals "x" dim).
  Local Notation y := (locals "y" dim).
  Local Notation z := (locals "z" dim).
  Local Notation sdata := (vars2es (locals "sdata" dim)).
  Local Notation sdata' := (map Sh sdata).
  Local Notation len := (Var "n").
  Local Notation tid := (Var "tid").
  Local Notation bid := (Var "bid").
  
  Notation perm_n n := (1 / injZ (Zn n))%Qc.
  Variable e_b : nat.
  Hypothesis max_th_size : ntrd <= 2 ^ e_b.
  Hypothesis eb_neq_0 : e_b <> 0.
    
  Section ReduceBlock.
    Variable l : nat.
    Hypothesis l_leq_ntrd : l <= ntrd.
  
    Variable f_in : nat -> list val.
    Hypothesis f_in_wf :
      forall i, length (f_in i) = dim.
    
    Definition s n := 2 ^ (e_b - n).

    Lemma sn_double n : S n <= e_b -> s (S n) + s (S n) = s n.
    Proof.
      intros Hsneb. unfold s.
      assert (Heq : e_b - n = S (e_b - S n)) by omega; rewrite Heq; simpl; eauto.
    Qed.
    
    Definition reduce_body n s :=
      (Cbarrier (n - 1) ;;
       Cif (Band (tid +C Zn s <C len) (tid <C Zn s)) (
         gen_read Sh x sdata (tid + Zn s) ;;
         fst (func y x) ;;
         read_tup z (snd (func y x)) ;;
         read_tup y (vars2es z) ;;
         catcmd (gen_write Sh sdata tid (vars2es y))
       ) Cskip
      )%exp.

    Fixpoint reduce_aux t m :=
      match m with
      | O => Cskip    
      | S m =>
        reduce_body t (s t) ;; reduce_aux (S t) m 
      end.
    
    Definition reduce := reduce_aux 1 e_b.  
    
    Section simfun.
      
      Fixpoint f n i :=
        match n with
        | O => f_in i
        | S n => if Sumbool.sumbool_and _ _ _ _ (lt_dec (i + s (S n)) l) (lt_dec i (s (S n))) 
                 then (f n i |+| f n (i + s (S n))%nat)%Z
                 else f n i
        end.
    
      Lemma sn_decr n : s (S n) <= s n.
      Proof.
        apply Nat.pow_le_mono_r; omega.
      Qed.
      
      Notation sum_of_vs := (sum_of_f_opt (list val) f_fun).
      Notation "a '+++' b" := (op' _ f_fun a b) (at level 40, left associativity).
      Lemma f_inv n :
        S n <= e_b ->
        sum_of_vs 0 (min l (s (S n))) (f (S n)) = sum_of_vs 0 (min l (s n)) (f n).
      Proof.
        intros Hsneb.
        simpl.
        lets Hsn : (>>sn_double n ___); try omega.
        assert (l <= s (S n) \/ s (S n) < l < s n \/ s n <= l) as [HsSnl | [HsSnl | HsSnl] ] by omega.
        - erewrite sum_of_eq.
          Focus 2.
          { simpl; intros i Hi.
            assert (i <= l) by nia.
            destruct Sumbool.sumbool_and; try omega.
            reflexivity. } Unfocus.
          rewrite !min_l; try omega; eauto.
        - erewrite sum_of_eq.
          Focus 2.
          { simpl; intros i Hi.
            instantiate (1 := fun i => if lt_dec i (min (l - s (S n)) (s (S n)))
                                       then (f n i |+| f n (i + s (S n))%nat)%Z
                                       else f n i); simpl.
            destruct Sumbool.sumbool_and, lt_dec; rewrite Nat.min_glb_lt_iff in *; try omega; eauto.
          } Unfocus.
          rewrite sum_of_f_split; try omega.
          2: now intros; rewrite f_fun_assoc; eauto.
          2: now simpl; rewrite Nat.min_glb_lt_iff; repeat rewrite Nat.min_lt_iff; split; try omega. 
          rewrite <-minus_n_O.
          rewrite (min_l _ (s n)); try omega.
          rewrite min_l; try omega.
          rewrite min_r; try omega.
          cutrewrite (s (S n) - (l - s (S n)) = s n - l); [|omega].
          rewrite <-shift_values; simpl; eauto.
          assert (Heq : l = (l - s (S n)) + s (S n)) by omega; rewrite Heq at 5.
          Lemma shuffle a b c: a +++ b +++ c = a +++ c +++ b.
          Proof.
            destruct a, b, c; simpl; eauto.
            rewrite f_fun_assoc, (f_fun_comm l1 l2), <-f_fun_assoc; eauto.
            rewrite f_fun_comm; eauto.
          Qed.
          rewrite shuffle.
          rewrite opopt_assoc; eauto.
          rewrite sum_of_concat; f_equal; clear Heq; eauto.
          assert (Heq : s (S n) = s n - l + (l - s (S n))) by omega; rewrite Heq.
          rewrite <-plus_n_O.
          rewrite sum_of_concat; f_equal; eauto.
          rewrite <-Heq; f_equal; omega; eauto.
        - repeat rewrite min_r; try omega.
          erewrite sum_of_eq.
          Focus 2.
          { simpl; intros i Hi.
            destruct Sumbool.sumbool_and; try omega.
            reflexivity.
            
          } Unfocus.
          rewrite <-Hsn; rewrite sum_of_concat; eauto.
          rewrite <-shift_values; f_equal; eauto.
          f_equal; omega.
      Qed.

      Lemma fn_ok n :
        n <= e_b ->
        sum_of_vs 0 (min l (s n)) (f n) = sum_of_vs 0 l f_in.
      Proof.
        induction n; simpl.
        - unfold s; rewrite <-minus_n_O, min_l; try omega.
          intros; apply sum_of_eq; intros; eauto.
        - intros; rewrite f_inv; eauto.
          apply IHn; omega.
      Qed.

      Lemma feb_ok : match sum_of_vs 0 l f_in with None => l = 0 | Some v => v = f e_b 0 end.
      Proof.
        rewrite <-(fn_ok e_b); eauto.
        unfold s; rewrite minus_diag; simpl.
        assert (l = 0 \/ l > 0) as [|] by omega; subst; simpl; eauto.
        rewrite min_r; try omega; simpl; auto.
      Qed.
    End simfun.

    Definition Binv (fc : nat -> list val) n i :=
      (if Sumbool.sumbool_and _ _ _ _ (lt_dec (i + s (S n)) l) (lt_dec i (s (S n))) then
         (sdata' +ol (Zn i) -->l (1, vs2es (fc i))) **
         (sdata' +ol (Zn i + Zn (s (S n)))%Z -->l (1, vs2es (fc (i + (s (S n))))))
       else emp) **
       (if Nat.eq_dec i 0 then
          is_tuple_array_p (sdata') (min (s (S n)) ntrd - min (l - s (S n)) (s (S n))) fc (min (l - s (S n)) (s (S n))) 1 **
          is_tuple_array_p (sdata') (ntrd - (min (l - s (S n)) (s (S n)) + s (S n))) fc
          (min (l - s (S n)) (s (S n)) + s (S n)) 1
        else emp).

    Lemma sep_comm P Q stk :
      stk ||= P ** Q <=> Q ** P.
    Proof.
      split; intros; repeat sep_cancel.
    Qed.
    
    Lemma is_array_change (e : loc_exp) (f1 f2 : nat -> Z) n:
      forall s, (forall x, x < n -> f1 (x + s) = f2(x + s)) ->
                forall stc,
                  stc ||= is_array e n f1 s <=> is_array e n f2 s.
    Proof.
      induction n; simpl; intros s Hf stk; try reflexivity.
      rewrite IHn.
      cutrewrite (f1 s = f2 s); [reflexivity|].
      pose proof (Hf 0); rewrite plus_O_n in H; rewrite H; omega.
      intros x Hx; rewrite <-Nat.add_succ_comm; apply Hf; omega.
    Qed.
    
    Lemma is_array_p_change (e : loc_exp) (f1 f2 : nat -> Z) n p:
      forall s, (forall x, x < n -> f1 (x + s) = f2(x + s)) ->
                forall stc,
                  stc ||= is_array_p e n f1 s p <=> is_array_p e n f2 s p.
    Proof.
      induction n; simpl; intros s Hf stk; try reflexivity.
      rewrite IHn.
      cutrewrite (f1 s = f2 s); [reflexivity|].
      pose proof (Hf 0); rewrite plus_O_n in H; rewrite H; omega.
      intros x Hx; rewrite <-Nat.add_succ_comm; apply Hf; omega.
    Qed.

    Lemma is_tup_array_change (e : list loc_exp) (f1 f2 : nat -> list Z) n p:
      forall s, (forall x, x < n -> f1 (x + s) = f2(x + s)) ->
                forall stc,
                  stc ||= is_tuple_array_p e n f1 s p <=> is_tuple_array_p e n f2 s p.
    Proof.
      revert f1 f2; induction e; simpl; intros f1 f2 s Hf stk; try reflexivity.
      rewrite IHe, is_array_p_change; try reflexivity.
      - intros; unfold fst_of_vals; rewrite Hf; eauto.
      - intros; unfold tl_of_vals; rewrite Hf; eauto.
    Qed.

    Lemma is_array_concat e f f1 f2 len1 len2 : forall s stc,
        (forall off, off < len1 + len2 ->
                     f (s + off) = if lt_dec off len1 then f1 (s + off) else f2 (s + off)) ->
        stc||=
           is_array e (len1 + len2) f s <=>
           is_array e len1 f1 s ** is_array e len2 f2 (s + len1).
    Proof.
      induction len1; simpl; intros s stc H.
      - rewrite emp_unit_l, <-plus_n_O.
        rewrite is_array_change; [reflexivity|..].
        intros; rewrite plus_comm; eauto.
      - intros. rewrite <-Nat.add_succ_comm, <-sep_assoc, IHlen1.
        cutrewrite (f s = f1 s); [reflexivity|].
        cutrewrite (s = s + 0); [apply H; omega|omega].
        intros off ?; cutrewrite (S s + off = s + S off); [rewrite H; repeat destruct lt_dec|]; omega.
    Qed.

    Lemma is_array_p_concat e f f1 f2 len1 len2 p : forall s stc,
        (forall off, off < len1 + len2 ->
                     f (s + off) = if lt_dec off len1 then f1 (s + off) else f2 (s + off)) ->
        stc||=
           is_array_p e (len1 + len2) f s p <=>
           is_array_p e len1 f1 s p ** is_array_p e len2 f2 (s + len1) p.
    Proof.
      induction len1; simpl; intros s stc H.
      - rewrite emp_unit_l, <-plus_n_O.
        rewrite is_array_p_change; [reflexivity|..].
        intros; rewrite plus_comm; eauto.
      - intros. rewrite <-Nat.add_succ_comm, <-sep_assoc, IHlen1.
        cutrewrite (f s = f1 s); [reflexivity|].
        cutrewrite (s = s + 0); [apply H; omega|omega].
        intros off ?; cutrewrite (S s + off = s + S off); [rewrite H; repeat destruct lt_dec|]; omega.
    Qed.

    Lemma is_tuple_array_p_concat e f f1 f2 len1 len2 p : forall s stc,
        (forall off, off < len1 + len2 ->
                     f (s + off) = if lt_dec off len1 then f1 (s + off) else f2 (s + off)) ->
        stc||=
           is_tuple_array_p e (len1 + len2) f s p <=>
           is_tuple_array_p e len1 f1 s p ** is_tuple_array_p e len2 f2 (s + len1) p.
    Proof.
      revert f f1 f2; induction e; simpl; intros f f1 f2 s stc H.
      - rewrite emp_unit_l; reflexivity.
      - rewrite (IHe _ (tl_of_vals f1) (tl_of_vals f2)).
        rewrite (is_array_p_concat _ _ (fst_of_vals f1) (fst_of_vals f2)).
        rewrite <-!sep_assoc; split; intros; repeat sep_cancel.
        unfold fst_of_vals; intros; rewrite H; eauto; destruct (lt_dec _ _); eauto.
        unfold tl_of_vals; intros; rewrite H; eauto; destruct (lt_dec _ _); eauto.
    Qed.

    Lemma Binv_ok fc n stk:
      (forall i : nat, Datatypes.length (fc i) = dim) ->
      stk ||= @Bdiv.Aistar_v ntrd (MyVector.init (fun i => Binv fc n (nf i))) <=>
          is_tuple_array_p sdata' ntrd fc 0 1.
    Proof.
      intros Hfcwf; unfold Binv.
      rewrite sc_v2l; rewrite (vec_to_list_init0 _ emp); erewrite ls_init_eq0.
      2: intros i Hi; destruct (Fin.of_nat i ntrd) as [|[? Hex]] eqn:Heq; try omega.
      2: apply Fin_nat_inv in Heq; rewrite Heq; reflexivity.
      rewrite ls_star.
      rewrite sep_comm.
      rewrite <-(firstn_skipn 1) at 1.
      rewrite firstn_init, skipn_init.
      rewrite min_l; try omega; simpl.
      rewrite <-!sep_assoc.
      erewrite ls_init_eq'.
      Focus 2. {
        intros i Hi; destruct Nat.eq_dec; try omega.
        cutrewrite (emp = id (fun _ => emp) (1 + i)); eauto. } Unfocus.
      unfold id.
      rewrite init_emp_emp; rewrite emp_unit_l.
      rewrite <-(firstn_skipn (min (l - s (S n)) (s (S n))) (ls_init _ _ _)).
      rewrite firstn_init, skipn_init, conj_xs_app, <-plus_n_O.
      erewrite (ls_init_eq' _ _ (min (l - s (S n)) (s (S n)))).
      Focus 2. {
        intros i Hi; destruct Sumbool.sumbool_and.
        assert (l - s (S n) < s (S n) \/ s (S n) <= l - s (S n)) as [H | H]by omega.
        rewrite min_l in *; try omega.
        rewrite min_r in *; try omega.
        cutrewrite (emp = id (fun _ => emp) (min (l - s (S n)) (s (S n)) + i)); eauto. } Unfocus.
      unfold id.
      rewrite init_emp_emp; rewrite emp_unit_r.
      assert (l <= s (S n) \/ s (S n) < l) as [HsSnl | HsSnl ] by omega.
      - remember (min (s (S n)) ntrd) as msnt.
        rewrite !min_l; try  omega.
        cutrewrite (l - s (S n) = 0); [|omega]; simpl.
        rewrite <-!minus_n_O.
        assert (s (S n) <= ntrd \/ ntrd < s (S n)) as [H | H] by omega.
        + rewrite min_l in Heqmsnt; subst msnt; try omega.
          assert (Heq : ntrd = s (S n) + (ntrd - s (S n))) by omega; rewrite Heq at 2.
          rewrite is_tuple_array_p_concat; simpl; [rewrite emp_unit_r; reflexivity|intros; destruct lt_dec; eauto].
        + rewrite min_r in Heqmsnt; subst msnt; try omega.
          cutrewrite (ntrd - s (S n) = 0); [|omega].
          simpl; rewrite is_array_tup_0, !emp_unit_r; reflexivity.
      - assert (l - s (S n)  <= s (S n) \/ s (S n) <= l - s (S n)) as [Hsnl | Hsnl] by omega.
        + rewrite !min_l; try omega.
          erewrite ls_init_eq0.
          Focus 2. { intros i Hi; destruct Sumbool.sumbool_and; try omega; reflexivity. } Unfocus.
          rewrite ls_star.
          Lemma is_array_p_distr e n (f' : nat -> Z) p:
            forall s stk,
              stk ||= conj_xs (ls_init s n (fun i => e +o Zn i -->p (p, f' i))) <=>
                  is_array_p e n f' s p.
          Proof.
            induction n; intros s stk; simpl.
            - reflexivity.
            - rewrite IHn; reflexivity.
          Qed.
          Lemma is_tuple_array_p_distr e n (f' : nat -> list Z) p:
            (forall i, length (f' i) = length e) ->
            forall s stk,
              stk ||= conj_xs (ls_init s n (fun i => e +ol Zn i -->l (p, vs2es (f' i)))) <=>
                  is_tuple_array_p e n f' s p.
          Proof.
            revert f'; induction e; intros f' Hf' s stk; simpl.
            - erewrite ls_init_eq'.
              2: intros; destruct vs2es; cutrewrite (emp = id (fun _ => emp) (s + i)); eauto.
              unfold id; rewrite init_emp_emp; reflexivity.
            - rewrite <-IHe, <-is_array_p_distr, <-ls_star.
              lazymatch goal with [|- _ ||= conj_xs ?l <=> conj_xs ?l'] => 
                                  cutrewrite (l = l'); try reflexivity end.
              apply ls_init_eq'; intros i Hi; unfold fst_of_vals, tl_of_vals;
                specialize (Hf' (s + i)); destruct (f' (s + i)); simpl; try reflexivity.
              simpl in *; omega.
              intros i; lets: (Hf' i); unfold tl_of_vals; destruct (f' i); simpl in *; try omega.
          Qed.
          Lemma is_array_p_distr_off e n off (f' : nat -> Z) p:
            forall s stk,
              stk ||= conj_xs (ls_init s n (fun i => e +o (Zn i + Zn off)%Z -->p (p, f' (i + off)))) <=>
                  is_array_p e n f' (s + off) p.
          Proof.
            induction n; intros s stk; simpl.
            - reflexivity.
            - rewrite IHn.
              rewrite Nat2Z.inj_add; reflexivity.
          Qed.

          Lemma is_tuple_array_p_distr_off e n off (f' : nat -> list Z) p:
            (forall i, length (f' i) = length e) ->
            forall s stk,
              stk ||= conj_xs (ls_init s n (fun i => e +ol (Zn i + Zn off)%Z -->l (p, vs2es (f' (i + off))))) <=>
                  is_tuple_array_p e n f' (s + off) p.
          Proof.
            revert f'; induction e; intros f' Hf' s stk; simpl.
            - erewrite ls_init_eq'.
              2: intros; destruct vs2es; cutrewrite (emp = id (fun _ => emp) (s + i)); eauto.
              unfold id; rewrite init_emp_emp; reflexivity.
            - rewrite <-IHe, <-is_array_p_distr_off, <-ls_star.
              lazymatch goal with [|- _ ||= conj_xs ?l <=> conj_xs ?l'] => 
                                  cutrewrite (l = l'); try reflexivity end.
              apply ls_init_eq'; intros i Hi; unfold fst_of_vals, tl_of_vals;
                specialize (Hf' (s+i+ off)); destruct (f' (s+i+ off)); simpl; try reflexivity.
              simpl in *; omega.
              intros i; lets: (Hf' i); unfold tl_of_vals; destruct (f' i); simpl in *; try omega.
          Qed.
          
          rewrite is_tuple_array_p_distr.
          rewrite is_tuple_array_p_distr_off; simpl.
          cutrewrite (l - s (S n) + s (S n) = l); [|omega].
          assert (Heq : ntrd = (l - s (S n)) + (s (S n) - (l - s (S n))) + (l - s (S n)) + (ntrd - l))
            by lia.
          rewrite Heq at 2.
          repeat (rewrite is_tuple_array_p_concat; [|intros; destruct lt_dec; reflexivity]).
          cutrewrite (l - s (S n) + (s (S n) - (l - s (S n))) = s (S n)); [|lia].
          cutrewrite (s (S n) + (l - s (S n)) = l); [|lia].
          simpl; rewrite <-!sep_assoc; split; intros; repeat sep_cancel.
          intros; unfold es2shs, vars2es; rewrite !map_length, locals_length; eauto.
          intros; unfold es2shs, vars2es; rewrite !map_length, locals_length; eauto.
        + repeat rewrite (min_l _ ntrd); try omega.
          2: rewrite Nat.min_le_iff; try omega.
          repeat rewrite min_r; try omega.
          rewrite minus_diag; simpl; rewrite is_array_tup_0, emp_unit_l.
          erewrite ls_init_eq0.
          Focus 2. { intros i Hi; destruct Sumbool.sumbool_and; try omega; reflexivity. } Unfocus.
          rewrite ls_star, is_tuple_array_p_distr, is_tuple_array_p_distr_off; simpl.
          assert (Heq : ntrd = s (S n) + s (S n) + (ntrd - (s (S n) + s (S n)))) by lia.
          rewrite Heq at 2; clear Heq.
          repeat (rewrite is_tuple_array_p_concat; [|intros; destruct lt_dec; reflexivity]).
          simpl; rewrite <-!sep_assoc.
          split; intros; repeat sep_cancel.
          intros; unfold es2shs, vars2es; rewrite !map_length, locals_length; eauto.
          intros; unfold es2shs, vars2es; rewrite !map_length, locals_length; eauto.
    Qed.

    Definition BSpre n i :=
      match n with
      | O => (sdata' +ol (Zn i)) -->l (1, vs2es (f_in i))
      | S n => Binv (f (S n)) n i
      end.

    Definition BSpost n i := Binv (f n) n i.

    Definition BS n := (@MyVector.init _ ntrd (fun i =>(BSpre n (nf i))),
                        @MyVector.init _ ntrd (fun i =>(BSpost n (nf i)))).

    Lemma reduce_body_ok n i:
      CSL BS i
          (!(tid === Zn (nf i)) **
            !(len === Zn l) **
            !(vars2es y ==t f n (nf i)) **
            BSpre n (nf i))
          (reduce_body (S n) (s (S n)))
          (!(tid === Zn (nf i)) **
            !(len === Zn l) **
            !(vars2es y ==t f (S n) (nf i)) **
            BSpre (S n) (nf i)).
    Proof.
      remember (S n) as sn.
      unfold reduce_body.
      eapply rule_seq; simpl.
      { subst sn; simpl; rewrite <-minus_n_O; unfold BS.
        hoare_forward.
        - intros s h H; sep_cancel; eauto.
        - simpl; rewrite MyVector.init_spec.
          unfold BSpost, Binv.
          intros s h H; sep_normal_in H; eauto. }
      hoare_forward; eauto.
      { eapply Hbackward.
        Focus 2. {
          intros st h H.
          sep_split_in H.
          change_in H.
          { unfold_pures; unfold_conn_in (HP0, HP1); simpl in HP0, HP1.
            destruct Z_lt_dec; try congruence.
            destruct Sumbool.sumbool_and; unfold lt in *; try omega.
            sep_normal_in H.
            assert ((Zn (nf i) === tid) st (emp_ph loc)).
            { unfold_conn_all; simpl in *; zify; unfold lt in *; omega. }
            sep_rewrite_in mps_eq1_tup' H; [|exact H0].
            assert (((Zn (nf i) + Zn (s (S n)))%Z ===
                                               (tid +C Zn (s (S n)))) st (emp_ph loc)).
            { unfold_conn_all; simpl in *; f_equal; zify; unfold lt in *; omega. }
            sep_lift_in H 1.
            sep_rewrite_in mps_eq1_tup' H; [|subst sn; exact H1].
            apply H. }
          sep_combine_in H; exact H. } Unfocus.
        eapply rule_seq; [apply rule_frame; [apply gen_read_correct|]; eauto; simpl|];
          try now (simplify; prove_inde; simplify; try first [now eauto | congruence]).
        { Lemma f_length n i : length (f n i) = dim.
          Proof.
            revert i; induction n; simpl; eauto.
            intros i; destruct Sumbool.sumbool_and; eauto.
          Qed.
          rewrite f_length; simplify; eauto. }
        { prove_inde; simplify; try (rewrite gen_read_writes in H; simplify; eauto; try congruence);
          simplify; try (rewrite gen_read_writes in H0; simplify; try congruence). }
        eapply rule_seq.
        { eapply Hbackward.
          Focus 2.
          { intros stk h H; evar (P : assn);
            assert (((!(vars2es y ==t f n (nf i)) ** !(vars2es x ==t f n (nf i + s sn))) ** P) stk h) by
                (unfold P; sep_normal_in H; sep_normal; sep_split; sep_split_in H; auto;
                 sep_combine_in H; eauto). 
            unfold P in *; exact H0. } Unfocus.
          eapply rule_frame; [apply func_denote|]; eauto.
          { apply f_fun_den; apply f_length. }
          { apply locals_length. }
          { apply not_in_disjoint; simplify.
            forwards: func_local; eauto; simpl in *; congruence. }
          { apply not_in_disjoint; simplify.
            forwards: func_local; eauto; simpl in *; congruence. }
          prove_inde; simplify; forwards: func_local; eauto; simpl in *; try congruence. }
        eapply rule_seq.
        { eapply Hbackward.
          Focus 2.
          { intros stk h H; evar (P : assn);
            assert ((!(snd (func y x) ==t  f n (nf i) |+| f n (nf i + s sn)) ** P) stk h) by 
                (unfold P; sep_normal_in H; sep_normal; sep_split; sep_split_in H; auto;
                 sep_combine_in H; eauto). 
            unfold P in *; exact H0. } Unfocus.
          eapply rule_frame; [eapply read_tup_correct|].
          { simplify; forwards: func_res_fv; eauto.
            simplify; congruence. }
          { apply locals_disjoint_ls. }
          { lets H: (f_fun_den (f n (nf i)) (f n (nf i + s sn)));
            try rewrite !f_length; eauto;
            lets: (>> f_den_wf H); try rewrite !f_length; eauto.
            lets: (func_wf x y); congruence. }
          { rewrite locals_length, func_wf; eauto. }
          { lets H: (>>read_tup_writes z (snd (func y x)) ___); [|rewrite H].
            { rewrite locals_length, func_wf; eauto. }
            prove_inde; simplify; eauto; simpl in *; try congruence.
            forwards: func_res_fv; eauto; simplify; congruence. } }
        eapply rule_seq.
        { eapply Hbackward.
          Focus 2.
          { intros stk h H; evar (P : assn);
            assert ((!(vars2es z ==t f n (nf i) |+| f n (nf i + s sn)) ** P) stk h).
            { unfold P; sep_normal_in H; sep_normal; sep_split; sep_split_in H; auto.
              clear HP0 HP5; sep_combine_in H; eauto. }
            unfold P in *; exact H0. } Unfocus.
          eapply rule_frame; [eapply read_tup_correct|].
          { simplify; congruence. }
          { apply locals_disjoint_ls. }
          { lets H: (f_fun_den (f n (nf i)) (f n (nf i + s sn)));
            try rewrite !f_length; eauto;
            lets: (>> f_den_wf H); try rewrite !f_length; eauto.
            unfold vars2es; rewrite map_length, locals_length; congruence. }
          { lets H: (f_fun_den (f n (nf i + s sn)) (f n (nf i)));
            try rewrite !f_length; eauto;
            lets: (>> f_den_wf H); try rewrite !f_length; eauto.
            unfold vars2es; rewrite map_length, !locals_length; congruence. }
          { rewrite read_tup_writes.
            prove_inde; simplify; eauto; simpl in *; try congruence.
            { unfold vars2es; rewrite map_length, !locals_length; eauto. } } }
        eapply Hbackward.
        Focus 2.
        { intros stk h H; evar (P : assn);
          assert (((sdata' +ol tid -->l (1, vs2es (f n (nf i)))) ** P) stk h).
          { unfold P, lt in *; clear P; sep_normal_in H; sep_normal; sep_split;
            sep_split_in H; sep_cancel.
            sep_combine_in H0; eauto. } 
          unfold P; exact H0. } Unfocus.

        apply rule_frame; [apply gen_write_correct|]; eauto; simpl;
          try now (simplify; prove_inde; simplify; try first [now eauto | congruence]).
        unfold vs2es, vars2es; rewrite !map_length, f_length, !locals_length; auto.
        Lemma inde_nil P : inde P nil.
        Proof.
          unfold inde; intros; inversion H.
        Qed.
        rewrite writes_var_gen_write; apply inde_nil. }
      { eapply rule_skip. }
      intros st h  [H | H]; sep_split_in H; unfold_pures; sep_split; eauto; sep_cancel.
      - destruct Z_lt_dec; try congruence; unfold_conn; subst sn; simpl; eauto.
        destruct Sumbool.sumbool_and; unfold lt in *; try lia.
        eauto.
      - unfold BSpre, Binv; subst sn; simpl.
        destruct Z_lt_dec; try congruence; try omega.
        destruct Sumbool.sumbool_and; unfold lt in *; try omega.
        destruct Sumbool.sumbool_and; try omega.
        assert (Heq :(tid === Zn (nf i)) st (emp_ph loc)) by (unfold_conn; eauto).
        sep_rewrite_in mps_eq1_tup' H; [|exact Heq]; clear Heq.
        sep_rewrite_in mps_eq2_tup H; [|exact HP].
        sep_normal_in H; sep_normal.
        unfold lt in *; sep_cancel.
        assert (Heq :(tid +C Zn (s (S n)) === (Zn (nf i) + Zn (s (S n)))%Z) st (emp_ph loc)).
        { unfold_conn; simpl; rewrite HP3; unfold lt; ring. }
        sep_rewrite_in mps_eq1_tup' H0; [|exact Heq]. clear Heq.
        unfold lt in *; repeat sep_cancel.
        destruct Nat.eq_dec; eauto.
        sep_rewrite is_tup_array_change; [sep_rewrite sep_comm; sep_rewrite is_tup_array_change|].
        sep_rewrite sep_comm; eauto.
        intros; destruct Sumbool.sumbool_and; try lia; eauto.
        intros; destruct Sumbool.sumbool_and; try lia; eauto.
      - unfold_conn; subst sn; simpl; eauto.
        destruct Sumbool.sumbool_and; unfold lt in *; try lia; eauto.
        destruct Z_lt_dec; simpl in *; try congruence; try lia.
        unfold_conn_all; simpl in *; try omega.
      - unfold BSpre, Binv; subst sn; simpl.
        destruct Z_lt_dec; simpl in *; try congruence; try omega.
        unfold_conn_in (HP0, HP1); simpl in HP0, HP1; try omega.
        destruct Sumbool.sumbool_and; unfold lt in *; try omega.
        sep_normal_in H; sep_normal.
        destruct Nat.eq_dec; eauto.
        sep_rewrite is_tup_array_change; [sep_rewrite sep_comm; sep_rewrite is_tup_array_change|].
        sep_rewrite sep_comm; eauto.
        intros; destruct Sumbool.sumbool_and; try lia; eauto.
        intros; destruct Sumbool.sumbool_and; try lia; eauto.
      - unfold_conn; subst sn; simpl; eauto.
        unfold_conn_in (HP0, HP1); simpl in HP0, HP1; try omega.
        destruct Sumbool.sumbool_and; unfold lt in *; try lia; eauto.
      - unfold BSpre, Binv; subst sn; simpl.
        unfold_conn_in (HP0, HP1); simpl in HP0, HP1; try omega.
        destruct Sumbool.sumbool_and; unfold lt in *; try omega.
        sep_normal_in H; sep_normal.
        destruct Nat.eq_dec; eauto.
        sep_rewrite is_tup_array_change; [sep_rewrite sep_comm; sep_rewrite is_tup_array_change|].
        sep_rewrite sep_comm; eauto.
        intros; destruct Sumbool.sumbool_and; try lia; eauto.
        intros; destruct Sumbool.sumbool_and; try lia; eauto.
    Qed.

    Lemma is_tuple_array_cons es n f s q stk :
      (forall i, length (f i) = length es) ->
      stk ||= is_tuple_array_p es (S n) f s q <=>
          is_tuple_p (es +ol Zn s) (vs2es (f s)) q ** is_tuple_array_p es n f (S s) q.
    Proof.
      revert s f; induction es; intros s f Hl; simpl.
      - destruct vs2es; rewrite emp_unit_l; reflexivity.
      - lets: (>> Hl s).
        assert (length (vs2es (f s)) = length (a :: es))
          by (simpl; unfold vs2es; rewrite map_length; eauto); [simpl in *|..].
        rewrite IHes, <-!sep_assoc.
        unfold fst_of_vals, tl_of_vals.
        destruct (f s); simpl in *; try omega.
        rewrite <-!sep_assoc.
        split; intros; repeat sep_cancel.
        intros; lets: (Hl i); unfold tl_of_vals; destruct (f i); simpl in *; try omega.
    Qed.

    Lemma reduce_aux_ok i t m :
      CSL BS i
          (!(tid === Zn (nf i)) **
            !(len === Zn l) **
            !(vars2es y ==t f t (nf i)) **
            BSpre t (nf i))
          (reduce_aux (S t) m)
          (!(tid === Zn (nf i)) **
            !(len === Zn l) **
            !(vars2es y ==t f (t + m) (nf i)) **
            BSpre (t + m) (nf i)).
    Proof.
      revert t; induction m; simpl; intros t.
      - rewrite <-plus_n_O; apply rule_skip.
      - eapply rule_seq; eauto.
        apply reduce_body_ok.
        cutrewrite (t + S m = S t + m); [|omega]; eauto.
    Qed.

    Require Import Program.
    Lemma reduce_ok0 i :
      CSL BS i
          (!(tid === Zn (nf i)) **
            !(len === Zn l) **
            !(vars2es y ==t f_in (nf i)) **
            (sdata' +ol (Zn (nf i)) -->l (1, vs2es (f_in (nf i)))))
          reduce
          (!(tid === Zn (nf i)) **
            !(len === Zn l) **
            !(vars2es y ==t f e_b (nf i)) **
            if Nat.eq_dec (nf i) 0 then is_tuple_array_p sdata' ntrd (f e_b) 0 1 else emp).
    Proof.
      unfold reduce.
      eapply rule_conseq; eauto using reduce_aux_ok.
      simpl; intros st h H.
      repeat sep_cancel.
      clear h H h0 H0 h1 H1.
      unfold BSpre, Binv in *.
      unfold s in *.
      destruct e_b; try omega; remember (S n) as e_b'.
      rewrite minus_diag in *; simpl in *.
      clear Heqe_b' n.
      destruct Nat.eq_dec.
      2: destruct Sumbool.sumbool_and; try omega; sep_normal_in H2; eauto.
      rewrite e in *; simpl in *.
      destruct Sumbool.sumbool_and; try lia.
      - destruct ntrd; try omega.
        rewrite min_r in H2; try omega; simpl in H2; sep_normal_in H2.
        simpl; sep_cancel.
        destruct n; simpl in *; try omega; repeat sep_cancel.
        rewrite <-minus_n_O in H2; eauto.
        repeat sep_rewrite is_tuple_array_cons; eauto;
          try (intros; unfold vars2es; rewrite f_length, !map_length, locals_length; eauto).
        repeat sep_rewrite_r sep_assoc; repeat sep_cancel.
        sep_rewrite_in is_array_tup_0 H2; sep_rewrite_in emp_unit_l H2.
        apply H2.
      - destruct ntrd; sep_normal_in H2; try omega.
        rewrite min_l in H2; try omega.
        cutrewrite (l - 1 = 0) in H2; [|omega]; simpl in H2.
        rewrite <-minus_n_O in H2.
        cutrewrite (S n = 1 + n); [|omega];
          sep_rewrite (is_tuple_array_p_concat sdata' (f e_b') (f e_b') (f e_b')); simpl; eauto.
        intros; destruct lt_dec; eauto.
    Qed.

    Theorem BS_ok b :
      Bdiv.Aistar_v (fst (BS b)) |= Bdiv.Aistar_v (snd (BS b)). 
    Proof.
      unfold BS, BSpre, BSpost; simpl.
      intros s h H.
      destruct b.
      - istar_simplify_in H.
        apply is_tuple_array_p_distr in H.
        apply Binv_ok; simpl; eauto.
        intros; unfold vars2es; rewrite f_in_wf, !map_length, locals_length; auto.
      - apply Binv_ok; try (intros; rewrite f_length; auto).
        apply Binv_ok in H; eauto.
        intros; destruct Sumbool.sumbool_and; try (rewrite f_length; auto).
        lets: (>>f_fun_den ___); try (apply f_length).
        lets: (>>f_den_wf H0); try (rewrite f_length; auto); eauto.
    Qed.
  End ReduceBlock.
  
  Variable get : var -> cmd * list exp.
  
  Hypothesis get_wf :
    forall x, length (snd (get x)) = dim.
  Hypothesis get_wr :
    forall x y, In x (writes_var (fst (get (y)))) -> prefix "l" (var_of_str y) = true.
  Hypothesis get_res_fv :
    forall x y e, In e (snd (get x)) -> In y (fv_E e) ->
                  y = x \/ prefix "l" (var_of_str y) = true.
  Hypothesis get_no_bar :
    forall x, barriers (fst (get x)) = nil.
  Variable get_den : val -> list val -> Prop.
  Hypothesis get_den_wf :
    forall x ys, get_den x ys -> length ys = dim.
  Local Notation nt_gr := (nblk * ntrd).
  (* free variable environment (de-bruijn indices, dimensions) *)
  Variable env : list (nat * nat).
  (** runtime values *)
  (* runtime value of the input arrays: length * elements *)
  Variable env_den : list (list Z * nat * (nat -> list val)).

  (* env is consistent with env_den *)
  Hypothesis env_env_den_same_len : length env = length env_den.
  
  Hypothesis get_denote : forall nt x (tid : Fin.t nt) v gv BS,
      get_den v gv ->
      ~In x (writes_var (fst (get x))) ->
      CSL BS tid 
        (!(x === v) ** input_spec env env_den (perm_n nt_gr))
        (fst (get x))
        (!(snd (get x) ==t gv) ** input_spec env env_den (perm_n nt_gr)).

  Variable l : nat.
  Notation sh := (Var "sh").

  Section SeqReduce.
    Notation ix := (Var "ix").
    Definition seq_reduce inv :=
      read_tup y (nseq dim (Enum 0%Z)) ;;
      catcmd (gen_write Sh sdata tid (nseq dim (Enum 0%Z))) ;;
      ix ::= (tid +C bid *C Z.of_nat ntrd) ;;
      Cif (ix <C sh) (
        (fst (get ix)) ;;
        read_tup y (snd (get ix)) ;;
        ix ::= ix +C Z.of_nat ntrd *C Z.of_nat nblk ;;
        WhileI inv (ix < sh) (
          (fst (get ix)) ;;
          read_tup x (snd (get ix)) ;;
          (fst (func y x)) ;;
          read_tup z (snd (func y x)) ;;
          read_tup y (vars2es z) ;;
          ix ::= ix +C Z.of_nat ntrd *C Z.of_nat nblk
        );;
        catcmd (gen_write Sh sdata tid (vars2es y))
      ) Cskip.


    Notation sum_of_vs := (sum_of_f_opt (list val) f_fun).
    Close Scope exp_scope.
    Notation skip_sum_of_vs := (skip_sum_of_opt (list val) f_fun).

    Section Skip_sum_of.
      Variable T : Type.
      Variable op : T -> T -> T.
      Variable f : nat -> T.
      Variable skip i : nat.
      Hypothesis op_comm : forall x y, op x y = op y x. 
      Lemma skip_sum_opt_nil next fc : forall s (len : nat),
          (forall j, j < next -> (s + j) mod skip <> i) ->
          skip_sum_of_opt T op skip s len fc i =
          skip_sum_of_opt T op skip (s + next) (len - next) fc i.
      Proof.
        induction next; intros s len Hj; simpl.
        - rewrite <-plus_n_O, <-minus_n_O; auto.
        - destruct len; auto.
          cutrewrite (s + S next = S s + next); [|omega].
          cutrewrite (S len - S next = len - next); [|omega].
          rewrite <-IHnext.
          + simpl; destruct Nat.eq_dec; auto.
            specialize (Hj 0); rewrite <-plus_n_O in Hj; apply Hj in e; [tauto|omega].
          + intros j Hjn; cutrewrite (S s + j = s + S j); [|omega]; apply Hj; omega.
      Qed.
      
      Lemma skip_sum_opt_unfold (len : nat) fc : forall s,
          skip <> 0 ->
          (i < len)%nat -> (i < skip)%nat ->
          skip_sum_of_opt T op skip (s * skip) len fc i =
          ((op' T op) (skip_sum_of_opt T op skip (S s * skip)%nat (len - skip)%nat fc i)%Z
                      (Some (fc (i + s * skip)%nat))).
      Proof.
        intros s Hskip Hil His.
        rewrite skip_sum_opt_nil with (next:=i). 
        2: intros; rewrite plus_comm, Nat.add_mod; auto.
        2: rewrite Nat.mod_mul; auto; rewrite <-plus_n_O, Nat.mod_mod; auto; rewrite Nat.mod_small; omega.
        assert (exists li, len - i = S li) as [li Hli] by (exists (len - i - 1); omega).
        rewrite (plus_comm (s * skip));
          rewrite Hli; simpl; destruct Nat.eq_dec as [He | He].
        2 : rewrite Nat.mod_add in He; auto; rewrite Nat.mod_small in He; omega.
        f_equal.
        rewrite skip_sum_opt_nil with (next:= skip - S i).
        lazymatch goal with [|- context [skip_sum_of_opt _ _ _ ?X _ _ _]] => cutrewrite (X = skip + s * skip); [|omega] end.
        cutrewrite (li - (skip - S i) = len - skip); [|omega]; auto.
        intros j Hj. 
        lazymatch goal with [|- context [?X mod _]] => cutrewrite (X = (S i + j) + s * skip); [|omega] end.
        rewrite Nat.mod_add; auto; rewrite Nat.mod_small; omega.
      Qed.

      Lemma skip_sum_opt_sum s n m :
        i < skip ->
        skip * n + i < m + skip <= skip * S n + i ->
        skip_sum_of_opt T op skip (s * skip) m f i =
        sum_of_f_opt T op s n (fun j => f (i + j * skip)).
      Proof.
        revert s m; induction n; simpl; intros s m His Hmi.
        - assert (m <= i) by omega.
          rewrites* (>>skip_sum_opt_nil m).
          { intros; rewrite plus_comm; rewrite Nat.mod_add; try omega;
            rewrite Nat.mod_small; try omega. }
          rewrite minus_diag; simpl; eauto.
        - rewrites* skip_sum_opt_unfold; [|nia..].
          destruct n; simpl.
          + rewrite (skip_sum_opt_nil (m - skip)); try rewrite minus_diag; simpl; eauto.
            intros; cutrewrite (skip + s * skip + j = j + (S s) * skip); [|ring];
              rewrite Nat.mod_add; try omega; rewrite Nat.mod_small; try omega.
          + cutrewrite (skip + s * skip = S s * skip); [|ring].
            rewrite IHn; [|try omega..].
            2: nia.
            unfold op'; simpl.
            lazymatch goal with
            | [|- context [match ?X with Some _ => _ | None => _ end]] => destruct X
            end; eauto.
            rewrite op_comm; auto.
      Qed.
      
      Lemma skip_sum_sum0 n m:
        i < skip ->
        skip * n + i < m + skip <= skip * S n + i ->
        skip_sum_of_opt T op skip 0 m f i =
        sum_of_f_opt T op 0 n (fun j => f (i + j * skip)).
      Proof.
        cutrewrite (0 = 0 * skip); [|omega]; apply skip_sum_opt_sum.
      Qed.
    End Skip_sum_of.
            
    Variable i : Fin.t ntrd.
    Variable j : Fin.t nblk.
    Variable vi_ini : list Z.
    Hypothesis vi_ini_wf : length (vi_ini) = dim.
    Notation gid := (nf i + nf j * ntrd).
    Notation xix x := (x * nt_gr + gid).

    Definition maybe {T : Type} (x : option T) y := match x with Some z => z | None => y end.

    Definition inv g :=
      Ex nl,
        !(pure (0 < nl)) **
        !(tid === Zn (nf i)) ** !(bid === Zn (nf j)) ** !(sh === Zn l) **
        !(ix === (Zn (nl * nt_gr + (nf i + nf j * ntrd)))) **
        !(vars2es y ==t maybe (skip_sum_of_vs nt_gr 0 (min (xix nl) l) g gid) (nseq dim 0%Z)) **
        (sdata' +ol tid -->l (1, vs2es (nseq dim 0%Z))) **
        input_spec env env_den (perm_n nt_gr).

    Hypothesis get_safe :
      forall i, i < l -> exists v, get_den (Zn i) v.
    
    Lemma get_ex : exists g, forall i, i < l -> get_den (Zn i) (g i).
    Proof.
      generalize l get_safe; intros len Hgs; induction len.
      - exists (fun _ : nat => @nil val); intros; omega.
      - lets (g & Hg): (>>IHlen ___); intros.
        apply Hgs; try omega.
        lets (gvl & Hgvl): (Hgs len); try omega.
        exists (fun x => if Nat.eq_dec x len then gvl else g x); 
          intros; destruct Nat.eq_dec; subst; intuition.
    Qed.

    Lemma sublEs_mapsh x v le : sublEs x v (map Sh le) = map Sh (subEs x v le).
    Proof.
      induction le; simpl; eauto.
      f_equal; eauto.
    Qed.

    Lemma sublEs_locals x v y d :
      prefix y (var_of_str x) = false ->
      subEs x v (vars2es (locals y d)) = vars2es (locals y d).
    Proof.
      induction d; simpl; eauto.
      intros.
      destruct var_eq_dec; simpl; try now (rewrite IHd); eauto.
      subst; simpl in *; rewrite prefix_cat in *; congruence.
    Qed.

    Hint Rewrite sublEs_mapsh sublEs_tarr_idx subEs_vs2es subE_vars2es sublEs_locals.

    Lemma hback nt (R : Prop) C P Q BS tid:
      (R -> @CSL nt BS tid P C Q) <-> (@CSL nt BS tid (!(pure R) ** P) C Q).
    Proof.
      split; intros H.
      intros s h H'; sep_split_in H'; simpl in *.
      apply H; eauto.
      intros Hr; eapply Hbackward; eauto.
      intros; sep_split; eauto.
    Qed.
    Lemma ntgr_gid : gid < nt_gr.
    Proof. eauto. Qed.

    Definition vi g v := 
      maybe (skip_sum_of_vs nt_gr 0 l g (nf i + nf j * ntrd)) v.

    Lemma eq_tup_nseq s x n : (nseq n (Enum x) ==t nseq n x) s (emp_ph loc).
    Proof.
      induction n; simpl; eauto.
      sep_split; apply emp_emp_ph.
      sep_normal; sep_split; try now (unfold_conn; eauto).
    Qed.

    Lemma seq_reduce_correct BS g:
      (forall i, i < l -> get_den (Zn i) (g i)) ->
      CSL BS i
       (!(tid === Zn (nf i)) ** !(bid === Zn (nf j)) ** !(sh === Zn l) **
        (sdata' +ol Zn (nf i) -->l (1, vs2es vi_ini)) **
        input_spec env env_den (perm_n nt_gr))

       (seq_reduce (inv g))

       (!(tid === Zn (nf i)) **
        !(vars2es y ==t vi g (nseq dim 0%Z)) **
        (sdata' +ol Zn (nf i) -->l (1, vs2es (vi g (nseq dim 0%Z)))) **
        input_spec env env_den (perm_n nt_gr) ** !(sh === Zn l)).
      Proof.
        unfold seq_reduce; intros Hg.
        eapply Hbackward.
        Focus 2. {
          intros s h H.
          evar (P : assn); assert ((!(nseq dim (Enum 0%Z) ==t nseq dim 0%Z) ** P) s h).
          { sep_split; eauto using eq_tup_nseq.
            unfold P; eauto. }
          unfold P; apply H0. } Unfocus.
        eapply rule_seq.
        eapply rule_frame.
        eapply read_tup_correct; eauto; try congruence.
        { intros; simplify; eauto; rewrite Heq in *; simpl in *; tauto. }
        { apply locals_disjoint_ls. }
        { rewrite !length_nseq; auto. }
        { rewrite locals_length, length_nseq; eauto. }
        { rewrite read_tup_writes.
          prove_inde; simplify; simpl in *; try congruence.
          apply inde_input_spec; simplify; simpl; eauto.
          rewrite locals_length, length_nseq; eauto. }

        eapply Hbackward.
        Focus 2. {
          intros s h H.
          assert ( Heq : (Zn (nf i) === tid) s (emp_ph loc)).
          { sep_split_in H; unfold_conn; simpl; eauto. }
          sep_rewrite_in mps_eq1_tup' H; [|exact Heq]; clear Heq.
          evar (P : assn); assert ((sdata' +ol tid -->l (1, vs2es vi_ini) ** P) s h).
          { sep_split_in H; sep_cancel.
            unfold P; sep_combine_in H0; apply H0. }
          unfold P in *; apply H0. } Unfocus.
        eapply rule_seq.
        eapply rule_frame.
        eapply gen_write_correct.
        { unfold vs2es, vars2es; rewrite !map_length, locals_length; eauto. }
        { unfold vs2es, vars2es; rewrite !map_length, locals_length, length_nseq; eauto. }
        { rewrite writes_var_gen_write; unfold inde; simpl; tauto. }

        Lemma nseq_subEs x e d (v : Z) : subEs x e (nseq d (Enum v)) = nseq d (Enum v).
        Proof.
          induction d; simpl; congruence.
        Qed.
        Hint Rewrite nseq_subEs.

        eapply rule_seq; [hoare_forward|].
        { intros ? ? [v H]; subA_normalize_in H with (fun H => first
            [ apply subA_distribute_tup in H | apply subA_eq_tup in H
              | apply subA_is_tuple_p in H | apply subA_input_spec in H; eauto ] ).
          autorewrite with core in H; simpl in *; eauto. }
             hoare_forward; eauto using rule_skip.

        - eapply Hbackward.
          Focus 2.
          { intros stk h H; sep_split_in H.
            clear HP1.
            assert (pure (nf i + nf j * ntrd < l) stk (emp_ph loc))
              by (unfold_conn; simpl; unfold_pures; nia).
            assert ((ix=== Zn (nf i + nf j * ntrd)) stk (emp_ph loc))
              by (unfold_conn; simpl; unfold_pures; nia).
            clear HP HP0.
            evar (P : assn);
              assert ( Hnxt : ((!(pure (nf i + nf j * ntrd < l)) **
                                (!(ix === Zn (nf i + nf j * ntrd)) **
                                  input_spec env env_den (perm_n nt_gr)) ** P)) stk h).
            { sep_normal; sep_split; eauto.
              unfold P; sep_combine_in H; repeat sep_cancel; eauto. }
            apply Hnxt. } Unfocus.
          rewrite <-hback; intros Hl.
          eapply rule_seq.
          { eapply rule_frame; [apply get_denote|].
            forwards: get_safe; eauto.
            intros Hc; forwards: get_wr; eauto; simpl in *; congruence.
            prove_inde; simplify; forwards: get_wr; eauto; simplify; simpl in *; try congruence. }
          eapply rule_seq.
          { eapply Hbackward.
            Focus 2. {
              intros stk h H; sep_normal_in H; sep_split_in H.
              evar (P : assn);
                assert (Hnxt :(!(snd (get ix) ==t g (nf i + nf j * ntrd)) ** P) stk h)
                by (sep_split; eauto; unfold P; sep_combine_in H; eauto).
              unfold P; apply Hnxt. } Unfocus.
            apply rule_frame; [apply read_tup_correct|];
              try now (simplify; forwards * : get_res_fv; eauto; simplify; try congruence).
            { lets: (>> get_den_wf (Zn (nf i + nf j * ntrd)) ___); eauto.
              rewrite H, get_wf; eauto. }
            { rewrite locals_length, get_wf; eauto. }
            { rewrite read_tup_writes.
              prove_inde; simplify; simpl in *; autorewrite with core in *; try congruence.
              { apply inde_input_spec; simplify; simpl in *; eauto. }
              { forwards: get_res_fv; eauto; simplify; congruence. }
              { rewrite locals_length, get_wf; eauto. } } }

          eapply rule_seq; [hoare_forward|].
          { intros stk h [v H]; subA_normalize_in H with (fun H => first
            [ apply subA_distribute_tup in H | apply subA_eq_tup in H
              | apply subA_is_tuple_p in H | apply subA_input_spec in H; eauto ] ).
            autorewrite with core in H; try now (simpl; congruence); simpl in H.
            sep_split_in H.
            clear HP1; unfold_conn_in HP6; simpl in HP6.
            assert (HP' :(ix === v + Zn ntrd * Zn nblk)%Z stk (emp_ph loc))
              by (unfold_pures; simpl; eauto).
            rewrite HP6 in HP'; clear HP.
            simpl in *; sep_combine_in H; exact H. }
          { eapply rule_seq; [hoare_forward|]; eauto.
            - eapply Hbackward.
              Focus 2. { 
                unfold inv; intros stk h H.
                apply ex_lift_l_in in H as [nl H].
                sep_split_in H.
                assert (pure (xix nl < l) stk (emp_ph loc))
                  by (unfold_pures; unfold_conn_all; simpl in *; nia).
                clear HP.
                evar (P : assn);
                  assert (Hnxt : (!(pure (xix nl < l)) **
                                  (!(ix === Zn (xix nl)) **
                                  input_spec env env_den (perm_n nt_gr)) ** P) stk h).
                { unfold P; sep_normal; sep_split; eauto; sep_cancel.
                  sep_combine_in H1; apply H1. }
                unfold P in *; ex_intro nl Hnxt; apply Hnxt. } Unfocus.
              apply rule_ex; intros nl; rewrite <-hback; intros Hnl.
              eapply rule_seq.
              { apply rule_frame; [apply get_denote|]; eauto.
                simplify; lets: (>>get_wr ix ix H); simplify; simpl in *; congruence.
                prove_inde; simplify; forwards: get_wr; eauto; simpl in *; congruence. }
              eapply rule_seq.
              { eapply Hbackward.
                Focus 2. {
                  intros stk h H.
                  sep_normal_in H; sep_split_in H.
                  evar (P : assn);
                    assert (Hnxt : (!(snd (get ix) ==t g (xix nl)) ** P) stk h) by
                      (sep_split; auto; sep_combine_in H; unfold P; eauto).
                  apply Hnxt. } Unfocus.
                apply rule_frame; [eapply read_tup_correct|]; eauto using locals_disjoint_ls.
                - simplify.
                  forwards: get_res_fv; eauto; simplify; congruence.
                - forwards * H : (>>get_den_wf (Zn (xix nl))); rewrite H, get_wf; eauto.
                - rewrite locals_length, get_wf; eauto.
                - rewrite read_tup_writes; prove_inde; simplify; try congruence.
                  + apply inde_input_spec; simpl; intros; forwards: locals_pref; eauto; simplify;
                      simpl; try congruence.
                  + forwards* : get_res_fv; eauto; simplify; try congruence. }
              eapply rule_seq.
              { eapply Hbackward.
                Focus 2. {
                  intros stk h H; sep_split_in H.
                  clear HP0.
                  evar (P : assn);
                  assert (Hnxt : ((!(vars2es y ==t
                                     maybe (skip_sum_of_vs nt_gr 0 (min (xix nl) l) g gid) (nseq dim 0%Z)) **
                                   !(vars2es x ==t g (xix nl))) **
                                   P) stk h)
                  by (unfold P; sep_normal; sep_split; auto; sep_combine_in H; eauto).
                  unfold P in *; apply Hnxt. } Unfocus.
                apply rule_frame; [apply func_denote|]; eauto using locals_length.
                - apply f_fun_den; eauto.
                  unfold maybe.
                  Lemma skip_sum_of_vs_wf skip k s len v g:
                    (forall ix, s <= ix < s + len -> length (g ix) = length vi_ini) ->
                    skip_sum_of_vs skip s len g k = Some v ->
                    length v = length vi_ini.
                  Proof.
                    revert s v; induction len; simpl; intros; try congruence.
                    destruct (skip_sum_of_vs skip (S s0) len g k) eqn:Heq.
                    - forwards: (>>IHlen Heq); [intros; apply H; omega|..].
                      destruct Nat.eq_dec; inverts H0; eauto.
                      rewrite (f_den_wf l0 (g s0)); try congruence.
                      rewrite H; eauto; try omega.
                      forwards: (f_fun_den l0 (g s0)); try congruence.
                      rewrite H; eauto; try omega.
                    - destruct Nat.eq_dec; unfold op' in H0; simpl in H0; inverts H0.
                      rewrite H; eauto; try omega.
                  Qed.                    
                  destruct (skip_sum_of_vs nt_gr 0 (min (xix nl) l) g gid) eqn:Heq; eauto.
                  forwards : (>>skip_sum_of_vs_wf Heq); try congruence; eauto.
                  intros; erewrite get_den_wf; eauto.
                  apply Hg; try nia.
                  rewrite length_nseq; eauto.
                - apply not_in_disjoint; simplify; forwards: func_local; eauto; simpl in *; congruence.
                - apply not_in_disjoint; simplify; forwards: func_local; eauto; simpl in *; congruence.
                - prove_inde; simplify; try (forwards*: func_local; simpl in *; congruence).
                  apply inde_input_spec; simplify;
                    forwards*: func_local; simplify; simpl in *; congruence. }
              eapply rule_seq.
              { apply rule_frame; [apply read_tup_correct|]; eauto using locals_disjoint_ls.
                - simplify; forwards*: func_res_fv; simpl in *; simplify; congruence.
                - unfold maybe; destruct (skip_sum_of_vs nt_gr 0 (min (xix nl) l) g gid) eqn:Heq; eauto.
                  forwards : (>>skip_sum_of_vs_wf Heq); try congruence; eauto.
                  intros; erewrite get_den_wf; eauto.
                  apply Hg; try nia.
                  rewrite func_wf; forwards*: (f_fun_den l0 (g (xix nl))); try congruence.
                  forwards*: (f_den_wf l0 (g (xix nl))); congruence.
                  lets: (>>length_nseq dim 0%Z); eauto.
                  rewrite func_wf; forwards*: (f_fun_den (nseq dim 0%Z) (g (xix nl))); try congruence.
                - rewrite func_wf, locals_length; eauto.
                - rewrite read_tup_writes.
                  prove_inde; simplify; try now (simplify; simpl in *; congruence).
                  
                  apply inde_input_spec; intros; simplify; simpl; congruence.
                  rewrite locals_length, func_wf; eauto. }

              eapply rule_seq. 
              { eapply Hbackward.
                Focus 2. {
                  intros stk h H; sep_split_in H.
                  clear HP6.
                  evar (P : assn);
                  assert (Hnxt : ((!(vars2es z ==t
                     maybe (skip_sum_of_vs nt_gr 0 (min (xix nl) l) g gid) (nseq dim 0%Z) |+|
                       g (xix nl)) **
                     P) stk h))
                  by (unfold P; sep_normal; sep_split; auto; sep_combine_in H; eauto).
                  unfold P in *; apply Hnxt. } Unfocus.
                eapply rule_frame; [apply read_tup_correct|].

                - simplify; try congruence.
                - apply locals_disjoint_ls.
                - unfold vars2es; rewrite map_length, locals_length.
                  unfold maybe.
                  unfold maybe; destruct (skip_sum_of_vs nt_gr 0 (min (xix nl) l) g gid) eqn:Heq; eauto.
                  forwards : (>>skip_sum_of_vs_wf Heq); try congruence; eauto.

                  intros; erewrite get_den_wf; eauto.
                  apply Hg; try nia.
                  forwards*: (f_fun_den l0 (g (xix nl))); try congruence.
                  forwards*: (f_den_wf l0 (g (xix nl))); congruence.
                  forwards*: (>>length_nseq dim 0%Z).
                  forwards*: (f_den_wf (nseq dim 0%Z) (g (xix nl))); congruence. 
                - unfold vars2es; rewrite map_length, !locals_length; eauto.
                - rewrite read_tup_writes.
                  prove_inde; simplify; try (simpl in *; congruence).
                  apply inde_input_spec; intros; simplify; simpl; try congruence.
                  unfold vars2es; rewrite map_length, !locals_length; eauto. }
              hoare_forward.
              intros s h [nix H]; subA_normalize_in H with (fun H => first
            [ apply subA_distribute_tup in H | apply subA_eq_tup in H
              | apply subA_is_tuple_p in H | apply subA_input_spec in H; eauto ] ).
              autorewrite with core in H; simpl in *; try congruence.
              sep_normal_in H; sep_split_in H.
              unfold inv; exists (S nl); sep_split; try now (unfold_conn_all; simpl in *; eauto; nia);
                try now (unfold lt in *; repeat sep_split).
              equates 3; eauto.
              lets Heq: (>>skip_sum_sum0 f_fun nt_gr gid (S nl)); eauto.
              assert (nt_gr <> 0) by (apply Nat.neq_mul_0; eauto).
              rewrite (Heq (min (xix (S nl)) l)) at 1; eauto; clear Heq.
              2: unfold_conn_in HP6; lets [? | ?]: (Nat.min_spec (xix (S nl)) l); split; try nia.
              
              lets Heq: (>>skip_sum_sum0 f_fun nt_gr gid nl); eauto.
              assert (nt_gr <> 0) by (apply Nat.neq_mul_0; eauto).
              rewrite (Heq (min (xix nl) l)) at 1; eauto; clear Heq.
              2: unfold_conn_in HP6; lets [? | ?]: (Nat.min_spec (xix nl) l); split; try nia.

              cutrewrite (S nl = nl + 1); [|ring].
              erewrite sum_of_concat; simpl; eauto.
                  
              lets Heq: (>>skip_sum_sum0 f_fun nt_gr gid nl); eauto.
              assert (nt_gr <> 0) by (apply Nat.neq_mul_0; eauto).
              rewrite <-plus_n_O.
              unfold maybe.
              destruct nl; unfold_pures; try omega; simpl.
              destruct (sum_of_vs 1 nl (fun j => g (gid + j * nt_gr))); simpl.
              do 2 f_equal; ring.
              do 2 f_equal; ring.

              apply scC in H; apply H.
              
            - unfold inv.
              intros stk h H; sep_normal_in H; sep_split_in H.
              exists 1; sep_split; eauto; try now (unfold_conn_all; simpl in *; nia).
              unfold maybe;
                lazymatch goal with [|- context [match ?X with Some _ => _ | None => _ end]] =>
                cutrewrite (X = Some (g gid)); eauto
              end.
              rewrites (>>skip_sum_sum0 1); eauto; simpl.
              lets* [? | ?]  : (>>Min.min_spec (ntrd + 0 + gid) l);
                lets* :ntgr_gid; try nia.
              do 2 f_equal; try omega.
              repeat sep_cancel.
              Lemma vs2es_nseq d v : vs2es (nseq d v) = nseq d (Enum v).
              Proof.
                induction d; simpl; congruence.
              Qed.
              rewrite vs2es_nseq; repeat sep_cancel.
            - unfold inv.
              eapply Hbackward.
              Focus 2. {
                intros stk h H; apply ex_lift_l_in in H; destruct H as [nl H].
                sep_normal_in H; sep_split_in H.
                rewrite min_r in HP4; [|unfold_pures; unfold_conn_all; simpl in *; nia].
                (* assert (Heq : (Zn (nf i) === tid) stk h) by (unfold_conn_all; simpl in *; eauto). *)
                (* sep_rewrite_in mps_eq1_tup' H; [|exact Heq]. *)
                evar (P : assn); assert (Hnxt : (sdata' +ol tid -->l (1, vs2es (nseq dim 0%Z)) ** P) stk h).
                { unfold P; sep_cancel.
                  assert (pure (gid < l) stk (emp_ph loc)) by eauto.
                  clear HP HP3 HP5; sep_combine_in H0; apply H0. }
                apply Hnxt. } Unfocus.
              apply rule_frame; [apply gen_write_correct|]; simplify; eauto.
              rewrite !length_nseq; auto.
              rewrite writes_var_gen_write; apply inde_nil. } 
        - (* eapply Hforward; [apply rule_disj; hoare_forward; *)
          (*   intros s h [v H]; subA_normalize_in H with (fun H => first *)
          (*   [ apply subA_distribute_tup in H | apply subA_eq_tup in H *)
          (*     | apply subA_is_tuple_p in H | apply subA_input_spec in H; eauto ] )|]. *)
          (* autorewrite with core in *; eauto. simpl in H. exact H. *)
          (* autorewrite with core in *; eauto. simpl in H. exact H. *)
          intros stk h [H|H]; sep_normal_in H; sep_split_in H.
          Lemma skip_sum_of_small s sk len f k :
            k < sk ->
            skip_sum_of_vs sk s len f k = None ->
            forall j : nat, j < len -> (s + j) mod sk <> k.
          Proof.
            revert s; induction len; simpl; intros; try omega.
            destruct Nat.eq_dec; simpl in *; try omega.
            - unfold op' in *; destruct skip_sum_of_vs; congruence.
            - destruct j0; [ rewrite <- plus_n_O; eauto |].
              cutrewrite (s0 + S j0 = S s0 + j0); [|ring].
              apply IHlen; try omega; eauto.
          Qed.

          Lemma skip_sum_of_nil sk len f k :
            sk <> 0 ->
            k < sk -> skip_sum_of_vs sk 0 len f k = None -> len <= k.
          Proof.
            intros; lets*: (>>skip_sum_of_small 0 sk len f k __ __); eauto.
            cut (~(len > k)); try omega; intros Hc; simpl in *.
            assert (k mod sk = k) by (apply Nat.mod_small; omega).
            forwards* : (>>H2 k); try omega.
          Qed.
          + unfold vi; destruct (skip_sum_of_vs nt_gr 0 l g (nf i + nf j * ntrd)) eqn:Heq.
            * sep_rewrite_in mps_eq2_tup H; [|exact HP2].
              sep_rewrite_in mps_eq1_tup' H; [|exact HP].
              sep_split; eauto.
              (* unfold_pures; unfold_conn_all; simpl in *. *)
              (* congruence. *)
            * sep_rewrite_in mps_eq2_tup H; [|exact HP2].
              sep_rewrite_in mps_eq1_tup' H; [|exact HP].
              sep_split; eauto.
              (* unfold_pures; unfold_conn_all; simpl in *. *)
              (* congruence. *)
              (* apply skip_sum_of_nil in Heq; eauto. *)
              (* unfold_conn_in HP3; try omega. *)
              (* nia. *)
          + unfold vi.
            rewrites (>>skip_sum_opt_nil g l).
            unfold_pures; unfold_conn_all; simpl in *; intros;
              rewrite Nat.mod_small; lets: ntgr_gid; try nia.
            rewrite minus_diag; simpl; sep_split; eauto.
            (* unfold_pures; unfold_conn_all; simpl in *. *)
            (* congruence. *)
            assert (Heq : (Zn (nf i) === tid) stk h) by (unfold_conn_all; simpl in *; eauto).
            sep_rewrite mps_eq1_tup'; [|exact Heq].
            rewrite vs2es_nseq; sep_cancel.
            Grab Existential Variables.
            apply (fun _ => nil).
      Qed.

  Notation t := (locals "w" dim).

(* seq_reduce_correct: *)
(*   forall (BS : nat -> Vector.t assn ntrd * Vector.t assn ntrd) (g : nat -> list val), *)
(*   (forall i : nat, i < l -> get_den (Zn i) (g i)) -> *)
(*   CSL BS i *)
(*     (!(tid === Zn (` (Fin.to_nat i))) ** *)
(*      !(bid === Zn (` (Fin.to_nat j))) ** *)
(*      !(sh === Zn l) ** (sdata' +ol Zn (` (Fin.to_nat i)) -->l (1, vs2es vi_ini)) ** input_spec env env_den (perm_n nt_gr))  *)
(*     (seq_reduce (inv g)) *)
(*     (!(tid === Zn (` (Fin.to_nat i))) ** *)
(*      !(len === Z.min (Zn l - Zn (` (Fin.to_nat j)) * Zn ntrd) (Zn ntrd)) ** *)
(*      !(vars2es y ==t vi g (nseq dim 0%Z)) ** *)
(*      (sdata' +ol Zn (` (Fin.to_nat i)) -->l (1, vs2es (vi g (nseq dim 0%Z)))) ** input_spec env env_den (perm_n nt_gr) ** !(sh === Zn l)) *)
(* f_in i := vi g (nseq dim 0%Z) *)

(* reduce_ok0: *)
(*   forall (l : nat) (f_in : nat -> list val), *)
(*   (forall i : nat, Datatypes.length (f_in i) = dim) -> *)
(*   ntrd <= 2 ^ e_b -> *)
(*   l <= ntrd -> *)
(*   e_b <> 0 -> *)
(*   forall i : Fin.t ntrd, *)
(*   CSL (BS l f_in) i *)
(*     (!(tid === Zn (` (Fin.to_nat i))) ** *)
(*      !(len === Zn l) ** !(vars2es y ==t f_in (` (Fin.to_nat i))) ** (sdata' +ol Zn (` (Fin.to_nat i)) -->l (1, vs2es (f_in (` (Fin.to_nat i)))))) *)
(*     reduce *)
(*     (!(tid === Zn (` (Fin.to_nat i))) ** *)
(*      !(len === Zn l) ** *)
(*      !(vars2es y ==t f l f_in e_b (` (Fin.to_nat i))) ** *)
(*      (if Nat.eq_dec (` (Fin.to_nat i)) 0 then is_tuple_array_p sdata' ntrd (f l f_in e_b) 0 1 else emp)) *)


  Definition setToLen :=
    Cif (sh <C bid *C Zn ntrd) (
      len ::= 0%Z 
    ) (
      Cif (sh <C (bid +C 1%Z) *C Zn ntrd) (
         len ::= sh -C bid *C Zn ntrd 
      ) (
         len ::= Zn ntrd
      )
    ).

  Lemma setToLen_correct BS :
    CSL BS i
         (!(bid === Zn (nf j)) ** !(sh === Zn l))
         setToLen
         (!(bid === Zn (nf j)) ** !(sh === Zn l) ** !(len === Zn (min (l - nf j * ntrd) ntrd))).
  Proof.
    unfold setToLen.
    repeat (first [eapply rule_seq; [|hoare_forward; eauto] | hoare_forward; eauto]).
    intros s h [[v H]|[[v H]|[v H]]]; subA_normalize_in H.
    - simpl in *; sep_split; sep_split_in H; unfold_pures; eauto.
      rewrite Nat.min_l; try nia.
      rewrite not_le_minus_0; try nia; eauto.
    - simpl in *; sep_split; sep_split_in H; unfold_pures; eauto.
      rewrite Nat.min_l; try nia.
      unfold_conn; simpl; nia.
    - simpl in *; sep_split; sep_split_in H; unfold_pures; eauto.
      rewrite Nat.min_r; try nia.
      unfold_conn; simpl; eauto.
  Qed.
  
  Definition mkFoldAll :=
    seq_reduce FalseP ;;
    setToLen ;;
    reduce ;;
    Cif (tid == 0%Z) (
      gen_read Sh t sdata 0%Z ;;
      catcmd (gen_write Gl (vars2es Outs) bid (vars2es t))
    ) Cskip.

  Definition f_seq g j i := maybe (skip_sum_of_vs nt_gr 0 l g (i + j * ntrd)) (nseq dim 0%Z).

  Definition BS' g := BS (Nat.min (l - nf j * ntrd) ntrd) (f_seq g (nf j)).

  Definition sh_decl := map (fun sv => (sv, ntrd)) (locals "sdata" dim).

  Theorem reduce_ok_th g :
    (forall i, i < l -> get_den (Zn i) (g i)) ->
    CSL (BS' g) i
     (!(tid === Zn (nf i)) ** !(bid === Zn (nf j)) ** !(sh === Zn l) ** !(Outs' ==t out) **
      (sdata' +ol Zn (nf i) -->l (1, vs2es vi_ini)) **
      input_spec env env_den (perm_n nt_gr) **
      if Nat.eq_dec (nf i) 0 then map Gl Outs' +ol Zn (nf j) -->l (1, vs2es (fout (nf j))) else emp)
        
     mkFoldAll
     
     ((if Nat.eq_dec (nf i) 0 then sh_spec sh_decl else emp) **
      (if Nat.eq_dec (nf i) 0 then
         map Gl (vs2es out) +ol Zn (nf j) -->l
             (1, vs2es (f (Nat.min (l - nf j * ntrd) ntrd) (f_seq g (nf j)) e_b 0))
       else emp) **
      input_spec' env_den (perm_n nt_gr)).
  Proof.
    intros Hg.
    eapply rule_seq.
    { eapply Hbackward.
      Focus 2. {
        intros s h H.
        evar (P : assn);
          assert (((!(tid === Zn (nf i)) **
                    !(bid === Zn (nf j)) **
                    !(sh === Zn l) **
                    (sdata' +ol Zn (` (Fin.to_nat i)) -->l (1, vs2es vi_ini)) **
                    input_spec env env_den (perm_n nt_gr)) ** P) s h).
        { sep_normal; sep_split_in H; sep_split; eauto; repeat sep_cancel.
          unfold P; sep_combine_in H1; eauto. }
        unfold P in *; eauto. } Unfocus.
      eapply rule_frame; [apply seq_reduce_correct; eauto |].
      unfold seq_reduce; simpl.
      repeat prove_inde; try apply inde_is_tup;
        rewrite !read_tup_writes, !writes_var_gen_write; eauto;
          repeat (
              simplify;
              try rewrite !map_length; try rewrite !locals_length; try rewrite !length_nseq;
              try rewrite !func_wf; try rewrite !get_wf); eauto; try congruence;
            (try now (forwards *: (>>get_wr); simpl in *; congruence));
            (try now (forwards *: (>>func_local); simpl in *; congruence));
      try (rewrite Forall_forall); intros;
      unfold Outs in *; intros; simplify; simpl in *;
        (try now (forwards *: (>>get_wr); simpl in *; congruence));
        (try now (forwards *: (>>func_local); simpl in *; congruence)). }
    
    eapply rule_seq.
    { eapply Hbackward.
      Focus 2. {
        intros s h H.
        evar (P : assn);
          assert (((!(bid === Zn (nf j)) ** !(sh === Zn l)) ** P) s h).
        { sep_normal; repeat sep_cancel; unfold P; eauto. }
        unfold P in *; eauto. } Unfocus.
      apply rule_frame; [apply setToLen_correct|].
      unfold setToLen; simpl; prove_inde; unfold Outs; simplify; try congruence.
      apply inde_input_spec; simplify; simpl; congruence. } 
    
    eapply rule_seq.
    { eapply Hbackward.
      Focus 2. {
        intros s h H.
        evar (P : assn);
          assert (((!(tid === Zn (nf i)) **
                    !(len === Zn (min (l - nf j * ntrd) ntrd)) **
                    !(vars2es y ==t vi g (nseq dim 0%Z)) **
                    (sdata' +ol Zn (` (Fin.to_nat i)) -->l (1, vs2es (vi g (nseq dim 0%Z))))) ** P)
                  s h).
        { sep_normal; sep_normal_in H; repeat sep_cancel; unfold P; eauto. }
        unfold P in *; eauto. } Unfocus.
      eapply rule_frame; [apply reduce_ok0; eauto|].
      { apply Min.le_min_r. }
      { unfold f_seq, maybe.
        intros; destruct (skip_sum_of_vs _ _ _ _ _) eqn:H.
        - erewrite skip_sum_of_vs_wf; eauto.
          intros ix ?; forwards * : (>>get_den_wf (Zn ix)); rewrite vi_ini_wf.
          congruence.
        - rewrite length_nseq; eauto. }
      { Lemma reduce_writes n m w :
          In w (writes_var (reduce_aux n m)) ->
          (In w (if Nat.eq_dec m 0 then nil else (x ++ y ++ z)%list) \/
           prefix "l" (var_of_str w) = true).
        Proof.
          revert n; induction m; simpl; eauto.
          intros n; rewrite !gen_read_writes; [|unfold vars2es; rewrite map_length, !locals_length; auto].
          rewrite !read_tup_writes;
            try (unfold vars2es; rewrite map_length, !locals_length; auto).
          rewrite !writes_var_gen_write.
          2: rewrite func_wf, locals_length; auto.
          rewrite !in_app_iff.
          lets: (func_local y x w).
          generalize dependent IHm; generalize dependent H; clear; intros; simpl; intuition.
          apply IHm in H1; destruct m; simpl in *; intuition.
          rewrite !in_app_iff in H0; eauto.
        Qed.
        prove_inde; simplify;
          try now (forwards * : reduce_writes; destruct e_b; try omega; simpl in *;
                   simplify; try congruence).
        apply inde_input_spec; intros; forwards * : reduce_writes; destruct e_b; 
          try omega; simpl in *; simplify; simpl; try congruence.
        unfold Outs in *.
        forwards * : reduce_writes; destruct e_b; 
          try omega; simpl in *; simplify; simpl; try congruence.
        unfold Outs in *; forwards * : reduce_writes; destruct e_b; 
          try omega; simpl in *; simplify; simpl; try congruence. } }
    hoare_forward; eauto using rule_skip.
    { eapply rule_seq.
      { eapply Hbackward.
        Focus 2.
        { intros s h H.
          sep_normal_in H; sep_split_in H.
          change_in H.
          { destruct Nat.eq_dec; [|clear HP6; unfold_pures; try omega].
            sep_rewrite_in (is_array_tup_unfold sdata' 0) H; try omega.
            Focus 2. {
              intros; unfold vars2es; rewrite f_length, !map_length, locals_length; eauto.
              intros; unfold f_seq.
              unfold maybe; destruct (skip_sum_of_vs _ _ _ _ _) eqn:Heq.
              - erewrite skip_sum_of_vs_wf; eauto.
                intros ix ?; forwards * : (>>get_den_wf (Zn ix)); rewrite vi_ini_wf.
                congruence.
              - rewrite length_nseq; auto. } Unfocus.
            simpl in H.

            eauto. }
          clear  HP0 HP1 HP3 HP4 HP5; sep_combine_in H.
          evar (P : assn);
            assert (((sdata' +ol 0%Z -->l (1, vs2es (f (min (l - nf j * ntrd) ntrd) (f_seq g (nf j)) e_b 0))) ** P) s h). 
          { sep_normal_in H; sep_cancel; unfold P; eauto. }
          unfold P in *; eauto. } Unfocus.
        
        apply rule_frame; [apply gen_read_correct; eauto|].
        - intros; simplify; congruence.
        - apply locals_disjoint_ls.
        - unfold vars2es; rewrite map_length, !locals_length; eauto.
        - rewrite locals_length, f_length; eauto.
          unfold f_seq, maybe; intros; destruct (skip_sum_of_vs _ _ _ _ _) eqn:Heq.
          + erewrite skip_sum_of_vs_wf; eauto.
            intros ix ?; forwards * : (>>get_den_wf (Zn ix)); rewrite vi_ini_wf.
            congruence.
          + rewrite length_nseq; auto. 
        - rewrite gen_read_writes; [|unfold vars2es; rewrite map_length, !locals_length; eauto].
          unfold Outs in *; prove_inde; simplify; simpl in *; try congruence.
          apply inde_input_spec; simplify; simpl; congruence. }
      
      { eapply Hbackward.
        Focus 2. {

          Fixpoint eq_tup_loc (es : list loc_exp) (es' : list loc_exp) : assn :=
            match es with
            | nil => match es' with
                     | nil => emp
                     | _ :: _ => FalseP
                     end
            | e :: es0 => match es' with
                          | nil => FalseP
                          | e' :: es0' => !(e ===l e') ** eq_tup_loc es0 es0'
                          end
            end.

          Lemma eq_tup_loc_nth (es es' : list loc_exp) s :
            length es = length es' ->
            (forall i, i < length es -> (nth i es (Sh 0%Z) ===l nth i es' (Sh 0%Z)) s (emp_ph loc)) ->
            (eq_tup_loc es es') s (emp_ph loc).
          Proof.
            revert es'; induction es; simpl; intros [|e' es'] H H'; simpl in *; try omega.
            - apply emp_emp_ph.
            - sep_split.
              + forwards: (>>H' 0); eauto; omega.
              + apply IHes; try omega.
                intros i' ?; forwards: (H' (S i')); eauto; omega.
          Qed.
            
          Lemma mps_eq1_tup (E1 : list loc_exp) (E1' : list loc_exp) (E2 : list exp) (p : Qc) (s : stack) :
            (eq_tup_loc E1 E1') s (emp_ph loc) ->
            s ||= is_tuple_p E1 E2 p <=>
                  is_tuple_p E1' E2 p.
          Proof.
            revert E1' E2; induction E1; intros [|e1' E1'] [|e2 E2] Heq; simpl in *; try reflexivity;
              try now destruct Heq.
            sep_split_in Heq.
            Lemma ls_idx l1 l2 e s h : (l1 ===l l2) s h -> (l1 +o e ===l l2 +o e) s h.
            Proof.
              revert l2 e; induction l1; simpl; intros [?|?|?] e' H;
                unfold_conn_all; simpl in *; inverts H; try congruence;
              rewrite H1; eauto.
            Qed.
            rewrite mps_eq1; eauto.
            rewrite IHE1; try reflexivity; eauto.
          Qed.

          intros s h H.
          assert (Heq : (Zn (nf j) === bid) s (emp_ph loc)).
          { sep_split_in H; unfold_pures; unfold_conn; simpl; congruence. }
          sep_lift_in H 8.
          sep_rewrite_in mps_eq1_tup' H; [|exact Heq].

          evar (P : assn);
          assert (((map Gl Outs' +ol bid -->l (1, vs2es (fout (` (Fin.to_nat j))))) ** P) s h).
          { sep_cancel; unfold P; eauto. }
          unfold P in *; eauto. } Unfocus.
        apply rule_frame; [apply gen_write_correct|].
        { unfold vs2es, vars2es, Outs; rewrite !map_length, fout_wf, locals_length; auto. }
        { unfold vs2es, vars2es, Outs; rewrite !map_length, !locals_length; auto. }
        rewrite writes_var_gen_write; apply inde_nil. } }
    intros s h [H | H]; sep_normal_in H; sep_split_in H; unfold_pures.
    - destruct Nat.eq_dec; [|clear HP2; unfold_pures; omega].
      assert (Heq : (bid === Zn (nf j)) s (emp_ph loc)) by (unfold_conn; simpl; eauto).
      sep_rewrite_in mps_eq1_tup' H; [|exact Heq]; clear Heq.
      sep_rewrite_in mps_eq2_tup H; [|exact HP].

      Lemma sh_spec_is_tup_array d n sh stk:
        stk ||= sh_spec (map (fun sv => (sv, n)) (locals sh d)) <=>
            Ex f, (is_tuple_array_p (map Sh (vars2es (locals sh d))) n f 0 1).
      Proof.
        induction d; simpl; eauto.
        - split; intros.
          + exists (fun _ : nat => @nil val); sep_split; unfold_conn; eauto.
          + destruct H; sep_split_in H; eauto.
        - simpl; rewrite IHd; split; intros H.
          + apply ex_lift_l_in in H as [f0 H].
            apply ex_lift_r_in in H as [f1 H].
            exists (fun x => f0 x :: f1 x); simpl.
            revert H; apply scRw; intros s h' H'; eauto.
            apply is_array_p1; eauto.
          + destruct H as [f H].
            sep_split_in H.
            apply ex_lift_l; exists (fun x => hd 0%Z (f x)).
            apply scC, ex_lift_l; exists (fun x => tl (f x)).
            apply scC; revert H; apply scRw; intros s h' H'; eauto.
            apply is_array_p1 in H'; eauto.
      Qed.

      Lemma sh_spec_is_tup_array_with_l d n sh stk:
        stk ||= sh_spec (map (fun sv => (sv, n)) (locals sh d)) <=>
            Ex f, (is_tuple_array_p (map Sh (vars2es (locals sh d))) n f 0 1 **
                   !(pure (forall i, length (f i) = d))).
      Proof.
        induction d; simpl; eauto.
        - split; intros.
          + exists (fun _ : nat => @nil val); sep_split; unfold_conn; eauto.
          + destruct H; sep_split_in H; eauto.
        - simpl; rewrite IHd; split; intros H.
          + apply ex_lift_l_in in H as [f0 H].
            apply ex_lift_r_in in H as [f1 H].
            exists (fun x => f0 x :: f1 x); simpl.
            sep_split; [|revert H; apply scRw; intros s h' H'; eauto].
            2: apply is_array_p1; eauto.
            sep_split_in H; unfold_conn_all; intros; rewrite HP; congruence.
            sep_split_in H'; auto.
          + destruct H as [f H].
            sep_split_in H.
            apply ex_lift_l; exists (fun x => hd 0%Z (f x)).
            apply scC, ex_lift_l; exists (fun x => tl (f x)).
            apply scC; revert H; apply scRw; intros s h' H'; eauto.
            apply is_array_p1 in H'; eauto.
            sep_split; eauto.
            unfold_conn_all; simpl; intros.
            lets: (HP i0); destruct (f i0); simpl in *; try omega.
      Qed.
      unfold sh_decl; sep_rewrite sh_spec_is_tup_array.
      apply ex_lift_l; exists (f (min (l - nf j * ntrd) ntrd) (f_seq g (nf j)) e_b).
      sep_rewrite (is_array_tup_unfold sdata' 0); try omega; simpl.
      Focus 2. {
        intros; unfold vars2es; rewrite f_length, !map_length, locals_length; eauto.
        intros; unfold f_seq.
        unfold maybe; destruct (skip_sum_of_vs _ _ _ _ _) eqn:Heq.
        - erewrite skip_sum_of_vs_wf; eauto.
          intros ix ?; forwards * : (>>get_den_wf (Zn ix)); rewrite vi_ini_wf.
          congruence.
        - rewrite length_nseq; auto. } Unfocus.
      sep_normal; repeat sep_cancel.
      revert H2; apply scRw_stack; eauto; intros.
      lets Heq : (Skel_lemma.mps_eq1_tup Outs' out); unfold es2gls in Heq; eauto.
      sep_rewrite_in Heq H2; eauto.
      (* sep_rewrite_in mps_eq1_tup *)
      eapply input_spec_forget; eauto.
    - destruct Nat.eq_dec; [clear HP6; unfold_pures; omega|].
      repeat sep_rewrite emp_unit_l.
      sep_rewrite_in emp_unit_l H; sep_rewrite_in emp_unit_r H.
      eapply input_spec_forget; eauto.
      Grab Existential Variables.
      (* too ugly.. *)
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
  Qed.
  End SeqReduce.

  Definition bth_pre (j : Fin.t nblk) :=
    !(sh === Zn l) ** !(Outs' ==t out) **
    conj_xs (ls_init 0 ntrd (fun i => input_spec env env_den (perm_n nt_gr))) **
    (map Gl Outs' +ol Zn (nf j) -->l (1, vs2es (fout (nf j)))).

  Definition tr_pres (j : Fin.t nblk) := MyVector.init (fun i : Fin.t ntrd =>
    Ex vi_ini, 
      !(bid === Zn (nf j)) ** !(sh === Zn l) ** !(Outs' ==t out) ** !(pure (length vi_ini = dim)) **
      (sdata' +ol Zn (nf i) -->l (1, vs2es vi_ini)) **
      input_spec env env_den (perm_n nt_gr) **
      if Nat.eq_dec (nf i) 0 then map Gl Outs' +ol Zn (nf j) -->l (1, vs2es (fout (nf j))) else emp).

  Definition tr_posts g (j : Fin.t nblk) := MyVector.init (fun i : Fin.t ntrd =>
    input_spec' env_den (perm_n nt_gr) **
    (if Nat.eq_dec (nf i) 0 then sh_spec sh_decl else emp) **
    (if Nat.eq_dec (nf i) 0 then
       map Gl (vs2es out) +ol Zn (nf j) -->l
           (1, vs2es (f (Nat.min (l - nf j * ntrd) ntrd) (f_seq g (nf j)) e_b 0))
     else emp)).

  Definition bth_post g (j : Fin.t nblk) := 
    (map Gl (vs2es out) +ol Zn (nf j) -->l
        (1, vs2es (f (Nat.min (l - nf j * ntrd) ntrd) (f_seq g (nf j)) e_b 0))) **
    conj_xs (ls_init 0 ntrd (fun i => input_spec' env_den (perm_n nt_gr))).

  Definition E (t : var) :=
    if var_eq_dec t (Var "bid") then Lo
    else if var_eq_dec t (Var "sh") then Lo
    else if prefix "sdata" (var_of_str t) then Lo
    else if prefix "Out" (var_of_str t) then Lo
    else if prefix "sh" (var_of_str t) then Lo
    else if prefix "arr" (var_of_str t) then Lo
    else Hi.

  Lemma read_tup_no_bars xs es : barriers (read_tup xs es) = nil.
  Proof.
    revert es; induction xs; destruct es; simpl; eauto.
  Qed.

  Ltac env_dec :=
    repeat lazymatch goal with
      | [|- context [prefix ?X ?Y]] => destruct (prefix X Y) eqn:?
      | [|- context [var_eq_dec ?X ?Y]] => destruct (var_eq_dec X Y) eqn:?
      end.
    
  Lemma reduce_aux_Lo a b : typing_cmd E (reduce_aux a b) Lo.
  Proof.
    revert a; induction b; simpl; constructor; eauto.
    unfold E, reduce_body.
    constructor; [constructor|].
    repeat econstructor; repeat instantiate (1 := Hi); eauto; unfold join;
      apply typing_cmd_Hi; try rewrite read_tup_no_bars; try rewrite gen_read_no_bars;
        try rewrite gen_write_no_bars; auto;
          try rewrite read_tup_writes; try rewrite writes_var_gen_write;
            try rewrite gen_read_writes; try destruct var_eq_dec; subst;
              intros; repeat destruct var_eq_dec; substs; simpl in *; try congruence; eauto;
                (try now (forwards*: locals_pref; simpl in *; congruence));
                (try now (forwards * : func_local; simpl in *; congruence));
                (try now (unfold vars2es; repeat rewrite map_length; repeat rewrite locals_length;
                         repeat rewrite get_wf; repeat rewrite func_wf; eauto));
                env_dec; eauto; simplify; simpl; try congruence;
    forwards* : func_local; simpl in *; congruence.
    Grab Existential Variables.
    apply (Var "").
    apply 1.
    apply "".
    apply (Var "").
    apply 1.
    apply "".
    apply (Var "").
    apply 1.
    apply "".
  Qed.
 
  Lemma fold_has_type : typing_cmd E mkFoldAll Lo.
  Proof.
    unfold mkFoldAll, seq_reduce, reduce, setToLen, E.
    repeat constructor.
    - eapply weaken_type; try apply read_tup_hi; eauto.
      intros; env_dec; simplify; try congruence.
    - eapply weaken_type; try apply typing_cmd_Hi; eauto.
      + apply gen_write_no_bars.
      + intros; rewrite writes_var_gen_write in H; simpl in *; tauto.
    - econstructor; repeat constructor; simpl.
      instantiate (1 := Hi); eauto.
      repeat instantiate (1 := Hi); eauto.
    - eapply weaken_type; try apply typing_cmd_Hi; eauto; simpl.
      + rewrite get_no_bar, func_no_bars, !read_tup_no_bars, gen_write_no_bars; eauto.
      + rewrite !read_tup_writes;
        try now (unfold vars2es; repeat rewrite map_length; repeat rewrite locals_length;
                 repeat rewrite get_wf; repeat rewrite func_wf; eauto).
        rewrite !writes_var_gen_write;
        intros; env_dec; substs;
        repeat (rewrite in_app_iff in H; simpl in H);
        simplify; try congruence;
        (try now (forwards*: get_wr; eauto; simplify; simpl in *; congruence));
        (try now (forwards*: func_local; eauto; simplify; simpl in *; congruence)).
    - eapply weaken_type; try apply typing_cmd_Hi; simpl; eauto.
      intros; simplify; eauto; destruct var_eq_dec; congruence.
    - apply reduce_aux_Lo.
    - applys (>>weaken_type Hi); eauto.
      apply typing_cmd_Hi; simpl; eauto.
      rewrite gen_read_no_bars, gen_write_no_bars; auto.
      rewrite gen_read_writes, writes_var_gen_write; simpl.
      intros; repeat rewrite in_app_iff in H;
        env_dec; substs; simplify; congruence.
      unfold vars2es; rewrite map_length, !locals_length; auto.
      Grab Existential Variables.
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
      apply (Var "").
  Qed.

  Lemma prefix_nil s : prefix "" s = true. destruct s; eauto. Qed.
  Notation skip_sum_of_vs := (skip_sum_of_opt (list val) f_fun).

  Lemma reduce_ok_bl g (j : Fin.t nblk) :
    (forall i, i < l -> get_den (Zn i) (g i)) ->
    CSLp ntrd E
         (!(bid === Zn (nf j)) ** sh_spec sh_decl ** bth_pre j)
         mkFoldAll 
         (sh_spec sh_decl ** bth_post g j).
  Proof.
    intros Hg.
    applys (>> rule_par (BS' j g) (tr_pres j) (tr_posts g j)).
    - destruct ntrd; try omega; eexists; eauto.
    - intros; split; intros;
      unfold BS', BS, BSpre, BSpost, Binv, E, CSL.low_assn; simpl;
      rewrite MyVector.init_spec; simpl;
      destruct i; repeat prove_low_assn;
        (try now (first [apply low_assn_is_tuple|apply low_assn_is_tup_arr]; simplify; repeat econstructor;
                  cutrewrite (Lo = join Lo Lo); [|auto]; repeat econstructor; simpl;
                  rewrite prefix_nil; auto)).
    - unfold BS'; intros; apply BS_ok; eauto.
      rewrite Nat.le_min_r; auto.
      intros; unfold f_seq, maybe; destruct (skip_sum_of_vs _ _ _ _ _) eqn:Heq.
      + erewrite skip_sum_of_vs_wf; eauto.
        intros ix ?; forwards * : (>>get_den_wf (Zn ix)); rewrite out_wf.
        congruence.
      + rewrite length_nseq; auto.
    - Lemma precise_pts : forall (e1 : loc_exp) (e2 : exp) (q : Qc), precise (e1 -->p (q,  e2)).
      Proof.
        intros; unfold precise; simpl; intros; unfold_conn_all.
        destruct h1, h1'; apply pheap_eq; extensionality x; simpl in *.
        rewrite H, H0; destruct (eq_dec _ _); eauto.
      Qed.

      Lemma is_tup_precise E q v : precise (E -->l (q, v)).
      Proof.
        revert v; induction E; simpl; destruct v; eauto using precise_emp.
        apply precise_star; eauto using precise_pts.
      Qed.
      
      Lemma precise_is_array_p e len s f' p : precise (is_array_p e len f' s p).
      Proof.
        revert s; induction len; simpl; intros; eauto using precise_emp, precise_star, precise_pts.
      Qed.  

      Lemma is_tup_arr_precise E len f s q  : precise (is_tuple_array_p E len f s q).
      Proof.
        revert f; induction E; simpl; eauto using precise_emp.
        intros f; eauto using precise_star, precise_is_array_p.
      Qed.
        
      split; unfold BS', BS, BSpre, BSpost, Binv; simpl; rewrite MyVector.init_spec;
        destruct i; repeat destruct Sumbool.sumbool_and; repeat destruct Nat.eq_dec;
      repeat apply precise_star; eauto using precise_emp, is_tup_precise, is_tup_arr_precise.

    - unfold bth_pre, tr_pres; intros; istar_simplify.
      sep_rewrite (@ls_exists0 _ (ls_init 0 dim (fun i => 0%Z))).
      unfold sh_decl in H.
      sep_rewrite_in sh_spec_is_tup_array_with_l H.
      sep_split_in H.
      apply ex_lift_l_in in H as [f_sm H].
      sep_normal_in H; sep_split_in H.
      exists (ls_init 0 ntrd f_sm).
      sep_split; [unfold_conn; simpl; rewrite init_length; auto|].
      repeat sep_rewrite (@ls_star); repeat sep_rewrite (@ls_pure); sep_split.
      apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; eauto; cbv; auto.
      apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; eauto; cbv; auto.
      apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; eauto; cbv; auto.
      apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; unfold_conn; eauto;[| cbv; auto].
      rewrite ls_init_spec; destruct lt_dec; try omega; unfold_conn_in HP2; rewrite HP2; auto.
      sep_cancel.
      sep_rewrite is_tuple_array_p_distr; sep_cancel.
      2: intros; rewrite ls_init_spec; destruct lt_dec; try rewrite init_length.
      2: unfold_conn_in HP2; unfold vars2es; rewrite HP2, !map_length, !locals_length; auto.
      2: unfold vars2es; rewrite !map_length, locals_length; auto.
      2: instantiate (1 := nseq dim 0%Z); rewrite length_nseq; auto.
      apply scC; rewrite <-(@firstn_skipn assn 1) at 1; rewrite firstn_init, skipn_init.
      rewrite Nat.min_l; try omega; simpl; sep_normal.
      erewrite ls_init_eq'.
      2: intros; destruct Nat.eq_dec; try omega;
        cutrewrite (emp = id (fun _ => emp) (1 + i)); eauto.
      unfold id; sep_rewrite init_emp_emp.
      sep_rewrite emp_unit_l; sep_normal.
      sep_cancel.
      eapply is_tup_array_change; eauto.
      intros; rewrite ls_init_spec; destruct lt_dec; try omega; f_equal; omega.
    - (* not completed!!!! *)
      unfold tr_posts, bth_post; intros s h H; istar_simplify_in H.
      sep_lift_in H 2.
      rewrite <-(firstn_skipn 1) in H at 1; rewrite firstn_init, skipn_init in H.
      sep_rewrite_in conj_xs_app H.
      rewrite Nat.min_l in H; try omega; simpl in H.
      erewrite (@ls_init_eq' _ _ _ _ 1) in H.
      2: intros; destruct Nat.eq_dec; try omega;
        cutrewrite (emp = id (fun _ => emp) (1 + i)); eauto.
      unfold id in H; sep_rewrite_in init_emp_emp H.
      sep_normal_in H; sep_lift_in H 2.
      rewrite <-(firstn_skipn 1) in H at 1; rewrite firstn_init, skipn_init in H.
      rewrite Nat.min_l in H; try omega; simpl in H.
      erewrite ls_init_eq' in H.
      2: intros; destruct Nat.eq_dec; try omega;
        cutrewrite (emp = id (fun _ => emp) (1 + i)); eauto.
      unfold id in H; sep_rewrite_in init_emp_emp H.
      sep_normal_in H; repeat sep_cancel.
    - intros; unfold low_assn, tr_pres; rewrite MyVector.init_spec.
      unfold E; repeat prove_low_assn;
        (try now (constructor; eauto));
        try now (unfold Outs; first [apply low_assn_eqt | apply low_assn_is_tuple];
                 simplify; cutrewrite (Lo = join Lo Lo); repeat econstructor; simpl;
                 try rewrite prefix_nil; auto).
      apply low_assn_input_spec;
      intros; env_dec; simplify; simpl in *; congruence.
    - intros; unfold low_assn, tr_posts; rewrite MyVector.init_spec.
      unfold E, sh_decl; simpl.
      repeat prove_low_assn;
        (try now (constructor; eauto));
        try now (unfold Outs; first [apply low_assn_eqt | apply low_assn_is_tuple];
                 simplify; cutrewrite (Lo = join Lo Lo); repeat econstructor; simpl;
                 try rewrite prefix_nil; auto).

      Lemma sh_spec_low_assn E sdec :
        (forall x y, In (x, y) sdec -> E x = Lo) -> low_assn E (sh_spec sdec).
      Proof.
        intros.
        induction sdec as [|[? ?] ?]; simpl; unfold low_assn; repeat prove_low_assn.
        repeat constructor; erewrite H; eauto.
        simpl; eauto.
        apply IHsdec; simpl in H; eauto.
      Qed.
      apply low_assn_input_spec'.
      apply sh_spec_low_assn; simplify; inverts H; simpl; rewrite prefix_nil; auto.
    - apply fold_has_type.
    - unfold tr_pres, tr_posts; intros; rewrite !MyVector.init_spec.
      eapply Hbackward.
      Focus 2. {
        intros; apply ex_lift_l_in in H as [? H].
        sep_normal_in H.
        evar (P : assn); assert ((!(pure (Datatypes.length x = dim)) ** P) s0 h) by
                           (sep_cancel; unfold P; eauto).
        unfold P in *; ex_intro x H0; eauto. } Unfocus.
      apply rule_ex; intros vi_ini.
      apply hback; intros Hvini.
      eapply rule_conseq; try apply (reduce_ok_th tid j vi_ini); intros; eauto; repeat sep_cancel.
  Qed.

  Theorem reduce_ok_gl g :
    (forall i, i < l -> get_den (Zn i) (g i)) ->
    CSLg ntrd nblk
         (!(sh === Zn l) **
          !(Outs' ==t out) **
          input_spec env env_den 1 **
          is_tuple_array_p (map Gl Outs') nblk fout 0 1)

         (Pr sh_decl mkFoldAll)

         (input_spec' env_den 1 **
          is_tuple_array_p (map Gl (vs2es out)) nblk
          (fun j => f (Nat.min (l - j * ntrd) ntrd) (f_seq g j) e_b 0) 0 1).
  Proof.
    intros Hg.
    applys (>> rule_grid E (MyVector.init bth_pre) (MyVector.init (bth_post g))); eauto.
    - intros s h H.
      unfold bth_pre; sep_split_in H; istar_simplify.
      repeat sep_rewrite (@ls_star nblk).
      repeat sep_rewrite (@ls_pure nblk); sep_split.
      apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
      apply ls_emp'; intros; rewrite ls_init_spec; destruct lt_dec; auto; cbv; auto.
      sep_rewrite conj_xs_init_flatten; simpl.
      sep_rewrite input_spec_p1; eauto; try nia.
      sep_rewrite (is_tuple_array_p_distr); eauto.
      intros; unfold vars2es, Outs; rewrite fout_wf, !map_length, locals_length; auto.
    - intros; eapply CSLp_backward; [eapply CSLp_forward|]; try applys* (>> reduce_ok_bl g bid).
      + rewrite MyVector.init_spec; auto.
      + rewrite MyVector.init_spec; intros; repeat sep_cancel.
    - unfold bth_post; intros s h H; istar_simplify_in H.
      sep_rewrite_in conj_xs_init_flatten H; simpl in H.
      sep_rewrite_in input_spec'_p1 H; eauto; try nia.
      sep_rewrite_in (is_tuple_array_p_distr) H; repeat sep_cancel.
      unfold vs2es; intros; rewrite f_length; [rewrite !map_length, out_wf; auto|].
      unfold f_seq, maybe; intros; destruct (skip_sum_of_vs _ _ _ _ _) eqn:Heq.
      + erewrite skip_sum_of_vs_wf; eauto.
        intros ix ?; forwards * : (>>get_den_wf (Zn ix)); rewrite out_wf.
        congruence.
      + rewrite length_nseq; auto. 
    - unfold sh_decl, mkFoldAll; simpl.
      Lemma inde_ex T P xs :
        (forall x : T, inde (P x) xs) ->
        inde (Ex x, (P x)) xs.
      Proof.
        unfold inde; simpl; intros.
        split; intros [w Pw]; exists w.
        - rewrite <-H; auto.
        - rewrite <-H in Pw; auto.
      Qed.          
          
      Lemma sh_spec_inde sdec xs :
        (disjoint (map fst sdec) xs) -> inde (sh_spec sdec) xs.
      Proof.
        intros.
        induction sdec as [|[? ?] ?]; simpl; unfold low_assn; repeat prove_inde.
        2: simpl in *; jauto.
        apply inde_ex; intros; apply inde_is_array.
        simpl in *; rewrite Forall_forall; intros.
        apply indelE_fv; simpl; intros [Hc |[]]; subst; tauto.
      Qed.
      apply sh_spec_inde; rewrite map_map; simpl.
      rewrite read_tup_writes; [|rewrite locals_length, length_nseq; auto].
      rewrite !writes_var_gen_write; simpl.
      repeat (rewrite read_tup_writes; [|rewrite locals_length, get_wf; auto]).
      repeat (rewrite read_tup_writes; [|rewrite locals_length, func_wf; auto]).
      rewrite gen_read_writes; [|unfold vars2es; rewrite map_length, !locals_length; auto].
      rewrite read_tup_writes; [|unfold vars2es; rewrite map_length, !locals_length; auto].
      apply not_in_disjoint; simpl; intros; simplify; try congruence;
        (try now (forwards*: get_wr; eauto; simplify; simpl in *; congruence));
        (try now (forwards*: func_local; eauto; simplify; simpl in *; congruence)).
      unfold reduce in H0.
      apply reduce_writes in H0; destruct Nat.eq_dec; try omega; simplify; try congruence.
    - intros; rewrite MyVector.init_spec; unfold bth_pre.
      prove_inde.
      + apply inde_eq_tup; simpl; unfold Outs; simplify; try congruence.
      + apply inde_conj_xs; simpl; rewrite init_length; intros.
        rewrite ls_init_spec; destruct lt_dec; try omega.
        apply inde_input_spec; simplify; eauto.
      + unfold Outs; apply inde_is_tup; simplify; try congruence.
    - intros; rewrite MyVector.init_spec; unfold bth_pre.
      unfold E; repeat prove_low_assn;
        try now (constructor; eauto).
      + unfold Outs; apply low_assn_eqt; simplify; constructor; simpl; rewrite prefix_nil; auto.
      + apply low_assn_conj_xs; rewrite init_length; intros.
        rewrite ls_init_spec; destruct lt_dec; try omega.
        apply low_assn_input_spec;
        introv Hpre; apply prefix_ex in Hpre as [? Hpre]; destruct v; simpl in Hpre; subst.
        * simpl; rewrite prefix_nil; auto.
        * repeat (destruct var_eq_dec; try congruence).
          simpl; rewrite prefix_nil; auto.
      + unfold Outs; apply low_assn_is_tuple; simplify.
        equates 1; [repeat constructor|].
        instantiate (1 := Lo); simpl; rewrite prefix_nil; eauto.
        instantiate (1 := Lo); auto.
        constructor.
    - intros; rewrite MyVector.init_spec; unfold bth_post.
      repeat has_no_vars_assn.
      apply has_no_vars_is_tup; simplify; auto.
      apply has_no_vars_conj_xs; intros; rewrite ls_init_spec; destruct lt_dec;
        eauto using has_no_vars_input_spec, has_no_vars_emp.
    - unfold sh_decl; rewrite map_map; simpl.
      simplify.
      unfold E; simpl; rewrite prefix_nil; auto.
    (* - cbv; auto. *)
    (* - cbv; auto. *)
    - unfold sh_decl; rewrite map_map; simpl.
      simplify; congruence.
    - unfold sh_decl; rewrite map_map; simpl.
      simplify; congruence.
    - unfold sh_decl; rewrite map_map; simpl.
      rewrite map_id; apply locals_disjoint_ls.
  Qed.

  Notation sum_of_vs := (sum_of_f_opt (list val) f_fun).

  Lemma feb_ok' ds len f_in:
    0 < len -> len <= ntrd ->
    (forall i : nat, Datatypes.length (f_in i) = dim) ->
    f len f_in e_b 0 = maybe (sum_of_vs 0 len f_in) ds.
  Proof.
    intros.
    forwards*: (>>feb_ok len f_in); simpl in *.
    destruct len; simpl in *; try omega; intros.
    destruct (sum_of_vs _ _ _) eqn:Heq; eauto.
  Qed.
  
  Lemma reduce_res_ok g :
    (forall i, i < l -> get_den (Zn i) (g i)) ->
    sum_of_vs 0 (Nat.min ((l + ntrd - 1) / ntrd) nblk )
              (fun j => f (Nat.min (l - j * ntrd) ntrd) (f_seq g j) e_b 0) = 
    sum_of_vs 0 l g.
  Proof.
    intros Hg.
    assert (ntrd * nblk <= l \/ l < ntrd * nblk) as [Hntl | Hntl] by omega.
    - assert (Hl0 : 0 < l) by nia.
      rewrite Nat.min_r.
      Focus 2.
      { lets: (>>Nat.div_mod (l + ntrd - 1) ntrd __); eauto.
        lets: (>>Nat.mod_upper_bound (l + ntrd - 1) ntrd __); eauto.
        nia. } Unfocus.
      erewrite sum_of_eq.
      Focus 2.
      { simpl; intros.
        rewrite Nat.min_r; try nia.
        rewrites* (feb_ok' (nseq dim 0%Z)); try nia.
        intros; unfold f_seq, maybe; destruct (skip_sum_of_vs _ _ _ _ _) eqn:Heq.
        + erewrite skip_sum_of_vs_wf; eauto.
          intros ix ?; forwards * : (>>get_den_wf (Zn ix)); rewrite out_wf.
          congruence.
        + rewrite length_nseq; auto. } Unfocus.
      unfold f_seq.
      
    
      Lemma sum_of_vs_off s s' n f  :
        s >= s' -> sum_of_vs s n f = sum_of_vs s' n (fun i => f ((s - s') + i)).
      Proof.
        revert s s'; induction n; simpl; intros; eauto.
        rewrite (IHn (S s0) (S s')); try omega.
        erewrite sum_of_eq.
        Focus 2. {
          intros; cutrewrite (S s0 - S s' + i = s0 - s' + i); [|omega].
          reflexivity. } Unfocus.
        destruct (sum_of_vs _ _ _); simpl; try omega.
        cutrewrite (s0 - s' + s' = s0); [|omega]; eauto.
        cutrewrite (s0 - s' + s' = s0); [|omega]; eauto.
      Qed.

      Lemma sum_of_vs_off0 s n f :
        sum_of_vs s n f = sum_of_vs 0 n (fun i => f (s + i)).
      Proof.
        rewrite (sum_of_vs_off s 0); try omega.
        erewrite sum_of_eq; eauto.
        intros; simpl; f_equal; omega.
      Qed.

      Lemma sum_of_vs_nested s f d nt nb :
        nt <> 0 ->
        sum_of_vs s nb (fun j => maybe (sum_of_vs 0 nt (fun i => f (i + j * nt))) d) =
        sum_of_vs (s * nt) (nt * nb) f.
      Proof.
        intros.
        revert s; induction nb; intros; simpl.
        - rewrite mult_0_r; auto.
        - cutrewrite (nt * S nb = nt + nt * nb); [|ring].
          rewrite sum_of_concat; eauto; unfold op', maybe.
          rewrite IHnb.
          cutrewrite (S s0 * nt = nt + s0 * nt); [|ring].
          destruct (sum_of_vs (nt + s0 * nt) (nt * nb)); simpl.
          rewrite (sum_of_vs_off0 (s0 * nt)).
          erewrite sum_of_eq.
          2: intros; rewrite plus_comm; reflexivity.
          destruct (sum_of_vs _ _ _) eqn:Heq; eauto; simpl in *.
          destruct nt; simpl in *; try congruence.
          destruct (sum_of_vs _ _ _); simpl in *; try congruence.
          rewrite (sum_of_vs_off0 (s0 * nt)).
          erewrite sum_of_eq.
          2: intros; rewrite plus_comm; reflexivity.
          destruct (sum_of_vs _ _ _) eqn:Heq; eauto; simpl in *.
          destruct nt as [|nt]; simpl in *; try congruence.
          destruct (sum_of_vs _ _ _); try congruence.
      Qed.

      rewrite (sum_of_vs_nested 0 (fun x =>
         maybe (skip_sum_of_vs nt_gr 0 l g x) (nseq dim 0%Z))); eauto.
      simpl.
      
      cutrewrite (ntrd * nblk = nt_gr); [|ring].

      Lemma sum_of_split s n f g :
        sum_of_vs s n (fun i => f i |+| g i) = op' _ f_fun (sum_of_vs s n f) (sum_of_vs s n g).
      Proof.
        revert s; induction n; simpl; eauto.
        intros; rewrite IHn.
        unfold op'; 
          repeat lazymatch goal with
        | [|- context [sum_of_vs ?X ?Y ?Z]] => destruct (sum_of_vs X Y Z)
        end; eauto.
        rewrite !f_fun_assoc; do 2 f_equal.
        rewrite <-f_fun_assoc, (f_fun_comm (g s0) l0), f_fun_assoc; eauto.
        rewrite f_fun_assoc, (f_fun_comm (g s0) l0), <-f_fun_assoc; eauto.
        rewrite f_fun_assoc, (f_fun_comm (g s0) l0), <-f_fun_assoc; eauto.
      Qed.

      Lemma skip_sum_of_sum_of n s d f none:
        d <> 0 -> 
        sum_of_vs 0 (min n d) (fun x => maybe (skip_sum_of_vs d (s * d) n f x) none) =
        sum_of_vs (s * d) n f.
      Proof.
        intros Hd0; rewrite (Nat.div_mod n d); eauto.
        generalize (n / d); intros n0.
        revert n d Hd0 s; induction n0; simpl; intros n d Hd0 s.
        - cutrewrite (d * 0 = 0); [|ring]; simpl.
          rewrite Nat.min_l; [|lets: (Nat.mod_upper_bound n d); nia].
          rewrite (sum_of_vs_off (s * d) 0); try nia.
          simpl; erewrite sum_of_eq; eauto; intros; unfold maybe.
          rewrites (>>skip_sum_opt_sum d i s 1); eauto; try (lets:(Nat.mod_upper_bound n d); nia).
          simpl.
          f_equal; nia.
        - rewrite Nat.min_r; try nia.
          erewrite sum_of_eq.
          Focus 2. {
            simpl; intros.
            rewrite skip_sum_opt_unfold; eauto; try nia.
            cutrewrite (d * S n0 + n mod d - d = d * n0 + n mod d); [|nia].
            unfold op'.
            instantiate (1 := fun i =>
              if lt_dec i (d * n0 + n mod d)
              then maybe (skip_sum_of_vs d (S s * d) (d * n0 + n mod d) f i) none |+| f (i + s * d)
              else f (i + s * d)); simpl.
            unfold maybe.
            destruct lt_dec, (skip_sum_of_vs _ _ _ _ _) eqn:Heq'; eauto.
            + assert (Heq'' : d + s * d = S s * d) by nia; rewrite Heq'' in Heq'; clear Heq''.
              rewrite skip_sum_opt_unfold in Heq'; simpl in Heq'; eauto; try omega.
              unfold op' in Heq'; destruct (skip_sum_of_vs _ _ _ _ _); congruence.
            + rewrites* (>>skip_sum_opt_nil (d * n0 + n mod d)) in Heq'.
              intros.
              cutrewrite (d + s * d + j = j + S s * d); [|ring]; rewrite Nat.mod_add; eauto.
              rewrite Nat.mod_small; nia.
              rewrite minus_diag in Heq'; simpl in *; congruence. } Unfocus.
          assert (d <= d * n0 + n mod d \/ d * n0 + n mod d < d) as [H | H] by omega.
          + erewrite sum_of_eq; [|intros; destruct lt_dec; try omega; reflexivity].
            rewrite sum_of_split.
            forwards* Ht: (>>IHn0 n d (S s)); rewrite Nat.min_r in *; eauto.
            rewrite Ht; clear Ht.
            cutrewrite (d * S n0 + n mod d = d + (d * n0 + n mod d)); [|ring].
            rewrites (>>sum_of_concat d (d * n0 + n mod d)); eauto.
            rewrite opopt_comm; f_equal; eauto.
            rewrite (sum_of_vs_off0 (s * d)); erewrite sum_of_eq; eauto.
            simpl; intros; f_equal; ring.
          + rewrite sum_of_f_split; eauto; try nia.
            rewrite <-!minus_n_O.
            rewrite sum_of_split.
            erewrite sum_of_eq.
            Focus 2.
            { intros.
              rewrites (>>skip_sum_opt_sum d i 1); eauto; try nia.
              simpl; reflexivity. } Unfocus.
            cutrewrite (d * S n0 + n mod d = (d * n0 + n mod d) + (d - (d * n0 + n mod d)) +
                                             (d * n0 + n mod d)); [|nia].
            remember (d * n0 + n mod d).
            rewrite !sum_of_concat; eauto.
            rewrite (sum_of_vs_off0 (s * d)), (sum_of_vs_off0 (n1 + s * d)),
              (sum_of_vs_off0 (n1 + (d - n1) + s * d)), (sum_of_vs_off0 n1).
            assert (forall x y z, op' _ f_fun (op' _ f_fun x y) z =
                                  op' _ f_fun (op' _ f_fun y z) x).
            { intros. rewrite opopt_assoc, opopt_comm; eauto. }
            rewrite H0; [f_equal; [f_equal|]].
            * erewrite sum_of_eq; eauto.
              simpl; intros; f_equal; ring.
            * erewrite sum_of_eq; eauto.
              simpl; intros; f_equal; ring.
            * erewrite sum_of_eq; eauto.
              simpl; intros; f_equal; nia.
      Qed.

      assert (Heq : nt_gr = min l nt_gr) by (rewrite Nat.min_r; nia); rewrite Heq at 1; clear Heq.
      assert (Heq : 0 = 0 * nt_gr) by (auto).
      erewrite sum_of_eq; [|intros; rewrite Heq; reflexivity].
      rewrite skip_sum_of_sum_of; eauto; nia.

    - lets: (>>Nat.div_mod (l + ntrd - 1) ntrd __); eauto.
      lets: (>>Nat.mod_upper_bound (l + ntrd - 1) ntrd __); eauto.
      lets: (>>Nat.div_mod l ntrd __); eauto.
      lets: (>>Nat.mod_upper_bound l ntrd __); eauto.
      rewrite Nat.min_l; [|nia].
      assert (l = 0 \/ l > 0) as [Hl0|Hl0] by omega.
      { (* case l = 0 *)
        subst; simpl.
        rewrite Nat.div_small; [|omega]; eauto. }
      erewrite sum_of_eq.
      Focus 2. {
        intros.
        rewrite (feb_ok' (nseq dim 0%Z)).
        2: apply Nat.min_glb_lt_iff.
        2: nia.
        2: apply Nat.le_min_r.
        2: intros; unfold f_seq, maybe; destruct (skip_sum_of_vs _ _ _ _ _) eqn:Heq.
        2: erewrite skip_sum_of_vs_wf; eauto.
        2: intros ix ?; forwards * : (>>get_den_wf (Zn ix)); rewrite out_wf.
        2: congruence.
        2: rewrite length_nseq; auto.
        unfold f_seq.
        erewrite sum_of_eq.
        Focus 2. {
          simpl in *; intros.
          rewrite Nat.min_glb_lt_iff in H4.
          rewrites (>>skip_sum_sum0 1); [eauto|nia|nia|].
          simpl; rewrite <-plus_n_O; reflexivity. } Unfocus.
        reflexivity. } Unfocus.
      assert ((l + ntrd - 1) / ntrd = l / ntrd \/
              (l + ntrd - 1) / ntrd = l / ntrd + 1) as [H'|H']; [|rewrite H'..].
      { assert ((l + ntrd - 1)  mod ntrd = 0 \/
                (l + ntrd - 1)  mod ntrd > 0) as [|] by omega; nia. } 
      + erewrite sum_of_eq.
        Focus 2. { 
          intros.
          rewrite Nat.min_r; [|nia].
          reflexivity. } Unfocus.
        rewrite sum_of_vs_nested; eauto; simpl.
        cutrewrite (ntrd * (l / ntrd) = l); eauto; nia.
      + rewrite sum_of_concat; eauto; simpl.
        erewrite sum_of_eq.
        Focus 2. {
          intros.
          rewrite Nat.min_r; [|nia].
          reflexivity. } Unfocus.
        rewrite sum_of_vs_nested; eauto; simpl.
        rewrite Nat.min_l; [|nia].
        rewrite <-!plus_n_O.
        cutrewrite (l - l / ntrd * ntrd = l mod ntrd); [|nia].
        rewrite H1 at 3; rewrite sum_of_concat; eauto.
        f_equal.
        unfold maybe.
        rewrite <-plus_n_O, (sum_of_vs_off0 (ntrd * (l / ntrd))).
        erewrite sum_of_eq; [|intros;
                              cutrewrite (i + l / ntrd * ntrd = ntrd * (l / ntrd) + i); [|ring];
                              reflexivity].
        destruct (sum_of_vs _ _ _) eqn:Heq; eauto.
        destruct (l mod ntrd) eqn:Heq'; simpl in *; [|destruct (sum_of_vs _ _ _); congruence].
        nia.
  Qed.
End Reduce.
