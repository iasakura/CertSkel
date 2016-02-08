Require Import GPUCSL.
Require Import scan_lib.
Require Import LibTactics Psatz.
Require Import Skel_lemma.

Notation "l '+ol' i" := (tarr_idx l i) (at level 40).
Notation "l '-->l' ( p , e )" := (is_tuple_p l e p) (at level 75, right associativity).

Ltac simplify :=
  unfold vars2es, tarr_idx, vs2es in *;
  repeat (simpl in *; subst; lazymatch goal with
          | [|- In _ (map _ _) -> _] =>
            rewrite in_map_iff; intros [? [? ?]]; subst
          | [H:In _ (map _ _) |-_] =>
            rewrite in_map_iff in H; destruct H as [? [? H]]; subst
          | [|- indeE _ _] => apply indeE_fv
          | [|- indelE _ _] => apply indelE_fv
          | [H : _ \/ False|-_] =>destruct H as [H|[]];subst
          | [H : _ \/ _ |-_] =>destruct H as [?|H]
          | [|- ~(_ \/ _)] => intros [?|?]
          | [|- context [In _ (_ ++ _)]] => rewrite in_app_iff
          | [|- forall _, _] => intros ?
          | [H : In _ (locals _ _) |- _] => apply locals_pref in H
          | [H : prefix _ _ = true |- _] => apply prefix_ex in H as [? ?]; subst
          | [|- disjoint_list (locals _ _)] => apply locals_disjoint_ls
          | [|- context [length (locals _ _)]] => rewrite locals_length
          | [H :context [length (locals _ _)]|- _] => rewrite locals_length in H
          | [H :context [length (vars2es _)]|- _] => unfold vars2es in *; rewrite map_length
          | [|- context [length (vars2es _)]] => unfold vars2es; rewrite map_length
          | [H :context [In _ (vars2es _)]|- _] =>
            unfold vars2es in *; rewrite in_map_iff in H;
            destruct H as [? [? H]]; subst
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
          end; simpl in *; subst).

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

  Definition Outs := fst (fst (writeArray "Out" dim Gl)).
  Definition Len := snd (fst (writeArray "Out" dim Gl)).
  Definition setOut ix es := snd (writeArray "Out" dim Gl) ix es.
  
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
  
  Section ReduceBlock.
    Variable e_b : nat.
    Variable l : nat.
    
    Variable f_in : nat -> list val.
    Hypothesis f_in_wf :
      forall i, length (f_in i) = dim.
    
    Hypothesis max_th_size : ntrd <= 2 ^ e_b.
    Hypothesis l_leq_ntrd : l <= ntrd.
    Hypothesis eb_neq_0 : e_b <> 0.
    
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
        !(vars2es y ==t maybe (skip_sum_of_vs nt_gr 0 (min (xix nl) l) g gid) vi_ini) **
        (sdata' +ol Zn (nf i) -->l (1, vs2es vi_ini)) **
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

    Definition vi g := 
      maybe (skip_sum_of_vs nt_gr 0 l g (nf i + nf j * ntrd)) vi_ini.


    Lemma seq_reduce_correct BS g:
      (forall i, i < l -> get_den (Zn i) (g i)) ->
      CSL BS i
       (!(tid === Zn (nf i)) ** !(bid === Zn (nf j)) ** !(sh === Zn l) **
        (sdata' +ol Zn (nf i) -->l (1, vs2es vi_ini)) **
        input_spec env env_den (perm_n nt_gr))

       (seq_reduce (inv g))

       (sdata' +ol Zn (nf i) -->l (1, vs2es (vi g)) **
        input_spec env env_den (perm_n nt_gr) ** !(sh === Zn l)).
      Proof.
        unfold seq_reduce; intros Hg.
        eapply rule_seq; [hoare_forward|].
        { intros ? ? [v H]; subA_normalize_in H with (fun H => first
            [ apply subA_distribute_tup in H | apply subA_eq_tup in H
              | apply subA_is_tuple_p in H | apply subA_input_spec in H; eauto ] ).
          autorewrite with core in H; simpl in *; eauto; apply H. }
        hoare_forward; eauto using rule_skip.

        - eapply Hbackward.
          Focus 2.
          { intros stk h H; sep_split_in H.
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
              prove_inde; simplify; simpl in *; try congruence.
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
                                     maybe (skip_sum_of_vs nt_gr 0 (min (xix nl) l) g gid) vi_ini) **
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
                  rewrite func_wf; forwards*: (f_fun_den vi_ini (g (xix nl))); try congruence.
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
                     maybe (skip_sum_of_vs nt_gr 0 (min (xix nl) l) g gid) vi_ini |+| g (xix nl)) **
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
                  forwards*: (f_den_wf vi_ini (g (xix nl))); congruence. 
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
            - unfold inv.
              eapply Hbackward.
              Focus 2. {
                intros stk h H; apply ex_lift_l_in in H; destruct H as [nl H].
                sep_normal_in H; sep_split_in H.
                rewrite min_r in HP4; [|unfold_pures; unfold_conn_all; simpl in *; nia].
                assert (Heq : (Zn (nf i) === tid) stk h) by (unfold_conn_all; simpl in *; eauto).
                sep_rewrite_in mps_eq1_tup' H; [|exact Heq].
                evar (P : assn); assert (Hnxt : (sdata' +ol tid -->l (1, vs2es vi_ini) ** P) stk h).
                { unfold P; sep_cancel.
                  assert (pure (gid < l) stk (emp_ph loc)) by eauto.
                  clear HP HP3 HP5; sep_combine_in H0; apply H0. }
                apply Hnxt. } Unfocus.
              apply rule_frame; [apply gen_write_correct|]; simplify; eauto.
              rewrite writes_var_gen_write; apply inde_nil. } 
        - intros stk h [H|H]; sep_normal_in H; sep_split_in H.
          + unfold vi; destruct skip_sum_of_vs.
            * sep_rewrite_in mps_eq2_tup H; [|exact HP2].
              sep_rewrite_in mps_eq1_tup' H; [|exact HP].
              sep_split; eauto.
            * sep_rewrite_in mps_eq2_tup H; [|exact HP2].
              sep_rewrite_in mps_eq1_tup' H; [|exact HP].
              sep_split; eauto.
          + unfold vi.
            rewrites (>>skip_sum_opt_nil g l).
            unfold_pures; unfold_conn_all; simpl in *; intros;
              rewrite Nat.mod_small; lets: ntgr_gid; try nia.
            rewrite minus_diag; simpl; sep_split; eauto.
            Grab Existential Variables.
            apply (fun _ => nil).
      Qed.
  End SeqReduce.