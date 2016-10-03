Require Import Monad DepList GPUCSL TypedTerm Compiler.
Require Import Program.Equality LibTactics.
Require Import CUDALib CodeGen CSLLemma CSLTactics Correctness mkMap.
Import Skel_lemma.
Require Import SkelLib Psatz.

Variable sorry : forall A, A.
Arguments sorry {A}.

Ltac unfoldM := repeat (unfold bind_opt, ret; simpl).

Lemma freshes_incr ty m n xs :
  freshes ty n = (xs, m) ->
  m = n + 1.
Proof.
  unfold freshes; unfoldM; inversion 1; auto.
Qed.

(* some lemma for generetated variables *)
Lemma freshes_vars ty n m xs:
  freshes ty n = (xs, m) ->
  (forall x, In x (flatTup xs) -> exists l, x = Var (lpref n ++ nat2str l) /\ l < (nleaf ty)).
Proof.
  unfold freshes; unfoldM; inversion 1.
  intros; forwards* [j [? ?]]: locals_pref; eexists; split; substs; unfold lpref; simpl; eauto.
  omega.
Qed.

Lemma var_pnat_inj n m n' m' : Var (str_of_pnat n m) = Var (str_of_pnat n' m') -> n = n' /\ m = m'.
Proof.
  intros Heq.
  apply str_of_pnat_inj; inversion Heq.
  unfold str_of_pnat; f_equal; eauto.
Qed.

(* Arguments assn_of_svs _ _ _ _ _ : simpl never. *)
(* Arguments assn_of_avs : simpl never. *)
(* Tactic Notation "simpl_avs" "in" hyp(HP) := unfold assn_of_svs, SE.assn_of_vs, SE.fold in HP; simpl in HP. *)
(* Tactic Notation "simpl_avs" := unfold assn_of_svs, SE.assn_of_vs, SE.fold; simpl. *)
(* Tactic Notation "simpl_avs" "in" "*" := unfold assn_of_svs, SE.assn_of_vs, SE.fold in *; simpl in *. *)
(* Arguments flip / _ _ _ _ _ _. *)
Require Import SetoidClass.
(* Instance ban_proper stk : Proper (equiv_sep stk ==> equiv_sep stk) ban. *)
(* Proof. *)
(*   intros P1 P2 Heq h; lets:(Heq h). *)
(*   unfold ban, Aconj; rewrite H; split; eauto. *)
(* Qed. *)
Ltac unfoldM_in H := repeat (unfold bind_opt, ret in H; simpl in H).
Lemma compile_op_don't_decrease t1 t2 t3 (op : Skel.BinOp t1 t2 t3) x1 x2 n m c es :
  compile_op op x1 x2 n = ((c, es), m)
  -> n < m.
Proof.
  unfold compile_op; destruct op; simpl in *; unfoldM; inversion 1; omega.
Qed.

Lemma compile_don't_decrease GA GS typ
  (se : Skel.SExp GA GS typ) c es
  (avar_env : AVarEnv GA) (svar_env : SVarEnv GS) n0 n1 :
  compile_sexp se avar_env svar_env n0 = ((c, es), n1) ->
  n0 <= n1.
Proof.
  revert n0 n1 svar_env c es; induction se; simpl;
    intros n0 n1 svar_env c es' Hsuc; eauto; inverts Hsuc as Hsuc; eauto; try (unfoldM_in Hsuc);
  (repeat lazymatch type of Hsuc with
     | context [compile_sexp ?X ?Y ?Z ?n] => destruct (compile_sexp X Y Z n) as ((?, ?), ?) eqn:?
     | context [freshes ?X ?Y] => destruct (freshes X Y) as (? & ?) eqn:?
     | context [compile_op ?X ?Y ?Z ?n] => destruct (compile_op X Y Z n) as ((?, ?), ?) eqn:?; forwards*: compile_op_don't_decrease
     end);
  (repeat lazymatch goal with [H : context [match ?E with | _ => _ end]|- _] => destruct E eqn:? end); try omega;
        try now (inverts Hsuc; first
          [now auto| omega|
           forwards*: IHse1; forwards*: IHse2; omega |
           forwards*: IHse1; forwards*: IHse2; forwards*: IHse3; omega |
           forwards*: IHse; omega |
           forwards*: IHse1; forwards*: IHse2; forwards*: freshes_incr; omega |
           forwards*: IHse1; forwards*: IHse2; forwards*: IHse3; forwards*: freshes_incr; omega |
           forwards*: IHse; forwards*: freshes_incr; omega |
           forwards*: IHse; omega]).
Qed.

Lemma inde_equiv P P' xs :
  (forall stk, stk ||= P <=> P') ->
  (inde P xs <-> inde P' xs).
Proof.
  unfold inde, equiv_sep.
  intros; simpl.
  split; intros; split; intros; intuition;
    try (apply H, H0, H); eauto.
  apply H; apply <-H0; eauto; apply H; eauto.
  apply H; apply <-H0; eauto; apply H; eauto.
Qed.

Fixpoint hIn {A B : Type} {l : list A} (x : B) (ys : hlist (fun _ => B) l) :=
  match ys with
  | HNil => False
  | y ::: ys => x = y \/ hIn x ys
  end.

(* Lemma inde_assn_of_svs GS (seval_env : SEvalEnv GS) *)
(*       (svar_env : SVarEnv GS) (xs : list var) : *)
(*   (forall x ty (m : member ty GS), In x xs -> ~In x (hget svar_env m)) -> *)
(*   inde (assn_of_svs seval_env svar_env) xs. *)
(* Proof. *)
(*   unfold assn_of_svs. *)
(*   dependent induction seval_env; dependent destruction svar_env; intros H; simpl; repeat prove_inde. *)
(*   (* rewrites (>>inde_equiv). *) *)
(*   (* { intros; rewrite SE.fold_left_assns; reflexivity. } *) *)
(*   { apply inde_eq_tup. *)
(*     rewrite Forall_forall; intros. *)
(*     forwards*: (>>H (@HFirst _ x ls)); simpl in *. *)
(*     simplify; eauto. } *)
(*   { apply IHseval_env; intros. *)
(*     forwards*: (>>H (@HNext _ _ x _ m)). } *)
(* Qed. *)

(* Lemma inde_assn_of_avs GA (aeval_env : AEvalEnv GA) (avar_env : AVarEnv GA) (xs : list var) : *)
(*   (forall x ty (m : member ty GA), In x xs -> ~In x (snd (hget avar_env m))) -> *)
(*   (forall ty (m : member ty GA), ~In (fst (hget avar_env m)) xs) -> *)
(*   inde (assn_of_avs aeval_env avar_env) xs. *)
(* Proof. *)
(*   unfold assn_of_avs. *)
(*   dependent induction aeval_env; dependent destruction avar_env; intros H1 H2; simpl; repeat prove_inde. *)
(*   - destruct p as [len arrs] eqn:Heq; repeat prove_inde; *)
(*     try now (rewrite Forall_forall; simplify; eauto). *)
(*     + forwards*: (>>H2 (@HFirst _ x ls)); simplify; eauto. *)
(*     + unfold S.es2gls in *; apply inde_is_tup_arr; intros; forwards*: (>>H1 (@HFirst _ x ls)); simplify; eauto. *)
(*   - apply IHaeval_env; intros. *)
(*     + forwards*: (>>H1 (@HNext _ _ x _ m)). *)
(*     + forwards*: (>>H2 (@HNext _ _ x _ m)). *)
(* Qed. *)

(* Ltac unfoldM' := unfold get, set, ret in *; simpl in *; unfold bind_opt in *. *)

Lemma ctyps_of_typ__len_of_ty t : 
  length (ctyps_of_typ t) = len_of_ty t.
Proof.
  induction t; simpl; eauto.
  rewrite app_length; auto.
Qed.
Hint Resolve ctyps_of_typ__len_of_ty app_length.

Lemma assigns_writes ty (vs : vars ty) (ts : ctys ty) (es : exps ty) :
  forall x, In x (writes_var (assigns vs ts es)) -> In x (flatTup vs).
Proof.
  induction ty; simpl; eauto.
  introv; rewrite !in_app_iff; firstorder.
Qed.

Lemma reads_writes ty (xs : vars ty) (ts : ctys ty) (es : lexps ty):
  forall x,  In x (writes_var (reads xs ts es)) -> In x (flatTup xs).
Proof.
  induction ty; simpl; eauto.
  introv; rewrite !in_app_iff; firstorder.
Qed.

Lemma compile_op_wr_vars t1 t2 t3 (op : Skel.BinOp t1 t2 t3)
      (n0 n1 : nat) x1 x2 c es :
  compile_op op x1 x2 n0 = ((c, es), n1) ->
  (forall x, In x (writes_var c) ->
             (Var (lpref n0 ++ nat2str 0)) = x).
Proof.
  induction op; simpl; unfoldM; inversion 1; simpl; intros ? [ ? | []]; auto.
Qed.

Lemma string_app_assoc a b c : ((a ++ b) ++ c = a ++ b ++ c)%string.
Proof.
  induction a; simpl; congruence.
Qed.

Lemma lpref_inj a b c d : (lpref a ++ b = lpref c ++ d -> a = c /\ b = d)%string.
Proof.
  unfold lpref; intros H.
  inverts H as Heq.
  forwards*: (sep_var_inj (nat2str a) (nat2str c)); simpl in *; eauto using nat_to_str_underbar.
  rewrite !string_app_assoc in Heq; simpl in *; eauto.
  forwards*: (>>nat_to_string_inj H); split; eauto.
  substs; apply string_inj2 in Heq; eauto.
Qed.      

Arguments lpref _ : simpl never.
Arguments append _ _ : simpl nomatch.
Arguments append _ _ : simpl never.

Lemma compile_wr_vars GA GS typ (se : Skel.SExp GA GS typ)
      (svar_env : SVarEnv GS) (avar_env : AVarEnv GA) (n0 n1 : nat) c es :
  compile_sexp se avar_env svar_env n0 = ((c, es), n1) ->
  (forall x, In x (writes_var c) ->
             exists k l, (Var (lpref k ++ nat2str l)) = x /\ n0 <= k < n1).
Proof.
  Lemma id_mark A (x : A) :
    x = id x. eauto. Qed.
  Ltac t := do 2 eexists; splits*; omega.
  Ltac fwd H := first [forwards* (? & ? & ? & ?): H | forwards* (? & ? & ?): H ].
  revert n0 n1 svar_env c es; induction se; simpl;
    intros n0 n1 svar_env c es' Hsuc; eauto; (try inverts Hsuc as Hsuc);
  eauto; (try (unfoldM_in Hsuc); 
        (repeat lazymatch type of Hsuc with
           | context [compile_sexp ?X ?Y ?Z ?n] => destruct (compile_sexp X Y Z n) as [(? & ?)?] eqn:?
           | context [compile_op ?X ?Y ?Z ?n] => destruct (compile_op X Y Z n) as [(? & ?) ?] eqn:? 
           | context [freshes ?X ?Y] => destruct (freshes X Y) as ([?] & ?) eqn:?
           end));
  (repeat lazymatch goal with [H : context [match ?E with | _ => _ end]|- _] => destruct E eqn:? end);
  (repeat lazymatch goal with [H : (_, _) = (_, _) |- _] => inverts* H end);
  (try inverts Hsuc); simpl; try tauto; intros; repeat rewrite in_app_iff in *;
  (repeat lazymatch goal with
    | [H : False |- _] => destruct H
    | [H : _ \/ _ |- _] => destruct H
    end; simpl in *; try tauto);
  (try (forwards (? & ? & ? & ?): IHse; [now auto_star..|idtac]; substs));
  (try (forwards (? & ? & ? & ?): IHse1; [now auto_star..|idtac]; substs));
  (try (forwards (? & ? & ? & ?): IHse2; [now auto_star..|idtac]; substs));
  (try (forwards (? & ? & ? & ?): IHse3; [now auto_star..|idtac]; substs));
  repeat lazymatch goal with
    | [H : compile_sexp ?A ?B ?C ?D = ?E |- _] =>
        forwards*: (>>compile_don't_decrease H);
          rewrite (id_mark _ (compile_sexp A B C D = E)) in H
    | [H : freshes ?A ?B = ?C |- _] =>
      forwards*: (>>freshes_incr H);
          rewrite (id_mark _ (freshes A B = C)) in H
    end;
  unfold id in *; substs;  (try now (do 2 eexists; split; simpl; eauto; omega));
  try (forwards ?: reads_writes; [now auto_star..|idtac]);
  try (forwards ?: assigns_writes; [now auto_star..|idtac]);
  try (forwards (? & ? & ?): freshes_vars; [now auto_star..|idtac]);
  try (substs; repeat eexists; eauto; omega).
  - exists n0 0; split; eauto; omega.
  - exists x0 x1; split; eauto; forwards*: compile_op_don't_decrease; omega.
  - exists x0 x1; split; eauto; forwards*: compile_op_don't_decrease; omega.
  - forwards*: compile_op_wr_vars; forwards*: compile_op_don't_decrease; substs; exists n2 0; split; eauto; omega.
  - exists n0 0; split; eauto; omega.
Qed.

Lemma freshes_disjoint d n m xs :
  freshes d n = (xs, m) ->
  disjoint_list (flatTup xs).
Proof.
  unfold freshes; unfoldM; inversion 1; apply locals_disjoint_ls.
Qed.

Lemma var_str_of_pnat_inj :
  forall n m n' m' : nat, Var (str_of_pnat n m) = Var (str_of_pnat n' m') -> n = n' /\ m = m'.
Proof.
  Arguments str_of_pnat : simpl never.
  intros.
  assert (str_of_pnat n m = str_of_pnat n' m') by congruence.
  apply str_of_pnat_inj; auto.
Qed.

(* Lemma member_assn_svs GS ty (m : member GS ty) svar_env seval_env s: *)
(*   assn_of_svs seval_env svar_env s (emp_ph loc) ->  *)
(*   (S.vars2es (hget svar_env m) ==t vs_of_sval (hget seval_env m)) s (emp_ph loc). *)
(* Proof. *)
(*   unfold assn_of_svs; dependent induction seval_env; *)
(*   dependent destruction svar_env; dependent destruction m; simpl; intros H; *)
(*   sep_split_in H; eauto. *)
(* Qed. *)

Fixpoint remove_by_mem {A t} (ls : list A) : member t ls -> list A :=
  match ls with
  | nil => fun m => nil
  | x :: ls => fun m =>
                 match m with
                 | HFirst _ => fun _ => ls
                 | HNext _ _ m => fun rec => rec m
                 end (remove_by_mem ls)
  end.

(* Fixpoint remove_member {A B} {ls : list A} {t : A} *)
(*          (hls : hlist B ls) : forall (m : member t ls), hlist B (remove_by_mem ls m) := *)
(*   match hls with *)
(*   | HNil => fun m => match m with *)
(*                      | HFirst _ => _ *)
(*                      | HNext _ _ m => _ *)
(*                      end *)
(*   | HCons x ls hx hls => fun m => match m with  *)
(*                                 | HFirst _ => hls *)
(*                                 | HNext _ _ m => remove_member hls m  *)
(*                                 end *)
(*   end. *)

(* Lemma member_assn_avs GA ty (m : member ty GA) avar_env aeval_env: *)
(*   exists P, (forall stk, *)
(*   stk ||= assn_of_avs aeval_env avar_env <=> *)
(*           !(fst (hget avar_env m) === G.Zn (length (hget aeval_env m))) ** *)
(*           (S.is_tuple_array_p (S.es2gls (S.vars2es (snd (hget avar_env m)))) *)
(*              (length (hget aeval_env m)) (fun i : nat => vs_of_sval (nth_arr i (hget aeval_env m))) 0 1) ** P) /\ *)
(*             (forall xs, (forall (x : var) (ty : Skel.Typ) (m : member ty GA),  *)
(*                 In x xs -> ~ In x (snd (hget avar_env m))) -> *)
(*              (forall (ty : Skel.Typ) (m : member ty GA), ~ In (fst (hget avar_env m)) xs) -> *)
(*              inde P xs). *)
(* Proof. *)
(*   unfold assn_of_avs; dependent induction aeval_env; *)
(*   dependent destruction avar_env; dependent destruction m; *)
(*   destruct p. *)
(*   - eexists; split; intros; [simpl; rewrite <-!sep_assoc; reflexivity..|]. *)
(*     forwards*: (>>inde_assn_of_avs aeval_env avar_env xs). *)
(*     intros; forwards*: (>>H (@HNext _ _ x _ m)). *)
(*     intros; forwards*: (>>H0 (@HNext _ _ x _ m)). *)
(*   - forwards*(P & Heq & ?): (>>IHaeval_env m avar_env). *)
(*     eexists; split.  *)
(*     + intros; simpl; rewrite Heq, <-!sep_assoc. *)
(*       split; intros; repeat sep_cancel; eauto. *)
(*     + intros. *)
(*       prove_inde. *)
(*       * rewrite Forall_forall; intros. *)
(*         forwards*: (>>H1 (@HFirst _ x ls)); simplify; eauto. *)
(*       * simplify; auto. *)
(*       * apply inde_is_tup_arr. *)
(*         intros; forwards*: (>>H0 (@HFirst _ x ls)). *)
(*         unfold S.es2gls, S.vars2es in *; simplify; auto. *)
(*       * apply H. *)
(*         intros; forwards*: (>>H0 (@HNext _ _ x _ m0)). *)
(*         intros; forwards*: (>>H1 (@HNext _ _ x _ m0)). *)
(* Qed.   *)

(* Lemma len_of_val typ (v : Skel.typDenote typ) : length (vs_of_sval v) = len_of_ty typ. *)
(* Proof. induction typ; simpl; eauto; rewrite app_length; auto. Qed. *)

Hint Rewrite prefix_nil ctyps_of_typ__len_of_ty gen_read_writes : core.
Ltac sep_rewrites_in lem H :=
  match type of H with
  | ?X _ _ => pattern X in H
  end; rewrites lem in H; cbv beta in H.
Ltac sep_rewrites_in_r lem H :=
  match type of H with
  | ?X _ _ => pattern X in H
  end; rewrites <- lem in H; cbv beta in H.
Ltac sep_rewrites lem :=
  match goal with
  | |- ?X _ _ => pattern X
  end; rewrites lem; cbv beta.
Ltac sep_rewrites_r lem :=
  match goal with
  | |- ?X _ _ => pattern X
  end; rewrites <- lem; cbv beta.
(* Hint Rewrite len_of_val : core. *)
(* Hint Unfold S.es2gls S.vars2es. *)

Lemma nth_error_lt' A (arr : list A) i v : 
  List.nth_error arr i = Some v -> i < length arr.
Proof.
  revert i v; induction arr; intros i v; destruct i; simpl; inversion 1; try omega.
  forwards*: IHarr; omega.
Qed.
Lemma nth_error_lt A (arr : list A) i v : 
  nth_error arr i = Some v -> (0 <= i /\ i < len arr)%Z.
Proof.
  unfold nth_error, Z_to_nat_error.
  destruct Z_le_dec; try now inversion 1.
  unfold ret; simpl; unfold bind_opt.
  intros H; apply nth_error_lt' in H.
  rewrite Nat2Z.inj_lt in H.
  rewrite !Z2Nat.id in H; unfold len; omega.
Qed.
Hint Rewrite prefix_nil ctyps_of_typ__len_of_ty gen_read_writes : core.

Ltac no_side_cond tac :=
  tac; [now auto_star..|idtac].

Opaque freshes. 
Lemma flatTup_map ty T1 T2 (f : T1 -> T2) (xs : typ2Coq T1 ty) :
  flatTup (maptys f xs) = map f (flatTup xs).
Proof.
  induction ty; simpl; eauto.
  rewrite map_app; congruence.
Qed.

Lemma in_v2e ty (xs : vars ty) e :
  In e (flatTup (v2e xs)) -> exists x, e = Evar x /\ In x (flatTup xs).
Proof.
  unfold v2e; intros H; rewrite flatTup_map, in_map_iff in H; destruct H as [? [? ?]]; eexists; split; eauto.
Qed.

Ltac simplify :=
  unfold vars2es, tarr_idx, vs2es in *;
  repeat (simpl in *; substs; lazymatch goal with
        | [|- In _ (map _ _) -> _] =>
          rewrite in_map_iff; intros [? [? ?]]; substs
        | [H:In _ (map _ _) |-_] =>
          rewrite in_map_iff in H; destruct H as [? [? H]]; substs
        | [H : In _ (flatTup (v2e _)) |- _] =>
          apply in_v2e in H as [? [? H]]; substs
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
        (* | [|- context [length (locals _ _)]] => rewrite locals_length *)
        (* | [H :context [length (locals _ _)]|- _] => rewrite locals_length in H *)
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
        | [H : context [str_of_var ?x] |- _] => destruct x
        | [|- inde (_ ==t _) _] => apply inde_eq_tup
        | [|- inde (_ -->l (_, _)) _] => apply inde_is_tup
        | [|- inde (is_tuple_array_p _ _ _ _ _) _] => apply inde_is_tup_arr
        | [|- context [length (map _ _)]] => rewrite map_length
        | [H : context [length (map _ _)] |- _] => rewrite map_length in H
        | [H : In _ (names_of_array _ _) |- _] => apply names_of_array_in in H
        | [|- ~_] => intros ?
        end; simpl in *; try substs).

Lemma compile_gens GA GS typ (se : Skel.SExp GA GS typ) avar_env svar_env n0 n1 c es :
  compile_sexp se avar_env svar_env n0 = ((c, es), n1) ->
  senv_ok svar_env n0 -> (* fvs are not in the future generated vars *)
  aenv_ok avar_env ->
  (forall e k l , In e (flatTup es) -> In (Var (lpref k ++ l)) (fv_E e) -> k < n1).
Proof.
  Definition used {A : Type} (x : A) := x.
  Lemma used_id (A : Type) (x : A) : x = used x. auto. Qed.

  Lemma evar_inj x y : Var x = Var y -> x = y. intros H; inverts* H. Qed.
  revert avar_env svar_env n0 n1 c es; induction se; introv; simpl;
  intros H; unfold bind_opt, compile_op, aenv_ok, senv_ok in *; unfoldM_in H;
  repeat match type of H with
         | context [compile_sexp ?x ?y ?z ?w] =>
           destruct (compile_sexp x y z w) as [(? & ?) ?] eqn:?; inversion H; simpl in *
         | context [hget avar_env ?y] =>
           destruct (hget avar_env y) eqn:?; simpl in *
         | context [freshes ?x ?y ] =>
           destruct (freshes x y) as [? ?] eqn:?; inversion H; simpl in *
         | context [match ?t with _ => _ end] =>
           lazymatch type of t with list _ => idtac | Skel.BinOp _ _ _ => idtac end;
             destruct t; try now inversion H
         end; inverts H; intros; simplify; try tauto;
  (try now forwards*: H);
  repeat match goal with
  | [H : compile_sexp ?x ?y ?z ?w = ?u |- _] =>
    forwards*: (>>compile_don't_decrease H);
      rewrite (used_id _ (compile_sexp x y z w = u)) in H
  end; unfold used in *;
  try (forwards ?: IHse; [simpl; try rewrite !in_app_iff in *; now auto_star..|idtac]);
  try (forwards ?: IHse1; [simpl; now auto_star..|idtac]);
  try (forwards ?: IHse2; [first [simpl; now auto_star | intros; forwards*: H; omega]..|idtac]);
  try (forwards ?: IHse3; [first [simpl; now auto_star | intros; forwards*: H; omega]..|idtac]); try omega;
  try (forwards* (? & ? & ?): freshes_vars;
        forwards*: freshes_incr; simpl in *;
        try  (forwards* (? & ? & ?): (@freshes_vars Skel.TZ); [now (simpl; eauto)..|]); 
        try  (forwards* (? & ? & ?): (@freshes_vars Skel.TBool); [now (simpl; eauto)..|]); 
        repeat lazymatch goal with
          | [H : Var _ = Var _ |- _] => apply evar_inj in H
          | [H : (lpref _ ++ _)%string = (lpref _ ++ _)%string |- _ ] =>
            apply lpref_inj in H
          end;
        omega);
  try (try (forwards* (? & H' & ?): (@freshes_vars Skel.TZ); [now (simpl; eauto)..|]);
        try (forwards* (? & H' & ?): (@freshes_vars Skel.TBool); [now (simpl; eauto)..|]);
        try (forwards* ?: (@freshes_incr Skel.TZ); [now (simpl; eauto)..|]);
        try (forwards* ?: (@freshes_incr Skel.TBool); [now (simpl; eauto)..|]);
        apply evar_inj, lpref_inj in H';
        omega).
  - forwards*: IHse2.
    intros.
    dependent destruction m; simpl in *.
    + forwards* (? & ? & ?): (freshes_vars).
      forwards*: freshes_incr.
      repeat lazymatch goal with
        | [H : Var _ = Var _ |- _] => apply evar_inj in H
        | [H : (lpref _ ++ _)%string = (lpref _ ++ _)%string |- _ ] =>
          apply lpref_inj in H
        end; omega.
    + forwards*: H.
      forwards*: freshes_incr.
      omega.
Qed.    

Lemma scInv_incl GS e (svar_env : SVarEnv GS) seval_env ty (m : member ty GS) :
  In e ((hget svar_env m) |=> sc2CUDA (hget seval_env m)) ->
  In e (scInv svar_env seval_env).
Proof.
  unfold scInv; induction GS; simpl in *;
  dependent destruction m; dependent destruction svar_env; dependent destruction seval_env;
  simpl in *; rewrite in_app_iff; eauto.
Qed.

Lemma remove_gen_vars GS GA
      (svar_env : SVarEnv GS) (seval_env : SEvalEnv GS)
      (avar_env : AVarEnv GA) (aptr_env : APtrEnv GA) (aeval_env : AEvalEnv GA) ty (xs : vars ty) n m :
  freshes ty n = (xs, m) 
  -> aenv_ok avar_env 
  -> senv_ok svar_env n
  -> remove_vars (scInv svar_env seval_env ++ arrInvVar avar_env aptr_env aeval_env) (flatTup xs) =
     (scInv svar_env seval_env ++ arrInvVar avar_env aptr_env aeval_env).
Proof.
intros; repeat rewrite remove_vars_app.
  Lemma remove_gen_vars_senv GS ty n xs m (svar_env : SVarEnv GS) (seval_env : SEvalEnv GS):
    freshes ty n = (xs, m)
    -> senv_ok svar_env n
    -> remove_vars (scInv svar_env seval_env) (flatTup xs) =
       (scInv svar_env seval_env).
  Proof.
    induction GS; simpl;
    dependent destruction svar_env; dependent destruction seval_env;
    intros; unfold scInv in *; simpl.
    - simpl; rewrite* remove_vars_nil.
    - rewrite remove_vars_app, IHGS; eauto.
      f_equal.
      rewrite* remove_vars_disjoint.
      Lemma ents_map ty (xs : vars ty) vs : map ent_e (xs |=> vs) = flatTup xs.
      Proof.
        induction ty; simpl; eauto.
        rewrite map_app; congruence.
      Qed.
      rewrite ents_map.
      apply not_in_disjoint; intros x Hin Hc.
      forwards* (l & (? & ?)): (>>freshes_vars H); substs.
      forwards*: (>>H0 (@HFirst _ a GS)); simpl; eauto; omega.
      intros ty' m' k l ?; forwards*: (>> H0 (@HNext _ ty' a _ m')); simpl.
  Qed.
  
  Lemma remove_gen_vars_aenv GA
        (avar_env : AVarEnv GA) (aptr_env : APtrEnv GA) (aeval_env : AEvalEnv GA) ty (xs : vars ty) n m :
    freshes ty n = (xs, m)
    -> aenv_ok avar_env
    -> remove_vars (arrInvVar avar_env aptr_env aeval_env) (flatTup xs) =
    arrInvVar avar_env aptr_env aeval_env.
  Proof.
    unfold aenv_ok in *.
    induction GA; simpl;
    dependent destruction avar_env; dependent destruction aptr_env; dependent destruction aeval_env; 
    intros; unfold arrInvVar in *; simpl.
    - rewrite* remove_vars_nil.
    - destruct p; rewrite remove_vars_app, IHGA; eauto.
      f_equal.
      rewrite* remove_vars_disjoint; simpl.
      rewrite ents_map.
      destruct H0.
      split.
      + intros Hc; forwards*H': (>>H0 (@HFirst _ a GA)); simpl in H'.
        forwards* (l & (? & ?)): (>>freshes_vars H); substs.
        unfold lpref, append in H'; simpl in H'; congruence.
      + apply not_in_disjoint; intros x Hin Hc.
        forwards*: (>>H1 (@HFirst _ a GA)).
        forwards* (l & (? & ?)): (>>freshes_vars H); substs.
        unfold lpref, append in H2; simpl in H2; congruence.
      + destruct H0; split.
        * intros ty' m'; forwards*: (>> H0 (@HNext _ ty' a _ m')).
        * intros ty' m' ? ?; forwards*: (>> H1 (@HNext _ ty' a _ m')).
  Qed.
  unfold aenv_ok, senv_ok in *.
  rewrites* (>>remove_gen_vars_senv H).
  rewrites* (>>remove_gen_vars_aenv H).
Qed.

Lemma remove_gen_vars_senvZ GS
      (svar_env : SVarEnv GS) (seval_env : SEvalEnv GS)
      (xs : var) n m :
  freshes Skel.TZ n = (xs, m) 
  -> senv_ok svar_env n
  -> remove_var (scInv svar_env seval_env) xs =
     (scInv svar_env seval_env).
Proof.
  intros; forwards*: (>>remove_gen_vars_senv Skel.TZ); simpl in *; eauto.
Qed.

Lemma remove_gen_vars_senvB GS
      (svar_env : SVarEnv GS) (seval_env : SEvalEnv GS)
      (xs : var) n m :
  freshes Skel.TBool n = (xs, m) 
  -> senv_ok svar_env n
  -> remove_var (scInv svar_env seval_env) xs =
     (scInv svar_env seval_env).
Proof.
  intros; forwards*: (>>remove_gen_vars_senv Skel.TBool); simpl in *; eauto.
Qed.

Lemma remove_gen_varsZ GS GA
      (svar_env : SVarEnv GS) (seval_env : SEvalEnv GS)
      (avar_env : AVarEnv GA) (aptr_env : APtrEnv GA) (aeval_env : AEvalEnv GA) (xs : var) n m :
  freshes Skel.TZ n = (xs, m) 
  -> aenv_ok avar_env 
  -> senv_ok svar_env n
  -> remove_var (scInv svar_env seval_env ++ arrInvVar avar_env aptr_env aeval_env) xs =
     (scInv svar_env seval_env ++ arrInvVar avar_env aptr_env aeval_env).
Proof.
  intros; forwards*: (>>remove_gen_vars Skel.TZ); simpl in *; eauto.
Qed.

Lemma remove_gen_vars_aenvZ GA
      (avar_env : AVarEnv GA) (aptr_env : APtrEnv GA) (aeval_env : AEvalEnv GA) (xs : var) n m :
  freshes Skel.TZ n = (xs, m) 
  -> aenv_ok avar_env
  -> remove_var (arrInvVar avar_env aptr_env aeval_env) xs =
     (arrInvVar avar_env aptr_env aeval_env).
Proof.
  intros; forwards*: (>>remove_gen_vars_aenv Skel.TZ); simpl in *; eauto.
Qed.

Lemma remove_gen_vars_aenvB GA
      (avar_env : AVarEnv GA) (aptr_env : APtrEnv GA) (aeval_env : AEvalEnv GA) (xs : var) n m :
  freshes Skel.TZ n = (xs, m) 
  -> aenv_ok avar_env 
  -> remove_var (arrInvVar avar_env aptr_env aeval_env) xs =
     (arrInvVar avar_env aptr_env aeval_env).
Proof.
  intros; forwards*: (>>remove_gen_vars_aenv Skel.TZ); simpl in *; eauto.
Qed.

Lemma remove_gen_varsB GS GA
      (svar_env : SVarEnv GS) (seval_env : SEvalEnv GS)
      (avar_env : AVarEnv GA) (aptr_env : APtrEnv GA) (aeval_env : AEvalEnv GA) (xs : var) n m :
  freshes Skel.TBool n = (xs, m)
  -> aenv_ok avar_env
  -> senv_ok svar_env n
  -> remove_var (scInv svar_env seval_env ++ arrInvVar avar_env aptr_env aeval_env) xs =
     (scInv svar_env seval_env ++ arrInvVar avar_env aptr_env aeval_env).
Proof.
  intros; forwards*: (>>remove_gen_vars Skel.TBool); simpl in *; eauto.
Qed.

Lemma senv_ok_ge GS (svar_env : SVarEnv GS) n m :
  n <= m
  -> senv_ok svar_env n
  -> senv_ok svar_env m.
Proof.
  unfold senv_ok; intros; forwards*: H0; omega.
Qed.    

Lemma compile_op_ok ntrd BS (tid : Fin.t ntrd) ty1 ty2 ty3 (op : Skel.BinOp ty1 ty2 ty3)
      (x : vars ty1) (y : vars ty2) (res : vars ty3) v1 v2 n m Res c env P:
  compile_op op x y n = (c, res, m) ->
  CSL BS tid
      (Assn Res P
            (y |=> sc2CUDA v2 ++ x |=> sc2CUDA v1 ++ env))
      c
      (Assn Res P
            (res |=> sc2CUDA (Skel.opDenote _ _ _ op v1 v2) ++ remove_vars env (flatTup res))).
Proof.
  destruct op; simpl; unfoldM; destruct (freshes _ _) as (? & ?); simpl; inversion 1; substs;
  hoare_forward; repeat rewrite in_app_iff; simpl; eauto;
  prove_imp; repeat rewrite remove_var_app, in_app_iff in *; simpl in *;
  repeat destruct var_eq_dec; simpl in *; substs; try tauto;
  (try now (destruct (eq_dec _ _), (Z.eqb_spec v1 v2); eauto; tauto));
  (try now (destruct (Z_lt_dec _ _), (Z.ltb_spec v1 v2); substs; try tauto; omega)).
Qed.

Lemma remove_gen_vars_res resEnv ty n m xs :
  freshes ty n = (xs, m) ->
  resEnv_ok resEnv n ->
  remove_vars resEnv (flatTup xs) = resEnv.
Proof.
  induction resEnv; simpl; try rewrite remove_vars_nil; eauto.
  intros; rewrite env_assns_removes_cons.
  rewrite IHresEnv; eauto.
  unfold resEnv_ok in *; intros; simpl in *; eauto.
  unfold resEnv_ok in *.
  intros Hc; forwards*(? & ? & ?): freshes_vars.
  destruct a as [y v].
  forwards*: H0; simpl in *; subst; eauto.
  omega.
Qed.

Lemma remove_gen_vars_resZ resEnv n m xs :
  freshes Skel.TZ n = (xs, m) ->
  resEnv_ok resEnv n ->
  remove_var resEnv xs = resEnv.
Proof.
  intros; forwards*: remove_gen_vars_res; eauto.
Qed.

Lemma remove_gen_vars_resB resEnv n m xs :
  freshes Skel.TBool n = (xs, m) ->
  resEnv_ok resEnv n ->
  remove_var resEnv xs = resEnv.
Proof.
  intros; forwards*: remove_gen_vars_res; eauto.
Qed.

Lemma resEnv_ok_ge resEnv n m :
  n <= m
  -> resEnv_ok resEnv n
  -> resEnv_ok resEnv m.
Proof.
  unfold resEnv_ok; intros; forwards*: H0; omega.
Qed.    

Lemma resEnv_ok_cons resEnv n e :
  resEnv_ok (e :: nil) n
  -> resEnv_ok resEnv n
  -> resEnv_ok (e :: resEnv) n.
Proof.
  unfold resEnv_ok; simpl in *.
  intros He Hres; intros.
  destruct H; [forwards*: He| forwards*: Hres].
Qed.

Lemma resEnv_ok_app res1 res2 n :
  resEnv_ok res1 n
  -> resEnv_ok res2 n
  -> resEnv_ok (res1 ++ res2) n.
Proof.
  unfold resEnv_ok; simpl in *.
  intros He Hres; intros.
  rewrite in_app_iff in *.
  destruct H; [forwards*: He| forwards*: Hres].
Qed.    
    
Lemma compile_gen_resEnv_ok GA GS (avar_env : AVarEnv GA) (svar_env : SVarEnv GS)
      ty (se : Skel.SExp GA GS ty) c (xs : vars ty) v n m k :
  aenv_ok avar_env
  -> senv_ok svar_env n
  -> compile_sexp se avar_env svar_env n = (c, xs, m)
  -> m <= k
  -> resEnv_ok (xs |=> v) k.
Proof.
  unfold aenv_ok, senv_ok, resEnv_ok; intros Haenv Hsenv; intros.
  intros; forwards*: (compile_gens).
  Lemma eeq_tup_in ty x v (xs : vars ty) vs:
    In (x |-> v) (xs |=> vs) -> In x (flatTup xs).
  Proof.
    induction ty; simpl; [intros [H|[]]; inverts H; eauto..|].
    rewrite !in_app_iff; intros; firstorder.
  Qed.
  apply eeq_tup_in in H1; eauto.
  simpl; eauto.
  omega.
Qed.

Lemma compile_op_vars ty1 ty2 ty3 (op : Skel.BinOp ty1 ty2 ty3)
      (xs : vars ty1) (ys : vars ty2) (res : vars ty3) n m c:
  compile_op op xs ys n = (c, res, m) ->
  freshes ty3 n = (res, m).
Proof.
  destruct op; simpl; unfoldM; destruct (freshes _ _) eqn:Heq; inversion 1; substs; eauto.
Qed.

Lemma nth_error_ok' T (ls : list T) i d v : List.nth_error ls i = Some v -> nth i ls d = v.
Proof.
  revert ls; induction i; simpl; destruct ls; (try now inversion 1); simpl; intros.
  rewrite IHi; auto.
Qed.

Lemma nth_error_ok T (ls : list T) i d v : nth_error ls i = Some v -> nth (Z.to_nat i) ls d = v.
Proof.
  intros H; forwards*: nth_error_lt.
  unfold nth_error, Z_to_nat_error in *.
  unfoldM_in H; unfold Monad.bind_opt in *; destruct Z_le_dec; try lia.
  eapply nth_error_ok' in H; eauto.
Qed.

Lemma arrInvRes_unfold GA (aptr_env : APtrEnv GA) (aeval_env : AEvalEnv GA)
      ty (m : member ty GA) p :
  exists R,
        (arrInvRes aptr_env aeval_env p ==
        (arrays (val2gl (hget aptr_env m)) (arr2CUDA (hget aeval_env m)) p *** R))%type.
Proof.
  unfold arrInvRes; induction GA; 
  dependent destruction m;
  dependent destruction aptr_env;
  dependent destruction aeval_env; simpl.
  - eexists; reflexivity.
  - forwards*(R & Heq): (>>IHGA m).
    eexists.
    rewrite Heq.
    rewrite res_CA.
    reflexivity.
Qed.

Lemma rule_reads_ainv ntrd BS (tid : Fin.t ntrd) GA GS 
      (svar_env : SVarEnv GS)
      (seval_env : SEvalEnv GS)
      (avar_env : AVarEnv GA)
      (aptr_env : APtrEnv GA)
      (aeval_env : AEvalEnv GA)
      (n m : nat)
      ty (xs : vars ty) resEnv len (aname : vars ty) (ix : vars Skel.TZ) (i : Skel.typDenote Skel.TZ)
      v P R (m' : member ty GA) p :
  senv_ok svar_env n (* fvs are not in the future generated vars *)
  -> aenv_ok avar_env
  -> resEnv_ok resEnv n
  -> hget avar_env m' = (len, aname)
  -> nth_error (hget aeval_env m') i = Some v
  -> disjoint (flatTup xs) (fv_lEs (v2gl aname))
  -> disjoint (flatTup xs) (fv_E ix)
  -> disjoint_list (flatTup xs)
  -> CSL BS tid  (* correctness of gen. code *)
         (Assn (arrInvRes aptr_env aeval_env p *** R) P
               ((ix |=> sc2CUDA i ++ resEnv) ++
                scInv svar_env seval_env ++ arrInvVar avar_env aptr_env aeval_env))
         (reads xs (ty2ctys ty) (v2gl aname +os ix))
         (Assn (arrInvRes aptr_env aeval_env p *** R) P
               ((xs |=> sc2CUDA v ++ remove_vars resEnv (flatTup xs)) ++
                remove_vars (scInv svar_env seval_env ++ arrInvVar avar_env aptr_env aeval_env) (flatTup xs))).
Proof.
  Lemma remove_vars_cons e env xs :
    remove_vars (e :: env) xs = remove_vars (e :: nil) xs ++ remove_vars env xs.
  Proof.
    cutrewrite (e :: env = (e :: nil) ++ env); [|eauto].
    rewrite* remove_vars_app.
  Qed.
  
  intros Hsok Haok Hresok Hget Hnth Hdisj1 Hdisj2 Hdisj3.
  forwards* (R' & Heq): (>>arrInvRes_unfold aptr_env aeval_env m').
  eapply forward; [|applys* (>>rule_reads_arrays xs (arr2CUDA (hget aeval_env m')) (Z.to_nat i))].
  prove_imp; simpl;
  rewrite remove_vars_cons, !remove_vars_app in *;
  repeat rewrite in_app_iff in *; eauto.
  - forwards*: nth_error_lt.
    unfold arr2CUDA, SkelLib.len in *.
    rewrites (>>(@nth_map) v).
    zify; rewrite Z2Nat.id; lia.
    rewrites (>>nth_error_ok Hnth); eauto.
  - Lemma aname_eval GA (avar_env : AVarEnv GA) (aptr_env : APtrEnv GA) (aeval_env : AEvalEnv GA)
          ty (m : member ty GA) len aname :
      hget avar_env m = (len, aname) ->
      evalLExps (arrInvVar avar_env aptr_env aeval_env) (v2gl aname) (val2gl (hget aptr_env m)).
    Proof.
      unfold arrInvVar; induction GA;
      dependent destruction m;
      dependent destruction avar_env;
      dependent destruction aptr_env; 
      dependent destruction aeval_env; simpl; intros; substs.
      
      apply evalLExps_gl.

      apply evalExps_vars.
      repeat rewrite <-app_assoc; simpl.
      apply incl_cons_ig.
      apply incl_app_iff; eauto.
      
      destruct p; simpl.

      apply evalLExps_cons_ig, evalLExps_app_ig; eauto.
    Qed.

    do 2 apply evalLExps_app_ig.
    applys (>>aname_eval Hget).
  - constructor; simpl.
    forwards*: nth_error_lt.
    rewrite Z2Nat.id; try omega; eauto.
  - intros ? s h Hsat; rewrite Heq in Hsat.
    repeat rewrite <-res_assoc in Hsat.
    apply Hsat.
  - unfold arr2CUDA.
    rewrite map_length.
    forwards*: nth_error_lt.
    zify; rewrite Z2Nat.id; try lia.
    unfold SkelLib.len in *; lia.
Qed.

Lemma disjoint_arr_sc GA (avar_env : AVarEnv GA) typ (m : member typ GA) len aname n xs n' :
  aenv_ok avar_env
  -> hget avar_env m = (len, aname)
  -> freshes typ n = (xs, n')
  -> disjoint (flatTup xs) (flatTup aname).
Proof.
  unfold aenv_ok; intros [? ?] ? ?; apply not_in_disjoint; intros.
  forwards* (? & ? & ?): freshes_vars; substs.
  intros Hc; forwards*: (>>H0 m).
  rewrite H1; simpl; eauto.
  simpl in H4.
  congruence.
Qed.
Lemma fv_lEs_v2gl typ (aname : vars typ) : fv_lEs (v2gl aname) = flatTup aname.
Proof.
  unfold v2gl, e2gl, v2e; induction typ; simpl; eauto.
  congruence.
Qed.

Lemma alen_in GA ty (avar_env : AVarEnv GA) (aptr_env : APtrEnv GA) (aeval_env : AEvalEnv GA) 
  (m : member ty GA) len (arr : vars ty) :
  hget avar_env m = (len, arr) 
  -> In (len |-> Zn (length (hget aeval_env m))) (arrInvVar avar_env aptr_env aeval_env).
Proof.
  unfold arrInvVar; induction GA; 
  dependent destruction m;
  dependent destruction avar_env;
  dependent destruction aptr_env;
  dependent destruction aeval_env; simpl; intros; substs; eauto;
  repeat rewrite <-app_assoc; simpl; eauto.
  destruct p; simpl.
  rewrite in_app_iff; eauto.
Qed.

Lemma fvEs_v2e ty (xs : vars ty) : fv_Es (v2e xs) = flatTup xs.
Proof.
  unfold v2e; induction ty; simpl; eauto; congruence.
Qed.

Lemma compile_sexp_ok ntrd BS (tid : Fin.t ntrd) GA GS typ (se : Skel.SExp GA GS typ)
      (svar_env : SVarEnv GS)
      (seval_env : SEvalEnv GS)
      (avar_env : AVarEnv GA)
      (aptr_env : APtrEnv GA)
      (aeval_env : AEvalEnv GA)
      (n m : nat) 
      (v : Skel.typDenote typ) c es resEnv R P p:
  Skel.sexpDenote GA GS typ se aeval_env seval_env = Some v ->
  compile_sexp se avar_env svar_env n = (c, es, m) ->
  (* (forall ty (m : member ty GS), length (hget svar_env m) = len_of_ty ty) -> *)
  (* (forall ty (m : member ty GA), length (snd (hget avar_env m)) = len_of_ty ty) -> *)
  senv_ok svar_env n  -> (* fvs are not in the future generated vars *)
  aenv_ok avar_env ->
  resEnv_ok resEnv n ->
  (* (iii) return exps. don't have future generated vars*)
  CSL BS tid  (* correctness of gen. code *)
      (sexpInv svar_env seval_env avar_env aptr_env aeval_env R P resEnv p)
      c
      (sexpInv svar_env seval_env avar_env aptr_env aeval_env R P (es |=> sc2CUDA v ++ resEnv) p).
Proof.
  revert typ se seval_env svar_env n m v c es R P resEnv.
  induction se;
  introv Heval Hcompile Hsok Haok Hresok;
  unfold bind_opt in Hcompile; unfold sexpInv in *; unfoldM_in Hcompile.
  - (* case of var *)
    inverts Hcompile.
    inverts Heval.
    destruct (freshes _ _) as (? & ?) eqn:Heq.
    eapply forwardR.
    apply rule_assigns; eauto using freshes_disjoint.
    { rewrite fvEs_v2e.
      apply not_in_disjoint; intros; intros Hc; simpl in *.
      forwards* (? & ? & ?): (>>freshes_vars Heq).
      substs; unfold senv_ok in *; forwards*: (>>Hsok).
      omega. }
    { apply evalExps_vars.
      apply incl_app_iff; right; apply incl_app_iff; left; eauto using scInv_incl.
      unfold incl; intros; eapply scInv_incl; eauto. }
    repeat rewrite remove_vars_app.
    rewrites* (>>remove_gen_vars_senv Heq).
    rewrites* (>>remove_gen_vars_aenv Heq).
    rewrites* (>>remove_gen_vars_res Heq).
    prove_imp.
  - (* case const *)
    destruct (freshes _ _) as (? & ?) eqn:Heq.
    inverts Hcompile; inverts Heval; substs.
    hoare_forward.
    repeat rewrite remove_var_app.
    rewrites* (>>remove_gen_vars_senvZ Heq).
    rewrites* (>>remove_gen_vars_aenvZ Heq).
    rewrites* (>>remove_gen_vars_resZ Heq).
  - (* the case of binop *) 
    destruct (compile_sexp se1 _ _ _) as [[? ?] ?] eqn:Hceq1.
    destruct (compile_sexp se2 _ _ _) as [[? ?] ?] eqn:Hceq2.
    destruct (compile_op _ _ _ _) as [[? ?] ?] eqn:Hcop; inverts Hcompile.
    simpl in Heval; unfold Monad.bind_opt in *.
    destruct (Skel.sexpDenote _ _ _ se1 _ _) eqn:Heval1; [|inverts Heval].
    destruct (Skel.sexpDenote _ _ _ se2 _ _) eqn:Heval2; inverts Heval.
    forwards*: (>>compile_don't_decrease Hceq1).
    forwards*: (>>compile_don't_decrease Hceq2).
    
    eapply rule_seq; [forwards*: IHse1|].
    eapply rule_seq; [forwards*: IHse2|]; eauto using senv_ok_ge, resEnv_ok_ge.
    apply resEnv_ok_app; [|eauto using resEnv_ok_ge].
    forwards*: compile_gen_resEnv_ok.
    repeat rewrite <-app_assoc.
    eapply forward; [|forwards*: (>>compile_op_ok Hcop); eauto using resEnv_ok_ge].
    repeat rewrite remove_vars_app.
    forwards*Heq: compile_op_vars.
    rewrites* (>>remove_gen_vars_senv Heq); eauto using senv_ok_ge.
    rewrites* (>>remove_gen_vars_aenv Heq).
    rewrites* (>>remove_gen_vars_res Heq); eauto using resEnv_ok_ge.
  - destruct (compile_sexp se _ _ _) as [[? ?] ?] eqn:Hceq1.
    destruct (hget avar_env m) as [? aname] eqn:Haeq.
    destruct (freshes _ _) as [? ?] eqn:Hfreq; inverts Hcompile.

    simpl in Heval; unfold Monad.bind_opt in *.
    destruct (Skel.sexpDenote _ _ _ se _ _) eqn:Heval1; try now inverts Heval.
    
    forwards*: (>>compile_don't_decrease Hceq1).
    eapply rule_seq; [forwards*: IHse|].
    eapply forward; [|forwards*: rule_reads_ainv].
    prove_imp;
      try rewrite !remove_vars_app; rewrite !in_app_iff;
      (rewrites* (>>remove_gen_vars_senv Hfreq); eauto using senv_ok_ge;
       rewrites* (>>remove_gen_vars_aenv Hfreq); 
       rewrites* (>>remove_gen_vars_res Hfreq); eauto using resEnv_ok_ge);
    eauto using freshes_disjoint.

    rewrite fv_lEs_v2gl; eauto using disjoint_arr_sc.

    apply not_in_disjoint; intros; intros [Hc | []]; simpl in *.
    forwards*(? & ? & ?): (>>freshes_vars Hfreq).
    forwards*: (>>compile_gens Hceq1); substs; eauto.
    simpl; eauto.
    simpl; eauto.
    omega.

    forwards*: freshes_disjoint.
  - destruct (hget avar_env m) as [l ?] eqn:Heq.
    destruct (freshes _ _) as [? ?] eqn:Hceq; inverts Hcompile.
    simpl in Heval; inverts Heval. 
    hoare_forward.
    repeat rewrite in_app_iff; forwards*: alen_in.
    repeat rewrite remove_var_app.
    rewrites* (>>remove_gen_vars_senvZ Hceq).
    rewrites* (>>remove_gen_vars_aenvZ Hceq).
    rewrites* (>>remove_gen_vars_resZ Hceq).
  - destruct (compile_sexp se1 _ _ _) as [[? ?] ?] eqn:Hceq1.
    destruct (compile_sexp se2 _ _ _) as [[? ?] ?] eqn:Hceq2.
    destruct (compile_sexp se3 _ _ _) as [[? ?] ?] eqn:Hceq3.
    destruct (freshes _ _) as [? ?] eqn:Hfreq; inverts Hcompile.
    simpl in Heval; unfold Monad.bind_opt in Heval.
    destruct (Skel.sexpDenote  _ _ _ se1 _ _)  as [?|] eqn:Heval1; [|inverts Heval].
    destruct (Skel.sexpDenote  _ _ _ se2 _ _)  as [?|] eqn:Heval2; [|inverts Heval].
    destruct (Skel.sexpDenote  _ _ _ se3 _ _)  as [?|] eqn:Heval3; [|inverts Heval];
    inverts Heval.
    forwards*: (>>compile_don't_decrease Hceq1).
    forwards*: (>>compile_don't_decrease Hceq2).
    forwards*: (>>compile_don't_decrease Hceq3).
    eapply rule_seq; [forwards*: IHse1|].
    Opaque EEq_tup.
    hoare_forward.
    Transparent EEq_tup.
    simpl; eauto.
    + eapply rule_seq.
      applys* IHse2; eauto using senv_ok_ge, resEnv_ok_ge.
      apply resEnv_ok_app; eauto using resEnv_ok_ge.
      applys* compile_gen_resEnv_ok.
      eapply rule_assigns.

      rewrite fvEs_v2e.
      apply not_in_disjoint; intros; intros Hc; simpl in *.
      forwards* (? & ? & ?): (>>freshes_vars Hfreq).
      forwards*: (>>compile_gens Hceq2); simpl; substs; eauto using senv_ok_ge.
      omega.
      applys* freshes_disjoint. 
      apply evalExps_vars; rewrite <-app_assoc; apply incl_app_iff; eauto.
    + eapply rule_seq.
      applys* IHse3; eauto using senv_ok_ge, resEnv_ok_ge.
      apply resEnv_ok_app; eauto using resEnv_ok_ge.
      applys* compile_gen_resEnv_ok.
      eapply rule_assigns.

      rewrite fvEs_v2e.
      apply not_in_disjoint; intros; intros Hc; simpl in *.
      forwards* (? & ? & ?): (>>freshes_vars Hfreq).
      forwards*: (>>compile_gens Hceq3); simpl; substs; eauto using senv_ok_ge.
      omega.
      applys* freshes_disjoint. 
      apply evalExps_vars; rewrite <-app_assoc; apply incl_app_iff; eauto.
    + repeat rewrite remove_vars_app.
      repeat (rewrites* (>>remove_gen_vars_senv Hfreq); eauto using senv_ok_ge).
      repeat (rewrites* (>>remove_gen_vars_aenv Hfreq)).
      repeat (rewrites* (>>remove_gen_vars_res Hfreq);
               try now applys* (>>resEnv_ok_ge Hresok); omega).
      applys* (>>compile_gen_resEnv_ok Hceq2); eauto using senv_ok_ge.
      applys* (>>compile_gen_resEnv_ok Hceq1); eauto using senv_ok_ge; omega.
      applys* (>>compile_gen_resEnv_ok Hceq3); eauto using senv_ok_ge; omega.
      prove_imp; simpl; destruct H3; destruct t0; try omega; eauto.
  - destruct (compile_sexp se1 _ _ _) as [[? ?] ?] eqn:Hceq1.
    destruct (compile_sexp se2 _ _ _) as [[? ?] ?] eqn:Hceq2; inverts Hcompile.
    simpl in Heval; unfold Monad.bind_opt in *.
    destruct (Skel.sexpDenote _ _ _ se1 _ _) eqn:Heval1; [|inverts Heval].
    destruct (Skel.sexpDenote _ _ _ se2 _ _) eqn:Heval2; inverts Heval.
    forwards*: (>>compile_don't_decrease Hceq1).
    eapply rule_seq.
    forwards*: IHse1.
    eapply forwardR.
    forwards*: IHse2; eauto using senv_ok_ge.
    apply resEnv_ok_app; eauto using resEnv_ok_ge.
    applys* (>>compile_gen_resEnv_ok Hceq1).
    prove_imp.
  - destruct (compile_sexp se _ _ _) as [[? ?] ?] eqn:Hceq1; inverts Hcompile.
    simpl in Heval; unfold Monad.bind_opt in *.
    destruct (Skel.sexpDenote _ _ _ se _ _) eqn:Heval1; inverts Heval.
    eapply forwardR.
    forwards*: IHse.
    prove_imp.
  - destruct (compile_sexp se _ _ _) as [[? ?] ?] eqn:Hceq1; inverts Hcompile.
    simpl in Heval; unfold Monad.bind_opt in *.
    destruct (Skel.sexpDenote _ _ _ se _ _) eqn:Heval1; inverts Heval.
    eapply forwardR.
    forwards*: IHse.
    prove_imp.
  - destruct (compile_sexp se1 _ _ _) as [[? ?] ?] eqn:Hceq1.
    destruct (freshes _ _) as [? ?] eqn:Hfreq.
    destruct (compile_sexp se2 _ _ _) as [[? ?] ?] eqn:Hceq2; inverts Hcompile. 
    simpl in Heval; unfold Monad.bind_opt in Heval.
    destruct (Skel.sexpDenote _ _ _ se1 _ _) eqn:Heval1; [|inverts Heval].
    destruct (Skel.sexpDenote _ _ _ se2 _ _) eqn:Heval2; inverts Heval.
    
    forwards*: (>>compile_don't_decrease Hceq1).
    forwards*: freshes_incr.

    eapply rule_seq.
    applys* IHse1.
    eapply rule_seq.
    
    applys* rule_assigns.
    { rewrite fvEs_v2e.
      apply not_in_disjoint; intros; intros Hc; simpl in *.
      forwards* (? & ? & ?): (>>freshes_vars Hfreq).
      forwards*: (>>compile_gens Hceq1); simpl; substs; eauto using senv_ok_ge.
      omega. }
    { applys* freshes_disjoint. }
    { apply evalExps_vars.
      rewrite <-app_assoc.
      applys* incl_app_iff. }
    rewrite !remove_vars_app.
    rewrites* (>>remove_gen_vars_senv Hfreq);  eauto using senv_ok_ge.
    rewrites* (>>remove_gen_vars_aenv Hfreq).
    repeat (rewrites* (>>remove_gen_vars_res Hfreq);
             try now applys* (>>resEnv_ok_ge Hresok); omega).
    applys* compile_gen_resEnv_ok.
    
    eapply rule_conseq.
    applys* (>>IHse2 P).
    { unfold senv_ok in *; intros.
      dependent destruction m0; simpl in *.
      - forwards* (? & ? & ?): freshes_vars.
        apply evar_inj, lpref_inj in H2; omega.
      - forwards*: (>>Hsok m0); omega. }
    { applys* (>>resEnv_ok_ge Hresok); omega. }
    prove_imp; eauto.
    { unfold scInv in *; simpl in *; rewrite in_app_iff in *; tauto. }
    prove_imp; eauto.
    unfold scInv in *; simpl in *; rewrite in_app_iff in *; tauto.
Qed.

Lemma freshes_prefix ty n m res :
  freshes ty n = (res, m) 
  -> forall l, In l (flatTup res) -> is_local l.
Proof.
  Transparent freshes.
  unfold freshes; unfoldM; simpl; intros H l Hin; inverts H.
  forwards*(? & ? & ?): locals_pref; substs.
  unfold is_local, lpref; simpl; rewrite prefix_nil; auto.  
Qed.
Opaque freshes.

Lemma compile_op_wr_vars' t1 t2 t3 (op : Skel.BinOp t1 t2 t3) xs ys n c res m :
  compile_op op xs ys n = (c, res, m)
  -> forall l, In l (writes_var c) -> is_local l.
Proof.
  destruct op; simpl; unfoldM; inversion 1; substs; simpl;
  repeat destruct (freshes _ _) eqn:Heq; simpl; intros; forwards*: freshes_prefix;
  destruct H0 as [|[]]; substs; simpl; eauto.
Qed.

Ltac compile_sexp_des Hceq :=
  repeat match type of Hceq with
  | (_, _) = (_, _) => inverts Hceq
  | context [compile_sexp ?se ?aenv ?senv ?n] => destruct (compile_sexp se aenv senv n) as [[? ?] ?] eqn:?
  | context [compile_op ?op ?xs ?ys ?n] => destruct (compile_op op xs ys n) as [[? ?] ?] eqn:?
  | context [hget ?ls ?m] => destruct (hget ls m) as [? ?] eqn:?
  | context [freshes ?ty ?n] => destruct (freshes ty n) as [? ?] eqn:?
  end.

Lemma compile_sexp_wr_vars GA GS (avar_env : AVarEnv GA) (svar_env : SVarEnv GS) typ (se : Skel.SExp GA GS typ) n m c res :
  compile_sexp se avar_env svar_env n = (c, res, m)
  -> forall l, In l (writes_var c) -> is_local l.
Proof.
  unfold is_local;
  revert svar_env n m c res; induction se; simpl; 
  intros svar_env n m' c res; unfoldM; intros Hceq;
  compile_sexp_des Hceq;
  simpl; introv; repeat rewrite in_app_iff;
  let H := fresh in intros H; des_disj H;
  try first [tauto | now forwards*: IHse | now forwards*: IHse1 | now forwards*: IHse2 | now forwards*: IHse3];
  try no_side_cond ltac:(forwards*: assigns_writes);
  try no_side_cond ltac:(forwards*: reads_writes);
  (try now forwards*: compile_op_wr_vars');
  try forwards*: freshes_prefix;
  substs; simpl; eauto.
Qed.

Lemma compile_op_res_vars t1 t2 t3 (op : Skel.BinOp t1 t2 t3) xs ys n c res m :
  compile_op op xs ys n = (c, res, m)
  -> forall l, In l (flatTup res) -> is_local l.
Proof.
  destruct op; simpl; unfoldM; intros Hceq;
  compile_sexp_des Hceq; intros l H; des_disj H;
  forwards*: freshes_prefix; substs; simpl; eauto.
Qed.

Lemma compile_sexp_res_vars GA GS (avar_env : AVarEnv GA) (svar_env : SVarEnv GS) typ (se : Skel.SExp GA GS typ) n m c res :
  compile_sexp se avar_env svar_env n = (c, res, m)
  -> forall l, In l (flatTup res) -> is_local l.
Proof.
  revert svar_env n m c res; induction se; simpl;
  intros svar_env n m' c res; unfoldM; intros Hceq;
  compile_sexp_des Hceq;
  repeat rewrite in_app_iff;
  let H := fresh in introv H;
  repeat rewrite in_app_iff in H; des_disj H;
  (try first [now forwards*: freshes_prefix |
              now forwards*: freshes_prefix; subst; simpl; eauto |
              now forwards*: IHse | now forwards*: IHse1 | now forwards*: IHse2 | now forwards*: IHse3 ]).
  forwards*: compile_op_res_vars.
  destruct v; forwards*: IHse; simpl in *; rewrites* in_app_iff.
  destruct v; forwards*: IHse; simpl in *; rewrites* in_app_iff.
Qed.

Lemma assigns_no_barrs ty (xs : vars ty) tys es : barriers (assigns xs tys es) = nil.
Proof.
  induction ty; simpl; eauto; rewrite IHty1, IHty2; auto.
Qed.

Lemma reads_no_barrs ty (xs : vars ty) tys es : barriers (reads xs tys es) = nil.
Proof.
  induction ty; simpl; eauto; rewrite IHty1, IHty2; auto.
Qed.

Lemma writes_no_barrs ty (les : lexps ty) es : barriers (writes les es) = nil.
Proof.
  induction ty; simpl; eauto; rewrite IHty1, IHty2; auto.
Qed.

Lemma compile_op_no_barrs t1 t2 t3 (op : Skel.BinOp t1 t2 t3) xs ys n c res m :
  compile_op op xs ys n = (c, res, m)
  -> barriers c = nil.
Proof.
  destruct op; simpl; unfoldM; intros Hceq; compile_sexp_des Hceq; simpl; auto.
Qed.

Lemma compile_sexp_no_barrs GA GS (avar_env : AVarEnv GA) (svar_env : SVarEnv GS) typ (se : Skel.SExp GA GS typ) n m c res :
  compile_sexp se avar_env svar_env n = (c, res, m)
  -> barriers c = nil.
Proof.
  revert c res n m; induction se; simpl; unfoldM; intros c res n m' Hceq;
  compile_sexp_des Hceq; simpl;
  try rewrites (IHse);
  try rewrites IHse1;
  try rewrites IHse2;
  try rewrites IHse3;
  try repeat rewrites assigns_no_barrs;
  try rewrites reads_no_barrs;
  try rewrites writes_no_barrs; eauto.
  rewrites (>>IHse1 Heqp); rewrites (>>IHse2 Heqp0); rewrites (>>compile_op_no_barrs Heqp1); auto.
  rewrites (>>IHse Heqp); auto.
  rewrites (>>IHse1 Heqp); rewrites (>>IHse2 Heqp0); rewrites (>>IHse3 Heqp1); auto.
  rewrites (>>IHse1 Heqp); rewrites (>>IHse2 Heqp0); auto.
  rewrites (>>IHse1 Heqp); rewrites (>>IHse2 Heqp1); auto.
Qed.

Ltac des_mem := 
  let t := lazymatch goal with
      | [m : member _ _ |- _] => m
      end in dependent destruction m.

Lemma resEnv_ok0_is_local resEnv : 
  (forall l v, In (l |-> v) resEnv -> ~is_local l) -> resEnv_ok resEnv 0.
Proof.
  unfold resEnv_ok; intros H; intros; forwards*: H;
  unfold is_local, lpref in *; simpl in *; rewrite prefix_nil in *; try congruence.
Qed.

Lemma evalExps_env ty R P Env1 Env2 (xs : vars ty) vs s h:
  evalExps Env1 (v2e xs) vs
  -> sat s h (Assn R P (Env1 ++ Env2))
  -> sat s h (Assn R P (Env1 ++ (xs |=> vs ++ Env2))).
Proof.
  unfold sat, Assn; intros ? Hsat; sep_split_in Hsat; sep_split; eauto.
  rewrite !env_assns_app in *; repeat split; try tauto.
  clear HP Hsat; induction ty; simpl; eauto;
  inverts H; simpl in *;
  try (split; eauto using emp_emp_ph; forwards*: env_denote_in).
  rewrite env_assns_app; split; eauto.
Qed.
                         
Lemma compile_func_ok GA fty (f : Skel.Func GA fty) (func : type_of_ftyp fty) (avar_env : AVarEnv GA) : 
  compile_func f avar_env = func -> func_ok avar_env f func.
Proof.
  destruct fty; intros Hcp; simpl in *; substs; dependent destruction f; simpl;
  repeat split; introv; unfold evalM;
  destruct (compile_sexp _ _ _ _) as [[? ?] ?] eqn:Heq; simpl in *;
  eauto using compile_sexp_no_barrs, compile_sexp_wr_vars, compile_sexp_res_vars, compile_sexp_ok;
  unfold are_local; [intros Hx ? ? ?| intros Hx Hy ? ? ? ?];
  forwards*Htri: compile_sexp_ok; eauto using resEnv_ok0_is_local; unfold kernelInv, sexpInv, scInv in *; simpl in *;
  (* try first [eapply rule_conseq; try apply Htri; prove_imp; eauto; simpl in *; try tauto | (* discharging triples *) *)
  try (unfold senv_ok, is_local in *; introv Hin; false;
       repeat des_mem; simpl in *;
       try no_side_cond ltac:(forwards* Hin': Hx);
       try no_side_cond ltac:(forwards* Hin': Hy);
       unfold lpref in Hin'; simpl in *; rewrite prefix_nil in Hin'; congruence).
  eapply rule_conseq; try apply Htri; try now (prove_imp; eauto; simpl in *; try tauto).
  intros s' h H'; forwards*Hsat: evalExps_env; clear H'; revert s' h Hsat; prove_imp; simpl in *; try tauto.
  eapply rule_conseq; try apply Htri; try now (prove_imp; eauto; simpl in *; try tauto).
  intros s' h H'; forwards* Hsat: (>>evalExps_env H1).
  forwards* Hsat': (>>evalExps_env H2 Hsat).
  clear H' Hsat; revert s' h Hsat'; prove_imp; simpl in *; tauto.
Qed.

Lemma nth_error_some T (ls : list T) i d :
  i < length ls
  -> List.nth_error ls i = Some (nth i ls d).
Proof.
  revert ls; induction i; simpl; destruct ls; simpl in *; intros; try omega.
  reflexivity.
  intuition.
Qed.

Lemma nth_error_some' T (ls : list T) (i : Z) d :
  (0 <= i < Zn (length ls))%Z
  -> nth_error ls i = Some (nth (Z.to_nat i) ls d).
Proof.
  unfold nth_error; simpl; unfoldM; unfold Monad.bind_opt.
  intros.
  unfold Z_to_nat_error; destruct Z_le_dec; try lia; simpl.
  apply nth_error_some.
  zify; rewrite Z2Nat.id; lia.
Qed.

Lemma mapM_some A B (xs : list A) (ys : list B) i d1 d2 f :
    mapM f xs = Some ys ->
    Some (nth i ys d2) = if lt_dec i (length xs) then f (nth i xs d1) else Some d2.
Proof.
  unfold mapM; revert i ys; induction xs; simpl; introv Heq;
  destruct i, ys; try inverts Heq; simpl; eauto.
  - unfold Monad.bind_opt in *.
    destruct (f a) eqn:Heq1; inverts H0.
    destruct (sequence _); inverts H1.
  - unfold Monad.bind_opt in *.
    destruct (f a) eqn:Heq1; inverts H0.
    destruct (sequence _) eqn:Heq2; inverts H1; eauto.
  - unfold Monad.bind_opt in *.
    destruct (f a) eqn:Heq1; inverts H0.
    destruct (sequence _) eqn:Heq2; inverts H1; eauto.
  - unfold Monad.bind_opt in *.
    destruct (f a) eqn:Heq1; inverts H0.
    destruct (sequence _) eqn:Heq2; inverts H1; eauto.
    erewrite IHxs; destruct (lt_dec i (length xs)), (lt_dec (S i) (S (length xs))); try lia;
    eauto.
Qed.

    
Lemma mapM_length A B (xs : list A) (ys : list B) f :
  mapM f xs = Some ys -> length ys = length xs.
Proof.
  revert ys; unfold mapM; induction xs; introv.
  - inversion 1; eauto.
  - simpl.
    unfold Monad.bind_opt; destruct (f a), (@sequence _ _ _); simpl;
    destruct ys; inversion 1; substs; simpl; rewrite IHxs; eauto.
Qed.

Lemma seq'_length n m : length (seq' n m) = m.
Proof.
  revert n; induction m; simpl; congruence.
Qed.

Lemma seq'_nth n m i d : nth i (seq' n m) d = if lt_dec i m then (n + Zn i)%Z else d.
Proof.
  revert n i; induction m; simpl; intros n [|i]; eauto.
  destruct lt_dec; eauto; try lia.
  rewrites IHm.
  repeat destruct lt_dec; try lia.
Qed.

Lemma seq_length n m : length (seq n m) = Z.to_nat m.
Proof.
  unfold seq; rewrite seq'_length; eauto.
Qed.

Lemma seq_nth n m i d : nth i (seq n m) d = if lt_dec i (Z.to_nat m) then (n + Zn i)%Z else d.
Proof.
  unfold seq; apply seq'_nth.
Qed.


Lemma compile_AE_ok GA ty (ae : Skel.AE GA ty) (arr : var -> cmd * vars ty) (avar_env : AVarEnv GA) :
  compile_AE ae avar_env = arr -> ae_ok avar_env ae arr.
Proof.
  unfold ae_ok; destruct ae; simpl; intros Hceq Haok.
  - unfold accessor_of_array in Hceq.
    forwards*Hok: (>>compile_func_ok (Skel.Fun1 Skel.TZ t) arr Hceq Haok).
    simpl in *; unfold func_ok1 in *; repeat split; jauto.
    destruct Hok as (? & ? & Hok & ?).
    intros; forwards*: Hok.
    introv [? | []]; substs; eauto.
    intros. 
    inverts H5.
    erewrite nth_error_some'.
    rewrite Nat2Z.id.
    reflexivity.
    lia.
  - forwards*: (>>compile_func_ok (Skel.Fun1 Skel.TZ cod) Hceq Haok).
    unfold func_ok, func_ok1 in *; simpl in *.
    destruct H as (H1 & H2 & H3 & H4).
    repeat split; [apply H1| apply H2| idtac | apply H4].
    intros; forwards*: H3.
    intros ? [? | []]; substs; eauto.
    
    rewrites* (>>mapM_some i (@defval' cod) H6).
    forwards*: mapM_length.
    
    repeat rewrite seq_length in *.
    destruct lt_dec; try lia.
    repeat rewrite seq_nth.
    destruct lt_dec; eauto.
Qed.