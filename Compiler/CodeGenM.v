Require Import Monad DepList GPUCSL TypedTerm Compiler.
Require Import Program.Equality LibTactics.
Require Import CUDALib CodeGen CSLLemma CSLTactics Correctness mkMap.
Import Skel_lemma.
Require Import SkelLib Psatz Host.

Lemma rule_host_backward GM G P Q Q' C :
  CSLh_n GM G P C Q
  -> Q |= Q' -> CSLh_n GM G P C Q'.
Proof.
  unfold CSLh_n, CSLh_n_simp; intros.
  eauto using safe_nh_conseq.
Qed.  

Lemma rule_host_ex GM G T (P : T -> assn) Q C :
  (forall x, CSLh_n GM G (P x) C Q)
  -> CSLh_n GM G (Ex x, P x) C Q.
Proof.
  unfold CSLh_n, CSLh_n_simp; intros.
  destruct H1.
  eapply H; eauto.
Qed.

Lemma evalExp_removes Env xs e v :
  disjoint xs (fv_E e) ->
  evalExp Env e v ->
  evalExp (remove_vars Env xs) e v.
Proof.
  revert Env; induction xs; simpl; eauto; introv [? ?] Heval.
  rewrite <-remove_removes.
  apply IHxs; eauto.
  apply evalExp_remove; eauto.
Qed.

Lemma combine_map_fst T1 T2 (xs : list T1) (ys : list T2) : 
  length xs = length ys 
  -> map fst (combine xs ys) = xs.
Proof.
  revert ys; induction xs; intros [|? ?] Hlen; simpl in *; try congruence.
  rewrite IHxs; eauto.
Qed.

Lemma combine_map_snd T1 T2 (xs : list T1) (ys : list T2) : 
  length xs = length ys 
  -> map snd (combine xs ys) = ys.
Proof.
  revert ys; induction xs; intros [|? ?] Hlen; simpl in *; try congruence.
  rewrite IHxs; eauto.
Qed.

Axiom inde_fv_equiv :
  forall R P E xs,
    inde (Assn R P E) xs <-> (forall x v, In (x |-> v) E -> ~In x xs).

Lemma rule_host_allocs GM G R P E ty (xs : vars ty) e l :
  evalExp E e (Zn l)
  -> disjoint (flatTup xs) (fv_E e)
  -> disjoint_list (flatTup xs)
  -> CSLh_n GM G
            (Assn R P E)
            (alloc_tup_arr xs e)
            (Ex (ps : vals ty) (vs : list (vals ty)),
              Assn (arrays (val2gl ps) vs 1 *** R) (length vs = l /\ P)
                   (EEq_tup xs ps ++ remove_vars E (flatTup xs))).
Proof.
  intros; revert R P E H; induction ty; introv Heval; simpl.
  - eapply rule_host_backward; [applys* rule_host_alloc|].
    intros s h (? & ? & Hsat); revert s h Hsat; prove_imp.
    rewrites* mkReduce.arrays_TB.
  - eapply rule_host_backward; [applys* rule_host_alloc|].
    intros s h (? & ? & Hsat); revert s h Hsat; prove_imp.
    rewrites* mkReduce.arrays_TZ.
  - simpl in *; eapply rule_host_seq.
    { applys* IHty1; eauto using disjoint_app_r1, disjoint_list_proj1, disjoint_comm. }
    apply rule_host_ex; intros ps1.
    apply rule_host_ex; intros vs1.
    eapply rule_host_backward.
    { apply IHty2; eauto using disjoint_app_r2, disjoint_list_proj2, disjoint_comm.
      apply evalExp_app_ig.
      apply evalExp_removes; eauto using disjoint_app_r1, disjoint_comm. }
    repeat rewrite remove_vars_app.
    rewrite mpss_remove_vars; eauto using disjoint_list_app_disjoint.
    intros s h (ps2 & vs2 & Hsat).
    exists (ps1, ps2) (combine vs1 vs2).
    revert s h Hsat; prove_imp.
    + rewrite remove_vars_nest in *; eauto.
    + unfold val2gl in *; simpl.
      Require Import SetoidClass.
      rewrite mkReduce.arrays_TTup; simpl.
      rewrite <-res_assoc.
      repeat sep_cancel'; [rewrite combine_map_fst|rewrite combine_map_snd]; congruence.
    + unfold vals in *; simpl in *.
      rewrite (combine_length vs1 vs2).
      rewrite Nat.min_r; omega.
Qed.

Definition assnST : Type := nat -> stmt -> GModule -> Prop.

Definition ST_ok {T} (P : assnST) (gen : CUDAM T) (Q : T -> assnST) :=
  forall n n' st st' GM GM' v,
    P n st GM 
    -> gen (n, (st, GM)) = (v, (n', (st', GM')))
    -> Q v n' st' GM'.

Definition FC_ok (G : FC) : assnST := fun _ _ gm => sat_FC gm G G.
Parameter fv_assn : assn -> list var -> Prop.
Axiom fv_assn_ok : forall P xs ys,
    fv_assn P xs -> disjoint xs ys -> inde P ys.
Axiom fv_assn_base :
  forall R P E xs, fv_assn (Assn R P E) xs <-> incl (List.map ent_e E) xs.
Axiom fv_assn_Ex :
  forall T (P : T -> assn) xs, fv_assn (Ex v, P v) xs <-> (forall v, fv_assn (P v) xs).

Definition hvar n := Var ("h" ++ nat2str n).

Definition usable_var x n : Prop := forall m, x = hvar m -> m < n.

Definition usable (xs : list var) n : Prop :=
  List.Forall (fun x => usable_var x n) xs.

Definition code_ok G P Q xs ys : assnST := fun n s GM =>
  sat_FC GM G G /\ CSLh_n GM G P s Q /\ usable xs n /\ usable ys n /\
  fv_assn Q xs /\ disjoint ys xs.

(* Definition code_ok G P Q : assnST :=  *)
(*   fun _ c gm => CSLh_n gm G P c Q. *)
(* Definition usable_vars xs : assnST := fun n _ _ => usable_vars_pure xs n. *)

(* Definition env_ok xs P := incl (fv_assn P) xs. *)

(* Definition andST (P Q : assnST) := fun n st gm => P n st gm /\ Q n st gm.   *)

(* Definition assn_ok n P :=  *)
(*   (forall m, n <= m -> inde P (Var ("h" ++ nat2str m)%string :: nil)). *)

(* Definition prog_ok G P Q : assnST := *)
(*   fun n st GM => *)
(*     assn_ok n P /\ assn_ok n Q *)
(*     /\ sat_FC GM G G /\ CSLh_n GM G P st Q. *)

(* Definition gmST (f : GModule -> Prop) : assnST := fun _ _ GM => f GM. *)

(* Definition assn_ok' R : assnST := fun n _ _ => assn_ok n R. *)

(* Infix "/\ST" := andST (at level 80, right associativity). *)

(* Definition gmnST (f : nat -> GModule -> Prop) : assnST := fun n _ GM => f n GM. *)

Lemma hvar_inj m n : hvar m = hvar n -> m = n.
Proof.
  unfold hvar; intros H.
  inverts H.
  forwards*: (>>nat_to_string_inj H1).
Qed.

Lemma lt_usable_var n m :
  m < n -> usable_var (hvar m) n.
Proof.
  intros Hmn m' Heq.
  forwards*: (>>hvar_inj Heq); omega.
Qed.

Lemma usable_var_lt n m :
  usable_var (hvar m) n -> m < n.
Proof.
  unfold usable_var; intros H.
  forwards*: (H m).
Qed.

Lemma usable_var_weaken x n m : 
  m < n -> usable_var x m  -> usable_var x n.
Proof.
  unfold usable_var; intros.
  forwards*: H0; omega.
Qed.

Lemma usable_weaken n m xs  :
  m < n 
  -> usable xs m -> usable xs n.
Proof.
  intros Hmn H; induction H; constructor; eauto using usable_var_weaken.
Qed.

Lemma rule_fresh G P Q xs ys:
  ST_ok (code_ok G P Q xs ys) 
        fresh
        (fun y => code_ok G P Q xs (y :: ys)).
Proof.
  unfold ST_ok, fresh, setS, code_ok.
  introv (Hfs & Htri & Hxs & Hys & Henv & Hdisj) Heq.
  inverts Heq.
  splits; eauto.
  - applys (>>usable_weaken Hxs); omega.
  - constructor.
    + apply lt_usable_var; omega.
    + applys (>>usable_weaken Hys); omega.
  - split; eauto.
    intros Hc.
    unfold usable in Hxs; rewrite Forall_forall in Hxs.
    forwards* H: Hxs.
    apply usable_var_lt in H; omega.
Qed.  

Fixpoint remove_xs (xs : list var) (ys : list var) :=
  match xs with
  | nil => nil
  | x :: xs => if in_dec var_eq_dec x ys then remove_xs xs ys else x :: remove_xs xs ys
  end.

Lemma disjoint_remove_xs xs ys :
  disjoint (remove_xs xs ys) ys.
Proof.
  induction xs; simpl; eauto.
  destruct in_dec; eauto.
  simpl; eauto.
Qed.

Lemma Forall_app T (xs ys : list T) P :
  List.Forall P xs -> List.Forall P ys -> List.Forall P (xs ++ ys).
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma usable_app xs ys n :
  usable xs n -> usable ys n -> usable (xs ++ ys) n.
Proof.
  unfold usable; eauto using Forall_app.
Qed.

Lemma incl_nil_r T (xs : list T) : 
  incl xs nil -> xs = nil.
Proof.
  induction xs; simpl; eauto.
  intros H; unfold incl in H; forwards*: (H a).
Qed.

Lemma Forall_incl T (xs ys : list T) P :
  List.Forall P xs -> incl ys xs -> List.Forall P ys.
Proof.
  induction 1; simpl; eauto.
  - intros H; apply incl_nil_r in H; substs; eauto.
  - intros Hincl; rewrite Forall_forall in * ; unfold incl in *.
    intros a Hain.
    forwards* Hincl': (>>Hincl Hain); destruct Hincl' as [? | Hincl']; substs; eauto.
Qed.

Lemma usable_incl xs ys n :
  usable xs n -> incl ys xs -> usable ys n.
Proof. unfold usable; eauto using Forall_incl. Qed.

Lemma remove_xs_incl xs ys :
  incl (remove_xs xs ys) xs.
Proof.
  unfold incl; induction xs; simpl; eauto.
  intros x; destruct in_dec; eauto.
  intros [? | ?]; eauto.
Qed.

Lemma rule_setI G P Q R ss xs xs' ys :
  (forall GM, CSLh_n GM G Q ss R)
  -> (fv_assn R (xs ++ xs'))
  -> (incl xs' ys)
  -> ST_ok (code_ok G P Q xs ys)
           (setI ss)
           (fun _ => code_ok G P R (xs ++ xs') (remove_xs ys xs')).
Proof.
  unfold ST_ok, setI, setS, code_ok.
  introv Htri Hfv Hxs' (Hfs & Htr & Hxs & Hys & Henv & Hdisj) Heq; simpl in *.
  inverts Heq; splits; jauto.   
  - eapply rule_host_seq; eauto.
  - apply usable_app; eauto.
    applys* usable_incl.
  - eapply usable_incl; [|eauto using remove_xs_incl]; eauto.
  - rewrite disjoint_app; split; eauto.
    + apply disjoint_comm; applys (>>disjoint_incl ys); eauto using disjoint_comm.
      apply remove_xs_incl.
    + apply disjoint_remove_xs.
Qed.  

Definition nST P : assnST := fun n _ _ => P n.

Instance CUDAM_Monad : Monad CUDAM := state_Monad _.

Lemma rule_bind T1 T2 P (Q Q' : T1 -> assnST) R (gen : CUDAM T1) (gen' : T1 -> CUDAM T2) :
  ST_ok P gen Q
  -> (forall x n st gm, Q x n st gm -> Q' x n st gm)
  -> (forall x, ST_ok (Q' x) (gen' x) R)
  -> ST_ok P (do! x := gen in gen' x) R.
Proof.
  unfold ST_ok in *; intros.
  inverts H3.
  destruct (gen _) as (? & ? & ? & ?) eqn:Heq.
  forwards*: H.
Qed.

Lemma remove_var_incl Env x:
  incl (remove_var Env x) Env.
Proof.
  unfold incl; induction Env; simpl; eauto.
  intros; destruct var_eq_dec; simpl in *; eauto.
  destruct H; eauto.
Qed.

Definition env_ok xs E :=
  (forall x v, In (x |-> v) E -> In x xs).

Lemma rule_ret (T : Set) (v : T) (P : T -> assnST) :
  ST_ok (P v) (ret v : CUDAM T) (fun (x : T) => P x).
Proof.
  unfold ST_ok; introv ? H'; inverts H'; simpl; eauto.
Qed.

Arguments ret {f _ A} x : simpl never.
Lemma rule_forward T (P' P : assnST) (Q : T -> assnST) gen :
  ST_ok P gen Q -> (forall n c gm, P' n c gm -> P n c gm) -> ST_ok P' gen Q.
Proof.
  unfold ST_ok; eauto.
Qed.

Lemma code_ok_float T G P Q xs ys (m : CUDAM T) Post :
  (fv_assn Q xs -> disjoint ys xs -> ST_ok (code_ok G P Q xs ys) m Post)
  -> ST_ok (code_ok G P Q xs ys) m Post.
Proof.
  unfold ST_ok, code_ok; intros H; intros.
  forwards*: H.
Qed.  

Lemma remove_var_incl' E x :
  incl (map ent_e (remove_var E x)) (map ent_e E).
Proof.
  induction E as [|[? ?] ?]; simpl; eauto.
  unfold incl in *; intros; simpl in *.
  destruct var_eq_dec; eauto.
  simpl in *; destruct H; eauto.
Qed.

Lemma rule_fLet G Pre R P E xs ys e v :
  evalExp E e v
  -> ST_ok (code_ok G Pre (Assn R P E) xs ys)
           (fLet e)
           (fun x => code_ok G Pre (Assn R P (x |-> v :: E)) (x :: xs) (remove_xs ys (x :: nil))).
Proof.
  unfold fLet; intros Hveal.
  eapply rule_bind; [apply rule_fresh|eauto |].
  introv; apply code_ok_float; intros Hincl Hdisj; simpl in Hdisj.
  eapply rule_bind; [|eauto|].
  { applys* (>>rule_setI (x :: nil)).
    - intros; applys* rule_host_let.
    - rewrite fv_assn_base in *; simpl.
      unfold incl; simpl.
      introv; repeat (rewrite in_app_iff; simpl).
      intros [? | ?]; substs; eauto.
      left; apply Hincl.
      forwards*: remove_var_incl'. 
    - unfold incl; simpl; intros ? [|[]]; eauto. }
  introv.
  eapply rule_forward; [apply rule_ret|].
  introv (Hfs & Htri & Hxs & Hys & Henv' & Hdisj'); splits; eauto.
  - cutrewrite (E = remove_var E x); [eauto|].
    rewrites fv_assn_base in Hincl.
    rewrites* remove_var_disjoint.
  - applys* (>>usable_incl Hxs).
    unfold incl; simpl; introv [? | ?]; substs; eauto;
    repeat (rewrite in_app_iff; simpl); eauto.
  - applys* (>>usable_incl Hys); unfold incl; introv ?.
    simpl; destruct var_eq_dec; try congruence.
  - rewrite fv_assn_base in *; unfold incl in *; simpl.
    intros ? [?|?]; eauto.
  - apply disjoint_comm; simpl; split.
    + intros Hc.
      forwards*: (disjoint_remove_xs ys (x :: nil)).
      apply disjoint_comm in H; simpl in H; jauto.
    + destruct Hdisj as [_ Hdisj].
      apply disjoint_comm in Hdisj.
      applys (>>disjoint_incl Hdisj).
      apply remove_xs_incl.
Qed.

Lemma rule_fAlloc G Pre R P E xs ys e size :
  evalExp E e (Zn size)
  -> ST_ok (code_ok G Pre (Assn R P E) xs ys)
           (fAlloc e)
           (fun x => code_ok G Pre (Ex p vs, Assn (array (GLoc p) vs 1 *** R) (length vs = size /\ P)
                                                  (x |-> p :: E))
                             (x :: xs) (remove_xs ys (x :: nil))).
Proof.
  unfold fLet; intros Hveal.
  eapply rule_bind; [apply rule_fresh|eauto |].
  introv; apply code_ok_float; intros Hincl Hdisj; simpl in Hdisj.
  eapply rule_bind; [|eauto|].
  { applys* (>>rule_setI (x :: nil)).
    - intros; applys* rule_host_alloc.
    - repeat (rewrite fv_assn_Ex; introv); rewrite fv_assn_base in *; simpl.
      unfold incl; simpl.
      introv; repeat (rewrite in_app_iff; simpl).
      intros [? | ?]; substs; eauto.
      left; apply Hincl.
      forwards*: remove_var_incl'. 
    - unfold incl; simpl; intros ? [|[]]; eauto. }
  introv.
  eapply rule_forward; [apply rule_ret|].
  introv (Hfs & Htri & Hxs & Hys & Henv' & Hdisj'); splits; eauto.
  - cutrewrite (E = remove_var E x); [eauto|].
    rewrites fv_assn_base in Hincl.
    rewrites* remove_var_disjoint.
  - applys* (>>usable_incl Hxs).
    unfold incl; simpl; introv [? | ?]; substs; eauto;
    repeat (rewrite in_app_iff; simpl); eauto.
  - applys* (>>usable_incl Hys); unfold incl; introv ?.
    simpl; destruct var_eq_dec; try congruence.
  - repeat (rewrite fv_assn_Ex; introv); rewrite fv_assn_base in *; unfold incl in *; simpl.
    intros ? [?|?]; eauto.
  - apply disjoint_comm; simpl; split.
    + intros Hc.
      forwards*: (disjoint_remove_xs ys (x :: nil)).
      apply disjoint_comm in H; simpl in H; jauto.
    + destruct Hdisj as [_ Hdisj].
      apply disjoint_comm in Hdisj.
      applys (>>disjoint_incl Hdisj).
      apply remove_xs_incl.
Qed.

Lemma rule_fAllocs G Pre R P E xs ys e size :
  evalExp E e (Zn size)
  -> ST_ok (code_ok G Pre (Assn R P E) xs ys)
           (fAlloc e)
           (fun x => code_ok G Pre (Ex p vs, Assn (array (GLoc p) vs 1 *** R) (length vs = size /\ P)
                                                  (x |-> p :: E))
                             (x :: xs) (remove_xs ys (x :: nil))).
Proof.
  unfold fLet; intros Hveal.
  eapply rule_bind; [apply rule_fresh|eauto |].
  introv; apply code_ok_float; intros Hincl Hdisj; simpl in Hdisj.
  eapply rule_bind; [|eauto|].
  { applys* (>>rule_setI (x :: nil)).
    - intros; applys* rule_host_alloc.
    - repeat (rewrite fv_assn_Ex; introv); rewrite fv_assn_base in *; simpl.
      unfold incl; simpl.
      introv; repeat (rewrite in_app_iff; simpl).
      intros [? | ?]; substs; eauto.
      left; apply Hincl.
      forwards*: remove_var_incl'. 
    - unfold incl; simpl; intros ? [|[]]; eauto. }
  introv.
  eapply rule_forward; [apply rule_ret|].
  introv (Hfs & Htri & Hxs & Hys & Henv' & Hdisj'); splits; eauto.
  - cutrewrite (E = remove_var E x); [eauto|].
    rewrites fv_assn_base in Hincl.
    rewrites* remove_var_disjoint.
  - applys* (>>usable_incl Hxs).
    unfold incl; simpl; introv [? | ?]; substs; eauto;
    repeat (rewrite in_app_iff; simpl); eauto.
  - applys* (>>usable_incl Hys); unfold incl; introv ?.
    simpl; destruct var_eq_dec; try congruence.
  - repeat (rewrite fv_assn_Ex; introv); rewrite fv_assn_base in *; unfold incl in *; simpl.
    intros ? [?|?]; eauto.
  - apply disjoint_comm; simpl; split.
    + intros Hc.
      forwards*: (disjoint_remove_xs ys (x :: nil)).
      apply disjoint_comm in H; simpl in H; jauto.
    + destruct Hdisj as [_ Hdisj].
      apply disjoint_comm in Hdisj.
      applys (>>disjoint_incl Hdisj).
      apply remove_xs_incl.
Qed.
