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

Definition assnST : Type := nat -> nat -> Prop.
Definition assnStmt : Type := GModule -> stmt -> Prop.

Definition ST_ok {T} (P : assnST) (gen : CUDAM T) (Q : T -> assnST) (A : T -> assnStmt) :=
  forall (n m n' m' : nat) st GM v,
    P n m 
    -> gen n m = (v, (n', m', st, GM))
    -> Q v n' m' /\ A v GM (seqs st).

Parameter fv_assn : assn -> list var -> Prop.
Axiom fv_assn_ok : forall P xs ys,
    fv_assn P xs -> disjoint xs ys -> inde P ys.
Axiom fv_assn_base :
  forall R P E xs, fv_assn (Assn R P E) xs <-> incl (List.map ent_e E) xs.
Axiom fv_assn_Ex :
  forall T (P : T -> assn) xs, fv_assn (Ex v, P v) xs <-> (forall v, fv_assn (P v) xs).

Definition hvar n := Var ("h" ++ nat2str n).
Definition kname n := ("_ker" ++ nat2str n)%string.

Definition usable_var x n : Prop := forall m, x = hvar m -> m < n.

Definition usable (xs : list var) n : Prop :=
  List.Forall (fun x => usable_var x n) xs.

Definition usable_fn x n :=
  exists m, x = kname m /\ m < n.

Definition usable_fns (xs : list string) n : Prop :=
  List.Forall (fun x => usable_fn x n) xs.

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

Lemma safe_seqs_app : forall GM (n : nat) (C1 C2 : list stmt) (s : stack) (h : zpheap) (P Q : assn),
   safe_nh GM n s h (seqs C1) P
   -> (forall s h m, sat s (as_gheap h) P -> m <= n -> safe_nh GM n s h (seqs C2) Q)
   -> safe_nh GM n s h (seqs (C1 ++ C2)) Q.
Proof.
  induction n; [simpl; eauto|].
  introv.
  intros (Hskip & Hab1 & Hstep1) Hsafe2; split; [|split].
  - Lemma seqs_skip C : seqs C = host_skip -> C = nil.
    Proof.
      induction C; simpl; try congruence.
    Qed.
    intros Hsk; apply seqs_skip, app_eq_nil in Hsk.
    destruct Hsk; substs; simpl in Hskip.
    forwards*: Hskip; forwards*: Hsafe2; simpl in *; jauto.
  - Lemma seqs_app_abort GM C1 C2 s h :
      aborts_h GM (seqs (C1 ++ C2)) s h
      -> aborts_h GM (seqs C1) s h \/ (C1 = nil).
    Proof.
      induction C1; simpl; eauto.
      intros Hab; inverts Hab.
      left; constructor; eauto.
    Qed.
    introv Hdis Heq Hab; forwards* [Hab' | ?]: (>>seqs_app_abort Hab); substs.
    simpl in *; forwards*: Hskip; forwards*: Hsafe2.
  - introv Hdis Heq Hstep.
    Lemma seqs_app_step GM C1 C2 C' st1 st2 :
      stmt_exec GM (seqs (C1 ++ C2)) st1 C' st2
      -> (exists C'', stmt_exec GM (seqs C1) st1 (seqs C'') st2 /\ seqs (C'' ++ C2) = C')  \/
         (C1 = nil).
    Proof.
      induction C1; simpl; eauto.
      intros Hstep; inverts Hstep.
      - left; exists (s1' :: C1); split; constructor; eauto.
      - left; exists C1; split; eauto; constructor.
    Qed.
    forwards*[(C' & Hstep' & ?) | ?]: (>>seqs_app_step Hstep); substs; jauto.
    + forwards* (h'' & ? & ? & ?): Hstep1; exists h''; splits; jauto.
      applys* IHn; intros; forwards*: (>>Hsafe2 n).
      applys (>>safe_nh_mono); eauto.
    + simpl in Hstep.
      forwards*: Hskip; forwards* (? & ? & Hsafe2'): Hsafe2.
Qed.

Lemma rule_app_seqs GM G P Q R st1 st2 :
  CSLh_n GM G P (seqs st1) Q
  -> CSLh_n GM G Q (seqs st2) R
  -> CSLh_n GM G P (seqs (st1 ++ st2)) R.
Proof.
  unfold CSLh_n, CSLh_n_simp; intros H1 H2; intros.
  eauto using safe_seqs_app.
Qed.

Definition var_ok xs ys fns fns' : assnST := fun n m =>
  usable xs n /\ usable ys n /\ disjoint ys xs /\
  usable_fns fns m /\ usable_fns fns' m /\ disjoint fns fns'.

Definition code_ok Gp G P Q xs : assnStmt := fun GM st => 
  forall GMp,
    sat_FC GMp Gp Gp
    -> disjoint_list (map fst GMp)
    -> map fst GMp = map fst Gp
    -> sat_FC (GMp ++ GM) (Gp ++ G) (Gp ++ G) /\
       CSLh_n (GMp ++ GM) (Gp ++ G) P st Q /\
       fv_assn Q xs /\
       disjoint_list (map fst GM) /\ map fst GM = map fst G.

Lemma rule_fresh Gp Q xs ys fns fns' :
  fv_assn Q xs
  -> ST_ok (var_ok xs ys fns fns') 
           freshP
           (fun y => var_ok xs (y :: ys) fns fns')
           (fun y => code_ok Gp nil Q Q xs).
Proof.
  unfold ST_ok, freshP, setPn, code_ok.
  introv Hfv (Hxs & Hys & Hdisj &  Hfns & Hfns' & Hdisj') Heq.
  inverts Heq.
  splits; eauto.
  - splits; eauto.
    + applys (>>usable_weaken Hxs); omega.
    + constructor.
      * apply lt_usable_var; omega.
      * applys (>>usable_weaken Hys); omega.
    + split; eauto.
      intros Hc.
      unfold usable in Hxs; rewrite Forall_forall in Hxs.
      forwards* H: Hxs.
      apply usable_var_lt in H; omega.
  - intros; splits; try rewrite !app_nil_r; simpl; eauto.
    simpl; apply rule_host_skip.
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

(* Lemma rule_hseq GM G st st' P Q R: *)
(*   CSLh_n GM G P st Q  *)
(*   -> CSLh_n GM G Q st' R *)
(*   -> CSLh_n GM G P (hseq st st') R. *)
(* Proof. *)
(*   intros. *)
(*   destruct st'; simpl; eauto using rule_host_seq. *)
(*   intros n Hfc s h Hp. *)
(*   forwards*: (>>H0 n Hfc). *)
(*   forwards*: (>>H n Hfc s h Hp). *)
(*   clear Hp H; revert s h st H1 H2; clear; induction n; simpl; eauto; introv. *)
(*   intros Htri (? & ? & ?); splits; eauto. *)
(*   - intros; substs; forwards*H': H; forwards*: (>>Htri H); simpl in *; jauto. *)
(*   - intros; forwards*(h'' & ? & ?): H1; exists h''; splits; jauto. *)
(*     applys* IHn. *)
(*     intros ? ? Hq; forwards*: Htri; eauto using safe_nh_mono. *)
(* Qed. *)

Lemma rule_setI G P Q ss xs xs' ys fns fns' :
  (forall GM, CSLh_n GM G P ss Q)
  -> (fv_assn Q (xs ++ xs'))
  -> (incl xs' ys)
  -> ST_ok (var_ok xs ys fns fns')
           (setI ss)
           (fun _ => var_ok (xs ++ xs') (remove_xs ys xs') fns fns')
           (fun _ => code_ok G nil P Q (xs ++ xs')).
Proof.
  unfold code_ok.
  introv Htri Hfv Hxs' (Hxs & Hys & Hdisj &  Hfns & Hfns' & Hdisj') Heq; simpl in *.
  unfold var_ok; inverts Heq; splits; [splits|..]; jauto.   
  - apply usable_app; eauto.
    applys* usable_incl.
  - eapply usable_incl; [|eauto using remove_xs_incl]; eauto.
  - rewrite disjoint_app; split; eauto.
    + apply disjoint_comm; applys (>>disjoint_incl ys); eauto using disjoint_comm.
      apply remove_xs_incl.
    + apply disjoint_remove_xs.
  - intros; splits; try rewrite !app_nil_r; simpl; eauto.
    simpl; eauto.
    eapply rule_host_seq; eauto using rule_host_skip.
Qed.  

Lemma func_disp_not_in GM id : 
  func_disp GM id = None <-> (forall k, ~In (id, k) GM).
Proof. 
  induction GM as [|[? ?] ?]; simpl; splits; eauto.
  - destruct string_dec; substs; try congruence.
    introv Hdisp Hc.
    destruct Hc as [Heq | Hc]; [inverts Heq|]; eauto.
    rewrite IHGM in Hdisp; jauto.
  - intros Hc; destruct string_dec; [ substs|].
    + forwards*: Hc.
    + apply IHGM; introv Hc'.
      forwards*: (>>Hc k).
Qed.
Lemma func_disp_incl_none GM GM' id : 
  incl GM GM' 
  -> func_disp GM' id = None -> func_disp GM id = None.
Proof.
  unfold incl; intros Hinc HGM'.
  rewrite func_disp_not_in in *.
  introv Hc; forwards*: (>>HGM').
Qed.
Lemma func_disp_in GM id fd :
  disjoint_list (map fst GM)
  -> func_disp GM id = Some fd <-> (In (id, fd) GM).
Proof.
  induction GM as [|[? ?] ?]; simpl; intros Hdisj; splits; try congruence; try tauto.
  - intros Heq; destruct string_dec.
    + inverts Heq; substs; eauto.
    + forwards*: IHGM.
  - intros [Heq | Hin]; [inverts Heq|]; substs.
    + destruct string_dec; congruence.
    + destruct string_dec; eauto; substs.
      * destruct Hdisj as [Hnin _]; false; apply* Hnin.
        rewrite in_map_iff; exists (s, fd); jauto.
      * apply IHGM in Hin; jauto; rewrite Hin.
Qed.

Lemma func_disp_incl GM GM' id fd fd' :
  incl GM GM' 
  -> disjoint_list (map fst GM')
  -> func_disp GM id = Some fd -> func_disp GM' id = Some fd'
  -> fd = fd'.
Proof.
  induction GM as [|(? & ?) ?]; simpl; intros Hincl Hdisj Hdisp Hdisp'; try congruence.
  destruct string_dec; substs; [inverts Hdisp|].
  - rewrites* func_disp_in in Hdisp'.
    forwards*: (>> Hincl (s, fd)); simpl; eauto.
    Lemma disjoint_list_map A B x y (f : A -> B) xs :
      disjoint_list (map f xs) 
      -> In x xs -> In y xs -> f x = f y -> x = y.
    Proof.
      induction xs; simpl; try tauto.
      intros [Hnin Hdisj] [? | Hinx] [? | Hiny] Heq; substs; jauto.
      false; apply Hnin; apply in_map_iff; exists y; eauto.
      false; apply Hnin; apply in_map_iff; exists x; eauto.
    Qed.
    forwards*: (>>disjoint_list_map (s, fd') Hdisj); congruence.
  - applys* IHGM.
    unfold incl in *; simpl in *; eauto.
Qed.

Lemma safe_nh_weaken GM GM' n s h st Q :
  disjoint_list (map fst GM')
  -> safe_nh GM n s h st Q 
  -> incl GM GM' 
  -> safe_nh GM' n s h st Q .
Proof.
  revert s h st; induction n; simpl; eauto.
  introv HdisGM' (Hskip & Hsafe & Hstep) Hincl; splits; jauto.
  - introv Hdisj Heq Hc; applys* Hsafe.
    Lemma aborts_h_weaken GM GM' st s h : 
      aborts_h GM' st s h
      -> incl GM GM'
      -> disjoint_list (map fst GM')
      -> aborts_h GM st s h.
    Proof.
      intros Hab Hincl HHdisj; induction Hab; try now constructor; jauto.
      - destruct H1 as [Hdisp | [[f Hdisp] | [Hn0 | [ Hm0 | Harg] ]]]; 
        econstructor; eauto.
        + eauto using func_disp_incl_none.
        + destruct (func_disp GM kid) as [fd'|] eqn:Heq; eauto.
          forwards*: (>>func_disp_incl Heq Hdisp); substs; eauto.
        + destruct (func_disp GM kid) as [|ker] eqn:Heq; eauto.
          destruct (func_disp ke kid) as [|ker] eqn:Heq'; eauto.
          repeat right; introv He; inverts He.
          apply Harg; eauto.
          f_equal; symmetry; applys* (>>func_disp_incl Hincl).
          forwards*: (>>func_disp_incl_none Hincl Heq'); congruence.
      - econstructor. 
        destruct H as [Hdisp | [[f Hdisp] | Harg]]; eauto.
        + eauto using func_disp_incl_none.
        + destruct (func_disp GM fn) as [fd'|] eqn:Heq; eauto.
          forwards*: (>>func_disp_incl Heq Hdisp); substs; eauto.
        + destruct (func_disp GM fn) as [|ker] eqn:Heq; eauto.
          destruct (func_disp ke fn) as [|ker] eqn:Heq'; eauto.
          repeat right; introv He; inverts He.
          apply Harg; eauto.
          f_equal; symmetry; applys* (>>func_disp_incl Hincl).
          forwards*: (>>func_disp_incl_none Hincl Heq'); congruence.
    Qed.
    applys* aborts_h_weaken.
  - Lemma stmt_exec_weaken GM GM' st state st' state' :
      stmt_exec GM' st state st' state'
      -> disjoint_list (map fst GM')
      -> incl GM GM' 
      -> ~aborts_h GM st (st_stack state) (st_heap state)
      -> stmt_exec GM st state st' state'.
    Proof.
      induction 1; intros Hdisj Hincl Hnab; try econstructor; eauto.
      - destruct (func_disp GM kerID) eqn:Heq.
        + f_equal; applys* (>>func_disp_incl Hincl).
        + false; apply Hnab; econstructor; eauto.
      - destruct (func_disp GM fn) eqn:Heq.
        + f_equal; applys* (>>func_disp_incl Hincl).
        + false; apply Hnab; econstructor; eauto.
      - apply IHstmt_exec; eauto.
        intros Hc; apply Hnab; constructor; eauto.
      - apply IHstmt_exec; eauto.
        intros Hc; apply Hnab; constructor; eauto.
    Qed.
    introv Hdis Heq Hstep'; forwards* (h'' & ? & ? & ?): (>>Hstep).
    { applys* stmt_exec_weaken. }
Qed.

Lemma CSLh_n_weaken GM G GM' G' P st Q :
  disjoint_list (map fst GM')
  -> CSLh_n GM G P st Q
  -> fc_ok GM G = true
  -> sat_FC GM G G
  -> incl GM GM' -> incl G G'
  -> CSLh_n GM' G' P st Q.
Proof.
  unfold CSLh_n, CSLh_n_simp; intros.
  applys* (>>safe_nh_weaken GM GM').
  apply H0; eauto.
  assert (sat_FC GM nil G) by (applys* rule_module_rec).
  apply H7, Forall_forall; simpl; try tauto.
Qed.  

Lemma fc_ok_same GM G: 
  incl (map fst G) (map fst GM) 
  -> fc_ok GM G = true.
Proof.
  revert GM; induction G as [|[? ?] ?]; intros [|[? ?] ?]; simpl in *; try congruence; eauto.
  intros H; apply incl_nil_r in H; simpl in *; congruence.
  intros Heq; simpl.
  rewrite IHG; simpl; [|unfold incl in *; simpl in *; eauto].
  unfold incl in *; forwards*: (>>Heq s).
  Lemma fn_ok_in GM f :
    In f (map fst GM) -> fn_ok GM f = true.
  Proof.
    induction GM; simpl; try tauto.
    unfold fn_ok; simpl.
    destruct a; simpl.
    intros [? | ?]; destruct string_dec; eauto.
  Qed.
  rewrite fn_ok_in; simpl; eauto.
Qed.

Lemma rule_bind T1 T2 Pre Pst Pst' xs ys P Q Gp G G' R (gen : CUDAM T1) (gen' : T1 -> CUDAM T2) :
  ST_ok Pre gen (fun x => Pst x) (fun x => code_ok Gp G P (Q x) (xs x))
  -> (forall x, ST_ok (Pst x)
                      (gen' x) 
                      (fun y => Pst' y)
                      (fun y => code_ok (Gp ++ G) G' (Q x) (R y) (ys y)))
  -> disjoint (map fst Gp) (map fst G)
  -> disjoint (map fst Gp ++ map fst G) (map fst G')
  -> ST_ok Pre
           (do! x <- gen in gen' x)
           (fun y => Pst' y)
           (fun y => code_ok Gp (G ++ G') P (R y) (ys y)).
Proof.
  unfold ST_ok in *; intros ? ? HdisG HdisG'; intros.
  inverts H2.
  destruct (gen _ _) as [? [[[? ?] ?] ?]] eqn:Heq.
  forwards* (? & ?): H.
  destruct (gen' _ _ _) as [? [[[? ?] ?] ?]] eqn:Heq'.
  forwards* (? & ?): H0.
  inverts H4; splits; jauto.
  unfold code_ok in *.
  introv Hsat Hdisj Hname.
  forwards*: H3.
  forwards*: (>>H6 (GMp ++ g)); rewrite !map_app.
  { applys* disjoint_list_app.
    introv.
    unfold fdecl in *.
    rewrite Hname.
    destruct H4 as (? & ? & ? & ? & ->).
    intros; forwards*: (>>disjoint_not_in_r (disjoint_comm _ _ _ HdisG)). }
  { unfold fdecl in *; destruct H4 as (? & ? & ? & ? & ?); congruence. }
  rewrite <-!app_assoc in *.
  clear H H0 H3 H6.
  splits; jauto.
  - eapply rule_app_seqs; jauto.
    applys* (>>CSLh_n_weaken (GMp ++ g) (Gp ++ G)).
    + rewrite !map_app.
      applys* disjoint_list_app.
      unfold fdecl.
      applys* disjoint_list_app.
      destruct H4 as (? & ? & ? & ? & ->).
      destruct H7 as (? & ? & ? & ? & ->).
      intros; forwards*: (>>disjoint_not_in_r (disjoint_comm _ _ _ HdisG')).
      rewrites* in_app_iff.
      introv; unfold fdecl; rewrite Hname.
      destruct H4 as (? & ? & ? & ? & ->).
      destruct H7 as (? & ? & ? & ? & ->).
      rewrite in_app_iff.
      intros; forwards*: (>>disjoint_not_in_r (disjoint_comm _ _ _ HdisG)).
      intros [? | ?]; eauto.
      intros; forwards*: (>>disjoint_not_in_r (disjoint_comm _ _ _ HdisG')).
      rewrite in_app_iff; eauto.
    + applys* fc_ok_same.
      introv; unfold fdecl.
      rewrite !map_app.
      destruct H4 as (? & ? & ? & ? & ->).
      rewrites* Hname.
    + rewrite app_assoc; apply incl_app_iff; eauto.
    + rewrite app_assoc; apply incl_app_iff; eauto.
  - unfold fdecl; applys* disjoint_list_app.
    destruct H4 as (? & ? & ? & ? & ->).
    destruct H7 as (? & ? & ? & ? & ->).
    intros; forwards*: (>>disjoint_not_in_r (disjoint_comm _ _ _ HdisG')). 
    rewrites* in_app_iff.
  - unfold fdecl.
    destruct H4 as (? & ? & ? & ? & ->).
    destruct H7 as (? & ? & ? & ? & ->); eauto.
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

Lemma rule_ret (T : Set) (v : T) (P : T -> assnST) Gp Q xs :
  fv_assn Q xs
  -> ST_ok (P v) (ret v : CUDAM T) (fun (x : T) => P x) (fun (x : T) => code_ok Gp nil Q Q xs).
Proof.
  intros ?; unfold ST_ok; introv ? H'; inverts H'; simpl; splits; eauto.
  unfold code_ok; intros; splits; simpl; eauto.
  rewrite !app_nil_r; eauto.
  rewrite !app_nil_r; eauto using rule_host_skip.
Qed.

Arguments ret {f _ A} x : simpl never.
Arguments bind {f _ A B} _ _ : simpl never.
Lemma rule_forward T (P' P : assnST) (Q : T -> assnST) R gen :
  ST_ok P gen Q R -> (forall n c, P' n c -> P n c) -> ST_ok P' gen Q R.
Proof.
  unfold ST_ok; eauto.
Qed.

(* Lemma code_ok_float T G P Q xs ys (m : CUDAM T) Post : *)
(*   (fv_assn Q xs -> disjoint ys xs -> ST_ok (code_ok G P Q xs ys) m Post) *)
(*   -> ST_ok (code_ok G P Q xs ys) m Post. *)
(* Proof. *)
(*   unfold ST_ok, code_ok; intros H; intros. *)
(*   forwards*: H. *)
(* Qed.   *)

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
  eapply rule_bind; [apply rule_fresh| ].
  introv; apply code_ok_float; intros Hincl Hdisj; simpl in Hdisj.
  eapply rule_bind.
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

Definition ex_st {T} (f : T -> assnST) : assnST :=
  fun n st gm => exists x, f x n st gm.

Notation "'Ex_st' x .. y , p" := (ex_st (fun x => .. (ex_st (fun y => p)) ..))
  (at level 200, x binder, right associativity).

Lemma rule_fAlloc G Pre R P E xs ys e size :
  evalExp E e (Zn size)
  -> ST_ok (code_ok G Pre (Assn R P E) xs ys)
           (fAlloc e)
           (fun x => code_ok G Pre (Ex p vs, Assn (array (GLoc p) vs 1 *** R) (length vs = size /\ P)
                                                  (x |-> p :: E))
                             (x :: xs) (remove_xs ys (x :: nil))).
Proof.
  unfold fLet; intros Hveal.
  eapply rule_bind; [apply rule_fresh|].
  introv; apply code_ok_float; intros Hincl Hdisj; simpl in Hdisj.
  eapply rule_bind; [|].
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

Lemma rule_backward T (P : assnST) (Q Q' : T -> assnST) gen :
  ST_ok P gen Q -> (forall n c gm x, Q x n c gm -> Q' x n c gm) -> ST_ok P gen Q'.
Proof.
  unfold ST_ok; eauto.
Qed.

Lemma rule_fAllocs typ G Pre R P E xs ys (sz : var) size :
  evalExp E sz (Zn size)
  -> ST_ok (code_ok G Pre (Assn R P E) xs ys)
           (fAllocs' typ sz)
           (fun ls => code_ok G Pre (Ex ps vs, Assn (arrays (val2gl ps) vs 1 *** R)
                                                    (length vs = size /\ P)
                                                    (ls |=> ps ++ E))
                              (flatTup ls ++ xs) (remove_xs ys (flatTup ls))).
Proof.
  revert R P E xs ys; induction typ; simpl; eauto; introv Heval.
  - eapply rule_backward; [applys* rule_fAlloc |].
    simpl; introv (? & ? & ? & ? & ? & ?); splits; eauto.
    + eapply rule_host_backward; eauto.
      introv (p & vs & Hsat); exists p vs; revert s h Hsat; prove_imp.
      rewrite mkReduce.arrays_TB; eauto.
    + rewrite fv_assn_Ex in *; intros ps; specialize (H3 ps).
      rewrite fv_assn_Ex in *; intros vs; specialize (H3 vs).
      rewrites* fv_assn_base in *.
  - eapply rule_backward; [applys* rule_fAlloc |].
    simpl; introv (? & ? & ? & ? & ? & ?); splits; eauto.
    + eapply rule_host_backward; eauto.
      introv (p & vs & Hsat); exists p vs; revert s h Hsat; prove_imp.
      rewrite mkReduce.arrays_TZ; eauto.
    + rewrite fv_assn_Ex in *; intros ps; specialize (H3 ps).
      rewrite fv_assn_Ex in *; intros vs; specialize (H3 vs).
      rewrites* fv_assn_base in *.
  - simpl.
    eapply rule_bind; eauto.
    introv; simpl.
    Lemma rule_ex_gen A B T G Pre Pst xs ys G' Pst' xs' ys' (gen : CUDAM A) (k : A -> CUDAM B): 
      ST_ok (code_ok G Pre Pst xs ys) gen
            (fun x => code_ok (G' x) Pre (Ex y, Pst' y x) (xs' x) (ys' x))
      -> (forall x, ST_ok (code_ok (G' x) Pre (Ex y, Pst' y x) (xs' x) (ys' x))
                          (k x)
                          
    Proof.
      unfold ST_ok; introv Hsat Hok Hgen.
      unfold code_ok in *.
      forwards*: Hsat.
      splits; jauto.      
Qed.
