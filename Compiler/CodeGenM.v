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
  disjoint_list xs /\ disjoint_list ys /\
  usable_fns fns m /\ usable_fns fns' m /\ disjoint fns fns' /\
  disjoint_list fns /\ disjoint_list fns'.

Definition code_ok Gp G P Q xs : assnStmt := fun GM st => 
  forall GMp,
    sat_FC GMp Gp Gp
    -> disjoint_list (map fst GMp)
    -> map fst GMp = map fst Gp
    -> sat_FC (GMp ++ GM) (Gp ++ G) (Gp ++ G) /\
       CSLh_n (GMp ++ GM) (Gp ++ G) P st Q /\
       fv_assn Q xs /\
       disjoint_list (map fst GM) /\ map fst GM = map fst G.

Definition const {A B} (x : A) := fun (y : B) => x.

Lemma rule_fresh Gp Q xs ys fns fns' :
  fv_assn Q xs
  -> ST_ok (var_ok xs ys fns fns') 
           freshP
           (fun y => var_ok xs (y :: ys) fns fns')
           (fun y => code_ok Gp nil Q (const Q y) (const xs y)).
Proof.
  unfold ST_ok, freshP, setPn, code_ok.
  introv Hfv (Hxs & Hys & Hdisj & Hdxs & Hdys &  Hfns & Hfns' & Hdisj' & Hdfns & Hdfns') Heq.
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
    + simpl; splits; eauto.
      unfold usable, usable_var in *; rewrite Forall_forall in *.
      intros Hc; forwards*: Hys; omega.
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
  -> disjoint_list xs'
  -> (fv_assn Q (xs ++ xs'))
  -> (incl xs' ys)
  -> ST_ok (var_ok xs ys fns fns')
           (setI ss)
           (fun _ => var_ok (xs ++ xs') (remove_xs ys xs') fns fns')
           (fun x => code_ok G nil P (const Q x) (const (xs ++ xs') x)).
Proof.
  unfold code_ok.
  introv Htri Hfv Hdis' Hxs' (Hxs & Hys & Hdisj &  Hfns & Hfns' & Hdisj') Heq; simpl in *.
  unfold var_ok; inverts Heq; splits; [splits|..]; jauto.   
  - apply usable_app; eauto.
    applys* usable_incl.
  - eapply usable_incl; [|eauto using remove_xs_incl]; eauto.
  - rewrite disjoint_app; split; eauto.
    + apply disjoint_comm; applys (>>disjoint_incl ys); eauto using disjoint_comm.
      apply remove_xs_incl.
    + apply disjoint_remove_xs.
  - apply disjoint_list_app; eauto.
    introv ? ?; eapply disjoint_not_in_r in Hdisj; eauto.
  - Lemma disjoint_list_removed xs ys : 
      disjoint_list xs -> disjoint_list (remove_xs xs ys).
    Proof.
      induction xs; simpl; eauto.
      intros [? ?]; destruct in_dec; eauto.
      simpl; split; eauto.
      intros Hc; apply H; revert Hc; apply remove_xs_incl.
    Qed.
    apply disjoint_list_removed; eauto.
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

Lemma rule_bind T1 T2 Pre Pst Pst' xs ys P Q Gp G G' G'' R (gen : CUDAM T1) (gen' : T1 -> CUDAM T2) :
  ST_ok Pre gen (fun x => Pst x) (fun x => code_ok Gp G P (Q x) (xs x))
  -> (forall x, ST_ok (Pst x)
                      (gen' x) 
                      (fun y => Pst' y)
                      (fun y => code_ok (Gp ++ G) G' (Q x) (R y) (ys y)))
  -> disjoint (map fst Gp) (map fst G)
  -> disjoint (map fst Gp ++ map fst G) (map fst G')
  -> G'' = G ++ G'
  -> ST_ok Pre
           (bind gen gen')
           (fun y => Pst' y)
           (fun y => code_ok Gp G'' P (R y) (ys y)).
Proof.
  unfold ST_ok in *; intros ? ? HdisG HdisG' ?; substs; intros.
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

Lemma rule_ret (T : Type) (v : T) (P : assnST) (Q : T -> assnST) Gp p q xs :
  fv_assn (q v) (xs v)
  -> (p |= q v)
  -> (forall n m, P n m -> Q v n m)
  -> ST_ok P (ret v : CUDAM T) (fun (x : T) => Q x)
           (fun (x : T) => code_ok Gp nil p (q x) (xs x)).
Proof.
  intros ? ? ?; unfold ST_ok; introv ? H'; inverts H'; simpl; splits; eauto.
  unfold code_ok; intros; splits; simpl; eauto.
  rewrite !app_nil_r; eauto.
  rewrite !app_nil_r.
  eapply rule_host_backward.
  apply rule_host_skip.
  eauto.
Qed.

Arguments ret {f _ A} x : simpl never.
Arguments bind {f _ A B} _ _ : simpl never.
Lemma rule_forward T (P' P : assnST) (Q : T -> assnST) R gen :
  ST_ok P gen Q R -> (forall n c, P' n c -> P n c) -> ST_ok P' gen Q R.
Proof.
  unfold ST_ok; eauto.
Qed.

Lemma code_ok_float T xs ys fns fns' (m : CUDAM T) Q R :
  (disjoint ys xs -> disjoint_list xs -> disjoint_list ys
   -> disjoint fns fns' -> disjoint_list fns -> disjoint_list fns'
   -> ST_ok (var_ok xs ys fns fns') m Q R)
  -> ST_ok (var_ok xs ys fns fns') m Q R.
Proof.
  unfold ST_ok, var_ok; intros H; intros.
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

Lemma rule_fLet Gp R P E xs ys e v fns fns' :
  fv_assn (Assn R P E) xs 
  -> evalExp E e v
  -> ST_ok (var_ok xs ys fns fns')
           (fLet e)
           (fun x => var_ok (x :: xs) ys fns fns')
           (fun x => code_ok Gp nil (Assn R P E) (Assn R P (x |-> v :: E)) (x :: xs)).
Proof.
  unfold fLet; intros Hfv Hveal.
  applys* rule_bind; [applys* rule_fresh|..]; simpl; eauto.
  2: simpl; eauto.
  introv; apply code_ok_float; intros.
  applys* rule_bind; [apply rule_setI|..].
  { introv; applys* rule_host_let. }
  { instantiate (1 := x :: nil); simpl; tauto. }
  { rewrite fv_assn_base in *; simpl.
    apply incl_cons; try rewrite in_app_iff; simpl; eauto.
    apply incl_appl.
    eapply incl_tran; eauto using remove_var_incl'. }
  { Lemma incl_nil A {xs : list A} : incl nil xs. unfold incl; simpl; tauto. Qed.
    Lemma incl_hd A x {xs : list A} : incl (x :: nil) (x :: xs). unfold incl; simpl; tauto. Qed.
    eauto using incl_cons, incl_nil, incl_hd. }
  introv; apply rule_ret; eauto.
  { rewrite fv_assn_base in *; simpl.
    apply incl_cons; [apply incl_hd; simpl; eauto|applys* incl_tl]. }
  { apply Assn_imply; eauto.
    intros _; apply incl_cons; [apply incl_hd; simpl; auto|].
    rewrite fv_assn_base in Hfv.
    simpl in H; rewrites* remove_var_disjoint; eauto using incl_tl. }
  { intros n m (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); splits; eauto.
    - unfold usable in *; rewrite Forall_forall in *; simpl.
      intros ? [? | ?]; apply H5; rewrite in_app_iff; simpl; eauto.
    - simpl in H6, H1; destruct var_eq_dec; try congruence.
      simpl in H.
      Lemma remove_xs_nin xs ys :
        disjoint xs ys -> remove_xs xs ys = xs.
      Proof.
        induction xs; simpl; eauto.
        intros [? ?]; destruct in_dec; try tauto.
        rewrite IHxs; eauto.
      Qed.
      rewrite remove_xs_nin in H6; eauto.
      apply disjoint_comm; simpl; tauto.
    - simpl in H, H1.
      apply disjoint_comm; simpl; splits; try apply disjoint_comm; try tauto.
    - simpl in H |- *; try tauto.
    - simpl in *; try tauto. }
  simpl; eauto.
  simpl; eauto.
  simpl; eauto.
Qed.      

(* Definition ex_st {T} (f : T -> assnST) : assnST := *)
(*   fun n st gm => exists x, f x n st gm. *)

(* Notation "'Ex_st' x .. y , p" := (ex_st (fun x => .. (ex_st (fun y => p)) ..)) *)
(*   (at level 200, x binder, right associativity). *)

Lemma rule_fAlloc Gp R P E xs ys e len fns fns' :
  fv_assn (Assn R P E) xs 
  -> evalExp E e (Zn len)
  -> ST_ok (var_ok xs ys fns fns')
           (fAlloc e)
           (fun x => var_ok (x :: xs) ys fns fns')
           (fun x => code_ok Gp nil (Assn R P E)
                             (Ex p xs, Assn (array (GLoc p) xs 1 *** R) (length xs = len /\ P) (x |-> p :: E)) (x :: xs)).
Proof.
  unfold fLet; intros Hfv Hveal.
  applys* rule_bind; [applys* rule_fresh|..]; simpl; eauto.
  2: simpl; eauto.
  introv; apply code_ok_float; intros.
  applys* rule_bind; [apply rule_setI|..].
  { introv; applys* rule_host_alloc. }
  { instantiate (1 := x :: nil); simpl; tauto. }
  { rewrite fv_assn_Ex; intros p.
    rewrite fv_assn_Ex; intros vs.
    rewrite fv_assn_base in *.
    apply incl_cons; try rewrite in_app_iff; simpl; eauto.
    apply incl_appl.
    eapply incl_tran; eauto using remove_var_incl'. }
  { eauto using incl_cons, incl_nil, incl_hd. }
  introv; apply rule_ret; eauto.
  { rewrite fv_assn_Ex; intros p.
    rewrite fv_assn_Ex; intros vs.
    rewrite fv_assn_base in *.
    apply incl_cons; [apply incl_hd; simpl; eauto|applys* incl_tl]. }
  { intros s h (p & vs & Hsat); exists p vs; revert s h Hsat; apply Assn_imply.
    intros _; apply incl_cons; [apply incl_hd; simpl; auto|].
    rewrite fv_assn_base in Hfv.
    simpl in H; rewrites* remove_var_disjoint; eauto using incl_tl. 
    intros; eauto.
    intros; eauto. }
  { intros n m (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); splits; eauto.
    - unfold usable in *; rewrite Forall_forall in *; simpl.
      intros ? [? | ?]; apply H5; rewrite in_app_iff; simpl; eauto.
    - simpl in H6, H1; destruct var_eq_dec; try congruence.
      simpl in H.
      rewrite remove_xs_nin in H6; eauto.
      apply disjoint_comm; simpl; tauto.
    - simpl in H, H1.
      apply disjoint_comm; simpl; splits; try apply disjoint_comm; try tauto.
    - simpl in H |- *; try tauto.
    - simpl in *; try tauto. }
  simpl; eauto.
  simpl; eauto.
  simpl; eauto.
Qed.

Lemma forall_reorder A B T (f : A -> B -> T) : B -> A -> T.
Proof.
  eauto.
Qed.

Class hasDefval A := HD {default : A}.
Global Instance val_hasDefval : hasDefval val := {default := 0%Z}.
Global Instance vals_hasDefval T ty (d : hasDefval T) : hasDefval (typ2Coq T ty) :=
  {default := (fix f ty := match ty return typ2Coq T ty with Skel.TZ | Skel.TBool => default |
                                   Skel.TTup t1 t2 => (f t1, f t2)
                           end) ty}.
Global Instance listA_hasDefval A : hasDefval (list A) := {default := nil}.

Lemma rule_code_ex (T A : Type) `{hd_A : hasDefval A} (gen : CUDAM T) P (Q : T -> assnST) (Gp G : FC)
      (p : A -> assn) (q : T -> assn) (xs : T -> list var)  :
  (forall y, ST_ok P gen Q (fun (x : T) => code_ok Gp G (p y) (q x) (xs x)))
  -> ST_ok P gen Q (fun (x : T) => code_ok Gp G (Ex y : A, p y) (q x) (xs x)).
Proof.
  unfold ST_ok, code_ok; intros.
  assert (forall (n m n' m' : nat) (st : list stmt) 
        (GM : GModule) (v : T),
      P n m ->
      gen n m = (v, (n', m', st, GM)) ->
      Q v n' m' /\
      (forall GMp : GModule,
       sat_FC GMp Gp Gp ->
       disjoint_list (map fst GMp) ->
       map fst GMp = map fst Gp ->
       sat_FC (GMp ++ GM) (Gp ++ G) (Gp ++ G) /\
       (forall y, CSLh_n (GMp ++ GM) (Gp ++ G) (p y) (seqs st) (q v)) /\
       fv_assn (q v) (xs v) /\
       disjoint_list (map fst GM) /\ map fst GM = map fst G)).
  { intros.
    splits; [forwards*: (H default)|].
    intros; splits; (try forwards* (? &  H'): (>> H default); forwards*: H').
    intros; forwards*: (>>H y).
    destruct H9; forwards*: H10. }
  splits; forwards* (? & ?): H2.
  intros; splits; forwards*: H4.
  apply rule_host_ex; jauto.
Qed.

Lemma ret_intro T (m : CUDAM T) : m = (do! x <- m in ret x).
Proof.
  unfold bind, CUDAM_Monad; simpl.
  extensionality x; extensionality y; destruct (m x y) as (? & ((? & ?) & ?) & ?); simpl.
  rewrite !app_nil_r; eauto.
Qed.

Lemma rule_fAllocs' typ Gp R P E (size : var) xs ys len fns fns' :
  fv_assn (Assn R P E) xs 
  -> ST_ok (var_ok (size :: xs) ys fns fns')
           (fAllocs' typ size)
           (fun x => var_ok (size :: flatTup x ++ xs) ys fns fns')
           (fun x => code_ok Gp nil (Assn R P (size |-> Zn len :: E))
                             (Ex ps xs, Assn (arrays (val2gl ps) xs 1 *** R) (length xs = len /\ P)
                                             (size |-> Zn len :: x |=> ps ++ E)) (size :: flatTup x ++ xs)).
Proof.
  (* intros; unfold fAllocs; simpl. *)
  (* eapply rule_bind. *)
  (* { apply rule_fLet; eauto. } *)
  (* all: simpl; eauto. *)
  (* 2: apply disjoint_comm; simpl; eauto. *)
  (* intros x. *)
  rewrite fv_assn_base.
  revert R P E xs ys; induction typ; simpl; eauto; simpl; introv Hfv.
  - rewrites (ret_intro var (fAlloc size)).
    eapply rule_bind; [apply rule_fAlloc|..].
    rewrite fv_assn_base in *; simpl; eauto.
    apply incl_cons; [apply incl_hd; simpl; eauto|applys* incl_tl].
    evalExp.
    introv.
    apply rule_code_ex; [apply val_hasDefval | intros p].
    apply rule_code_ex; [apply listA_hasDefval |intros ps].
    apply rule_ret.
    all: simpl; eauto.
    repeat (rewrite fv_assn_Ex; intros); rewrite fv_assn_base in *.
    simpl.
    simpl; apply incl_cons; [apply incl_hd; simpl; eauto| applys* incl_tl].
    apply incl_cons; simpl; eauto.
    apply incl_tl; eauto.
    intros s h Hsat; exists p ps; revert s h Hsat; prove_imp.
    rewrite mkReduce.arrays_TB; eauto.
    unfold var_ok; intros; splits; jauto.
    destruct H as (H' & _); applys (>>usable_incl H'); eauto.
    repeat apply incl_cons; simpl; eauto.
    repeat apply incl_tl; eauto.
    destruct H as (_ & _ & H' & _); apply disjoint_comm in H'; apply disjoint_comm.
    simpl in *; tauto.
    simpl in *; splits; try tauto.
    intros [? | ?]; substs; tauto.
  - rewrites (ret_intro var (fAlloc size)).
    eapply rule_bind; [apply rule_fAlloc|..].
    rewrite fv_assn_base in *; simpl; eauto.
    apply incl_cons; [apply incl_hd; simpl; eauto|applys* incl_tl].
    evalExp.
    introv.
    apply rule_code_ex; [apply val_hasDefval | intros p].
    apply rule_code_ex; [apply listA_hasDefval |intros ps].
    apply rule_ret.
    all: simpl; eauto.
    repeat (rewrite fv_assn_Ex; intros); rewrite fv_assn_base in *.
    simpl.
    simpl; apply incl_cons; [apply incl_hd; simpl; eauto| applys* incl_tl].
    apply incl_cons; simpl; eauto.
    apply incl_tl; eauto.
    intros s h Hsat; exists p ps; revert s h Hsat; prove_imp.
    rewrite mkReduce.arrays_TZ; eauto.
    unfold var_ok; intros; splits; jauto.
    destruct H as (H' & _); applys (>>usable_incl H'); eauto.
    repeat apply incl_cons; simpl; eauto.
    repeat apply incl_tl; eauto.
    destruct H as (_ & _ & H' & _); apply disjoint_comm in H'; apply disjoint_comm.
    simpl in *; tauto.
    simpl in *; splits; try tauto.
    intros [? | ?]; substs; tauto.
  - eapply rule_bind; [applys* IHtyp1|..].
    all: simpl; eauto.
    2: apply disjoint_comm; simpl; eauto.
    intros xs1.
    apply rule_code_ex; [apply vals_hasDefval; apply val_hasDefval|].
    intros ps1.
    apply rule_code_ex; [apply listA_hasDefval|].
    intros vs1.
    eapply rule_bind.
    rewrite app_nil_r.
    apply IHtyp2; eauto.
    all: simpl; eauto.
    rewrite map_app.
    apply incl_app; apply incl_app_iff; eauto.
    Lemma map_flatTup typ (xs : vars typ) vs : 
      map ent_e (xs |=> vs) = flatTup xs.
    Proof.
      induction typ; simpl; eauto.
      rewrite map_app, IHtyp1, IHtyp2; eauto.
    Qed.
    rewrite map_flatTup; eauto.
    2: simpl; eauto.
    introv.
    apply rule_ret.
    + rewrite fv_assn_Ex; intros ps.
      rewrite fv_assn_Ex; intros vs.
      rewrite fv_assn_base.
      simpl.
      rewrite <-!app_assoc, !map_app.
      apply incl_cons; simpl; eauto.
      apply incl_tl.
      apply incl_app.
      apply incl_app_iff; rewrite map_flatTup; eauto.
      apply incl_app; [rewrite map_flatTup; apply incl_app_iff; right; applys* incl_app_iff|].
      apply incl_app_iff; right.
      applys* incl_app_iff.
    + intros s h (ps2 & vs2 & Hsat); exists (ps1, ps2) (combine vs1 vs2); revert s h Hsat; prove_imp.
      rewrite mkReduce.arrays_TTup; simpl.
      rewrite <-res_assoc.
      rewrite combine_map_fst, combine_map_snd; try omega.
      unfold val2gl in *.
      repeat sep_cancel'.
      unfold vals in *; simpl; rewrite combine_length.
      rewrite Nat.min_l; lia.
    + rewrite <-!app_assoc; simpl; eauto.
      unfold var_ok; intros; splits; jauto.
      destruct H as (H' & _); applys (>>usable_incl H'); eauto.
      unfold incl; introv; simpl; rewrite !in_app_iff; tauto.
      destruct H as (_ & ? & H'& _).
      applys* (>>disjoint_incl H').
      unfold incl; introv; simpl; rewrite !in_app_iff; tauto.
      destruct H as (_ & _ & _ & H' & _).
      Require Import Permutation.
      Lemma disjoint_list_perm A (xs : list A) ys :
        Permutation xs ys -> disjoint_list xs -> disjoint_list ys.
      Proof.
        induction 1; simpl; eauto.
        intros [? ?]; splits; eauto.
        intros Hc; apply H0.
        apply Permutation_sym in H.
        applys* (>>Permutation_in H).
        intros (? & ? & ?); splits; eauto.
        intros [?|  ?]; apply H; eauto; try tauto.
      Qed.
      revert H'; apply disjoint_list_perm.
      constructor.
      rewrite !app_assoc.
      apply Permutation_app_tail.
      apply Permutation_app_comm.
Qed.        

Lemma rule_fAllocs typ Gp R P E e xs ys len fns fns' :
  evalExp E e (Zn len)
  -> fv_assn (Assn R P E) xs
  -> ST_ok (var_ok xs ys fns fns')
        (fAllocs typ e)
        (fun x => var_ok (flatTup x ++ xs) ys fns fns')
        (fun x => code_ok Gp nil (Assn R P E)
                          (Ex ps xs, Assn (arrays (val2gl ps) xs 1 *** R) (length xs = len /\ P)
                                          (x |=> ps ++ E)) (flatTup x ++ xs)).       
Proof.
  rewrite fv_assn_base in *.
  intros; unfold fAllocs; simpl.
  eapply rule_bind.
  { apply rule_fLet; eauto. 
    rewrite fv_assn_base; eauto. }
  all: simpl; eauto.
  2: apply disjoint_comm; simpl; eauto.
  intros x.
  rewrite app_nil_r.
  rewrite (ret_intro _ (fAllocs' typ x)).
  eapply rule_bind.
  { apply rule_fAllocs'; eauto. 
    rewrite fv_assn_base; eauto. }
  all: simpl; eauto.
  all: simpl; eauto.
  introv.
  apply rule_ret.
  rewrite fv_assn_Ex; intros ps.
  rewrite fv_assn_Ex; intros vs.
  rewrite fv_assn_base.
  unfold incl; introv; rewrite !map_app, !in_app_iff, map_flatTup; eauto.
  unfold incl in *; intuition.
  
  intros s h (ps & vs & Hsat); exists ps vs; revert s h Hsat; prove_imp.
  
  unfold var_ok; intros; splits; jauto.
  destruct H1 as (H' & _); applys* (>>usable_incl H').
  unfold incl; introv; simpl; rewrite !in_app_iff; eauto.
  destruct H1 as (_ & _ & H' & _).
  applys* (>>disjoint_incl H'); unfold incl; introv; simpl; eauto.
  
  simpl in *; tauto.
Qed.

Lemma rule_freshF Gp Q xs ys fns fns' :
  fv_assn Q xs
  -> ST_ok (var_ok xs ys fns fns') 
           freshF
           (fun kn => var_ok xs ys fns (kn :: fns'))
           (fun kn => code_ok Gp nil Q (const Q kn) (const xs kn)).
Proof.
  unfold ST_ok, freshP, setPn, code_ok.
  introv Hfv (Hxs & Hys & Hdisj & Hdxs & Hdys &  Hfns & Hfns' & Hdisj' & Hdfns & Hdfns') Heq.
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
    + simpl; splits; eauto.
      unfold usable, usable_var in *; rewrite Forall_forall in *.
      intros Hc; forwards*: Hys; omega.
  - intros; splits; try rewrite !app_nil_r; simpl; eauto.
    simpl; apply rule_host_skip.
Qed.  

Lemma rule_gen_kernel k xs ys fns fns' :
  ST_ok (var_ok xs ys fns fns') 
        (gen_kernel k) 
        (fun kn => )
        (fun kn => )