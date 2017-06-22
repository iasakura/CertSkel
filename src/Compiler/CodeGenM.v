Require Import Monad DepList GPUCSL TypedTerm SeqCompiler Compiler.
Require Import Program.Equality LibTactics String List.
Require Import CUDALib CodeGen CSLLemma CSLTactics Correctness mkMap.
Require Import SkelLib Psatz Host.

Lemma rule_host_backward GM G P Q Q' C :
  CSLh GM G P C Q
  -> Q |= Q' -> CSLh GM G P C Q'.
Proof.
  unfold CSLh, with_ctx, CSLh_n_simp; intros.
  eauto using safe_nh_conseq.
Qed.  

Lemma rule_host_ex GM G T (P : T -> assn) Q C :
  (forall x, CSLh GM G (P x) C Q)
  -> CSLh GM G (Ex x, P x) C Q.
Proof.
  unfold CSLh, with_ctx, CSLh_n_simp; intros.
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

Definition STPre : Type := nat -> nat -> GModule -> Prop.
Definition STPost : Type := 
  nat -> nat (* pre state *)
  -> nat -> nat (* post state *)
  -> GModule -> GModule -> stmt (* generated funs, previous funs ++ generated funs, generated code *)
  -> Prop.
(* Definition assnStmt : Type := GModule -> stmt -> Prop. *)

Definition ST_ok {T} (P : STPre) (gen : CUDAM T) (Q : T -> STPost) :=
  forall (n m n' m' : nat) st GMp GM v,
    P n m GMp
    -> gen n m = (v, (n', m', st, GM))
    -> Q v n m n' m' GM (GMp ++ GM) (seqs st).

Definition hvar n := Var ("h" ++ nat2str n).
Definition kname n := ("_ker" ++ nat2str n)%string.

Definition fvOk xs n : Prop :=
  List.Forall (fun x => forall m, x = hvar m -> m < n) xs.
Definition fnOk fns n : Prop :=
  List.Forall (fun fn => forall m, fn = kname m -> m < n) fns.
Definition fnOk' fns n : Prop :=
  List.Forall (fun fn => exists m, fn = kname m /\ m < n) fns.

Definition preST ys fns P Gp : STPre := fun n m M =>
  (exists xs, fv_assn P xs /\ fvOk xs n /\ disjoint ys xs) /\
  fnOk' fns m /\ fvOk ys n /\ disjoint fns (map fst M) /\
  disjoint_list ys /\
  disjoint_list fns /\
  sat_FC M Gp Gp /\ disjoint_list (map fst M) /\
  fc_ok M Gp /\
  fnOk' (map fst M) m.

Definition postST ys fns (P Q : assn) (Gp G : FC) : STPost := fun n m n' m' Mc M st =>
  n <= n' /\ m <= m' /\
  
  (exists xs, fv_assn Q xs /\ fvOk xs n' /\ disjoint ys xs) /\
  fnOk' fns m' /\ fvOk ys n' /\ disjoint fns (map fst M) /\
  disjoint_list ys /\
  disjoint_list fns  /\
  disjoint_list (map fst M) /\
  fnOk' (map fst Mc) m' /\
  fnOk' (map fst M) m' /\
  fc_ok M G /\
  sat_FC M G G /\
  CSLh M G P st Q.

Lemma kname_inj m n : kname m = kname n -> m = n.
Proof.
  unfold kname; intros H.
  inverts H.
  forwards*: (>>nat_to_string_inj H1).
Qed.

Lemma fnOk'_fnOk fns n :
  fnOk' fns n -> fnOk fns n.
Proof.
  induction 1; constructor; eauto.
  destruct H as (? & ? & ?); intros; substs; jauto.
  apply kname_inj in H2; substs; jauto.
Qed.
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

(* Lemma lt_usable_var n m : *)
(*   m < n -> usable_var (hvar m) n. *)
(* Proof. *)
(*   intros Hmn m' Heq. *)
(*   forwards*: (>>hvar_inj Heq); omega. *)
(* Qed. *)

(* Lemma usable_var_lt n m : *)
(*   usable_var (hvar m) n -> m < n. *)
(* Proof. *)
(*   unfold usable_var; intros H. *)
(*   forwards*: (H m). *)
(* Qed. *)

(* Lemma usable_var_weaken x n m :  *)
(*   m < n -> usable_var x m  -> usable_var x n. *)
(* Proof. *)
(*   unfold usable_var; intros. *)
(*   forwards*: H0; omega. *)
(* Qed. *)

(* Lemma usable_weaken n m xs  : *)
(*   m < n  *)
(*   -> usable xs m -> usable xs n. *)
(* Proof. *)
(*   intros Hmn H; induction H; constructor; eauto using usable_var_weaken. *)
(* Qed. *)

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
      stmt_step GM (seqs (C1 ++ C2)) st1 C' st2
      -> (exists C'', stmt_step GM (seqs C1) st1 (seqs C'') st2 /\ seqs (C'' ++ C2) = C')  \/
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
  CSLh GM G P (seqs st1) Q
  -> CSLh GM G Q (seqs st2) R
  -> CSLh GM G P (seqs (st1 ++ st2)) R.
Proof.
  unfold CSLh, with_ctx, CSLh_n_simp; intros H1 H2; intros.
  eauto using safe_seqs_app.
Qed.

(* Definition var_ok xs ys fns fns' : assnST := fun n m => *)
(*   usable xs n /\ usable ys n /\ disjoint ys xs /\ *)
(*   disjoint_list xs /\ disjoint_list ys /\ *)
(*   usable_fns fns m /\ usable_fns fns' m /\ disjoint fns fns' /\ *)
(*   disjoint_list fns /\ disjoint_list fns'. *)

(* Definition code_ok Gp G P Q xs fnsP fns : assnStmt := fun GM st =>  *)
(*   forall GMp, *)
(*     sat_FC GMp Gp Gp *)
(*     -> disjoint_list (map fst GMp) *)
(*     -> disjoint (map fst GMp) (map fst GM) *)
(*     -> sat_FC (GMp ++ GM) (Gp ++ G) (Gp ++ G) /\ *)
(*        CSLh_n (GMp ++ GM) (Gp ++ G) P st Q /\ *)
(*        fv_assn Q xs /\  *)
(*        disjoint (map fst GM) fnsP /\ incl (map fst GM) fns /\ incl (map fst G) fns /\ *)
(*        disjoint_list (map fst GM) /\ map fst GM = map fst G. *)

Definition K {A B} (x : A) := fun (y : B) => x.

Lemma incl_nil_r T (xs : list T) : 
  incl xs nil -> xs = nil.
Proof.
  induction xs; simpl; eauto.
  intros H; unfold incl in H; forwards*: (H a).
Qed.

Lemma incl_nil_l A (l : list A) : incl nil l.
Proof.
  unfold incl; simpl; tauto.
Qed.

Lemma fvOk_weaken fvs n m :
  n <= m -> fvOk fvs n -> fvOk fvs m.
Proof.
  unfold fvOk; intros Hnm H; induction H; constructor; eauto.
  intros; forwards*: H; omega.
Qed.

Lemma fvOk_ge n m xs :
  fvOk xs n -> n <= m -> ~ In (hvar m) xs.
Proof.
  unfold fvOk; rewrite Forall_forall; intros H ? Hc.
  intros; forwards*: H; omega.
Qed.

Lemma rule_fresh P G fns ys :
  ST_ok (preST ys fns P G)
        freshP
        (fun x => postST (K (x :: ys) x) (K fns x) P (K P x) G (K G x)).
Proof.
  unfold ST_ok, freshP, postST, preST.
  introv (HxsOk & HfnsOk & HysOk & HgnsOk & Hys & Hgns) Heq. 
  inverts Heq.
  unfold K; splits; [..|splits]; repeat rewrite app_nil_r; jauto; try omega.
  - destruct HxsOk as (xs' & ? & ? & ?); exists xs'; splits; jauto.
    + applys (>>fvOk_weaken H0); omega.
    + constructor; eauto.
      applys* fvOk_ge.
  - constructor.
    + intros ? H'; apply hvar_inj in H'; substs; omega.
    + applys (>>fvOk_weaken HysOk); omega.
  - simpl; splits; jauto.
    eapply fvOk_ge; eauto.
  - constructor.
  - repeat rewrite app_nil_r.
    apply rule_host_skip.
Qed.

(* Lemma rule_fresh' P G fns ys : *)
(*   ST_ok (preST ys fns P G) *)
(*            freshP *)
(*            (fun x => postST (x :: ys) (K fns x) P (K P x) G nil). *)
(* Proof. *)
(*   apply rule_fresh. *)
(* Qed. *)

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

(* Lemma usable_app xs ys n : *)
(*   usable xs n -> usable ys n -> usable (xs ++ ys) n. *)
(* Proof. *)
(*   unfold usable; eauto using Forall_app. *)
(* Qed. *)

Lemma Forall_incl T (xs ys : list T) P :
  List.Forall P xs -> incl ys xs -> List.Forall P ys.
Proof.
  induction 1; simpl; eauto.
  - intros H; apply incl_nil_r in H; substs; eauto.
  - intros Hincl; rewrite Forall_forall in * ; unfold incl in *.
    intros a Hain.
    forwards* Hincl': (>>Hincl Hain); destruct Hincl' as [? | Hincl']; substs; eauto.
Qed.

Lemma fvOk_incl xs ys n :
  fvOk xs n -> incl ys xs -> fvOk ys n.
Proof. unfold fvOk; eauto using Forall_incl. Qed.

Lemma remove_xs_incl xs ys :
  incl (remove_xs xs ys) xs.
Proof.
  unfold incl; induction xs; simpl; eauto.
  intros x; destruct in_dec; eauto.
  intros [? | ?]; eauto.
Qed.

Lemma rule_hseq GM G st st' P Q R:
  CSLh GM G P st Q
  -> CSLh GM G Q st' R
  -> CSLh GM G P (hseq st st') R.
Proof.
  intros.
  destruct st'; simpl; eauto using rule_host_seq.
  intros n Hfc s h Hp.
  forwards*: (>>H0 n Hfc).
  forwards*: (>>H n Hfc s h Hp).
  clear Hp H; revert s h st H1 H2; clear; induction n; simpl; eauto; introv.
  intros Htri (? & ? & ?); splits; eauto.
  - intros; substs; forwards*H': H; forwards*: (>>Htri H); simpl in *; jauto.
  - intros; forwards*(h'' & ? & ?): H1; exists h''; splits; jauto.
    applys* IHn.
    intros ? ? Hq; forwards*: Htri; eauto using safe_nh_mono.
Qed.

Lemma fvOk_app xs ys n : fvOk xs n -> fvOk ys n -> fvOk (xs ++ ys) n. 
Proof. applys* Forall_app. Qed.

Lemma disjoint_list_removed xs ys : 
  disjoint_list xs -> disjoint_list (remove_xs xs ys).
Proof.
  induction xs; simpl; eauto.
  intros [? ?]; destruct in_dec; eauto.
  simpl; split; eauto.
  intros Hc; apply H; revert Hc; apply remove_xs_incl.
Qed.

Lemma disjoint_incl_r (A : Type) (xs ys zs : list A) : 
  incl ys xs -> disjoint xs zs -> disjoint ys zs.
Proof.
  intros.
  apply disjoint_comm in H0; apply disjoint_comm; eapply disjoint_incl; eauto.
Qed.

Lemma rule_setI G P Q ss ys xs' fns  :
  (forall GM, fc_ok GM G -> sat_FC GM G G -> CSLh GM G P ss Q)
  -> (forall xs, fv_assn P xs -> fv_assn Q (xs' ++ xs))
  -> incl xs' ys
  -> ST_ok (preST ys fns P G)
           (setI ss)
           (fun x => postST (K (remove_xs ys xs') x) (K fns x) P (K Q x) G (K G x)).
Proof.
  unfold ST_ok, freshP, postST, preST, K.
  introv Hsat Hfv Hincl (HxsOk & HfnsOk & HysOk & Hdisjysxs & Hdisjfns & HsatG & HdisjGM & HokGM) Heq. 
  inverts Heq.
  splits; [..|splits]; repeat rewrite app_nil_r; jauto.
  - destruct HxsOk as (xs0 & ? & ? & ?); exists (xs' ++ xs0); splits; jauto.
    apply fvOk_app; eauto.
    applys* fvOk_incl.
    rewrite disjoint_app; splits.
    apply disjoint_remove_xs.
    applys* (>>disjoint_incl_r H1); apply remove_xs_incl.
  - applys (>>fvOk_incl HysOk).
    apply remove_xs_incl.
  - applys* disjoint_list_removed.
  - constructor.
  - eapply rule_host_seq; [jauto|apply rule_host_skip].
Qed.  

(* Lemma rule_setI' G P Q ss ys xs' fns  : *)
(*   (forall GM, sat_FC GM G G -> CSLh GM G P ss Q) *)
(*   -> (forall xs, fv_assn P xs -> fv_assn Q (xs' ++ xs)) *)
(*   -> incl xs' ys *)
(*   -> ST_ok (preST ys fns P G) *)
(*            (setI ss) *)
(*            (fun x => postST (K (remove_xs ys xs') x) (K fns x) P (K Q x) G nil ). *)
(* Proof. *)
(*   apply rule_setI. *)
(* Qed. *)

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
  - Lemma stmt_step_weaken GM GM' st state st' state' :
      stmt_step GM' st state st' state'
      -> disjoint_list (map fst GM')
      -> incl GM GM' 
      -> ~aborts_h GM st (st_stack state) (st_heap state)
      -> stmt_step GM st state st' state'.
    Proof.
      induction 1; intros Hdisj Hincl Hnab; try econstructor; eauto.
      - destruct (func_disp GM kerID) eqn:Heq.
        + f_equal; applys* (>>func_disp_incl Hincl).
        + false; apply Hnab; econstructor; eauto.
      - destruct (func_disp GM fn) eqn:Heq.
        + f_equal; applys* (>>func_disp_incl Hincl).
        + false; apply Hnab; econstructor; eauto.
      - apply IHstmt_step; eauto.
        intros Hc; apply Hnab; constructor; eauto.
      - apply IHstmt_step; eauto.
        intros Hc; apply Hnab; constructor; eauto.
    Qed.
    introv Hdis Heq Hstep'; forwards* (h'' & ? & ? & ?): (>>Hstep).
    { applys* stmt_step_weaken. }
Qed.

Lemma safe_nhfun_weaken GM GM' n s h st ret Q :
  disjoint_list (map fst GM')
  -> safe_nhfun GM n s h st ret Q
  -> incl GM GM' 
  -> safe_nhfun GM' n s h st ret Q.
Proof.
  revert s h st; induction n; simpl; eauto.
  introv HdisGM' (Hskip & Hsafe & Hstep) Hincl; splits; jauto.
  - introv Hdisj Heq Hc; applys* Hsafe.
    applys* aborts_h_weaken.
  - introv Hdis Heq Hstep'; forwards* (h'' & ? & ? & ?): (>>Hstep).
    { applys* stmt_step_weaken. }
Qed.

Lemma CSLh_n_weaken GM G GM' G' P st Q :
  disjoint_list (map fst GM')
  -> CSLh GM G P st Q
  -> fc_ok GM G 
  -> sat_FC GM G G
  -> incl GM GM'
  -> CSLh GM' G' P st Q.
Proof.
  unfold CSLh, with_ctx, CSLh_n_simp; intros.
  applys* (>>safe_nh_weaken GM GM').
  apply H0; eauto.
  assert (sat_FC GM nil G) by (applys* rule_module_rec).
  apply H6, Forall_forall; simpl; try tauto.
Qed.  

(* Lemma fc_ok_same GM G:  *)
(*   incl (map fst G) (map fst GM)  *)
(*   -> fc_ok GM G. *)
(* Proof. *)
(*   revert GM; induction G as [|[? ?] ?]; intros [|[? ?] ?]; simpl in *; try congruence; eauto. *)
(*   intros H; apply incl_nil_r in H; simpl in *; congruence. *)
(*   intros Heq; simpl. *)
(*   split; [|apply IHG; unfold incl in *; simpl in *; eauto]. *)
(*   unfold incl in *; forwards*: (>>Heq s). *)
(*   Lemma fn_ok_in GM f : *)
(*     In f (map fst GM) -> fn_ok GM f fs. *)
(*   Proof. *)
(*     induction GM; simpl; try tauto. *)
(*     unfold fn_ok; simpl. *)
(*     destruct a; simpl. *)
(*     intros [? | ?]; destruct string_dec; eauto. *)
(*   Qed. *)
(*   rewrite fn_ok_in; simpl; eauto. *)
(* Qed. *)

Definition ExStmt {T} (f : T -> STPost) := fun n m n' m' Mc M st => exists x, f x n m n' m' Mc M st.

Lemma fnOk'_weaken fn n m :
  n <= m
  -> fnOk' fn n 
  -> fnOk' fn m.
Proof.
  unfold fnOk'; rewrite !Forall_forall; intros.
  forwards* (x' & ? & ?): H0; exists x'; splits; eauto; omega.
Qed.

Lemma rule_bind T1 T2
      ys fns 
      ys' fns'
      ys'' fns''
      P Q Gp G G' R
      (gen : CUDAM T1) (gen' : T1 -> CUDAM T2) :
  ST_ok (preST ys fns P Gp)
        gen
        (fun x => postST (ys' x) (fns' x) P (Q x) Gp (G x))
  -> (forall x,
         ST_ok (preST (ys' x) (fns' x) (Q x) (G x))
               (gen' x)
               (fun y => postST (ys'' x y) (fns'' x y) (Q x) (R x y) (G x) (G' x y)))
  -> ST_ok (preST ys fns P Gp)
           (bind gen gen')
           (fun y => ExStmt (fun x => postST (ys'' x y) (fns'' x y) P (R x y) Gp (G' x y))).
Proof.
  unfold ST_ok, freshP, postST, preST.
  intros Hgen Hgen' n m n'' m'' st0 M0 M1 v0 (HxsOk & HfnsOk & HysOk & Hdisjxy & Hfns & Hsat & HdisjM & HokM) Heq.
  inverts Heq.
  destruct (gen _ _) as [v [[[n' m'] st] M']] eqn:Heqgen.
  destruct (gen' _ _ _) as [v' [[[? ?] st'] M'']] eqn:Heqgen'.
  inverts H0.
  
  exists v.
  forwards* : Hgen; clear Hgen.
  forwards* : Hgen'; clear Hgen'.
  repeat rewrite map_app in *.
  repeat rewrite <-app_assoc in *.
  Time splits; [..|splits]; jauto; try omega.
  apply Forall_app; unfold fnOk' in *; jauto.
  applys* (>>fnOk'_weaken m').
  eapply rule_app_seqs; jauto.
  applys* (>>CSLh_n_weaken (M0 ++ M') (G v) ); try rewrite !map_app;
    (try now (rewrite app_assoc; apply incl_appl; apply incl_refl)); jauto.
Qed.  

Lemma rule_forward T (P' P : STPre) (Q : T -> STPost) gen :
  ST_ok P gen Q -> (forall n c M, P' n c M -> P n c M) -> ST_ok P' gen Q.
Proof.
  unfold ST_ok; eauto.
Qed.

Lemma rule_backward T (P : STPre) (Q Q' : T -> STPost) gen :
  ST_ok P gen Q -> (forall v n m n' m' Mc M st, Q v n m n' m' Mc M st -> Q' v n m n' m' Mc M st) -> ST_ok P gen Q'.
Proof.
  unfold ST_ok; eauto.
Qed.

Lemma rule_bind' T1 T2
      ys fns 
      ys' fns' 
      ys'' fns'' 
      P Q Gp G G' R 
      (gen : CUDAM T1) (gen' : T1 -> CUDAM T2) :
  ST_ok (preST fns ys P Gp)
        gen
        (fun x => postST (ys' x) (fns' x) P (Q x) Gp (G x))
  -> (forall x,
         ST_ok (preST (ys' x) (fns' x) (Q x) (G x))
               (gen' x)
               (fun y => postST (ys'' y) (fns'' y) (Q x) (R y) (G x) (G' y)))
  -> ST_ok (preST fns ys P Gp)
           (bind gen gen')
           (fun y => postST (ys'' y) (fns'' y) P (R y) Gp (G' y)).
Proof.
  intros.
  eapply rule_backward.
  eapply rule_bind; [apply H|apply H0].
  introv [? ?]; eauto.
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

Lemma rule_ret (T : Type) (v : T) ys fns P Gp :
  ST_ok (preST (ys v) (fns v) (P v) Gp) (ret v) (fun u => postST (ys u) (fns u) (P v) (P u) Gp (K Gp u)).
Proof.
  unfold ST_ok, preST, postST; intros.
  inverts H0.
  splits; [..|splits]; try rewrite !app_nil_r; try omega; jauto.
  constructor.
  apply rule_host_skip.
Qed.

Arguments ret {f _ A} x : simpl never.
Arguments bind {f _ A B} _ _ : simpl never.

Lemma code_ok_float T ys fns Gp (m : CUDAM T) P Q :
  (disjoint_list fns -> (exists xs, fv_assn P xs /\ disjoint ys xs) -> disjoint_list ys -> ST_ok (preST ys fns P Gp) m Q)
  -> ST_ok (preST ys fns P Gp) m Q.
Proof.
  unfold ST_ok, preST; intros H; intros.
  forwards*: H.
  destruct H0 as ((? & ? & ? & ?) & ?); eexists; split; eauto.
Qed.

Lemma remove_var_incl' E x :
  incl (map ent_e (remove_var E x)) (map ent_e E).
Proof.
  induction E as [|[? ?] ?]; simpl; eauto.
  unfold incl in *; intros; simpl in *.
  destruct var_eq_dec; eauto.
  simpl in *; destruct H; eauto.
Qed.

Lemma remove_xs_disj xs ys : disjoint xs ys -> remove_xs xs ys = xs.
Proof.
  induction xs; simpl; eauto.
  intros; destruct in_dec; try tauto; eauto.
  rewrite IHxs; jauto.
Qed.

Lemma incl_cons_lr A (x : A) xs ys : incl xs ys -> incl (x :: xs) (x :: ys).
Proof. unfold incl; introv; simpl; intuition. Qed.

Lemma rule_fLet Gp R P E ys e v fns :
  evalExp E e v
  -> ST_ok (preST ys fns (Assn R P E) Gp)
           (fLet e)
           (fun x => postST (K ys x) (K fns x) (Assn R P E) ((Assn R P (x |-> v :: E))) Gp (K Gp x)).
Proof.
  unfold fLet; intros Hfv Heval.
  eapply rule_bind'.
  applys* rule_fresh.
  introv.
  simpl.
  apply code_ok_float; intros Hdfns (xs' & Hfvxs & Hdxy) Hdy; simpl in Hdxy, Hdy.
  applys* (>>rule_bind' (Assn R P E)).

  applys (>>rule_setI (x :: nil)).
  { intros; applys* rule_host_let. }
  { introv; rewrite !fv_assn_base_eq; simpl.
    intros; applys* incl_cons_lr.
    lets: remove_var_incl'.
    unfold incl in *; intros.
    eapply H, H0; eauto. }
  apply incl_cons_lr, incl_nil_l.
  (* apply fv_assn_base_eq; simpl. *)
  (* unfold incl; introv; simpl; repeat rewrite in_app_iff in *; eauto. *)
  (* destruct 1; eauto. *)
  (* rewrite fv_assn_base_eq in Hfv. *)
  (* right; apply remove_var_incl' in H. *)
  (* applys* Hfv. *)
  (* unfold incl; introv; simpl; tauto. *)
  (* simpl; destruct var_eq_dec; try congruence. *)
  (* rewrites* remove_xs_disj. *)
  introv.
  unfold K in Hfvxs; rewrite fv_assn_base_eq in Hfvxs.
  rewrite remove_var_disjoint.
  2: intros Hc; apply Hfvxs in Hc; tauto.
  simpl; destruct var_eq_dec; try congruence.
  rewrite remove_xs_disj; [|apply disjoint_comm; simpl; tauto].
  eapply (rule_ret _ x  (fun x => K ys x)
                   (fun x => fns)
                   (fun x' => Assn R P (x' |-> v :: E))).
Qed.      

(* Definition ex_st {T} (f : T -> assnST) : assnST := *)
(*   fun n st gm => exists x, f x n st gm. *)

(* Notation "'Ex_st' x .. y , p" := (ex_st (fun x => .. (ex_st (fun y => p)) ..)) *)
(*   (at level 200, x binder, right associativity). *)

Lemma rule_fAlloc Gp R P E ys len l fns :
  evalExp E len (Zn l)
  -> ST_ok (preST ys fns (Assn R P E) Gp)
           (fAlloc len)
           (fun x => postST (K ys x) (K fns x) (Assn R P E)
                            (Ex p vs, (Assn (array (GLoc p) vs 1 *** R)) (Datatypes.length vs = l /\ P) (x |-> p :: E))
                            Gp (K Gp x)).
Proof.
  unfold fLet; intros Hfv Heval.
  eapply rule_bind'.
  applys* rule_fresh.
  introv.
  simpl.
  apply code_ok_float; intros Hdfns (xs' & Hfvxs & Hdxy) Hdy; simpl in Hdxy, Hdy.
  applys* (>>rule_bind' (Assn R P E)).
  applys (>>rule_setI (x :: nil)).
  { intros; applys* rule_host_alloc. }
  { intros; do 2 (apply fv_assn_Ex_eq; intros); rewrite fv_assn_base_eq in *; simpl.
    apply incl_cons_lr.
    forwards*: (>>remove_var_incl' E x).
    unfold incl in *; intuition. }
  { apply incl_cons_lr, incl_nil_l. }
  unfold incl; introv; simpl; repeat rewrite in_app_iff in *; eauto.
  (* destruct 1; eauto. *)
  (* rewrite fv_assn_base_eq in Hfv. *)
  (* right; apply remove_var_incl' in H. *)
  (* applys* Hfv. *)
  (* unfold incl; introv; simpl; tauto. *)
  simpl; destruct var_eq_dec; try congruence.
  rewrites* remove_xs_disj.
  introv.
  rewrite remove_var_disjoint.
  2: intros Hc; apply fv_assn_base_eq in Hfvxs; apply Hfvxs in Hc; tauto.
  eapply (rule_ret _ x (fun x => K ys x)
                   (fun x => fns)
                   (fun x' => Ex (p : val) (vs : list val),
                              Assn (array (GLoc p) vs 1 *** R) (Datatypes.length vs = l /\ P)
                                   (x' |-> p :: E))).
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

Lemma fc_ok_incl M G :
  fc_ok M G -> incl (map fst G) (map fst M).
Proof.
  revert M; induction G as [|[? ?] ?]; unfold incl; simpl; intros; try tauto.
  forwards*: IHG.
  destruct H0; [subst|apply H1; eauto].
  unfold fn_ok in H.
  destruct func_disp eqn:Heq; try tauto.
  Lemma func_disp_in' M fn fd :
    func_disp M fn = Some fd -> In fn (map fst M).
  Proof.
    induction M as [|[? ?] ?]; simpl; try congruence.
    destruct string_dec.
    intros H; inverts H; left; congruence.
    intros; eauto.
  Qed.
  eapply func_disp_in'; eauto.
Qed.

Lemma rule_code_ex (T A : Type) `{hd_A : hasDefval A} (gen : CUDAM T) Gp (G : T -> FC)
      ys0 fns0 ys fns (p : A -> assn) (q : T -> assn) :
  (forall y, ST_ok (preST ys0 fns0 (p y) Gp) gen (fun (x : T) => postST (ys x) (fns x) (p y) (q x) Gp (G x)))
  -> ST_ok (preST ys0 fns0 (Ex y, p y) Gp) gen (fun (x : T) => postST (ys x) (fns x) (Ex y, p y) (q x) Gp (G x)).
Proof.
  unfold ST_ok, postST; intros.
  assert (H' : forall (n m n' m' : nat) (st : list stmt) 
        (GMp GM : GModule) (v : T),
      (forall y, preST ys0 fns0 (p y) Gp n m GMp) ->
      gen n m = (v, (n', m', st, GM)) ->
      n <= n' /\
      m <= m' /\
      (exists xs, fv_assn (q v) xs /\ fvOk xs n' /\ disjoint (ys v) xs) /\
      fnOk' (fns v) m' /\
      fvOk (ys v) n' /\
      disjoint (fns v) (map fst (GMp ++ GM)) /\
      disjoint_list (ys v) /\
      disjoint_list (fns v) /\
      disjoint_list (map fst (GMp ++ GM)) /\
      fnOk' (map fst GM) m' /\
      fnOk' (map fst (GMp ++ GM)) m' /\
      fc_ok (GMp ++ GM) (G v) /\
      sat_FC (GMp ++ GM) (G v) (G v) /\
      forall y, CSLh (GMp ++ GM) (G v) (p y) (seqs st) (q v)).
  { intros.
    forwards*: (H default); splits; [..|splits]; jauto.
    introv; forwards*: (H y). }
  unfold preST in H0; destruct H0 as ((? & ? & ? & ?) & ?).
  rewrite fv_assn_Ex_eq in H0.
  forwards*: H'.
  unfold preST in *; intros; splits; jauto.
  splits; [..|splits]; jauto.
  apply rule_host_ex; jauto.
Qed.

Lemma ret_intro T (m : CUDAM T) : m = (do! x <- m in ret x).
Proof.
  unfold bind, CUDAM_Monad; simpl.
  extensionality x; extensionality y; destruct (m x y) as (? & ((? & ?) & ?) & ?); simpl.
  rewrite !app_nil_r; eauto.
Qed.

Lemma rule_fAllocs' typ Gp R P E (size : var) ys l fns :
  ST_ok (preST ys fns (Assn R P (size |-> Zn l :: E)) Gp)
        (fAllocs' typ size)
        (fun x => postST (K ys x) (K fns x) (Assn R P (size |-> Zn l :: E))
                         (Ex ps vs, (Assn (arrays (val2gl ps) vs 1 *** R)) (Datatypes.length vs = l /\ P) (size |-> Zn l :: x |=> ps ++ E))
                         Gp (K Gp x)).
Proof.
  revert R P E ys; induction typ; simpl; eauto; simpl; introv.
  - eapply rule_backward.
    applys (>>rule_fAlloc (size |-> G.Zn l :: E)).
    evalExp.
    (* rewrite fv_assn_base_eq; simpl. *)
    (* apply incl_cons_lr; eauto. *)
    simpl; intros.
    unfold postST in *; splits; [..|splits]; jauto.
    { destruct H as (_ & _ & (xs' & ? & ? & ?) & _).
      exists xs'; splits; jauto.
      do 2 (apply fv_assn_Ex_eq; intros).
      rewrite fv_assn_Ex_eq in H.
      specialize (H v0).
      rewrite fv_assn_Ex_eq in H.
      specialize (H v1).
      rewrite fv_assn_base_eq in *.
      unfold incl in *; simpl in *; intros; forwards*: H. }
    (* { destruct H as (_ & _ & _ & H' & _). *)
    (*   constructor; [|constructor]; inverts H' as ? H'; inverts H'; eauto. } *)
    (* { destruct H as (_ & _ & _ & _ & _ & _ & H' & _). *)
    (*   apply disjoint_comm in H'; apply disjoint_comm; simpl in *; tauto. } *)
    eapply rule_host_backward; [jauto|].
    intros s h (p & vs & Hsat); exists p vs; revert s h Hsat; prove_imp.
    rewrite mkReduce.arrays_TB; eauto.
  - eapply rule_backward.
    applys (>>rule_fAlloc (size |-> G.Zn l :: E)).
    evalExp.
    (* rewrite fv_assn_base_eq; simpl. *)
    (* apply incl_cons_lr; eauto. *)
    simpl; intros.
    unfold postST in *; splits; [..|splits]; jauto.
    { destruct H as (_ & _ & (xs' & ? & ? & ?) & _).
      exists xs'; splits; jauto.
      do 2 (apply fv_assn_Ex_eq; intros).
      rewrite fv_assn_Ex_eq in H.
      specialize (H v0).
      rewrite fv_assn_Ex_eq in H.
      specialize (H v1).
      rewrite fv_assn_base_eq in *.
      unfold incl in *; simpl in *; intros; forwards*: H. }
    (* { destruct H as (_ & _ & _ & H' & _). *)
    (*   constructor; [|constructor]; inverts H' as ? H'; inverts H'; eauto. } *)
    (* { destruct H as (_ & _ & _ & _ & _ & _ & H' & _). *)
    (*   apply disjoint_comm in H'; apply disjoint_comm; simpl in *; tauto. } *)
    eapply rule_host_backward; [jauto|].
    intros s h (p & vs & Hsat); exists p vs; revert s h Hsat; prove_imp.
    rewrite mkReduce.arrays_TZ; eauto.
  - eapply rule_bind'.
    applys* IHtyp1.
    intros xs1; simpl.
    unfold K.
    apply rule_code_ex; [apply vals_hasDefval; apply val_hasDefval|].
    intros ps1.
    apply rule_code_ex; [apply listA_hasDefval|].
    intros vs1.
    eapply rule_bind'.
    
    apply IHtyp2.
    Lemma map_flatTup typ (xs : vars typ) vs : 
      map ent_e (xs |=> vs) = flatTup xs.
    Proof.
      induction typ; simpl; eauto.
      rewrite map_app, IHtyp1, IHtyp2; eauto.
    Qed.
    (* { rewrite map_app, map_flatTup. *)
    (*   unfold incl in *; intros; rewrite in_app_iff in *; intuition. } *)
    Lemma rule_ret' T (v : T) ys fns P Q Gp :
      (P |= Q v)
      -> (forall xs, fv_assn P xs -> fv_assn (Q v) xs)
      -> ST_ok (preST (ys v) (fns v) P Gp) (ret v) 
               (fun x => postST (ys x) (fns x) P (Q x) Gp Gp).
    Proof.
      intros; unfold ST_ok, preST, postST; intros; splits; [..|splits]; inverts H2; repeat rewrite app_nil_r; jauto.
      constructor.
      eapply rule_host_backward; [apply rule_host_skip|eauto].
    Qed.
    intros xs2; simpl; unfold K.
    eapply rule_forward.
    apply  (rule_ret' _ (xs1,xs2)
                     (fun xs' => ys)
                     (fun xs' => fns)
                     _
                     (fun xs' : vars (Skel.TTup typ1 typ2) =>
                        (Ex (ps : vals (Skel.TTup typ1 typ2)) (vs : list (vals (Skel.TTup typ1 typ2))),
                         Assn
                           (arrays (val2gl ps) vs 1 *** R)
                           (Datatypes.length vs = l /\ P)
                           (size |-> G.Zn l :: xs' |=> ps ++ E)))).
    { intros s h (ps & vs & Hsat); exists (ps1, ps) (combine vs1 vs); fold_sat; fold_sat_in Hsat; revert s h Hsat; simpl; prove_imp.
      rewrite mkReduce.arrays_TTup; simpl.
      rewrite <-res_assoc.
      rewrite combine_map_fst, combine_map_snd; try omega.
      unfold val2gl in *.
      repeat sep_cancel'; eauto.
      unfold vals in *; simpl in *.
      rewrite combine_length.
      rewrite Nat.min_l; omega. }
    { intros xs Hfv.
      apply fv_assn_Ex_eq; intros ps.
      apply fv_assn_Ex_eq; intros vs.
      rewrite fv_assn_Ex_eq in Hfv; specialize (Hfv (snd ps)).
      rewrite fv_assn_Ex_eq in Hfv; specialize (Hfv (map snd vs)).
      rewrite fv_assn_base_eq in *; simpl in *.
      rewrite !map_app, !map_flatTup, <-app_assoc in *.
      unfold incl in *; simpl in *; intros x; specialize (Hfv x); repeat rewrite in_app_iff in *; intuition. }
    unfold vals; simpl; eauto.
    (* unfold preST; introv H; splits; [..|splits]; jauto. *)
    (* (* { destruct H as (_ & _ & H' & _). *) *)
    (* (*   do 2 (apply fv_assn_Ex_eq; intros); apply fv_assn_base_eq. *) *)
    (* (*   rewrite fv_assn_Ex_eq in H'; forwards*: (>>H' v0). *) *)
    (* (*   rewrite fv_assn_Ex_eq in H; forwards*: (>>H v1). *) *)
    (* (*   apply fv_assn_base_eq in H0. *) *)
    (* (*   unfold incl in *; simpl in *; introv; specialize (H0 a); repeat rewrite in_app_iff in *. *) *)
    (* (*   intuition. } *) *)
    (* { destruct H as (H' & _). *)
    (*   unfold fvOk in *; rewrite Forall_forall in *; introv; specialize (H' x); simpl in *;  *)
    (*   repeat rewrite in_app_iff in *; intuition. } *)
    (* { destruct H as (_ & _ & _ & H' & _). *)
    (*   apply disjoint_comm in H'; apply disjoint_comm; simpl in *. *)
    (*   splits; jauto. *) 
      (* repeat rewrite disjoint_app_l in *; tauto. } *)
Qed.

Lemma disjoint_app_l (T : Type) (xs ys zs : list T) :
  disjoint (ys ++ zs) xs <-> disjoint ys xs /\ disjoint zs xs.
Proof.
  splits; intros H; [split; apply disjoint_comm in H; apply disjoint_app in H; destruct H..
                    |apply disjoint_comm; apply disjoint_app; split; destruct H]; eauto using disjoint_comm.
Qed.


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

Lemma disjoint_incl_l A (xs ys zs : list A) :
  incl xs ys -> disjoint ys zs -> disjoint xs zs.
Proof.
  intros.
  apply disjoint_comm in H0; apply disjoint_comm.
  eauto using disjoint_incl.
Qed.

Lemma postST_imp P Q Q' Gp G G' ys ys' fns fns':
  Q |= Q' ->
  incl G' G ->
  (forall xs, fv_assn Q xs -> fv_assn Q' xs) ->
  incl ys' ys ->
  incl fns' fns ->
  (disjoint_list fns -> disjoint_list fns') ->
  (disjoint_list ys -> disjoint_list ys') ->
  forall n m n' m' Mc M st,
    postST ys fns P Q Gp G n m n' m' Mc M st ->
    postST ys' fns' P Q' Gp G' n m n' m' Mc M st.
Proof.
  unfold postST; intros.
  destruct H6 as (? & ? & (? & ? & ? & ?) & ? & ? & ? & ? & ? & ? & ? & ?); splits; [..|splits]; jauto;
  unfold fnOk, fnOk', fvOk, incl in *; repeat rewrite Forall_forall in *;
  intros; intuition.
  exists x; splits; eauto.
  rewrite Forall_forall; eauto.
  eapply disjoint_incl_l; eauto.
  forwards*: H10.
  forwards*: H13.
  eapply disjoint_incl_l; [|eapply disjoint_incl]; eauto.
  (* eapply disjoint_incl_l; [|eapply disjoint_incl]; eauto. *)
  Lemma sat_FC_strong M Gp G : sat_FC M nil G -> sat_FC M Gp G.
  Proof.
    intros.
    unfold sat_FC in *; intros.
    forwards*: H.
    unfold interp_FC_n in *; rewrite Forall_forall in *; intros; forwards*: H0.
    destruct H1.
  Qed.
  (* apply rule_module_rec in H17. *)
  (* 2: apply fc_ok_same; unfold incl; eauto. *)
  
  Lemma incl_fc_ok M G G' : incl G' G -> fc_ok M G -> fc_ok M G'.
  Proof.
    revert G; induction G' as [|[? ?] ?]; simpl; eauto.
    - introv Hin Hok.
      splits; [|eapply IHG'; [|eauto]].
      2: unfold incl in *; simpl in *; intuition.
      unfold incl in *; forwards*: (>>Hin (s, f)).
      
      Lemma in_fc_ok fn fs M G : In (fn, fs) G -> fc_ok M G -> fn_ok M fn fs.
      Proof.
        induction G as [|[? ?] ?]; simpl; try tauto.
        intros [? | ?] [? ?]; eauto.
        inverts H; eauto.
      Qed.

      applys* in_fc_ok.
  Qed.

  eapply incl_fc_ok; unfold incl; eauto.
  
  assert (sat_FC M nil G').
  { apply rule_module_rec in H18; eauto.
    intros ? ?; eapply Forall_incl.
    apply H18; eauto.
    unfold incl; eauto. }
  apply sat_FC_strong; eauto.

  eapply rule_host_backward; [|eauto..].
  intros ? ?; forwards*: H22.
  apply rule_module_rec in H20; eauto.
  apply H20; constructor.
Qed.

Lemma rule_fAllocs typ Gp R P E ys fns size l :
  evalExp E size (Zn l)
  -> ST_ok (preST ys fns (Assn R P E) Gp)
           (fAllocs typ size)
           (fun x => postST (K ys x) (K fns x) (Assn R P E)
                            (Ex ps vs, (Assn (arrays (val2gl ps) vs 1 *** R)) (Datatypes.length vs = l /\ P) (x |=> ps ++ E))
                            Gp (K Gp x)).
Proof.
  intros Heval.
  unfold fAllocs.
  apply code_ok_float; intros Hfns Hdxy Hdfs.
  eapply rule_bind'.
  { applys* rule_fLet. }
  intros s; simpl.
  eapply rule_backward.
  apply rule_fAllocs'; eauto.
  introv.
  apply postST_imp; eauto.
  - intros stk hp (ps & vs & Hsat); exists ps vs; revert stk hp Hsat; prove_imp.
  - introv H; rewrite !fv_assn_Ex_eq in *.
    introv; specialize (H v0).
    rewrite !fv_assn_Ex_eq in *.
    introv; specialize (H v1).
    rewrite fv_assn_base_eq in *; simpl in *.
    unfold incl in *; intros a Hin; forwards*: H; simpl in *; eauto.
Qed.

Lemma fnOk_weaken fn n m :
  n <= m
  -> fnOk fn n 
  -> fnOk fn m.
Proof.
  unfold fnOk; rewrite !Forall_forall; intros.
  forwards*: H0; omega.
Qed.

Lemma fnOk_ge n m xs :
  fnOk xs n -> n <= m -> ~ In (kname m) xs.
Proof.
  unfold fnOk; rewrite Forall_forall; intros H ? Hc.
  forwards*: H; omega.
Qed.
  
Lemma fnOk'_ge n m xs :
  fnOk' xs n -> n <= m -> ~ In (kname m) xs.
Proof.
  unfold fnOk'; rewrite Forall_forall; intros H ? Hc.
  forwards*(? & ? & ?): H.
  apply kname_inj in H1; substs; omega.
Qed.

Lemma rule_freshF G P ys fns :
  ST_ok (preST ys fns P G)
        freshF
        (fun fn => postST (K ys fn) (fn :: fns) P (K P fn) G (K G fn)).
Proof.
  unfold ST_ok, freshP, postST, preST.
  introv (HxsOk & HfnsOk & HysOk & HgnsOk & Hys & Hgns & HsatF & HdisGMp & HinclG & HGMpOk) Heq. 
  inverts Heq.
  splits; [..|splits]; repeat rewrite app_nil_r; jauto; try omega.
  - constructor.
    + exists m; splits; eauto.
    + applys (>>fnOk'_weaken HfnsOk); omega.
  - split; eauto.
    eapply fnOk'_ge; jauto.
  - split; jauto.
    eapply fnOk'_ge; eauto.
  - constructor.
  - eapply fnOk'_weaken; [|jauto]; omega.
  - repeat rewrite app_nil_r.
    apply rule_host_skip.
Qed.  

Lemma sat_FC_weaken M G fn fd fs : 
  ~In fn (map fst M)
  -> fc_ok M G
  -> fn_ok ((fn, fd) :: nil) fn fs
  -> interp_fd (M ++ (fn, fd) :: nil) (G ++ (fn, fs) :: nil) fd fs
  -> disjoint_list (map fst M)
  -> sat_FC M nil G
  -> sat_FC (M ++ (fn, fd) :: nil) nil (G ++ (fn, fs) :: nil).
Proof.
  intros Hnin Hcok Hnok Hf Hdis Hsat.
  apply rule_module_rec.
  { Lemma fc_ok_app M G G' :
      fc_ok M G -> fc_ok M G' -> fc_ok M (G ++ G').
    Proof.
      induction G as [|[? ?] ?]; simpl; eauto.
      intuition.
    Qed.
    apply fc_ok_app; simpl.
    Lemma fc_ok_weaken M M' G :
      fc_ok M G -> fc_ok (M ++ M') G.
    Proof.
      induction G as [|[? ?] ?]; simpl; eauto.
      intuition.
      Lemma fn_ok_weaken M M' fn fs :
        fn_ok M fn fs -> fn_ok (M ++ M') fn fs.
      Proof.
        unfold fn_ok; induction M as [|[? ?] ?]; simpl; try tauto.
        destruct string_dec; substs; eauto.
      Qed.
      apply fn_ok_weaken; eauto.
    Qed.
    applys* fc_ok_weaken.
    Lemma fn_ok_ignore M M' fn fs :
      fn_ok M' fn fs -> ~In fn (map fst M) -> fn_ok (M ++ M') fn fs.
    Proof.
      unfold fn_ok.
      Lemma func_disp_app M M' fn :
        func_disp (M ++ M') fn = match func_disp M fn with
                                 | Some fd => Some fd
                                 | None => func_disp M' fn
                                 end.
      Proof.
        induction M as [|[? ?] ?]; simpl; eauto.
        destruct string_dec; eauto.
      Qed.
      rewrite func_disp_app.
      intros; 
      cutrewrite (func_disp M fn = None); eauto.
      rewrite func_disp_not_in; intros ? Hc.
      apply H0; apply in_map_iff; eexists; split; simpl; eauto.
      eauto.
    Qed.
    split; eauto; applys* fn_ok_ignore. }
  unfold sat_FC in *; introv Hctx.
  specialize (Hsat n).
  unfold interp_FC_n in *; rewrite !Forall_forall in *.
  intros [fn' fs'] Hin; simpl in *.
  rewrite in_app_iff in *; simpl in *; destruct Hin as [Hin| [Hin | []]].
  - forwards*: (>>Hsat Hin).
    revert Hnin Hdis Hctx H; clear; intros.
    unfold interp_f_n in *.
    destruct (func_disp M fn') eqn:HMfn'; try tauto.
    apply func_disp_in in HMfn'; try tauto.
    rewrite in_map_iff in Hnin.
    destruct (func_disp (M ++ _) fn') eqn:HMfnfn'.
    Focus 2.
    { rewrite func_disp_not_in in HMfnfn'.
      specialize (HMfnfn' f); rewrite !in_app_iff in HMfnfn'; simpl in HMfnfn';
      apply HMfnfn'; eauto. } Unfocus.
    Lemma func_disp_pref M M' fn fd :
      func_disp M fn = Some fd -> func_disp (M ++ M') fn = Some fd.
    Proof.
      induction M; simpl; try congruence.
      destruct a, string_dec; eauto.
    Qed.            
    apply func_disp_in in HMfn'; eauto.
    erewrite func_disp_pref in HMfnfn'; eauto.
    inverts HMfnfn'; destruct f0; eauto.
    unfold interp_fd_simp, interp_hfun_n_simp in *.
    destruct fs' as [tag' params' tri'].
    revert Hnin Hdis Hctx H; clear; induction tri'; simpl; eauto; intros ? ? ?.
    unfold CSLhfun_n_simp; intros Hsat; intros.
    eapply safe_nhfun_weaken; eauto.
    2: unfold incl; intros; rewrite in_app_iff; simpl; eauto.
    rewrite map_app; simpl.
    apply disjoint_list_app; simpl; eauto.
    introv; rewrite in_map_iff; intros [? [? ?]] [Hc | []]; eauto.
    apply Hnin; eexists; splits; substs; eauto.
  - inverts Hin.
    unfold interp_f_n in *.
    Lemma func_disp_npref M M' fn :
      ~In fn (map fst M) -> func_disp (M ++ M') fn = func_disp M' fn.
    Proof.
      induction M as [|[? ?] ?]; simpl; eauto.
      destruct string_dec; substs.
      intros; false; eauto.
      intros; eauto.
    Qed.
    rewrites* func_disp_npref.
    simpl; destruct string_dec; try congruence.
    apply Hf.
    unfold interp_FC_n; rewrite Forall_forall.
    intros; applys* Hctx.
Qed.

Lemma rule_gen_kernel G P ys fns k fs:
  fs_tag fs = Kfun 
  -> fs_params fs = map fst (params_of k)
  -> (forall M, sat_FC M G G -> interp_kfun M G k fs)
  -> ST_ok (preST ys fns P G)
           (gen_kernel k)
           (fun fn => postST (K ys fn) (K fns fn) P (K P fn) G (G ++ (fn, fs) :: nil)).
Proof.
  intros Htag Hparams HkOk Hfv.
  unfold gen_kernel.
  applys* rule_bind'.
  (* { intros y; instantiate (1 := fun y => (y, fs) :: nil); instantiate (1 := nil); eauto. } *)
  { applys* rule_freshF. }
  intros fn; simpl.
  
  Lemma rule_ret_back (T T' : Type) (m : CUDAM T) (v : T') P Q Gp G fns ys fns' ys' :
    ST_ok (preST ys fns P Gp) (do! _ <- m in ret v) (fun x => postST (ys' v) (fns' v) P (Q v) Gp (G v))
    -> ST_ok (preST ys fns P Gp) (do! _ <- m in ret v) (fun x => postST (ys' x) (fns' x) P (Q x) Gp (G x)).
  Proof.
    unfold ST_ok; simpl; eauto; intros.
    unfold bind in *; simpl in *.
    destruct m as [? [[[? ?] ?] ?]] eqn:Heq.
    inversion H1; substs.
    lets*: (>>H n m0 n' m' H0).
    rewrite Heq in H2.
    forwards*: H2.
  Qed.
  apply rule_ret_back.
  apply code_ok_float; intros.
  eapply rule_bind'.
  (* { instantiate (1 := K nil); instantiate (1 := (fn, fs) :: nil); eauto. } *)
  { instantiate (1 := K (G ++ (fn, fs) :: nil)).
    instantiate (1 := K P).
    instantiate (1 := K fns).
    instantiate (1 := K ys).
    unfold postST; introv (HxsOk & HfnsOk & HysOk & HgnsOk & Hys & Hgns & HsatF & HdisGMp & HinclG & HGMpOk) Heq.  
    inverts Heq.
    repeat rewrite app_nil_r in *; repeat rewrite map_app in *.
    simpl in *.
    splits; [..|splits]; jauto.
    inverts HfnsOk; unfold fnOk; eauto.
    apply disjoint_app; splits; jauto.
    apply disjoint_list_app; jauto.
    simpl; eauto.
    introv ? [Hc | []]; substs; jauto.
    unfold fnOk in HfnsOk; inverts HfnsOk.
    constructor; eauto.
    apply Forall_app; jauto.
    inverts HfnsOk; constructor; eauto.
    apply fc_ok_app; simpl.
    applys* fc_ok_weaken.
    splits; eauto; applys* fn_ok_ignore.
    unfold fn_ok; simpl; destruct string_dec; try congruence.
    destruct k; splits; eauto.
    2: apply rule_host_skip.
    apply sat_FC_strong.
    forwards*: HkOk.
    apply rule_module_rec in HsatF; jauto.
    apply sat_FC_weaken; jauto.
    unfold fn_ok; simpl; destruct string_dec; try tauto; destruct k; split; eauto.
    unfold sat_FC in *; intros ? Hhyp.
    unfold  interp_FC_n in *; rewrite Forall_forall in *.
    simpl.
    apply H2.
    apply HsatF; constructor. }
  introv; simpl.
  apply (rule_ret _ _ (fun _ => ys) (fun _ => fns) (fun _ => P) (G ++ (fn, fs) :: nil)); eauto.
Qed.

Lemma rule_invokeKernel kerID fs ntrd nblk args G R (P : Prop) E Epre Rpre RF Ppre Q ys fns vs enb ent :
  In (kerID, fs) G
  -> fs_tag fs = Kfun
  -> length args = length (fs_params fs)
  -> (P -> inst_spec (fs_tri fs) (Assn Rpre Ppre Epre) Q)
  -> has_no_vars (Q 0%Z)
  -> evalExpseq E (enb :: ent :: args) (Zn nblk :: Zn ntrd :: vs)
  -> ntrd <> 0 -> nblk <> 0
  -> (P -> subst_env Epre (Var "nblk" :: Var "ntrd" :: fs_params fs) (Zn nblk :: Zn ntrd :: vs))
  -> (P -> Ppre)
  -> (P -> R |=R Rpre *** RF)
  -> ST_ok (preST ys fns (Assn R P E) G)
           (invokeKernel kerID ent enb args)
           (fun r => postST (K ys r) (K fns r) (Assn R P E) (K (Assn RF P E ** Q 0%Z) r) G (K G r)).
Proof.
  unfold ST_ok, preST, postST.
  intros.
  inverts H11.
  rewrite !app_nil_r.
  splits; [..|splits]; jauto.
  destruct H10 as ((xs' & ? & ? & ?) & _); exists xs'; splits; jauto.
  unfold K.
  
  apply fv_assn_sep_eq.
  exists xs' (nil : list var).
  splits; jauto.
  rewrites* fv_assn_base_eq in *.
  simpl; intros; tauto.
  Lemma CSLh_pure_prem M G R (P : Prop) E ss Q :
    (P -> CSLh M G (Assn R P E) ss Q)
    -> CSLh M G (Assn R P E) ss Q.
  Proof.
    intros H.
    intros n Hctx s h Hsat.
    unfold sat in Hsat; simpl in Hsat.
    apply H; jauto.
    unfold sat; simpl; jauto.
  Qed.
  constructor.
  apply CSLh_pure_prem; intros Hp.
  eapply rule_host_seq.
  applys (>>rule_invk H2 H4); jauto.
  apply rule_host_skip.
Qed.

Lemma rule_ret_ignore (T : Type) xs fns P Q Gp (v : T) :
  P |= Q
  -> (forall xs, fv_assn P xs -> fv_assn Q xs)
  -> ST_ok (preST xs fns P Gp) (ret v) (fun _ => postST xs fns P Q Gp Gp).
Proof.
  unfold ST_ok, preST, postST.
  introv Hpq Hfv (? & ? & ? & ? & ? & ? & ? & ? & ? & ?) Heq. 
  inverts Heq.
  destruct H as (? & ? & ? & ?).
  rewrite !app_nil_r.
  splits; [..|splits]; jauto.
  constructor.
  eapply rule_host_backward; eauto.
  eapply rule_host_skip.
Qed.

Lemma rule_equiv_mono_pre T xs fns xs' fns' (P P' : assn) (Q : T -> assn) Gp G (m : CUDAM T) :
  P' |= P
  -> (forall xs, fv_assn P' xs -> fv_assn P xs)
  -> ST_ok (preST xs fns P Gp) m (fun x => postST (xs' x) (fns' x) P (Q x) Gp (G x))
  -> ST_ok (preST xs fns P' Gp) m (fun x => postST (xs' x) (fns' x) P' (Q x) Gp (G x)).
Proof.
  unfold ST_ok, preST, postST; intros.
  forwards*: H1.
  splits; [..|splits]; jauto.
  splits; [..|splits]; jauto.
  Lemma rule_host_forward GM G P P' Q C :
    CSLh GM G P C Q -> P' |= P -> CSLh GM G P' C Q.
  Proof.
    intros ? ? ? ? ? ? ?.
    apply H; eauto.
  Qed.
  eapply rule_host_forward; jauto.
Qed.

Lemma ST_ok_exec T xs fns P Q Gp G (gen : CUDAM T) res ss Mp M n m n' m' :
  (exists fvs, fv_assn P fvs /\ forall x m, In x fvs -> x <> hvar m)
  -> fnOk' (map fst Mp) m
  -> sat_FC Mp Gp Gp
  -> fc_ok Mp Gp
  -> disjoint_list (map fst Mp)
  -> ST_ok (preST nil nil P Gp) gen (fun x => postST (xs x) (fns x) P (Q x) Gp (G x))
  -> (res, ((n', m'), ss, M)) = gen n m
  -> fc_ok (Mp ++ M) (G res) /\
     disjoint_list (map fst Mp ++ map fst M) /\
     fnOk' (map fst M) m' /\
     sat_FC (Mp ++ M) nil (G res) /\
     CSLh (Mp ++ M) (G res) P (seqs ss) (Q res).
Proof.
  unfold ST_ok, preST, postST.
  intros Hfv Hfn Hsat Hfc Hdisj Hok Heq.
  forwards*: (>>Hok ss Mp M).
  Hint Constructors Forall.
  splits; [..|splits]; simpl; try now (unfold fnOk, fvOk; jauto).
  { destruct Hfv as (? & ? & ?); eexists; splits; jauto.
    unfold fvOk; rewrite Forall_forall; intros.
    forwards*: (>>H0 H2). }
  constructor.
  rewrite map_app in *.
  splits; jauto.
  apply rule_module_rec; jauto.
Qed.
