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

Definition STPre : Type := nat -> nat -> GModule -> Prop.
Definition STPost : Type := 
  nat -> nat (* pre state *)
  -> nat -> nat (* post state *)
  -> GModule -> stmt (* generated code *)
  -> Prop.
(* Definition assnStmt : Type := GModule -> stmt -> Prop. *)

Definition ST_ok {T} (P : STPre) (gen : CUDAM T) (Q : T -> STPost) :=
  forall (n m n' m' : nat) st GMp GM v,
    P n m GMp
    -> gen n m = (v, (n', m', st, GM))
    -> Q v n m n' m' (GMp ++ GM) (seqs st).

Parameter fv_assn : assn -> list var -> Prop.
Axiom fv_assn_ok : forall P xs ys,
    fv_assn P xs -> disjoint xs ys -> inde P ys.
Axiom fv_assn_base :
  forall R P E xs, fv_assn (Assn R P E) xs <-> incl (List.map ent_e E) xs.
Axiom fv_assn_Ex :
  forall T (P : T -> assn) xs, fv_assn (Ex v, P v) xs <-> (forall v, fv_assn (P v) xs).

Definition hvar n := Var ("h" ++ nat2str n).
Definition kname n := ("_ker" ++ nat2str n)%string.

Definition fvOk xs n : Prop :=
  List.Forall (fun x => exists m, x = hvar m /\ m < n) xs.
Definition fnOk fns n : Prop :=
  List.Forall (fun fn => exists m, fn = kname m /\ m < n) fns.

Definition preST xs fns ys Gp : STPre := fun n m M =>
  fvOk xs n /\ fnOk fns m /\ fvOk ys n /\ 
  disjoint ys xs /\ disjoint fns (map fst M) /\
  disjoint_list ys /\
  sat_FC M Gp Gp /\ disjoint_list (map fst M) /\
  incl (map fst Gp) (map fst M) /\ 
  fnOk (map fst M) m.

Definition postST (P Q : assn) (Gp G : FC) xs fns ys : STPost := fun n m n' m' M st =>
  n <= n' /\ m <= m' /\
  fv_assn Q xs /\ 
  
  fvOk xs n' /\ fnOk fns m' /\ fvOk ys n' /\ 
  disjoint ys xs /\ disjoint fns (map fst M) /\
  disjoint_list ys /\
  disjoint_list (map fst M) /\
  fnOk (map fst M) m' /\

  incl (map fst (Gp ++ G)) (map fst M) /\
  sat_FC M (Gp ++ G) (Gp ++ G) /\
  CSLh_n M (Gp ++ G) P st Q.

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
  destruct H as (m' & ? & ?); exists m'; splits; eauto; omega.
Qed.

Lemma fvOk_ge n m xs :
  fvOk xs n -> n <= m -> ~ In (hvar m) xs.
Proof.
  unfold fvOk; rewrite Forall_forall; intros H ? Hc.
  forwards* (? & ? & ?): H.
  apply hvar_inj in H1; omega.
Qed.

Lemma rule_fresh P G xs fns ys :
  fv_assn P xs
  -> ST_ok (preST xs fns ys G)
           freshP
           (fun x => postST P (K P x) G (K nil x) (K xs x) (K fns x) (x :: ys)).
Proof.
  unfold ST_ok, freshP, postST, preST.
  introv (HxsOk & HfnsOk & HysOk & HgnsOk & Hys & Hgns) Heq. 
  inverts Heq.
  splits; [..|splits]; repeat rewrite app_nil_r; jauto; try omega.
  - applys (>>fvOk_weaken HxsOk); omega.
  - constructor.
    + exists n; splits; eauto.
    + applys (>>fvOk_weaken HysOk); omega.
  - split; eauto.
    applys* fvOk_ge.
  - simpl; splits; jauto.
    eapply fvOk_ge; eauto.
  - repeat rewrite app_nil_r.
    apply rule_host_skip.
Qed.      

Lemma rule_fresh' P G xs fns ys :
  fv_assn P xs
  -> ST_ok (preST xs fns ys G)
           freshP
           (fun x => postST P (K P x) G nil (K xs x) (K fns x) (x :: ys)).
Proof.
  cutrewrite ((fun x => postST P (K P x) G nil (K xs x) (K fns x) (x :: ys)) =
              (fun x => postST P (K P x) G (K nil x) (K xs x) (K fns x) (x :: ys))); [|eauto].
  apply rule_fresh.
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
  CSLh_n GM G P st Q
  -> CSLh_n GM G Q st' R
  -> CSLh_n GM G P (hseq st st') R.
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

Lemma rule_setI G P Q ss xs ys xs' fns  :
  (forall GM, sat_FC GM G G -> CSLh_n GM G P ss Q)
  -> fv_assn Q (xs' ++ xs)
  -> incl xs' ys
  -> ST_ok (preST xs fns ys G)
           (setI ss)
           (fun x => postST P (K Q x) G (K nil x) (K (xs' ++ xs) x) (K fns x) 
                            (K (remove_xs ys xs') x)).
Proof.
  unfold ST_ok, freshP, postST, preST, K.
  introv Hsat Hfv Hincl (HxsOk & HfnsOk & HysOk & Hdisjysxs & Hdisjfns & HsatG & HdisjGM & HokGM) Heq. 
  inverts Heq.
  splits; [..|splits]; repeat rewrite app_nil_r; jauto.
  - apply fvOk_app; eauto.
    applys* fvOk_incl.
  - applys (>>fvOk_incl HysOk).
    apply remove_xs_incl.
  - rewrite disjoint_app; splits.
    apply disjoint_remove_xs.
    applys* (>>disjoint_incl_r Hdisjysxs); apply remove_xs_incl.
  - applys* disjoint_list_removed.
  - eapply rule_host_seq; [eauto|apply rule_host_skip].
Qed.  

Lemma rule_setI' G P Q ss xs ys xs' fns  :
  (forall GM, sat_FC GM G G -> CSLh_n GM G P ss Q)
  -> fv_assn Q (xs' ++ xs)
  -> incl xs' ys
  -> ST_ok (preST xs fns ys G)
           (setI ss)
           (fun x => postST P (K Q x) G nil (K (xs' ++ xs) x) (K fns x) 
                            (K (remove_xs ys xs') x)).
Proof.
  cutrewrite ((fun x => postST P (K P x) G nil (K xs x) (K fns x) (x :: ys)) =
              (fun x => postST P (K P x) G (K nil x) (K xs x) (K fns x) (x :: ys))); [|eauto].
  apply rule_setI.
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

Definition ExStmt {T} (f : T -> STPost) := fun n m n' m' gm st => exists x, f x n m n' m' gm st.

Lemma rule_bind T1 T2
      xs ys fns 
      xs' ys' fns' 
      xs'' ys'' fns'' 
      P Q Gp G G' R 
      (gen : CUDAM T1) (gen' : T1 -> CUDAM T2) :
  ST_ok (preST xs fns ys Gp)
        gen
        (fun x => postST P (Q x) Gp (G x) (xs' x) (fns' x) (ys' x))
  -> (forall x,
         ST_ok (preST (xs' x) (fns' x) (ys' x) (Gp ++ G x))
               (gen' x)
               (fun y => postST (Q x) (R x y) (Gp ++ G x) (G' x y) 
                                (xs'' x y) (fns'' x y) (ys'' x y)))
  -> ST_ok (preST xs fns ys Gp)
           (bind gen gen')
           (fun y => ExStmt (fun x => postST P (R x y) Gp (G x ++ G' x y)
                                             (xs'' x y) (fns'' x y) (ys'' x y))).
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
  eapply rule_app_seqs; jauto.
  applys* (>>CSLh_n_weaken (M0 ++ M') (Gp ++ G v) ); try rewrite !map_app; 
    (try now (rewrite app_assoc; apply incl_appl; apply incl_refl)); jauto.
  apply fc_ok_same; rewrite !map_app; jauto.
Qed.  

Lemma rule_forward T (P' P : STPre) (Q : T -> STPost) gen :
  ST_ok P gen Q -> (forall n c M, P' n c M -> P n c M) -> ST_ok P' gen Q.
Proof.
  unfold ST_ok; eauto.
Qed.

Lemma rule_backward T (P : STPre) (Q Q' : T -> STPost) gen :
  ST_ok P gen Q -> (forall v n m n' m' M st, Q v n m n' m' M st -> Q' v n m n' m' M st) -> ST_ok P gen Q'.
Proof.
  unfold ST_ok; eauto.
Qed.

Lemma rule_bind' T1 T2
      xs ys fns 
      xs' ys' fns' 
      xs'' ys'' fns'' 
      P Q Gp G G' R 
      (gen : CUDAM T1) (gen' : T1 -> CUDAM T2) :
  ST_ok (preST xs fns ys Gp)
        gen
        (fun x => postST P (Q x) Gp G (xs' x) (fns' x) (ys' x))
  -> (forall x,
         ST_ok (preST (xs' x) (fns' x) (ys' x) (Gp ++ G))
               (gen' x)
               (fun y => postST (Q x) (R y) (Gp ++ G) (G' y) 
                                (xs'' y) (fns'' y) (ys'' y)))
  -> ST_ok (preST xs fns ys Gp)
           (bind gen gen')
           (fun y => postST P (R y) Gp (G ++ G' y)
                            (xs'' y) (fns'' y) (ys'' y)).
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

Lemma rule_ret (T : Type) (v : T) xs ys fns P Gp :
  fv_assn (P v) (xs v)
  -> ST_ok (preST (xs v) (ys v) (fns v) Gp) (ret v) (fun u => postST (P v) (P u) Gp (K nil u) (xs u) (ys u) (fns u)).
Proof.
  unfold ST_ok, preST, postST; intros.
  inverts H1.
  splits; [..|splits]; try rewrite !app_nil_r; try omega; jauto.
  apply rule_host_skip.
Qed.

Arguments ret {f _ A} x : simpl never.
Arguments bind {f _ A B} _ _ : simpl never.

Lemma code_ok_float T xs ys fns Gp (m : CUDAM T) Q :
  (disjoint ys xs -> disjoint_list ys -> ST_ok (preST xs fns ys Gp) m Q)
  -> ST_ok (preST xs fns ys Gp) m Q.
Proof.
  unfold ST_ok, preST; intros H; intros.
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

Lemma remove_xs_disj xs ys : disjoint xs ys -> remove_xs xs ys = xs.
Proof.
  induction xs; simpl; eauto.
  intros; destruct in_dec; try tauto; eauto.
  rewrite IHxs; jauto.
Qed.

Lemma incl_cons_lr A (x : A) xs ys : incl xs ys -> incl (x :: xs) (x :: ys).
Proof. unfold incl; introv; simpl; intuition. Qed.

Lemma rule_fLet Gp R P E xs ys e v fns :
  fv_assn (Assn R P E) xs 
  -> evalExp E e v
  -> ST_ok (preST xs ys fns Gp)
           (fLet e)
           (fun x => postST (Assn R P E) (Assn R P (x |-> v :: E)) Gp nil (x :: xs) ys fns).
Proof.
  unfold fLet; intros Hfv Heval.
  eapply rule_backward.
  eapply rule_bind'.
  applys* rule_fresh'.
  introv.
  simpl.
  apply code_ok_float; intros Hdxy Hdy; simpl in Hdxy, Hdy.
  applys* (>>rule_bind' (Assn R P E)).
  applys (>>rule_setI' (x :: nil)).
  { intros; applys* rule_host_let. }
  apply fv_assn_base; simpl.
  unfold incl; introv; simpl; repeat rewrite in_app_iff in *; eauto.
  destruct 1; eauto.
  rewrite fv_assn_base in Hfv.
  right; apply remove_var_incl' in H.
  applys* Hfv.
  unfold incl; introv; simpl; tauto.
  simpl; destruct var_eq_dec; try congruence.
  rewrites* remove_xs_disj.
  introv.
  rewrite remove_var_disjoint.
  2: intros Hc; rewrite fv_assn_base in *; apply Hfv in Hc; unfold K in *; tauto.
  eapply (rule_ret _ x (fun x => (x :: K xs x))
                   (fun x => K ys x)
                   (fun x => fns)
                   (fun x' => Assn R P (x' |-> v :: E))).
  unfold K; rewrite fv_assn_base.
  simpl.
  apply incl_cons_lr.
  rewrite fv_assn_base in Hfv; eauto; simpl.
  eauto.
Qed.      

(* Definition ex_st {T} (f : T -> assnST) : assnST := *)
(*   fun n st gm => exists x, f x n st gm. *)

(* Notation "'Ex_st' x .. y , p" := (ex_st (fun x => .. (ex_st (fun y => p)) ..)) *)
(*   (at level 200, x binder, right associativity). *)

Lemma rule_fAlloc Gp R P E xs ys len l fns :
  fv_assn (Assn R P E) xs 
  -> evalExp E len (Zn l)
  -> ST_ok (preST xs ys fns Gp)
           (fAlloc len)
           (fun x => postST (Assn R P E)
                            (Ex p vs, (Assn (array (GLoc p) vs 1 *** R)) (Datatypes.length vs = l /\ P) (x |-> p :: E))
                            Gp nil (x :: xs) ys fns).
Proof.
  unfold fLet; intros Hfv Heval.
  eapply rule_backward.
  eapply rule_bind'.
  applys* rule_fresh'.
  introv.
  simpl.
  apply code_ok_float; intros Hdxy Hdy; simpl in Hdxy, Hdy.
  applys* (>>rule_bind' (Assn R P E)).
  applys (>>rule_setI' (x :: nil)).
  { intros; applys* rule_host_alloc. }
  do 2 (apply fv_assn_Ex; intros); apply fv_assn_base; simpl.
  unfold incl; introv; simpl; repeat rewrite in_app_iff in *; eauto.
  destruct 1; eauto.
  rewrite fv_assn_base in Hfv.
  right; apply remove_var_incl' in H.
  applys* Hfv.
  unfold incl; introv; simpl; tauto.
  simpl; destruct var_eq_dec; try congruence.
  rewrites* remove_xs_disj.
  introv.
  rewrite remove_var_disjoint.
  2: intros Hc; rewrite fv_assn_base in *; apply Hfv in Hc; unfold K in *; tauto.
  eapply (rule_ret _ x (fun x => (x :: K xs x))
                   (fun x => K ys x)
                   (fun x => fns)
                   (fun x' => Ex (p : val) (vs : list val),
                              Assn (array (GLoc p) vs 1 *** R) (Datatypes.length vs = l /\ P)
                                   (x' |-> p :: E))).
  unfold K; do 2 (apply fv_assn_Ex; intros); rewrite fv_assn_base.
  simpl.
  apply incl_cons_lr.
  rewrite fv_assn_base in Hfv; eauto; simpl.
  eauto.
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

Lemma rule_code_ex (T A : Type) `{hd_A : hasDefval A} (gen : CUDAM T) (Gp G : T -> FC)
      P xs ys fns (p : T -> A -> assn) (q : T -> assn) :
  (forall y, ST_ok P gen (fun (x : T) => postST (p x y) (q x) (Gp x) (G x) (xs x) (fns x) (ys x)))
  -> ST_ok P gen (fun (x : T) => postST (Ex y, p x y) (q x) (Gp x) (G x) (xs x) (fns x) (ys x)).
Proof.
  unfold ST_ok, postST; intros.
  assert (H' : forall (n m n' m' : nat) (st : list stmt) 
        (GMp GM : GModule) (v : T),
      P n m GMp ->
      gen n m = (v, (n', m', st, GM)) ->
      n <= n' /\
      m <= m' /\
      fv_assn (q v) (xs v) /\
      fvOk (xs v) n' /\
      fnOk (fns v) m' /\
      fvOk (ys v) n' /\
      disjoint (ys v) (xs v) /\
      disjoint (fns v) (map fst (GMp ++ GM)) /\
      disjoint_list (ys v) /\
      disjoint_list (map fst (GMp ++ GM)) /\
      fnOk (map fst (GMp ++ GM)) m' /\
      incl (map fst (Gp v ++ G v)) (map fst (GMp ++ GM)) /\
      sat_FC (GMp ++ GM) (Gp v ++ G v) (Gp v ++ G v) /\
      forall (y : A), CSLh_n (GMp ++ GM) (Gp v ++ G v) (p v y) (seqs st) (q v)).
  { intros.
    forwards*: (H default); splits; [..|splits]; jauto.
    introv.
    forwards*: (H y). }
  forwards*H'': H'.
  splits; [..|splits]; jauto.
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

Lemma usable_fn_weaken fn n m :
  n <= m
  -> usable_fn fn n 
  -> usable_fn fn m.
Proof.
  unfold usable_fn; intros ? H ? H'; forwards*: (>>H H'); omega.
Qed.
  
Lemma usable_fns_weaken fns n m :
  n <= m
  -> usable_fns fns n 
  -> usable_fns fns m.
Proof.
  intros Hmn H; induction H; constructor; eauto using usable_fn_weaken.
Qed.

Lemma kname_inj m n : kname m = kname n -> m = n.
Proof.
  unfold kname; intros H.
  inverts H.
  forwards*: (>>nat_to_string_inj H1).
Qed.

Lemma lt_usable_fn n m :
  m < n -> usable_fn (kname m) n.
Proof.
  intros Hmn m' Heq.
  forwards*: (>>kname_inj Heq); omega.
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
    + applys (>>usable_fns_weaken Hfns); omega.
    + constructor.
      * apply lt_usable_fn; omega.
      * applys (>>usable_fns_weaken Hfns'); omega.
    + simpl; splits; eauto.
      * apply disjoint_comm; split; eauto using disjoint_comm.
        intros Hc.
        unfold usable_fns in Hfns; rewrite Forall_forall in Hfns.
        forwards* H: Hfns.
        forwards*: H; omega.
      * intros Hc.
        unfold usable_fns in Hfns'; rewrite Forall_forall in Hfns'.
        forwards* H: Hfns'.
        forwards*: H; omega.
  - intros; splits; try rewrite !app_nil_r; simpl; eauto.
    simpl; apply rule_host_skip.
Qed.  

Lemma rule_gen_kernel k xs ys fns fns' :
  ST_ok (var_ok xs ys fns fns') 
        (gen_kernel k) 
        (fun kn => )
        (fun kn => )