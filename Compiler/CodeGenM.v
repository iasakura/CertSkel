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
  disjoint_list fns /\
  sat_FC M Gp Gp /\ disjoint_list (map fst M) /\
  incl (map fst Gp) (map fst M) /\ 
  fnOk (map fst M) m.

Definition postST (P Q : assn) (Gp G : FC) xs fns ys : STPost := fun n m n' m' M st =>
  n <= n' /\ m <= m' /\
  fv_assn Q xs /\ 
  
  fvOk xs n' /\ fnOk fns m' /\ fvOk ys n' /\ 
  disjoint ys xs /\ disjoint fns (map fst M) /\
  disjoint_list ys /\
  disjoint_list fns  /\
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
  - eapply rule_host_seq; [jauto|apply rule_host_skip].
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
      P Q Gp G G' G'' R 
      (gen : CUDAM T1) (gen' : T1 -> CUDAM T2) :
  (forall y, G ++ G' y = G'' y) 
  -> ST_ok (preST xs fns ys Gp)
        gen
        (fun x => postST P (Q x) Gp G (xs' x) (fns' x) (ys' x))
  -> (forall x,
         ST_ok (preST (xs' x) (fns' x) (ys' x) (Gp ++ G))
               (gen' x)
               (fun y => postST (Q x) (R y) (Gp ++ G) (G' y) 
                                (xs'' y) (fns'' y) (ys'' y)))
  -> ST_ok (preST xs fns ys Gp)
           (bind gen gen')
           (fun y => postST P (R y) Gp (G'' y)
                            (xs'' y) (fns'' y) (ys'' y)).
Proof.
  intros.
  cutrewrite ((fun y : T2 => postST P (R y) Gp (G'' y) (xs'' y) (fns'' y) (ys'' y)) =
          (fun y : T2 => postST P (R y) Gp (G ++ G' y) (xs'' y) (fns'' y) (ys'' y))); [|eauto].
  eapply rule_backward.
  eapply rule_bind; [apply H0|apply H1].
  introv [? ?]; eauto.
  extensionality x; simpl; rewrites* H. 
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
  (disjoint_list fns -> disjoint ys xs -> disjoint_list ys -> ST_ok (preST xs fns ys Gp) m Q)
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
           (fun x => postST (Assn R P E) (Assn R P (x |-> v :: E)) Gp (K nil x) (x :: xs) (K ys x) (K fns x)).
Proof.
  unfold fLet; intros Hfv Heval.
  eapply rule_bind'.
  { instantiate (1 := fun _ => nil); instantiate (1 := nil); eauto. }
  applys* rule_fresh'.
  introv.
  simpl.
  apply code_ok_float; intros Hdfns Hdxy Hdy; simpl in Hdxy, Hdy.
  applys* (>>rule_bind' (Assn R P E)).
  { instantiate (1 := fun _ => nil); instantiate (1 := nil); eauto. }
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
                            Gp (K nil x) (x :: xs) (K ys x) (K fns x)).
Proof.
  unfold fLet; intros Hfv Heval.
  eapply rule_bind'.
  { instantiate (1 := K nil); instantiate (1 := nil); eauto. }
  applys* rule_fresh'.
  introv.
  simpl.
  apply code_ok_float; intros Hdfns Hdxy Hdy; simpl in Hdxy, Hdy.
  applys* (>>rule_bind' (Assn R P E)).
  { instantiate (1 := K nil); instantiate (1 := nil); eauto. }
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
      disjoint_list (fns v) /\
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

Lemma rule_fAllocs' typ Gp R P E (size : var) xs ys l fns :
  fv_assn (Assn R P E) xs 
  -> ST_ok (preST (size :: xs) fns ys Gp)
           (fAllocs' typ size)
           (fun x => postST (Assn R P (size |-> Zn l :: E))
                            (Ex ps vs, (Assn (arrays (val2gl ps) vs 1 *** R)) (Datatypes.length vs = l /\ P) (size |-> Zn l :: x |=> ps ++ E))
                            Gp (K nil x) (size :: flatTup x ++ xs) (K fns x) (K ys x)).
Proof.
  rewrite fv_assn_base.
  revert R P E xs ys; induction typ; simpl; eauto; simpl; introv Hfv.
  - eapply rule_backward.
    applys (>>rule_fAlloc (size |-> G.Zn l :: E)).
    2: evalExp.
    rewrite fv_assn_base; simpl.
    apply incl_cons_lr; eauto.
    simpl; intros.
    unfold postST in *; splits; [..|splits]; jauto.
    { do 2 (apply fv_assn_Ex; intros).
      destruct H as (_ & _ & H' & _).
      rewrite fv_assn_Ex in H'.
      specialize (H' v0).
      rewrite fv_assn_Ex in H'.
      specialize (H' v1).
      rewrite fv_assn_base in *.
      unfold incl in *; simpl in *; intros; forwards*: H'. }
    { destruct H as (_ & _ & _ & H' & _).
      constructor; [|constructor]; inverts H' as ? H'; inverts H'; eauto. }
    { destruct H as (_ & _ & _ & _ & _ & _ & H' & _).
      apply disjoint_comm in H'; apply disjoint_comm; simpl in *; tauto. }
    eapply rule_host_backward; [jauto|].
    intros s h (p & vs & Hsat); exists p vs; revert s h Hsat; prove_imp.
    rewrite mkReduce.arrays_TB; eauto.
  - eapply rule_backward.
    applys (>>rule_fAlloc (size |-> G.Zn l :: E)).
    2: evalExp.
    rewrite fv_assn_base; simpl.
    apply incl_cons_lr; eauto.
    simpl; intros.
    unfold postST in *; splits; [..|splits]; jauto.
    { do 2 (apply fv_assn_Ex; intros).
      destruct H as (_ & _ & H' & _).
      rewrite fv_assn_Ex in H'.
      specialize (H' v0).
      rewrite fv_assn_Ex in H'.
      specialize (H' v1).
      rewrite fv_assn_base in *.
      unfold incl in *; simpl in *; intros; forwards*: H'. }
    { destruct H as (_ & _ & _ & H' & _).
      constructor; [|constructor]; inverts H' as ? H'; inverts H'; eauto. }
    { destruct H as (_ & _ & _ & _ & _ & _ & H' & _).
      apply disjoint_comm in H'; apply disjoint_comm; simpl in *; tauto. }
    eapply rule_host_backward; [jauto|].
    intros s h (p & vs & Hsat); exists p vs; revert s h Hsat; prove_imp.
    rewrite mkReduce.arrays_TZ; eauto.
  - eapply rule_bind'.
    { instantiate (1 := K nil); instantiate (1 := nil); eauto. }
    applys* IHtyp1.
    intros xs1; simpl.
    unfold K.
    apply rule_code_ex; [apply vals_hasDefval; apply val_hasDefval|].
    intros ps1.
    apply rule_code_ex; [apply listA_hasDefval|].
    intros vs1.
    rewrite app_nil_r.
    eapply rule_bind'.
    { instantiate (1 := K nil); instantiate (1 := nil); eauto. }
    apply IHtyp2.
    Lemma map_flatTup typ (xs : vars typ) vs : 
      map ent_e (xs |=> vs) = flatTup xs.
    Proof.
      induction typ; simpl; eauto.
      rewrite map_app, IHtyp1, IHtyp2; eauto.
    Qed.
    { rewrite map_app, map_flatTup.
      unfold incl in *; intros; rewrite in_app_iff in *; intuition. }
    Lemma rule_ret' T (v : T) xs ys fns P Q Gp :
      (P |= Q v)
      -> fv_assn (Q v) (xs v)
      -> ST_ok (preST (xs v) (fns v) (ys v) Gp) (ret v) 
               (fun x => postST P (Q x) Gp nil (xs x) (fns x) (ys x)).
    Proof.
      intros; unfold ST_ok, preST, postST; intros; splits; [..|splits]; inverts H2; repeat rewrite app_nil_r; jauto.
      eapply rule_host_backward; [apply rule_host_skip|eauto].
    Qed.
    intros xs2; simpl; unfold K.
    rewrite app_assoc, !app_nil_r.
    eapply rule_forward.
    apply  (rule_ret' _ (xs1,xs2)
                     (fun xs' => size :: (flatTup (fst xs') ++ flatTup (snd xs')) ++ xs)
                     (fun xs' => ys)
                     (fun xs' => fns)
                     _
                     (fun xs' : vars (Skel.TTup typ1 typ2) =>
                        (Ex (ps : vals (Skel.TTup typ1 typ2)) (vs : list (vals (Skel.TTup typ1 typ2))),
                         Assn
                           (arrays (val2gl ps) vs 1 *** R)
                           (Datatypes.length vs = l /\ P)
                           (size |-> G.Zn l :: xs' |=> ps ++ E)))).
    { intros s h (ps & vs & Hsat); exists (ps1, ps) (combine vs1 vs); revert s h Hsat; simpl; prove_imp.
      rewrite mkReduce.arrays_TTup; simpl.
      rewrite <-res_assoc.
      rewrite combine_map_fst, combine_map_snd; try omega.
      unfold val2gl in *.
      repeat sep_cancel'; eauto.
      unfold vals in *; simpl in *.
      rewrite combine_length.
      rewrite Nat.min_l; omega. }
    { do 2 (apply fv_assn_Ex; intros); apply fv_assn_base; simpl; rewrite !map_app, !map_flatTup, <-app_assoc.
      unfold incl in *; simpl; introv; repeat rewrite in_app_iff; intuition. }
    unfold vals; simpl; eauto.
    unfold preST; introv H; splits; [..|splits]; jauto.
    (* { destruct H as (_ & _ & H' & _). *)
    (*   do 2 (apply fv_assn_Ex; intros); apply fv_assn_base. *)
    (*   rewrite fv_assn_Ex in H'; forwards*: (>>H' v0). *)
    (*   rewrite fv_assn_Ex in H; forwards*: (>>H v1). *)
    (*   apply fv_assn_base in H0. *)
    (*   unfold incl in *; simpl in *; introv; specialize (H0 a); repeat rewrite in_app_iff in *. *)
    (*   intuition. } *)
    { destruct H as (H' & _).
      unfold fvOk in *; rewrite Forall_forall in *; introv; specialize (H' x); simpl in *; 
      repeat rewrite in_app_iff in *; intuition. }
    { destruct H as (_ & _ & _ & H' & _).
      apply disjoint_comm in H'; apply disjoint_comm; simpl in *.
      splits; jauto.
      Lemma disjoint_app_l (T : Type) (xs ys zs : list T) :
        disjoint (ys ++ zs) xs <-> disjoint ys xs /\ disjoint zs xs.
      Proof.
        splits; intros H; [split; apply disjoint_comm in H; apply disjoint_app in H; destruct H..
                          |apply disjoint_comm; apply disjoint_app; split; destruct H]; eauto using disjoint_comm.
      Qed.
      repeat rewrite disjoint_app_l in *; tauto. }
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

Lemma postST_imp P P' Q Q' Gp G xs xs' ys ys' fns fns':
  P' |= P ->
  Q |= Q' ->
  (forall xs, fv_assn Q xs -> fv_assn Q' xs) ->
  incl xs' xs ->
  incl ys' ys ->
  incl fns' fns ->
  disjoint_list fns' -> disjoint_list ys' ->
  forall n m n' m' M st,
    postST P Q Gp G xs fns ys n m n' m' M st ->
    postST P' Q' Gp G xs' fns' ys' n m n' m' M st.
Proof.
  unfold postST; intros; destruct H7 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?); splits; [..|splits]; jauto;
  unfold fnOk, fvOk, incl in *; rewrite !Forall_forall in *;
  intros; intuition.
  admit.
  eapply disjoint_incl_l; [|eapply disjoint_incl]; eauto.
  eapply disjoint_incl_l; [|eapply disjoint_incl]; eauto.
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
  
  eapply rule_host_backward; [|eauto].
  Lemma rule_host_forward M G P P' st Q :
    CSLh_n M G P st Q -> P' |= P -> CSLh_n M G P' st Q.
  Proof.
    intros ? ? ? ? ? ? ?.
    apply H0 in H2; forwards*: H.
  Qed.
  eapply rule_host_forward; eauto. 
Qed.

Lemma rule_fAllocs typ Gp R P E xs ys fns size l :
  evalExp E size (Zn l)
  -> fv_assn (Assn R P E) xs 
  -> ST_ok (preST xs fns ys Gp)
           (fAllocs typ size)
           (fun x => postST (Assn R P E)
                            (Ex ps vs, (Assn (arrays (val2gl ps) vs 1 *** R)) (Datatypes.length vs = l /\ P) (x |=> ps ++ E))
                            Gp nil (flatTup x ++ xs) fns ys).
Proof.
  intros Heval Hfv.
  unfold fAllocs.
  apply code_ok_float; intros Hfns Hdxy Hdfs.
  eapply rule_bind'.
  { instantiate (1 := K nil); instantiate (1 := nil); eauto. }
  { applys* rule_fLet. }
  intros s; simpl.
  eapply rule_backward.
  apply rule_fAllocs'; eauto.
  introv; rewrite !app_nil_r.
  apply postST_imp; eauto.
  - intros stk hp (ps & vs & Hsat); exists ps vs; revert stk hp Hsat; prove_imp.
  - introv H; rewrite !fv_assn_Ex in *.
    introv; specialize (H v0).
    rewrite !fv_assn_Ex in *.
    introv; specialize (H v1).
    rewrite fv_assn_base in *; simpl in *.
    unfold incl in *; intros a Hin; forwards*: H; simpl in *; eauto.
  - unfold incl; intros; simpl in *; rewrite !in_app_iff in *; eauto.
Qed.

Lemma fnOk_weaken fn n m :
  n <= m
  -> fnOk fn n 
  -> fnOk fn m.
Proof.
  unfold fnOk; rewrite !Forall_forall; intros.
  forwards*(?&?&?): H0; eexists; splits; eauto.
  omega.
Qed.
  
Lemma kname_inj m n : kname m = kname n -> m = n.
Proof.
  unfold kname; intros H.
  inverts H.
  forwards*: (>>nat_to_string_inj H1).
Qed.

Lemma fnOk_ge n m xs :
  fnOk xs n -> n <= m -> ~ In (kname m) xs.
Proof.
  unfold fnOk; rewrite Forall_forall; intros H ? Hc.
  forwards* (? & ? & ?): H.
  apply kname_inj in H1; omega.
Qed.

Lemma rule_freshF G P xs ys fns :
  fv_assn P xs
  -> ST_ok (preST xs fns ys G)
           freshF
           (fun fn => postST P (K P fn) G nil (K xs fn) (fn :: fns) (K ys fn)).
Proof.
  unfold ST_ok, freshP, postST, preST.
  introv (HxsOk & HfnsOk & HysOk & HgnsOk & Hys & Hgns & HsatF & HdisGMp & HinclG & HGMpOk) Heq. 
  inverts Heq.
  splits; [..|splits]; repeat rewrite app_nil_r; jauto; try omega.
  - constructor.
    + exists m; splits; eauto.
    + applys (>>fnOk_weaken HfnsOk); omega.
  - split; eauto.
    eapply fnOk_ge; jauto.
  - split; jauto.
    eapply fnOk_ge; eauto.
  - eapply fnOk_weaken; [|jauto]; omega.
  - repeat rewrite app_nil_r.
    apply rule_host_skip.
Qed.  

Definition interp_fd M fd fs :=
  forall n,
    match fd with
    | Host f => interp_fs fs (fun P Q => CSLhfun_n_simp M P f Q n)
    | Kern k => interp_fs fs (fun P Q : assn => CSLgfun_n_simp P k Q n)
    end.

Lemma sat_FC_weaken M G fn fd fs : 
  ~In fn (map fst M)
  -> interp_fd (M ++ (fn, fd) :: nil) fd fs
  -> disjoint_list (map fst M)
  -> sat_FC M nil G
  -> sat_FC (M ++ (fn, fd) :: nil) nil (G ++ (fn, fs) :: nil).
Proof.
  intros Hnin Hf Hdis Hsat.
  unfold sat_FC in *; introv _.
  specialize (Hsat n).
  unfold interp_FC_n in *; rewrite !Forall_forall in *.
  intros [fn' fs'] Hin; simpl in *.
  rewrite in_app_iff in *; simpl in *; destruct Hin as [Hin| [Hin | []]].
  - forwards*: (>>Hsat Hin).
    revert Hnin Hdis H; clear; intros.
    unfold interp_htri_n in *.
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
    revert Hnin Hdis H; clear; induction fs'; simpl; eauto; intros ? ?.
    unfold CSLhfun_n_simp; intros Hsat; intros.
    forwards*:H.
    eapply safe_nh_weaken; eauto.
    2: unfold incl; intros; rewrite in_app_iff; simpl; eauto.
    rewrite map_app; simpl.
    apply disjoint_list_app; simpl; eauto.
    introv; rewrite in_map_iff; intros [? [? ?]] [Hc | []]; eauto.
    apply Hnin; eexists; splits; substs; eauto.
  - inverts Hin.
    unfold interp_htri_n in *.
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
Qed.

Lemma rule_gen_kernel G P xs ys fns k fs:
  (forall M, sat_FC M G G -> interp_kfun M G k fs)
  -> fv_assn P xs
  -> ST_ok (preST xs fns ys G)
           (gen_kernel k)
           (fun fn => postST P (K P fn) G ((fn, fs) :: nil) (K xs fn) (fn :: fns) ys).
Proof.
  intros HkOk Hfv.
  unfold gen_kernel.
  applys* rule_bind'.
  { intros y; instantiate (1 := fun y => (y, fs) :: nil); instantiate (1 := nil); eauto. }
  { applys* rule_freshF. }
  intros fn; simpl.
  Lemma rule_bind'' T1 T2
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
  cutrewrite ((fun y =>
                postST (K P fn) (K P y) (G ++ nil) ((y, fs) :: nil) 
                       (K xs y) (y :: fns) ys) =
              (fun y =>
                postST (K P fn) (K P y) (G ++ nil) (((y, fs) :: nil) ++ K nil y) 
                       (K xs y) (y :: fns) ys)); [|extensionality x; eauto].
  apply code_ok_float; intros.
  eapply rule_backward.
  eapply rule_bind''.
  { instantiate (1 := K ys).
    instantiate (1 := K fns).
    instantiate (1 := K xs). 
    instantiate (1 := (fn, fs) :: nil).
    instantiate (1 := K P).
    instantiate (1 := P).
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
    apply Forall_app; jauto.
    unfold incl in *; introv; rewrite !in_app_iff; intuition.
    2: apply rule_host_skip.
    apply sat_FC_strong.
    apply rule_module_rec in HdisGMp.
    2: applys* fc_ok_same.
    apply sat_FC_weaken; jauto.
    unfold interp_fd; eauto.

    
    unfold sat_FC in *; intros ? Hhyp.
    unfold interp_FC_n in *; rewrite Forall_forall in *.
    intros [fn' fs'] Hin.
    forwards* Hsat: (>>HdisGMp n).
    rewrite Forall_forall in Hsat.
    rewrite in_app_iff in *; simpl in *; destruct Hin as [Hin| [Hin | []]].
    forwards*: (>>Hsat (fn', fs')).
    apply interp_htri_n