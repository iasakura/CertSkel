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
    P n (seqs st) GM 
    -> gen n GM = (v, (n', st', GM'))
    -> Q v n' ((seqs (st ++ st'))) GM'.

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

Lemma rule_fresh G P Q xs ys:
  ST_ok (code_ok G P Q xs ys) 
        fresh
        (fun y => code_ok G P Q xs (y :: ys)).
Proof.
  unfold ST_ok, fresh, setC, code_ok.
  introv (Hfs & Htri & Hxs & Hys & Henv & Hdisj) Heq.
  inverts Heq.
  splits; eauto.
  - rewrite app_nil_r; eauto.
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

Lemma rule_setI G P Q R ss xs xs' ys :
  (forall GM, CSLh_n GM G Q ss R)
  -> (fv_assn R (xs ++ xs'))
  -> (incl xs' ys)
  -> ST_ok (code_ok G P Q xs ys)
           (setI ss)
           (fun _ => code_ok G P R (xs ++ xs') (remove_xs ys xs')).
Proof.
  unfold code_ok.
  introv Htri Hfv Hxs' (Hfs & Htr & Hxs & Hys & Henv & Hdisj) Heq; simpl in *.
  inverts Heq; splits; jauto.   
  - eapply rule_app_seqs; eauto; simpl.
    eapply rule_host_seq; eauto using rule_host_skip.
  - apply usable_app; eauto.
    applys* usable_incl.
  - eapply usable_incl; [|eauto using remove_xs_incl]; eauto.
  - rewrite disjoint_app; split; eauto.
    + apply disjoint_comm; applys (>>disjoint_incl ys); eauto using disjoint_comm.
      apply remove_xs_incl.
    + apply disjoint_remove_xs.
Qed.  

Definition nST P : assnST := fun n _ _ => P n.

Lemma rule_bind T1 T2 P (Q : T1 -> assnST) R (gen : CUDAM T1) (gen' : T1 -> CUDAM T2) :
  ST_ok P gen Q
  -> (forall x, ST_ok (Q x) (gen' x) R)
  -> ST_ok P (do! x <- gen in gen' x) R.
Proof.
  unfold ST_ok in *; intros.
  inverts H2.
  destruct (gen _ _) as (? & ((? & ?) & ?)) eqn:Heq.
  forwards*: H.
  destruct (gen' _ _) as (? & ((? & ?) & ?)) eqn:Heq'.
  forwards*: H0.
  inverts H4.
  rewrite app_assoc; eauto.
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
  rewrites* app_nil_r.
Qed.

Arguments ret {f _ A} x : simpl never.
Arguments bind {f _ A B} _ _ : simpl never.
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
    Lemma rule_ex_gen A T G Pre Pst xs ys G' Pre' Pst' xs' ys' (gen : CUDAM A) : 
      (forall x : T, ST_ok (code_ok G Pre (Pst x) xs ys) gen
                           (fun x => code_ok (G' x) (Pre' x) (Pst' x) (xs' x) (ys' x)))
      -> ST_ok (code_ok G Pre (Ex x : T, Pst x) xs ys) gen
               (fun x => code_ok (G' x) (Pre' x) (Pst' x) (xs' x) (ys' x)).
    Proof.
      unfold ST_ok; introv Hsat Hok Hgen.
      unfold code_ok in *.
      forwards*: Hsat.
      splits; jauto.      
Qed.
