Require Import LibTactics GPUCSL Grid Relations MyEnv CSLLemma.

(* Add kernel name *)
Record kernel := BuildKer { (* name : string; *) params_of : list (var * CTyp); body_of : program }.

(* Inductive expr := *)
(* | VarE (x : var) *)
(* | Const (n : Z) *)
(* | Min (e1 e2 : expr) *)
(* | Add (e1 e2 : expr) *)
(* | Sub (e1 e2 : expr) *)
(* | Div (e1 e2 : expr). *)
(* Definition kerID := nat. *)
(* Instance nat_eq : eq_type nat := {|eq_dec := Nat.eq_dec|}. *)

(* the syntax of host-side program *)
Inductive stmt :=
| host_skip : stmt
| host_alloc : var -> exp -> stmt
| host_iLet : var -> exp -> stmt
| host_invoke : string -> exp -> exp -> list exp -> stmt
(* runtime expression representing kernel execution *)
| host_exec_ker : forall ntrd nblk,
    Vector.t (klist ntrd) nblk
    -> Vector.t simple_heap nblk
    -> stmt
| host_call : string -> list exp -> stmt
(* runtime expression for executing another function *)
| host_exec_hfun : stmt -> stack -> stmt
| host_seq : stmt -> stmt -> stmt.

Record hostfun := Hf {
  host_params : list (var * CTyp);
  host_stmt : stmt;
  host_res : list var
}.

Inductive fd :=
| Host : hostfun -> fd
| Kern : kernel -> fd.

Definition fdecl : Type := string * fd. 

(* a program consists of several host/kernel function declarations *)
Definition GModule := list fdecl.

Record State := St {
  st_stack : stack;
  st_heap : simple_heap
}.

Fixpoint alloc_heap (start : nat) (vs : list Z) : simple_heap :=
  match vs with
  | nil => fun x => None
  | v :: vs => fun l => if Z.eq_dec l (Zn start) then Some v else alloc_heap (S start) vs l
  end.

Fixpoint bind_params (stk : stack) (xs : list var) (vs : list Z) : Prop :=
  match xs, vs with
  | nil, nil => True
  | x :: xs, v :: vs => bind_params stk xs vs /\ stk x = v
  | _, _ => False
  end.

Definition henv_get (e : stack) (x : var) := e x.

Definition lift {A B C : Type} (f : A -> B -> C) x y :=
  match x, y with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.

(* Fixpoint eval_expr (env : stack) (e : expr) : Z := *)
(*   match e with *)
(*   | VarE x => henv_get env x *)
(*   | Const c => c *)
(*   | Min e1 e2 => Z.min (eval_expr env e1) (eval_expr env e2) *)
(*   | Add e1 e2 => Z.add (eval_expr env e1) (eval_expr env e2) *)
(*   | Div e1 e2 => Z.div (eval_expr env e1) (eval_expr env e2) *)
(*   | Sub e1 e2 => Z.sub (eval_expr env e1) (eval_expr env e2) *)
(*   end. *)

Fixpoint func_disp (m : GModule) (name : string) :=
  match m with
  | nil => None
  | (fn, f) :: m => if string_dec name fn then Some f else func_disp m name
  end%list.

Section VecNot.

Import Vector.VectorNotations.

(* Fixpoint replace_nth {A : Type} (i : nat) (l : list A) (x : A) := *)
(*   match i, l with *)
(*   | O, _ :: l => x :: l *)
(*   | S i, y :: l => y :: y :: replace_nth i l x *)
(*   | _, _ => l *)
(*   end%list. *)

Instance var_eq_type : eq_type var := {|
  eq_dec := var_eq_dec
|}.

Inductive stmt_exec : GModule -> stmt -> State -> stmt -> State -> Prop :=
| Exec_alloc kenv (x : var) e (gst : State) start vs :
    edenot e (st_stack gst) = (Z.of_nat (length vs)) ->
    hdisj (st_heap gst) (alloc_heap start vs) ->
    stmt_exec kenv (host_alloc x e) gst
              host_skip (St (var_upd (st_stack gst) x (Z.of_nat start))
                            (hplus (st_heap gst) (alloc_heap start vs)))
| Exec_iLet kenv x e (gst : State) n :
    edenot e (st_stack gst) = n ->
    stmt_exec kenv (host_iLet x e) gst
              host_skip (St (var_upd (st_stack gst) x n) (st_heap gst))
| Exec_invoke ent nt enb nb kenv tst shp kerID ker args vs gst stk :
    edenot ent (st_stack gst) = Zn nt ->
    edenot enb (st_stack gst) = Zn nb ->
    List.Forall2 (fun a v => edenot a (st_stack gst) = v) args vs ->
    func_disp kenv kerID = Some (Kern ker) ->
    init_GPU nt nb (body_of ker) tst shp stk ->
    bind_params stk (map fst (params_of ker)) vs ->
    stmt_exec kenv
              (host_invoke kerID ent enb args) gst
              (host_exec_ker nt nb tst shp) gst
| Exec_invoke_step kenv ntrd nblk tst tst' shp shp' s h h' :
    red_g (Gs tst shp h)  (Gs tst' shp' h') ->
    stmt_exec kenv
              (host_exec_ker ntrd nblk tst shp) (St s h)
              (host_exec_ker ntrd nblk tst' shp') (St s h')
| Exec_invoke_end kenv ntrd nblk tst shp s h :
    (forall i j, fst tst[@j][@i] = Cskip) ->
    stmt_exec kenv
              (host_exec_ker ntrd nblk tst shp) (St s h)
              (host_skip) (St s h)
| Exec_call kenv st fn hf args vs new_stk :
    func_disp kenv fn = Some (Host hf)
    -> List.Forall2 (fun a v => edenot a (st_stack st) = v) args vs
    -> bind_params new_stk (map fst (host_params hf)) vs
    -> stmt_exec kenv 
                 (host_call fn args) st
                 (host_exec_hfun (host_stmt hf) (st_stack st)) (St new_stk (st_heap st))
| Exec_hfun_step kenv body1 body2 st1 st2 ret_st :
    stmt_exec kenv body1 st1 body2 st2
    -> stmt_exec kenv
                 (host_exec_hfun body1 ret_st) st1
                 (host_exec_hfun body2 ret_st) st2
| Exec_hfun_end kenv ret_st st :
    stmt_exec kenv
              (host_exec_hfun host_skip ret_st) st
              host_skip (St ret_st (st_heap st))
| Exec_seq1 kenv s1 s2 s1' st1 st2 :
    stmt_exec kenv s1 st1 s1' st2  ->
    stmt_exec kenv (host_seq s1 s2) st1 (host_seq s1' s2) st2
| Exec_seq2 kenv s st :
    stmt_exec kenv (host_seq host_skip s) st s st.
End VecNot.

(* TODO: check e >= 0 in alloc(e) *)
Inductive aborts_h : GModule -> stmt -> stack -> simple_heap -> Prop :=
  | aborts_host_seq : forall ke p p' s h, aborts_h ke p s h -> aborts_h ke (host_seq p p') s h
  | aborts_kernel_invk : forall ke kid en n em m args s h,
      edenot en s = Zn n ->
      edenot em s = Zn m ->
      (* func_disp ke kid = None \/ *)
      (* (exists f, func_disp ke kid = Some (Host f)) \/ *)
      n = 0 \/ m = 0 ->
      (* (forall ker, func_disp ke kid = Some (Kern ker) -> length args <> length (params_of ker)) -> *)
      aborts_h ke (host_invoke kid en em args) s h
  | aborts_kernel_exec : forall kenv ntrd nblk tst shp s h,
      (abort_g (Gs tst shp h) \/ bdiv_g ntrd nblk tst shp (htop h)) ->
      aborts_h kenv (host_exec_ker ntrd nblk tst shp) s h
  (* | aborts_hfun_call : forall ke fn args s h, *)
  (*     func_disp ke fn = None \/ *)
  (*     (exists f, func_disp ke fn = Some (Kern f)) \/ *)
  (*     (forall hf, func_disp ke fn = Some (Host hf) -> length args <> length (host_params hf)) -> *)
  (*     aborts_h ke (host_call fn args) s h *)
  | aborts_hfun_exec : forall kenv body ret_stk s h,
      aborts_h kenv body s h
      -> aborts_h kenv (host_exec_hfun body ret_stk) s h.

Notation zpheap := (gen_pheap Z).

Section Rules.

Variable GM : GModule.

Fixpoint safe_nh (n : nat) (s : stack) (gh : zpheap) (p : stmt) (Q : assn) :=
  match n with
  | 0 => True
  | S n =>
    (p = host_skip -> Q s (as_gheap gh)) /\
    (forall (hF : zpheap) (h' : simple_heap),
        pdisj gh hF 
        -> ptoheap (phplus gh hF) h'
        -> ~ aborts_h GM p s h') /\
    (forall (hF : zpheap) (h h' : simple_heap) (s' : stack) (p' : stmt),
        pdisj gh hF 
        -> ptoheap (phplus gh hF) h
        -> stmt_exec GM p (St s h) p' (St s' h') 
        -> exists (h'' : zpheap),
            pdisj h'' hF /\ ptoheap (phplus h'' hF) h' /\
            safe_nh n s' h'' p' Q)
  end.

Definition CSLh_n_simp (P : assn) (ss : stmt) (Q : assn) (n : nat) :=
  forall s h,
    sat s (as_gheap h) P -> safe_nh n s h ss Q.

(* Definition CSLh_simp P ss Q := forall n, CSLh_n_simp P ss Q n. *)

Definition CSLhfun_n_simp (P : assn) (f : hostfun) (Q : assn) (n : nat) :=
  forall vs s h,
    bind_params s (map fst (host_params f)) vs
    -> sat s (as_gheap h) P
    -> safe_nh n s h (host_stmt f) Q.

(* Definition CSLhfun_simp P f Q := forall n, CSLhfun_n_simp P f Q n. *)

Definition CSLkfun_n_simp (P : assn) (f : kernel) (Q : assn) (n : nat) :=
  forall ntrd nblk vs tst shs h s,
    ntrd <> 0 -> nblk <> 0
    -> init_GPU ntrd nblk (body_of f) tst shs s
    -> bind_params s (map fst (params_of f)) vs
    -> sat s (as_gheap h) P
    -> safe_ng ntrd nblk n tst shs h Q.

(* Definition CSLkfun_simp P f Q := forall n, CSLkfun_n_simp P f Q n. *)

Inductive FTag : Set := Hfun | Kfun.

Inductive FTri : Type :=
| FAll (T : Type) (tri : T -> FTri) : FTri
| FDbl (P : assn) (Q : assn) : FTri.

Notation "'All' x .. y ',' tri" := (FAll _ (fun x => .. (FAll _ (fun y => tri)) ..))
                                     (at level 200, x binder, y binder, tri at level 200).

Record FSpec := FS { fs_tag : FTag; fs_params : list var; fs_tri : FTri}.

Fixpoint interp_ftri (fs : FTri) (k : assn -> assn -> Prop) : Prop :=
  match fs with
  | FAll _ fs => forall x, interp_ftri (fs x) k
  | FDbl P Q => k P Q
  end.

Definition interp_kfun_n_simp k (fs : FSpec) n :=
  fs_tag fs = Kfun /\
  fs_params fs = map fst (params_of k) /\
  interp_ftri (fs_tri fs) (fun P Q => CSLkfun_n_simp P k Q n).

Definition interp_hfun_n_simp h (fs : FSpec) n :=
  fs_tag fs = Hfun /\
  fs_params fs = map fst (host_params h) /\
  interp_ftri (fs_tri fs) (fun P Q => CSLhfun_n_simp P h Q n).

Definition interp_fd_simp fd fs n := 
  match fd with
  | Host f => interp_hfun_n_simp f fs n
  | Kern k => interp_kfun_n_simp k fs n
  end.

Definition interp_f_n (name : string) (fs : FSpec) (n : nat) : Prop :=
  match n with
  | O => True
  | _ => 
    match func_disp GM name with
    | None => False
    | Some fd => interp_fd_simp fd fs n
    end
  end.

Definition FC := list (string * FSpec).

Definition interp_FC_n (G : FC) (n : nat) :=
  List.Forall (fun x => let '(fn, fs) := x in interp_f_n fn fs n) G.

Definition with_ctx G (f : nat -> Prop) :=
  forall n, interp_FC_n G (n - 1) -> f n.

Definition CSLh G P ss Q := with_ctx G (fun n => CSLh_n_simp P ss Q n).
Definition CSLhfun G P f Q := with_ctx G (fun n => CSLhfun_n_simp P f Q n).
Definition CSLkfun G P f Q := with_ctx G (fun n => CSLkfun_n_simp P f Q n).
Definition interp_kfun G k fs := with_ctx G (fun n => interp_kfun_n_simp k fs n).
Definition interp_hfun G f fs := with_ctx G (fun n => interp_hfun_n_simp f fs n).
Definition interp_fd G fd fs := with_ctx G (fun n => interp_fd_simp fd fs n).
Definition interp_f (G  : FC) fn fs := with_ctx G (fun n => interp_f_n fn fs n).
Definition sat_FC (G1 G2 : FC) :=
  forall n, interp_FC_n G1 (n - 1) -> interp_FC_n G2 n.

Definition params_fd fd :=
  match fd with
  | Host h => host_params h
  | Kern k => params_of k
  end.

Definition fn_ok fn fs :=
  match func_disp GM fn with
  | None => False
  | Some f => fs_params fs = map fst (params_fd f) /\
              match f with
              | Host _ => fs_tag fs = Hfun
              | Kern _ => fs_tag fs = Kfun
              end
  end.

Fixpoint fc_ok (G : FC) :=
  match G with
  | nil => True
  | (fn, fs) :: G => fn_ok fn fs /\ fc_ok G
  end.

Lemma interp_fd_0 fn fs : interp_f_n fn fs 0.
Proof.
  unfold interp_f_n, interp_fd_simp, interp_hfun_n_simp, interp_kfun_n_simp; unfold fn_ok.
  destruct func_disp; eauto.
Qed.

Lemma interp_fc_0 G : interp_FC_n G 0.
Proof.
  induction G as [|[? [? ?]] ?]; simpl.
  - intros; constructor.
  - constructor; eauto using interp_fd_0.
Qed.

Lemma rule_module_rec G : (* fc_ok G ->  *)sat_FC G G -> sat_FC nil G.
Proof.  
  unfold sat_FC; intros ? n; induction n; simpl.
  - intros; simpl.
    inverts H0.
    apply* interp_fc_0.
  - intros; apply H; simpl.
    rewrite <-minus_n_O; eauto.
    apply IHn.
    constructor.
Qed.

Lemma rule_module_each G1 G2 :
  (forall fn fs, In (fn, fs) G2 -> interp_f G1 fn fs)
  -> sat_FC G1 G2.
Proof.
  unfold sat_FC, interp_f, with_ctx, interp_FC_n.
  intros; repeat rewrite Forall_forall in *; intros.
  destruct x; apply* H.
  rewrite Forall_forall; intros.
  apply* H0.
Qed.  

Lemma rule_fun fn fd fs G :
  func_disp GM fn = Some fd 
  -> interp_fd G fd fs
  -> interp_f G fn fs.
Proof.
  intros Hname Hok n Hctx.
  unfold interp_f_n; rewrite Hname; cbn.
  destruct n; eauto.
Qed.

(* Lemma rule_hfun fn hf fs G : *)
(*   -> interp_hfun G hf fs *)
(*   -> interp_fd G (Host hf) fs. *)
(* Proof. *)
(*   intros Hname Hok n Hctx. *)
(*   unfold interp_fd_n; rewrite Hname; cbn. *)
(*   unfold interp_stmt_n, CSLh_n_simp, CSLhfun_n_simp in *. *)
(*   forwards* Hok': Hok. *)
(*   revert Hok'. *)
(*   induction fs; simpl; eauto. *)
(*   introv Hcsl; forwards*: Hcsl. *)
(* Qed. *)

(* Lemma rule_kfun fn kf fs G : *)
(*   func_disp GM fn = Some (Kern kf) *)
(*   -> interp_kfun G kf fs *)
(*   -> interp_f G fn fs. *)
(* Proof.   *)
(*   intros Hname Hok n Hctx. *)
(*   unfold interp_fd_n; rewrite Hname; cbn. *)
(*   unfold interp_kfun, interp_prog_n, CSLkfun_n_simp, CSLg_n in *. *)
(*   revert Hok. *)
(*   induction fs; simpl; eauto. *)
(* Qed. *)

Inductive inst_spec : FTri -> assn -> assn -> Prop :=
| IS_dbl P Q : inst_spec (FDbl P Q) P Q 
| IS_all T (v : T) f P Q : inst_spec (f v) P Q -> inst_spec (FAll _ f) P Q.

(* (y = v)[vs/xs], if variable remains in sustituted pred, it cannot holds *)
Fixpoint subst_ent (y : var) (v : val) (xs : list var) (vs : list val) : Prop :=
  match xs, vs with
  | x :: xs, v' :: vs => if var_eq_dec x y then v = v' else subst_ent y v xs vs
  | _, _ => False
  end.

Fixpoint subst_env (E : list entry) xs vs : Prop :=
  match E with
  | nil => True
  | (y |-> v') :: E => subst_ent y v' xs vs /\ subst_env E xs vs
  end.

Lemma interp_fs_inst fs k P Q :
  interp_ftri fs k 
  -> inst_spec fs P Q 
  -> k P Q.
Proof.
  intros Hint Hinst; induction Hinst; simpl in *; eauto.
Qed.

Lemma subst_ent_bind_params y v xs vs s :
  subst_ent y v xs vs
  -> bind_params s xs vs 
  -> (y === v) s (emp_ph loc).
Proof.
  revert vs; induction xs as [|x xs]; simpl; try tauto.
  intros [|v' vs]; try tauto.
  destruct var_eq_dec; substs; jauto.
  intros ? [? ?]; cbv; congruence.
Qed.

Lemma subst_env_bind_params E xs vs s : 
  subst_env E xs vs
  -> bind_params s xs vs
  -> env_assns_denote E s (emp_ph loc).
Proof.
  revert xs vs s; induction E as [| [y v'] E]; introv; simpl.
  - intros; apply emp_emp_ph.
  - intros; split.
    + applys* subst_ent_bind_params.
    + applys* IHE.
Qed.

Lemma phplus_gheap_comm (h1 : zpheap) (h2: zpheap) (dis : pdisj h1 h2) :
  phplus (as_gheap h1) (as_gheap h2) = as_gheap (phplus_pheap dis).
Proof.
  extensionality l; simpl; unfold phplus, as_gheap'.
  destruct l as [[|] ?]; eauto.
Qed.

Lemma safe_nh_frame n s (h hF : zpheap) ss R RF P E (dis : pdisj h hF) : 
  sat_res s (as_gheap hF) RF
  -> safe_nh n s h ss (Assn R P E)
  -> safe_nh n s (phplus_pheap dis) ss (Assn (R *** RF) P E).
Proof.
  revert s ss h hF dis; induction n; introv; simpl; eauto.
  intros HsatF (Hskip & Hsafe & Hstep); splits; eauto.
  - intros; forwards* Hsk: Hskip.
    unfold Assn in * ;sep_split; sep_split_in Hsk; jauto.
    exists (as_gheap h) (as_gheap hF); splits; eauto; eauto.
    + apply* as_gheap_pdisj.
    + apply (phplus_gheap_comm _ _ dis).
  - introv Hdis' Heq' Hab.
    rewrite padd_assoc in Heq'.
    rewrites* pdisj_padd_expand in Hdis'; eauto.
    destruct Hdis'.
    forwards*: (>>Hsafe (phplus_pheap H0)).
  - introv Hdis' Heq' Hstep'.
    rewrite padd_assoc in Heq'.
    rewrites* pdisj_padd_expand in Hdis'; eauto.
    destruct Hdis'.
    forwards* (h'' & Hdis'' & Heq'' & ?): (>>Hstep (phplus_pheap H0)).
    simpl in *.
    assert (Hdis''F : pdisj h'' hF) by eauto using pdisjE1.
    exists (phplus_pheap Hdis''F); splits; eauto using pdisj_padd_expand.
    + simpl; applys* pdisj_padd_expand.
    + simpl; rewrites* padd_assoc.
    + applys* IHn.
      unfold sat_res, sat in *; eauto using res_inde.
Qed.

Lemma as_gheap_pdisj (h1 h2 : zpheap) :
  pdisj h1 h2 <-> pdisj (as_gheap h1) (as_gheap h2).
Proof.
  split; eauto using as_gheap_pdisj.
  unfold pdisj, as_gheap; intros H l.
  forwards*: (H (GLoc l)).
Qed.

Lemma safe_nh_exec_hfun n s h body s_ret R P E E' :
  safe_nh n s h body (Assn R P E)
  -> env_assns_denote E' s_ret (emp_ph loc)
  -> safe_nh n s h (host_exec_hfun body s_ret) (Assn R P E').
Proof.
  revert s h body; induction n; simpl; introv; eauto.
  intros (Hskip & Hsafe & Hstep) Henv; splits; eauto.
  - inversion 1.
  - introv Hdis Heq Hab.
    inverts Hab.
    forwards*: Hsafe.
  - introv Hdis Heq Hst.
    inverts Hst as Hst'.
    + forwards* (h'' & ? & ? & ?): Hstep.
    + exists h; splits; eauto.
      destruct n; simpl; eauto; splits; eauto.
      * intros _.
        forwards* Hsat: Hskip.
        unfold Assn in Hsat |- * ;sep_split; sep_split_in Hsat; eauto.
      * introv ? ? Hab; inverts Hab.
      * introv ? ? Hst; inverts Hst.
Qed.

Lemma safe_nh_exec_ker nt nb n tst shp h s_ret R P E E' :
  safe_ng nt nb n tst shp h (Assn R P E)
  -> env_assns_denote E' s_ret (emp_ph loc)
  -> safe_nh n s_ret h (host_exec_ker nt nb tst shp) (Assn R P E').
Proof.
  revert tst shp h; induction n; simpl; introv; eauto.
  intros (Hskip & Hsafe1 & Hsafe2 & Hstep) Henv; splits; eauto.
  - inversion 1.
  - introv Hdis Heq Hab.
    inverts Hab.
    forwards*: Hsafe1.
  - introv Hdis Heq Hst.
    inverts Hst as Hst'.
    + forwards* (h'' & ? & ? & ?): (>> Hstep Hst').
    + exists h; splits; eauto.
      destruct n; simpl; eauto; splits; eauto.
      * intros _.
        forwards* Hsat: Hskip.
        unfold Assn in Hsat |- * ;sep_split; sep_split_in Hsat; eauto.
      * introv ? ? Hab; inverts Hab.
      * introv ? ? Hst; inverts Hst.
Qed.

Lemma safe_nh_conseq n s h body P P' :
  P |= P' 
  -> safe_nh n s h body P
  -> safe_nh n s h body P'.
Proof.
  revert s h body; induction n; simpl; eauto; introv.
  intros ? (? & ? & ?); splits; jauto.
  - intros; apply H; eauto.
  - intros; forwards* (? & ? & ? & ?): H2.
Qed.

Lemma safe_ng_conseq nt nb n tst shp h P P' :
  P |= P' 
  -> safe_ng nt nb n tst shp h P
  -> safe_ng nt nb n tst shp h P'.
Proof.
  revert tst shp h; induction n; simpl; eauto; introv.
  intros ? (? & ? & ? & ?); splits; jauto.
  - intros; apply H; eauto.
  - intros; forwards* (? & ? & ? & ?): H3.
Qed.

Lemma rule_call (G : FC) (fn : string) (es : list exp)
      vs fs 
      Rpre Ppre Epre
      Rpst Ppst
      RF R E (P : Prop) :
  In (fn, fs) G
  -> fs_tag fs = Hfun
  -> length es = length (fs_params fs)
  -> inst_spec (fs_tri fs) (Assn Rpre Ppre Epre) (Assn Rpst Ppst nil)
  -> List.Forall2 (fun e v => evalExp E e v) es vs
  -> (P -> subst_env Epre (fs_params fs) vs)
  -> (P -> Ppre)
  -> (P -> R |=R Rpre *** RF)
  -> CSLh G
            (Assn R P E)
            (host_call fn es)
            (Assn (Rpst *** RF) (P /\ Ppst) E).
Proof.
  intros Hinfn Htag Harg Hinst Heval Hsubst Hp Hr n HFC s h Hsat.
  destruct n; simpl; eauto.
  cutrewrite (S n - 1 = n) in HFC; [|omega].
  splits; eauto.
  - inversion 1.
  - introv Hdisj Htoh Habort.
    inverts Habort as Habort.
  - introv Hdis Htoh Hstep.
    (* simpl in HFC; rewrite <-minus_n_O in HFC. *)
    unfold interp_FC_n, interp_f_n in HFC; rewrite Forall_forall in HFC.
    forwards* Hfn: (>>HFC Hinfn).
    inverts Hstep as Hdisp Heval' Hbnd; simpl in *.
    destruct n; eauto.
    remember (S n) as n'.
    rewrite Hdisp in Hfn.
    forwards* Hfn': (>>interp_fs_inst Hfn Hinst); simpl in Hfn'.
    unfold CSLhfun_n_simp in Hfn'; simpl in Hfn'.
    unfold Assn, sat in Hsat.
    sep_split_in Hsat.
    forwards* (h1 & h2 & Hpre & HF & Hdis12 & Heq12): (>> Hr HP Hsat).
    forwards* (h1' & h2' & ? & ? & Heq12'): (>> phplus_gheap  Heq12); substs.
    forwards* Hsafe: (>>Hfn' h1' Hbnd).
    (* Proof that precond holds *)
    { unfold sat, Assn; sep_split; eauto.
      - applys* Hp.
      - applys* subst_env_bind_params.
        simpl in Hfn; unfold interp_hfun_n_simp in Hfn; destruct Hfn as (? & Hparams & ?).
        rewrite Hparams.
        cutrewrite (vs = vs0); eauto.
        revert Heval Heval' HP0; clear.
        intros H; revert vs0; induction H; inversion 1; intros; substs; eauto.
        forwards*: evalExp_ok.
        f_equal; eauto. }
    (* h **                                     hF -> 
       h1' ** (h2' : framed w.r.t. fun exec. ) ** hF -> *)
    exists h; splits; eauto.
    rewrite <-as_gheap_pdisj in Hdis12.
    asserts_rewrite (h = phplus_pheap Hdis12).
    { destruct h; apply pheap_eq; eauto. }
    applys* safe_nh_frame.
    { unfold sat, sat_res in *; now eauto using res_inde. }
    applys* (>>safe_nh_exec_hfun (@nil entry)).
    applys* (>>safe_nh_conseq Hsafe).
    applys* Assn_imply.
    unfold incl; eauto.
Qed.    

Lemma initGPU_ntrd nt nb body tst shp stk: 
  init_GPU nt nb body tst shp stk ->
  stk "ntrd" = Zn nt.
Proof. inversion 1; eauto. Qed.

Lemma initGPU_nblk nt nb body tst shp stk: 
  init_GPU nt nb body tst shp stk ->
  stk "nblk" = Zn nb.
Proof. inversion 1; eauto. Qed.

Lemma rule_invk (G : FC) (fn : string) (nt nb : nat) (es : list exp)
      (vs : list val)
      fs ent ntrd enb nblk
      Rpre Ppre Epre
      Rpst Ppst
      RF R E (P : Prop) :
  In (fn, fs) G
  -> fs_tag fs = Kfun
  -> length es = length (fs_params fs)
  -> inst_spec (fs_tri fs) (Assn Rpre Ppre Epre) (Assn Rpst Ppst nil)
  -> List.Forall2 (fun e v => evalExp E e v) (enb :: ent :: es) (Zn nblk :: Zn ntrd :: vs)
  -> ntrd <> 0 -> nblk <> 0
  -> (P -> subst_env Epre (Var "nblk" :: Var "ntrd" :: (fs_params fs)) (Zn nblk :: Zn ntrd :: vs))
  -> (P -> Ppre)
  -> (P -> R |=R Rpre *** RF)
  -> CSLh G
            (Assn R P E)
            (host_invoke fn ent enb es)
            (Assn (Rpst *** RF) (P /\ Ppst) E).
Proof.
  intros Hinfn Htag Harg Hinst Heval Hntrd Hnblk Hsubst Hp Hr n HFC s h Hsat.
  inverts Heval as Henb Heval.
  inverts Heval as Hent Heval.
  destruct n; simpl; eauto.
  splits; eauto.
  - inversion 1.
  - introv Hdisj Htoh Habort.
    inverts Habort as Hent0 Henb0 Habort.
    destruct Habort.
    + unfold Assn, sat in Hsat; sep_split_in Hsat.
      forwards* Hent': (>>evalExp_ok Hent).
      hnf in Hent'; simpl in Hent'; substs.
      rewrite Hent', Nat2Z.inj_iff in Hent0; eauto.
    + unfold Assn, sat in Hsat; sep_split_in Hsat.
      forwards* Henb': (>>evalExp_ok Henb).
      hnf in Henb'; simpl in Henb'; substs.
      rewrite Henb', Nat2Z.inj_iff in Henb0; eauto.
  - introv Hdis Htoh Hstep.
    simpl in HFC; rewrite <-minus_n_O in HFC.
    unfold interp_FC_n, interp_f_n in HFC; rewrite Forall_forall in HFC.
    inverts Hstep as Hent' Henb' Heval' Hdisp Hinit Hbnd; simpl in *.
    forwards* Hfn: (>>HFC Hinfn); rewrite Hdisp in Hfn.
    destruct n.
    { exists h; splits; eauto. }
    forwards* Hfn': (>>interp_fs_inst Hfn Hinst); simpl in Hfn'.
    remember (S n) as n'.
    unfold CSLkfun_n_simp in Hfn'; simpl in Hfn'.
    rewrite Hdisp in Hdisp; inverts Hdisp; simpl in *.
    unfold Assn, sat in Hsat.
    sep_split_in Hsat.
    forwards* (h1 & h2 & Hpre & HF & Hdis12 & Heq12): (>> Hr HP Hsat).
    forwards* (h1' & h2' & ? & ? & Heq12'): (>> phplus_gheap  Heq12); substs.
    assert (Heq : nb0 = nblk); [ | subst nb0 ].
    { unfold Assn, sat in Hsat; sep_split_in Hsat.
      forwards* Henb'': (>>evalExp_ok Henb).
      hnf in Henb''; simpl in Henb''; substs.
      rewrite Henb'', Nat2Z.inj_iff in Henb'; eauto. }
    assert (Heq : nt0 = ntrd); [ | subst nt0 ].
    { unfold Assn, sat in Hsat; sep_split_in Hsat.
      forwards* Hent'': (>>evalExp_ok Hent).
      hnf in Hent''; simpl in Hent''; substs.
      rewrite Hent'', Nat2Z.inj_iff in Hent'; substs; eauto. }
    forwards* Hsafe: (>>Hfn' h1' Hinit Hbnd).
    (* Proof that precond holds *)
    { unfold sat, Assn; sep_split; eauto.
      - applys* Hp.
      - applys* (>>subst_env_bind_params (Hsubst HP)).
        simpl in Hfn; destruct Hfn as (? & Hparams & ?).
        rewrite Hparams.
        repeat split; eauto using initGPU_ntrd, initGPU_nblk.
        simpl in Hsubst.
        cutrewrite (vs = vs0); eauto.
        revert Heval Heval' HP0; clear.
        intros H; revert vs0; induction H; inversion 1; intros; substs; eauto.
        forwards*: evalExp_ok.
        f_equal; eauto. }
    (* h **                                     hF -> 
       h1' ** (h2' : framed w.r.t. fun exec. ) ** hF -> *)
    exists h; splits; eauto.
    rewrite <-as_gheap_pdisj in Hdis12.
    asserts_rewrite (h = phplus_pheap Hdis12).
    { destruct h; apply pheap_eq; eauto. }
    applys* safe_nh_frame.
    applys* (>>safe_nh_exec_ker (@nil entry)).
    applys* (>>safe_ng_conseq Hsafe).
    applys* Assn_imply.
    unfold incl; eauto.
Qed.

Lemma rule_host_skip G P : CSLh G P host_skip P.
Proof.
  unfold  CSLh, with_ctx, CSLh_n_simp; induction n; simpl; eauto.
  introv _ Hsat; splits; eauto.
  - intros; intros Hc; inverts Hc.
  - introv Hdis Heq H; inverts H.
Qed.

Lemma safe_nh_skip n s h P:
  sat s (as_gheap h) P
  -> safe_nh n s h host_skip P.
Proof.
  destruct n; simpl; eauto.
  intros Hsat; splits; eauto.
  - introv ? ? Hc; inverts Hc.
  - introv ? ? Hc; inverts Hc.
Qed.

Lemma rule_host_let G R P E x e v : 
  evalExp E e v
  -> CSLh G (Assn R P E) (host_iLet x e) (Assn R P ((x |-> v) :: (remove_var E x))).
Proof.
  intros Heval n _ s h Hsat; destruct n; simpl; eauto; splits. 
  - inversion 1.
  - introv Hdis Heq Hc; inverts Hc.
  - introv Hdis Heq Hstep.
    inverts Hstep.
    exists h; splits; eauto.
    apply safe_nh_skip.
    unfold Assn, sat in Hsat |- *; sep_split_in Hsat; sep_split; eauto.
    simpl; split; eauto using remove_var_imp.
    + unfold "==="; simpl.
      unfold var_upd; destruct var_eq_dec; try congruence.
      forwards*: evalExp_ok.
    + apply remove_var_inde; simpl; eauto.
      applys* remove_var_imp.
Qed.

Lemma hdisjC loc (h1 h2 : heap loc) : hdisj h1 h2 -> hdisj h2 h1.
Proof. unfold hdisj; intros H x; specialize (H x); tauto. Qed.

Lemma hplusC loc (h1 h2 : heap loc) :
  hdisj h1 h2 
        -> hplus h1 h2 = hplus h2 h1.
Proof.
  intros Hdis.
  extensionality l; specialize (Hdis l); unfold hplus; destruct (h1 l), (h2 l); eauto.
  destruct Hdis; congruence.
Qed.

Require Import Psatz.

Lemma alloc_heap_gt x start vs v : 
  alloc_heap start vs x = Some v -> (Zn start <= x)%Z.
Proof.
  revert start; induction vs; simpl; intros; try congruence.
  destruct Z.eq_dec; substs; try lia; eauto.
  forwards*: IHvs; lia.
Qed.

Lemma alloc_heap_ok start vs s  :
  sat_res s (as_gheap (htop (alloc_heap start vs))) (array (GLoc (Zn start)) vs 1).
Proof.
  revert start; induction vs; introv; simpl.
  - unfold sat_res, sat; simpl; unfold_conn; simpl; unfold as_gheap', htop'.
    destruct x as [[|] ?]; eauto.
  - exists (as_gheap (htop (fun l => if Z.eq_dec l (Zn start) then Some a else None)))
           (as_gheap (htop (alloc_heap (S start) vs))); splits; eauto.
    + simpl; unfold_conn; simpl.
      unfold as_gheap', htop'; destruct x as [[|] ?]; eauto.
      destruct Z.eq_dec, eq_dec; eauto; try congruence.
    + cutrewrite ((Zn start + 1)%Z = Zn (S start)); [| lia].
      apply IHvs.
    + intros [[|] l]; simpl; eauto.
      unfold htop'; simpl.
      destruct Z.eq_dec; substs; eauto.
      destruct alloc_heap eqn:Heq; eauto.
      forwards*: alloc_heap_gt.
      revert H; clear; intros; false; zify; omega.
    + extensionality l; unfold phplus; simpl; unfold as_gheap', htop'.
      destruct l as [[|] l]; simpl; eauto.
      destruct Z.eq_dec; substs; eauto.
      destruct alloc_heap eqn:Heq; eauto.
      forwards*: alloc_heap_gt.
      revert H; clear; intros; false; zify; omega.
Qed.

Lemma phplus_gheap_comm' (h1 : zpheap) (h2: zpheap) (dis : pdisj h1 h2) :
  phplus_pheap (proj1 (as_gheap_pdisj h1 h2) dis) = as_gheap (phplus_pheap dis).
Proof.
  apply pheap_eq.
  extensionality l; simpl; unfold phplus, as_gheap'.
  destruct l as [[|] ?]; eauto.
Qed.

Lemma rule_host_alloc G R P E x e size : 
  evalExp E e (Zn size)
  -> CSLh G (Assn R P E)
            (host_alloc x e)
            (Ex p vs, Assn (array (GLoc p) vs 1 *** R) (length vs = size /\ P) ((x |-> p) :: (remove_var E x))).
Proof.
  intros Heval n _ s h Hsat; destruct n; simpl; eauto; splits. 
  - inversion 1.
  - introv Hdis Heq Hc; inverts Hc.
  - introv Hdis Heq Hstep.
    inverts Hstep as Heval' Hdis'; simpl in *.
    unfold Assn, sat in Hsat; sep_split_in Hsat.
    forwards* Heval'': evalExp_ok; unfold_conn_in Heval''; simpl in Heval''.
    assert (size = length vs); [|subst size].
    { rewrite Heval'' in Heval'; rewrite Nat2Z.inj_iff in Heval'; eauto. }
    pose (htop (alloc_heap start vs)) as h_alc.
    forwards* Heq': ptoheap_eq.
    lets Hdis_alc: Hdis'.
    rewrite hdisj_pdisj in Hdis'.
    rewrite <-Heq' in Hdis'.
    assert (Hdis'' : pdisj h_alc h).
    { apply pdisjC, pdisjE1, pdisjC in Hdis'; eauto. }
    exists (phplus_pheap Hdis''); splits; eauto.
    + apply pdisj_padd_expand; eauto.
    + cutrewrite (PHeap.this (phplus_pheap Hdis'') = phplus h_alc h); [|eauto].
      rewrite padd_assoc.
      rewrite Heq'.
      unfold h_alc; rewrite <-hplus_phplus; eauto using hdisjC.
      rewrite hplus_phplus; eauto using hdisjC.
      rewrite hplusC; eauto.
      apply ptoheap_plus; eauto using hdisjC.
      apply ptoheap_htop.
    + apply safe_nh_skip.
      exists (Zn start) vs.
      unfold Assn, sat in Hsat |- *; sep_split_in Hsat; sep_split; eauto.
      * unfold_conn; split; eauto.
      * simpl; split; eauto using remove_var_imp.
        -- unfold "==="; simpl.
           unfold var_upd; destruct var_eq_dec; try congruence.
        -- apply remove_var_inde; simpl; eauto.
           applys* remove_var_imp.
      * simpl; rewrite <-phplus_gheap_comm'.
        exists (as_gheap h_alc) (as_gheap h); splits; eauto.
        -- apply alloc_heap_ok.
        -- apply as_gheap_pdisj; eauto.
Qed.

Lemma safe_seq : forall (n : nat) (C C2 : stmt) (s : stack) (h : zpheap) (Q R : assn),
  safe_nh n s h C Q ->
  (forall m s' h', m <= n -> Q s' (as_gheap h') -> safe_nh m s' h' C2 R)%nat ->
  safe_nh n s h (host_seq C C2) R.
Proof.
  induction n; introv Hsafe H; simpl; eauto; unfold safe_nt in *.
  splits; try congruence.
  - introv Hdis Heq Haborts; inversion Haborts; subst; simpl in *; jauto.
  - introv Hdis Heq Hstep; inverts Hstep as Hstep'; eauto.
    + destruct Hsafe as (? & ? & Hstep); forwards* (h'' & ? & ? & ?): Hstep.
      exists h''; splits; eauto.
    + destruct Hsafe as (? & _).
      forwards*: (H n s' h).
Qed.

Lemma safe_nh_mono n m s h c P :
  safe_nh n s h c P -> m <= n -> safe_nh m s h c P.
Proof.
  revert m s h c P; induction n; simpl; introv.
  - intros; assert (m = 0); [omega|substs]; simpl; eauto.
  - intros (Hskip & Hsafe & Hstep) Hmn.
    destruct m; [simpl; eauto|]; simpl; splits; eauto.
    introv Hdis' Heq' Hstep'.
    forwards* (h'' & ? & ? & ?): Hstep; exists h''; splits; eauto.
    apply IHn; eauto; omega.
Qed.

Lemma safe_ng_mono nt nb n m tst shp h P :
  safe_ng nt nb n tst shp h P -> m <= n -> 
  safe_ng nt nb m tst shp h P.
Proof.
  revert m tst shp h P; induction n; simpl; introv.
  - intros; assert (m = 0); [omega|substs]; simpl; eauto.
  - intros (Hskip & Hsafe1 & Hsafe2 & Hstep) Hmn.
    destruct m; [simpl; eauto|]; simpl; splits; eauto.
    introv Hdis' Heq' Hstep'.
    forwards* (h'' & ? & ? & ?): Hstep; exists h''; splits; eauto.
    apply IHn; eauto; omega.
Qed.

Lemma interp_f_n_mono n m fn fs :
  interp_f_n fn fs n -> m <= n -> interp_f_n fn fs m.
Proof.
  unfold interp_f_n, interp_fd_simp, interp_hfun_n_simp, interp_kfun_n_simp.
  destruct n; [destruct m; try omega; eauto|].
  destruct m; eauto.
  remember (S n) as n'; remember (S m) as m'.
  destruct func_disp as [[|]|]; eauto; intros; splits; jauto.
  - destruct H as (_ & _ & H).
    destruct fs; simpl; simpl in *.
    induction fs_tri0; simpl; eauto.
    unfold CSLhfun_n_simp.
    intros.
    forwards*: H.
    eauto using safe_nh_mono.
  - destruct H as (_ & _ & H).
    destruct fs; simpl; simpl in *.
    induction fs_tri0; simpl; eauto.
    unfold CSLkfun_n_simp.
    intros.
    forwards*: (>>H H3).
    eauto using safe_ng_mono.
Qed.

Lemma interp_FC_n_mono G n m :  
  interp_FC_n G n -> m <= n -> interp_FC_n G m.
Proof.
  unfold interp_FC_n; rewrite !Forall_forall; intros H Hle [fn fs] Hin.
  forwards*: H; simpl in *.
  applys* interp_f_n_mono.
Qed.

Lemma rule_host_seq G P Q R s1 s2 :
  CSLh G P s1 Q
  -> CSLh G Q s2 R 
  -> CSLh G P (host_seq s1 s2) R.
Proof.
  unfold CSLh, CSLh_n_simp, with_ctx; intros.
  eapply safe_seq; eauto.
  intros; applys* H0.
  applys* interp_FC_n_mono; omega.
Qed.
   
End Rules.