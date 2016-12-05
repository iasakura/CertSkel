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

Definition alloc_heap (start len : nat) : simple_heap :=
  fun i => if Z_le_dec (Z.of_nat start) i then
             if Z_lt_dec i (Z.of_nat start + Z.of_nat len)%Z then Some (0%Z)
             else None
           else None.

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
  | (fn, f) :: m => if string_dec name fn then Some f else None
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
| Exec_alloc kenv (x : var) e (gst : State) start n :
    edenot e (st_stack gst) = (Z.of_nat n) ->
    hdisj (st_heap gst) (alloc_heap start n) ->
    stmt_exec kenv (host_alloc x e) gst
              host_skip (St (upd (st_stack gst) x (Z.of_nat start))
                            (hplus (st_heap gst) (alloc_heap start n)))
| Exec_iLet kenv x e (gst : State) n :
    edenot e (st_stack gst) = n ->
    stmt_exec kenv (host_iLet x e) gst
              host_skip (St (upd (st_stack gst) x n) (st_heap gst))
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
| Exec_seq2 kenv s st1 st2 :
    stmt_exec kenv (host_seq host_skip s) st1 s st2.
End VecNot.

Inductive aborts_h : GModule -> stmt -> stack -> simple_heap -> Prop :=
  | aborts_host_seq : forall ke p p' s h, aborts_h ke p s h -> aborts_h ke (host_seq p p') s h
  | aborts_kernel_invk : forall ke kid en n em m args s h,
      edenot en s = Zn n ->
      edenot em s = Zn m ->
      func_disp ke kid = None \/
      (exists f, func_disp ke kid = Some (Host f)) \/
      n = 0 \/ m = 0 \/
      (forall ker, func_disp ke kid = Some (Kern ker) -> length args <> length (params_of ker)) ->
      aborts_h ke (host_invoke kid en em args) s h
  | aborts_kernel_exec : forall kenv ntrd nblk tst shp s h,
      (abort_g (Gs tst shp h) \/ bdiv_g ntrd nblk tst shp (htop h)) ->
      aborts_h kenv (host_exec_ker ntrd nblk tst shp) s h
  | aborts_hfun_call : forall ke fn args s h,
      func_disp ke fn = None \/
      (exists f, func_disp ke fn = Some (Kern f)) \/
      (forall hf, func_disp ke fn = Some (Host hf) -> length args <> length (host_params hf)) ->
      aborts_h ke (host_call fn args) s h
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

Definition CSLh_simp P ss Q := forall n, CSLh_n_simp P ss Q n.

Definition CSLhfun_n_simp (P : assn) (f : hostfun) (Q : assn) (n : nat) :=
  forall vs s h,
    bind_params s (map fst (host_params f)) vs
    -> sat s (as_gheap h) P
    -> safe_nh n s h (host_stmt f) Q.

Definition CSLhfun_simp P f Q := forall n, CSLhfun_n_simp P f Q n.

Definition CSLgfun_n_simp (P : assn) (f : kernel) (Q : assn) (n : nat) :=
  forall ntrd nblk vs tst shs h s,
    ntrd <> 0 -> nblk <> 0
    -> init_GPU ntrd nblk (body_of f) tst shs s
    -> bind_params s (map fst (params_of f)) vs
    -> sat s (as_gheap h) P
    -> safe_ng ntrd nblk n tst shs h Q.

Definition CSLgfun_simp P f Q := forall n, CSLgfun_n_simp P f Q n.

Inductive FSpec : Type :=
| FAll (T : Type) (tri : T -> FSpec) : FSpec
| FDbl (P : assn) (Q : assn) : FSpec.

Notation "'All' x .. y ',' tri" := (FAll _ (fun x => .. (FAll _ (fun y => tri)) ..))
                                     (at level 200, x binder, y binder, tri at level 200).

Fixpoint interp_fs (fs : FSpec) (k : assn -> assn -> Prop) : Prop :=
  match fs with
  | FAll _ fs => forall x, interp_fs (fs x) k
  | FDbl P Q => k P Q
  end.

Definition interp_htri_n (name : string) (fs : FSpec) (n : nat) : Prop :=
  match func_disp GM name with
  | None => False
  | Some (Host f) => interp_fs fs (fun P Q => CSLhfun_n_simp P f Q n)
  | Some (Kern k) => interp_fs fs (fun P Q => CSLgfun_n_simp P k Q n)
  end.

Definition FC := list (string * FSpec).

Definition interp_FC_n (G : FC) (n : nat) :=
  List.Forall (fun x => let '(fn, fs) := x in interp_htri_n fn fs n) G.

Definition sat_htri (G  : FC) fn fs :=
  forall n, interp_FC_n G (n - 1) -> interp_htri_n fn fs n.

Definition sat_FC (G1 G2 : FC) :=
  forall n, interp_FC_n G1 (n - 1) -> interp_FC_n G2 n.

Definition fn_ok fn :=
  match func_disp GM fn with
  | None => false
  | Some _ => true
  end.

Fixpoint fc_ok (G : FC) :=
  match G with
  | nil => true
  | (fn, fs) :: G => andb (fn_ok fn) (fc_ok G)
  end.

Lemma interp_htri_0 fn fs : fn_ok fn = true -> interp_htri_n fn fs 0.
Proof.
  unfold interp_htri_n.
  induction fs; simpl; eauto.
  unfold fn_ok in *; destruct func_disp; try congruence.
  destruct f; simpl; auto.
  unfold fn_ok in *; destruct func_disp; try congruence.
  destruct f; unfold CSLhfun_n_simp, CSLgfun_n_simp; simpl; eauto.
Qed.

Lemma interp_fc_0 G : fc_ok G = true -> interp_FC_n G 0.
Proof.
  induction G as [|[? ?] ?]; simpl.
  - intros; constructor.
  - rewrite Bool.andb_true_iff; intros [? ?]; simpl.
    constructor; [apply* interp_htri_0|apply* IHG].
Qed.

Lemma rule_module_rec G : fc_ok G = true -> sat_FC G G -> sat_FC nil G.
Proof.  
  unfold sat_FC; intros ? ? n; induction n; simpl.
  - intros _.
    apply* interp_fc_0.
  - intros; apply H0; simpl.
    rewrite <-minus_n_O; eauto.
    apply IHn.
    constructor.
Qed.

Lemma rule_module_each G1 G2 :
  (forall fn fs, In (fn, fs) G2 -> sat_htri G1 fn fs)
  -> sat_FC G1 G2.
Proof.
  unfold sat_FC, sat_htri, interp_FC_n.
  intros; repeat rewrite Forall_forall in *; intros.
  destruct x; apply* H.
  rewrite Forall_forall; intros.
  apply* H0.
Qed.  

Definition CSLh_n G P ss Q :=
  forall n, interp_FC_n G (n - 1) -> CSLh_n_simp P ss Q n.

Definition interp_stmt_n G ss fs :=
  forall n, interp_FC_n G (n - 1) -> interp_fs fs (fun P Q => CSLh_n_simp P ss Q n).

Lemma rule_hfun fn hf fs G :
  func_disp GM fn = Some (Host hf)
  -> interp_stmt_n G (host_stmt hf) fs
  -> sat_htri G fn fs.
Proof.  
  intros Hname Hok n Hctx.
  unfold interp_htri_n; rewrite Hname; cbn.
  unfold interp_stmt_n, CSLh_n_simp, CSLhfun_n_simp in *.
  forwards* Hok': Hok.
  revert Hok'; clear.
  induction fs; simpl; eauto.
Qed.

Definition interp_prog_n ntrd nblk G kp sp :=
  forall n, interp_FC_n G (n - 1) -> interp_fs sp (fun P Q => CSLg_n ntrd nblk P kp Q n).

Lemma rule_kfun fn kf fs G :
  func_disp GM fn = Some (Kern kf)
  -> (forall ntrd nblk, interp_prog_n ntrd nblk G (body_of kf) fs)
  -> sat_htri G fn fs.
Proof.  
  intros Hname Hok n Hctx.
  unfold interp_htri_n; rewrite Hname; cbn.
  unfold interp_prog_n, CSLgfun_n_simp, CSLg_n in *.
  revert Hok.
  induction fs; simpl; eauto.
Qed.

Inductive inst_spec : FSpec -> assn -> assn -> Prop :=
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
  interp_fs fs k 
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

Lemma rule_call (G : FC) (fn : string) (nt nb : nat) (es : list exp)
      xs vs body res
      fs 
      Rpre Ppre Epre
      Rpst Ppst
      RF R E (P : Prop) :
  fc_ok G = true
  -> In (fn, fs) G
  -> func_disp GM fn = Some (Host (Hf xs body res))
  -> length es = length xs
  -> inst_spec fs (Assn Rpre Ppre Epre) (Assn Rpst Ppst nil)
  -> List.Forall2 (fun e v => evalExp E e v) es vs
  -> (P -> subst_env Epre (map fst xs) vs)
  -> (P -> Ppre)
  -> (P -> R |=R Rpre *** RF)
  -> CSLh_n G
            (Assn R P E)
            (host_call fn es)
            (Assn (Rpst *** RF) (P /\ Ppst) E).
Proof.
  intros Hfcok Hinfn Hdisp Harg Hinst Heval Hsubst Hp Hr n HFC s h Hsat.
  destruct n; simpl; eauto.
  splits; eauto.
  - inversion 1.
  - introv Hdisj Htoh Habort.
    inverts Habort as Habort.
    destruct Habort as [? | [ [? ?] | Hcallab] ]; try congruence.
    forwards* Hc: (>> Hcallab Hdisp); simpl in Hc.
  - introv Hdis Htoh Hstep.
    simpl in HFC; rewrite <-minus_n_O in HFC.
    unfold interp_FC_n, interp_htri_n in HFC; rewrite Forall_forall in HFC.
    forwards* Hfn: (>>HFC Hinfn); rewrite Hdisp in Hfn.
    forwards* Hfn': (>>interp_fs_inst Hfn Hinst); simpl in Hfn'.
    unfold CSLhfun_n_simp in Hfn'; simpl in Hfn'.
    inverts Hstep as Hdisp' Heval' Hbnd; simpl in *.
    rewrite Hdisp in Hdisp'; inverts Hdisp'; simpl in *.
    unfold Assn, sat in Hsat.
    sep_split_in Hsat.
    forwards* (h1 & h2 & Hpre & HF & Hdis12 & Heq12): (>> Hr HP Hsat).
    forwards* (h1' & h2' & ? & ? & Heq12'): (>> phplus_gheap  Heq12); substs.
    forwards* Hsafe: (>>Hfn' h1' Hbnd).
    (* Proof that precond holds *)
    { unfold sat, Assn; sep_split; eauto.
      - applys* Hp.
      - applys* subst_env_bind_params.
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
      (xs : list (var * CTyp)) (vs : list val) body
      fs ent ntrd enb nblk
      Rpre Ppre Epre
      Rpst Ppst
      RF R E (P : Prop) :
  fc_ok G = true
  -> In (fn, fs) G
  -> func_disp GM fn = Some (Kern (BuildKer xs body))
  -> length es = length xs
  -> inst_spec fs (Assn Rpre Ppre Epre) (Assn Rpst Ppst nil)
  -> List.Forall2 (fun e v => evalExp E e v) (enb :: ent :: es) (Zn nblk :: Zn ntrd :: vs)
  -> ntrd <> 0 -> nblk <> 0
  -> (P -> subst_env Epre (Var "nblk" :: Var "ntrd" :: map fst xs) (Zn nblk :: Zn ntrd :: vs))
  -> (P -> Ppre)
  -> (P -> R |=R Rpre *** RF)
  -> CSLh_n G
            (Assn R P E)
            (host_invoke fn ent enb es)
            (Assn (Rpst *** RF) (P /\ Ppst) E).
Proof.
  intros Hfcok Hinfn Hdisp Harg Hinst Heval Hntrd Hnblk Hsubst Hp Hr n HFC s h Hsat.
  inverts Heval as Henb Heval.
  inverts Heval as Hent Heval.
  destruct n; simpl; eauto.
  splits; eauto.
  - inversion 1.
  - introv Hdisj Htoh Habort.
    inverts Habort as Hent0 Henb0 Habort.
    destruct Habort as [? | [ [? ?] | [Hn0 | [Hm0 | Hcallab] ]]]; try congruence.
    + unfold Assn, sat in Hsat; sep_split_in Hsat.
      forwards* Hent': (>>evalExp_ok Hent).
      hnf in Hent'; simpl in Hent'; substs.
      rewrite Hent', Nat2Z.inj_iff in Hent0; eauto.
    + unfold Assn, sat in Hsat; sep_split_in Hsat.
      forwards* Henb': (>>evalExp_ok Henb).
      hnf in Henb'; simpl in Henb'; substs.
      rewrite Henb', Nat2Z.inj_iff in Henb0; eauto.
    + forwards* Hc: (>> Hcallab Hdisp); simpl in Hc.
  - introv Hdis Htoh Hstep.
    simpl in HFC; rewrite <-minus_n_O in HFC.
    unfold interp_FC_n, interp_htri_n in HFC; rewrite Forall_forall in HFC.
    forwards* Hfn: (>>HFC Hinfn); rewrite Hdisp in Hfn.
    forwards* Hfn': (>>interp_fs_inst Hfn Hinst); simpl in Hfn'.
    unfold CSLgfun_n_simp in Hfn'; simpl in Hfn'.
    inverts Hstep as Hent' Henb' Heval' Hdisp' Hinit Hbnd; simpl in *.
    rewrite Hdisp in Hdisp'; inverts Hdisp'; simpl in *.
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
End Rules. 

(* Fixpoint assn_of_bind (params : list var) (args : list Z) := *)
(*   match params, args with *)
(*   | nil, nil => emp *)
(*   | p :: ps, a :: _as => !(p === a) ** assn_of_bind ps _as *)
(*   | _, _ => FalseP *)
(*   end. *)

(* Import Vector.VectorNotations. *)

(* Lemma rule_ker_call ntrd nblk args P_F P P' ker Q gst gst' : *)
(*   CSLg ntrd nblk P (body_of ker) Q -> *)
(*   (P' ** !(assn_of_bind (map fst (params_of ker)) args) |= P) -> *)
(*   (forall s, (P' ** P_F) s (as_gheap (htop gst))) -> *)
(*   call_kernel gst ker ntrd nblk args gst' -> *)
(*   has_no_vars Q -> has_no_vars P_F -> *)
(*   (Q ** P_F) default_stack (as_gheap (htop gst')). *)
(* Proof. *)
(*   intros. *)

(*   inverts H2. *)
(*   lets HPstk: (H1 stk). *)
(*   destruct HPstk as (hp1 & hp2 & ? & ? & ? & ?). *)
(*   apply phplus_gheap in H17 as (h1' & h2' & ? & ? & ?); substs; eauto. *)
  
(*   lets*: (>>H __ __ __ __ __ __ __ __ __); eauto. *)
(*   exists (MyVector.init (fun (bid : Fin.t nblk) => *)
(*                            fun v => if var_eq_dec v (Var "bid") then Zn (nf bid) else stk v)); intros. *)
(*   { rewrite MyVector.init_spec; destruct var_eq_dec; substs. *)
(*     - rewrite H11; auto. *)
(*     - rewrite H12; auto. } *)
(*   exists stk; split; eauto. *)
(*   apply H0. *)
(*   sep_split. *)
(*   Lemma assn_of_bind_ok stk ps args : bind_params stk ps args -> assn_of_bind (map fst ps) args stk (emp_ph loc). *)
(*   Proof. *)
(*     revert args; induction ps as [|[? ?] ?]; destruct args; simpl; intros; eauto. *)
(*     apply emp_emp_ph. *)
(*     sep_split; unfold_conn; jauto. *)
(*   Qed. *)
(*   apply assn_of_bind_ok; eauto. *)
(*   apply H2. *)
  
(*   Lemma safe_ng_when_terminates ntrd nblk (h1 h2 : gen_pheap Z) Q gs gs' : *)
(*     (forall n, safe_ng ntrd nblk n (blks gs) (sh_hp gs) h1 Q) -> *)
(*     red_g_star nblk ntrd gs gs' -> *)
(*     (forall i j, fst (blks gs')[@j][@i] = Cskip) -> *)
(*     phplus h1 h2 = htop (gl_hp gs) -> *)
(*     pdisj (as_gheap h1) (as_gheap h2) -> *)
(*     exists (h' : gen_pheap Z), *)
(*       pdisj h' h2 /\ phplus h' h2 = htop (gl_hp gs') /\ *)
(*       Q default_stack (as_gheap h'). *)
(*   Proof. *)
(*     intros.     *)
(*     unfold red_g_star in H0. *)
(*     apply clos_rt_rt1n in H0. *)
(*     revert h1 h2 H H2 H3; induction H0; simpl in *; intros. *)
(*     - subst; simpl in *. *)
(*       specialize (H 1); simpl in *; destructs H. *)
(*       exists h1; split; eauto using pdisj_as_gheap. *)
(*     - lets: (H2 1); simpl in *; destructs H5. *)
(*       forwards*: H8; eauto using pdisj_as_gheap. *)
(*       { apply eq_ptoheap; unfold htop; jauto. } *)
(*       { destruct x; simpl; eauto. } *)
(*       destruct H9 as (? & ? & ? & ?). *)
(*       forwards* : (>>IHclos_refl_trans_1n x0 h2); eauto using pdisj_as_gheap. *)
(*       { intros n; lets: (H2 (S n)); simpl in *. *)
(*         destructs H12. *)
(*         forwards*: H15; eauto using pdisj_as_gheap. *)
(*         { apply eq_ptoheap; unfold htop; jauto. } *)
(*         { destruct x; simpl; eauto. } *)
(*         destruct H16 as (? & ? & ? & ?). *)
(*         assert (x1 = x0). *)
(*         { eapply padd_cancel2; eauto. *)
(*           apply ptoheap_eq in H10; apply ptoheap_eq in H17; congruence. } *)
(*         substs; eauto. } *)
(*       apply ptoheap_eq; eauto. *)
(*       apply as_gheap_pdisj; eauto. *)
(*   Qed. *)

(*   pose ({| blks := ks; sh_hp := (Vector.const sh nblk); gl_hp := gst |}) as x. *)
(*   cutrewrite (ks = blks x) in H17; [|substs; eauto]. *)
(*   cutrewrite (Vector.const sh nblk = sh_hp x) in H17; [|substs; eauto]. *)
(*   lets*: (>>safe_ng_when_terminates h1' h2' H17 H13 ___). *)
(*   destruct H18 as (h' & ? & ? & ?); simpl. *)
(*   exists (as_gheap h') (as_gheap h2'); repeat split; eauto using as_gheap_pdisj. *)
(*   eapply H4; simpl; eauto. *)
(*   unfold as_gheap; simpl; rewrite <-!phplus_as_gheap; eauto. *)
(*   f_equal; apply H20. *)
(* Qed. *)