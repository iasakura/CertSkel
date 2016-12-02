Require Import LibTactics GPUCSL Grid Relations MyEnv.

(* Add kernel name *)
Record kernel := BuildKer { (* name : string; *) params_of : list (var * CTyp); body_of : program }.

Inductive expr :=
| VarE (x : var)
| Const (n : Z)
| Min (e1 e2 : expr)
| Add (e1 e2 : expr)
| Sub (e1 e2 : expr)
| Div (e1 e2 : expr).

Definition kerID := nat.
Instance nat_eq : eq_type nat := {|eq_dec := Nat.eq_dec|}.

(* the syntax of host-side program *)
Inductive stmt :=
| host_skip : stmt
| host_alloc : var -> expr -> stmt
| host_iLet : var -> expr -> stmt
| host_invoke : string -> nat -> nat -> list expr -> stmt
(* runtime expression representing kernel execution *)
| host_exec_ker : forall ntrd nblk,
    Vector.t (klist ntrd) nblk
    -> Vector.t simple_heap nblk
    -> stmt
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

Record GPUstate := GS {
  gs_stack : stack;
  gs_heap : simple_heap
}.

Definition alloc_heap (start len : nat) : simple_heap :=
  fun i => if Z_le_dec (Z.of_nat start) i then
             if Z_lt_dec i (Z.of_nat start + Z.of_nat len)%Z then Some (0%Z)
             else None
           else None.

Fixpoint bind_params (stk : stack) (xs : list (var * CTyp)) (vs : list Z) : Prop :=
  match xs, vs with
  | nil, nil => True
  | (x, _) :: xs, v :: vs => bind_params stk xs vs /\ stk x = v
  | _, _ => False
  end.

Definition henv_get (e : stack) (x : var) := e x.

Definition lift {A B C : Type} (f : A -> B -> C) x y :=
  match x, y with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.

Fixpoint eval_expr (env : stack) (e : expr) : Z :=
  match e with
  | VarE x => henv_get env x
  | Const c => c
  | Min e1 e2 => Z.min (eval_expr env e1) (eval_expr env e2)
  | Add e1 e2 => Z.add (eval_expr env e1) (eval_expr env e2)
  | Div e1 e2 => Z.div (eval_expr env e1) (eval_expr env e2)
  | Sub e1 e2 => Z.sub (eval_expr env e1) (eval_expr env e2)
  end.

Fixpoint func_disp (m : GModule) (name : string) :=
  match m with
  | nil => None
  | (fn, f) :: m => if string_dec name fn then Some f else None
  end%list.

Section VecNot.

Import Vector.VectorNotations.

Inductive init_GPU (ntrd nblk : nat) : kernel -> list Z
                     -> Vector.t (klist ntrd) nblk
                     -> Vector.t simple_heap nblk
                     -> Prop :=
| C_ker (ker : kernel) (args : list Z) 
        (tst : Vector.t (klist ntrd) nblk) (shp : Vector.t simple_heap nblk) stk :
    ntrd <> 0 ->
    nblk <> 0 ->
    bind_params stk (params_of ker) args ->
    (forall i j, decl_sh (get_sh_decl (body_of ker)) (snd tst[@j][@i]) shp[@j]) ->
    (forall i j, fst tst[@j][@i]             = get_cmd (body_of ker)) ->
    (forall i j, snd tst[@j][@i] (Var "tid") = Zn (nf i)) ->
    (forall i j, snd tst[@j][@i] (Var "bid") = Zn (nf j)) ->
    (forall i j v, v <> Var "tid" -> v <> Var "bid" -> snd tst[@j][@i] v = stk v) ->
    init_GPU ntrd nblk ker args tst shp.

(* Fixpoint replace_nth {A : Type} (i : nat) (l : list A) (x : A) := *)
(*   match i, l with *)
(*   | O, _ :: l => x :: l *)
(*   | S i, y :: l => y :: y :: replace_nth i l x *)
(*   | _, _ => l *)
(*   end%list. *)

Instance var_eq_type : eq_type var := {|
  eq_dec := var_eq_dec
|}.

Inductive stmt_exec : GModule -> stmt -> GPUstate -> stmt -> GPUstate -> Prop :=
| Exec_alloc kenv (x : var) e (gst : GPUstate) start n :
    eval_expr (gs_stack gst) e = (Z.of_nat n) ->
    hdisj (gs_heap gst) (alloc_heap start n) ->
    stmt_exec kenv (host_alloc x e) gst
              host_skip (GS (upd (gs_stack gst) x (Z.of_nat start))
                            (hplus (gs_heap gst) (alloc_heap start n)))
| Exec_iLet kenv x e (gst : GPUstate) n :
    eval_expr (gs_stack gst) e = n ->
    stmt_exec kenv (host_iLet x e) gst
              host_skip (GS (upd (gs_stack gst) x n) (gs_heap gst))
| Exec_invoke ntrd nblk kenv tst shp kerID ker args vs gst :
    List.Forall2 (fun a v => eval_expr (gs_stack gst) a = v) args vs ->
    func_disp kenv kerID = Some (Kern ker) ->
    init_GPU ntrd nblk ker vs tst shp ->
    stmt_exec kenv
              (host_invoke kerID ntrd nblk args) gst
              (host_exec_ker ntrd nblk tst shp) gst
| Exec_invoke_step kenv ntrd nblk tst tst' shp shp' s h h' :
    red_g (Gs tst shp h)  (Gs tst' shp' h') ->
    stmt_exec kenv
              (host_exec_ker ntrd nblk tst shp) (GS s h)
              (host_exec_ker ntrd nblk tst' shp') (GS s h')
| Exec_invoke_end kenv ntrd nblk tst shp s h :
    (forall i j, fst tst[@j][@i] = Cskip) ->
    stmt_exec kenv
              (host_exec_ker ntrd nblk tst shp) (GS s h)
              (host_skip) (GS s h)
| Exec_seq1 kenv s1 s2 s1' st1 st2 :
    stmt_exec kenv s1 st1 s1' st2  ->
    stmt_exec kenv (host_seq s1 s2) st1 (host_seq s1' s2) st2
| Exec_seq2 kenv s st1 st2 :
    stmt_exec kenv (host_seq host_skip s) st1 s st2.
End VecNot.

Inductive aborts_h : GModule -> stmt -> stack -> simple_heap -> Prop :=
  | aborts_host_seq : forall ke p p' s h, aborts_h ke p s h -> aborts_h ke (host_seq p p') s h
  | aborts_kernel_call : forall ke kid n m args s h,
      func_disp ke kid = None \/
      (exists f, func_disp ke kid = Some (Host f)) \/
      n = 0 \/ m = 0 \/
      (forall ker, func_disp ke kid = Some (Kern ker) -> length args <> length (params_of ker)) ->
      aborts_h ke (host_invoke kid n m args) s h
  | aborts_kernel_exec : forall kenv ntrd nblk tst shp s h,
      (abort_g (Gs tst shp h) \/ bdiv_g ntrd nblk tst shp (htop h)) ->
      aborts_h kenv (host_exec_ker ntrd nblk tst shp) s h.

Notation zpheap := (gen_pheap Z).

Section Logic.

Variable GM : GModule.

Fixpoint safe_nh (n : nat) (s : stack) (gh : zpheap) (p : stmt) (Q : assn) :=
  match n with
  | 0 => True
  | S n =>
    (p = host_skip -> Q s (as_gheap gh)) /\
    (forall (hF : zpheap) (h' : simple_heap),
        pdisj gh hF 
        -> ptoheap (phplus gh hF) h'
        -> aborts_h GM p s h') /\
    (forall (hF : zpheap) (h h' : simple_heap) (s' : stack) (p' : stmt),
        pdisj gh hF 
        -> ptoheap (phplus gh hF) h'
        -> stmt_exec GM p (GS s h) p' (GS s' h') 
        -> exists (h'' : zpheap),
            pdisj h'' hF /\ ptoheap (phplus h'' hF) h' /\
            safe_nh n s h'' p' Q)
  end.

Definition CSL_nh (P : assn) (ss : stmt) (Q : assn) (n : nat) :=
  forall s h,
    P s (as_gheap h) -> safe_nh n s h ss Q.

Definition CSLh P ss Q := forall n, CSL_nh P ss Q n.

Definition CSLhfun_n (P : assn) (f : hostfun) (Q : assn) (n : nat) :=
  forall vs s h,
    length vs = length (host_params f)
    -> bind_params s (host_params f) vs
    -> P s (as_gheap h)
    -> safe_nh n s h (host_stmt f) Q.

Definition CSLhfun P f Q := forall n, CSLhfun_n P f Q n.

Definition CSLgfun_n (P : assn) (f : kernel) (Q : assn) (n : nat) :=
  forall ntrd nblk vs tst shs h s,
    ntrd <> 0 -> nblk <> 0
    -> init_GPU ntrd nblk f vs tst shs
    -> bind_params s (params_of f) vs
    -> P s (as_gheap h)
    -> safe_ng ntrd nblk n tst shs h Q.

Definition CSLgfun P f Q := forall n, CSLgfun_n P f Q n.

Inductive FSpec : Type :=
| FAll (T : Type) (tri : T -> FSpec) : FSpec
| FDbl (P : assn) (Q : assn) : FSpec.

Notation "'All' x .. y ',' tri" := (FAll _ (fun x => .. (FAll _ (fun y => tri)) ..))
                                     (at level 200, x binder, y binder, tri at level 200).

Fixpoint interp_htri_n (name : string) (fs : FSpec) (n : nat) : Prop :=
  match fs with
  | FAll _ tri => forall x, interp_htri_n name (tri x) n
  | FDbl P Q => 
    match func_disp GM name with
    | None => False
    | Some (Host f) => CSLhfun_n P f Q n
    | Some (Kern k) => CSLgfun_n P k Q n
    end
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
  induction fs; simpl; eauto.
  unfold fn_ok; destruct func_disp; try congruence. 
  unfold CSLhfun_n, CSLgfun_n; destruct f; simpl; auto.
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