Require Import LibTactics GPUCSL Relations SeqSkel.

Record kernel := BuildKer { params_of : list var; body_of : program }.

Inductive CUDA : Type -> Type :=
| alloc : nat -> CUDA Z
| memCpy : list Z -> Z -> CUDA unit
| callKer : kernel -> nat -> nat -> list Z -> CUDA unit (* ker<<<n, m>>>(ps) *)
| getRes : Z -> nat -> CUDA (list Z)
| ret : forall a, a -> CUDA a
| bind : forall a b, CUDA a -> (a -> CUDA b) -> CUDA b.

Notation "'let!' x := e1 'in' e2" := (bind _ _ e1 (fun x => e2)) (at level 200, x ident, e1 at level 100, e2 at level 200).

Arguments ret {a} n.

Definition GPUstate := simple_heap.

Definition alloc_heap (start len : nat) : simple_heap :=
  fun i => if Z_le_dec (Z.of_nat start) i then
             if Z_lt_dec i (Z.of_nat start + Z.of_nat len)%Z then Some (0%Z)
             else None
           else None.

Fixpoint fill_obj (ls : list Z) (s : Z) (h : simple_heap) := 
  match ls with
  | nil => Some h
  | x :: ls =>
    match h s with
    | None => None
    | Some _ =>
      match fill_obj ls (s + 1) h with
      | None => None
      | Some h' => Some (fun i => if eq_dec i s then Some x else h' i)
      end
    end
  end.

Fixpoint bind_params (stk : stack) (xs : list var) (vs : list Z) : Prop :=
  match xs, vs with
  | nil, nil => True
  | x :: xs, v :: vs => bind_params stk xs vs /\ stk x = v
  | _, _ => False
  end.

Fixpoint getResFromHeap (p : Z) (n : nat) (gst : simple_heap) : option (list Z) :=
  match n with
  | 0 => Some nil
  | S n => match (getResFromHeap (Z.succ p) n gst) with
           | None => None
           | Some vs =>
             match gst p with
             | Some v => Some (v :: vs)
             | None => None
             end
           end
  end.

Section VecNot.

Definition red_g_star nblk ntrd := clos_refl_trans _ (@red_g nblk ntrd).
Import Vector.VectorNotations.

Inductive call_kernel : GPUstate -> kernel -> nat -> nat -> list Z -> GPUstate -> Prop :=
| C_ker (gst gst' : GPUstate) (ker : kernel) (ntrd nblk : nat) (args : list Z)
        (ks : Vector.t (Vector.t (cmd * stack) ntrd) nblk) stk sh (gs : g_state nblk ntrd) :
    ntrd <> 0 ->
    nblk <> 0 ->
    bind_params stk (params_of ker) args ->
    (forall i j, decl_sh (get_sh_decl (body_of ker)) (snd ks[@j][@i]) sh) ->
    (forall i j, fst ks[@j][@i]             = get_cmd (body_of ker)) ->
    (forall i j, snd ks[@j][@i] (Var "tid") = Zn (nf i)) ->
    (forall i j, snd ks[@j][@i] (Var "bid") = Zn (nf j)) ->
    (forall i j v, v <> Var "tid" -> v <> Var "bid" -> snd ks[@j][@i] v = stk v) ->
    red_g_star nblk ntrd {| blks := ks; sh_hp := (Vector.const sh nblk); gl_hp := gst |} gs ->
    (forall i j, fst (blks gs)[@j][@i] = Cskip) ->
    call_kernel gst ker ntrd nblk args (gl_hp gs).

End VecNot.

Inductive CUDA_eval : forall a, CUDA a -> GPUstate -> a -> GPUstate -> Prop :=
| E_alloc n start gst : (* FIXME: more relaxed definition: one of the free area is chosen *)
    hdisj gst (alloc_heap start n) ->
    CUDA_eval _
      (alloc n) gst
      (Z.of_nat start) (hplus gst (alloc_heap start n))
| E_memCpy ls p h h' gst :
    fill_obj ls p h = Some h' ->
    CUDA_eval _
      (memCpy ls p) gst
      tt h'
| E_callKer ker ntrd nblk args gst gst' :
    call_kernel gst ker ntrd nblk args gst' -> 
    CUDA_eval _
      (callKer ker ntrd nblk args) gst 
      tt gst'
| E_getRes p n vs gst :
    getResFromHeap p n gst = Some vs ->
    CUDA_eval _
      (getRes p n) gst
      vs gst
| E_ret a (v : a) gst :
    CUDA_eval _
      (ret v) gst
      v gst
| E_bind a b (cu : CUDA a) v v' (k : a -> CUDA b) gst gst' gst'' :
    CUDA_eval _ cu gst v gst' ->
    CUDA_eval _ (k v) gst' v' gst'' ->
    CUDA_eval _ (bind _ _ cu k) gst v' gst''.

Parameter run : forall a, CUDA a -> a.
Axiom runCorrect : forall a (cu : CUDA a) gst gst' v, CUDA_eval _ cu gst v gst' <-> run _ cu = v.

Fixpoint assn_of_bind (params : list var) (args : list Z) :=
  match params, args with
  | nil, nil => emp
  | p :: ps, a :: _as => !(p === a) ** assn_of_bind ps _as
  | _, _ => FalseP
  end.

Import Vector.VectorNotations.

Lemma rule_ker_call ntrd nblk args P_F P P' ker Q gst gst' :
  CSLg ntrd nblk P (body_of ker) Q ->
  (P' ** !(assn_of_bind (params_of ker) args) |= P) ->
  (forall s, (P' ** P_F) s (as_gheap (htop gst))) ->
  call_kernel gst ker ntrd nblk args gst' ->
  has_no_vars Q -> has_no_vars P_F ->
  (Q ** P_F) default_stack (as_gheap (htop gst')).
Proof.
  intros.

  inverts H2.
  lets HPstk: (H1 stk).
  destruct HPstk as (hp1 & hp2 & ? & ? & ? & ?).
  apply phplus_gheap in H17 as (h1' & h2' & ? & ? & ?); substs; eauto.
  
  lets*: (>>H __ __ __ __ __ __ __ __ __); eauto.
  exists (MyVector.init (fun (bid : Fin.t nblk) =>
                           fun v => if var_eq_dec v (Var "bid") then Zn (nf bid) else stk v)); intros.
  { rewrite MyVector.init_spec; destruct var_eq_dec; substs.
    - rewrite H11; auto.
    - rewrite H12; auto. }
  exists stk; split; eauto.
  apply H0.
  sep_split.
  Lemma assn_of_bind_ok stk ps args : bind_params stk ps args -> assn_of_bind ps args stk (emp_ph loc).
  Proof.
    revert args; induction ps; destruct args; simpl; intros; eauto.
    apply emp_emp_ph.
    sep_split; unfold_conn; jauto.
  Qed.
  apply assn_of_bind_ok; eauto.
  apply H2.
  
  Lemma safe_ng_when_terminates ntrd nblk (h1 h2 : gen_pheap Z) Q gs gs' :
    (forall n, safe_ng ntrd nblk n (blks gs) (sh_hp gs) h1 Q) ->
    red_g_star nblk ntrd gs gs' ->
    (forall i j, fst (blks gs')[@j][@i] = Cskip) ->
    phplus h1 h2 = htop (gl_hp gs) ->
    pdisj (as_gheap h1) (as_gheap h2) ->
    exists (h' : gen_pheap Z),
      pdisj h' h2 /\ phplus h' h2 = htop (gl_hp gs') /\
      Q default_stack (as_gheap h').
  Proof.
    intros.    
    unfold red_g_star in H0.
    apply clos_rt_rt1n in H0.
    revert h1 h2 H H2 H3; induction H0; simpl in *; intros.
    - subst; simpl in *.
      specialize (H 1); simpl in *; destructs H.
      exists h1; split; eauto using pdisj_as_gheap.
    - lets: (H2 1); simpl in *; destructs H5.
      forwards*: H8; eauto using pdisj_as_gheap.
      { apply eq_ptoheap; unfold htop; jauto. }
      { destruct x; simpl; eauto. }
      destruct H9 as (? & ? & ? & ?).
      forwards* : (>>IHclos_refl_trans_1n x0 h2); eauto using pdisj_as_gheap.
      { intros n; lets: (H2 (S n)); simpl in *.
        destructs H12.
        forwards*: H15; eauto using pdisj_as_gheap.
        { apply eq_ptoheap; unfold htop; jauto. }
        { destruct x; simpl; eauto. }
        destruct H16 as (? & ? & ? & ?).
        assert (x1 = x0).
        { eapply padd_cancel2; eauto.
          apply ptoheap_eq in H10; apply ptoheap_eq in H17; congruence. }
        substs; eauto. }
      apply ptoheap_eq; eauto.
      apply as_gheap_pdisj; eauto.
  Qed.

  pose ({| blks := ks; sh_hp := (Vector.const sh nblk); gl_hp := gst |}) as x.
  cutrewrite (ks = blks x) in H17; [|substs; eauto].
  cutrewrite (Vector.const sh nblk = sh_hp x) in H17; [|substs; eauto].
  lets*: (>>safe_ng_when_terminates h1' h2' H17 H13 ___).
  destruct H18 as (h' & ? & ? & ?); simpl.
  exists (as_gheap h') (as_gheap h2'); repeat split; eauto using as_gheap_pdisj.
  eapply H4; simpl; eauto.
  unfold as_gheap; simpl; rewrite <-!phplus_as_gheap; eauto.
  f_equal; apply H20.
Qed.

Require Import pmap_skel.
Import Syntax Skel_lemma scan_lib Monad.

Section Compiler.
  Definition free_av_func (f : Func) :=
    match f with
    | F ps body => free_av body
    end.

  Definition free_av_AE (ae : AE) :=
    match ae with
    | DArr f len =>
      SA.union (free_av_func f) (free_av len)
    | VArr xa => SA.singleton xa
    end.

  Fixpoint map_opt {A B : Type} (f : A -> option B) (xs : list A) : option (list B) :=
    sequence (map f xs).

  Variable aty_env : Env varA (option Typ) _.
  
  Definition env_of_sa (xas : SA.t) : Env varA nat _ :=
    snd (SA.fold (fun xa (n_aenv : nat * Env varA nat _)  =>
               let (n, aenv) := n_aenv in
               (n + 1, upd aenv xa n)) xas (0, emp_def 0)).

  Definition arr_name n d := names_of_array (grpOfInt n) d.
  Definition len_name n := name_of_len (grpOfInt n).

  Definition zipWith {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B) :=
    map (fun xy => f (fst xy) (snd xy)) (combine xs ys).

  Definition compile_AE avar_env svar_env ae :=
    match A
  
  Fixpoint compile_prog (var_ptr_env : Env varA Z _) (p : prog) :=
    match p with
    | ALet xa sname fs aes p =>
      let fvs :=
          SA.union
            (List.fold_right (fun f sa => SA.union (free_av_func f) sa) SA.empty fs)
            (List.fold_right (fun ae sa => SA.union (free_av_AE ae) sa) SA.empty aes)
      in
      let avar2idx := env_of_sa fvs in
      let avar_env := option_map (fun xa =>
         (aty_env xa) >>= fun aty =>
         (len_name (avar2idx xa), arr_name (avar2idx xa) (len_of_ty aty))) fvs in
      let! out := alloc len in
      let! ker := {| params_of := ; body_of := |} in
      callKer ker ntrd nblk (out :: len :: )
    | ARet xa => ret (var_ptr_env xa).
