Require Export CSL.
Require Import array_dist Bdiv MyList.
Import PHeap Lang assertion_lemmas.
Require Import LibTactics.

Section GlobalCSL.
Variable ntrd : nat.
Variable nblk : nat.
Variable E : env.

Hypothesis ntrd_neq_0 : ntrd <> 0.
Hypothesis nblk_neq_0 : nblk <> 0.
Definition heap_of_sheap (h : simple_heap) :=
  fun l => 
    match l with
      | GLoc l => h l
      | SLoc l => None
    end.

Definition default_stack : stack := fun x => 0%Z.

Require Import MyVector.
Import VectorNotations.

Notation zpheap := (PHeap.gen_pheap Z).
Notation zpheap' := (PHeap.gen_pheap' Z).

Definition glist nblk ntrd := Vector.t (klist ntrd) nblk.

Definition as_npgheap (h : simple_heap) : heap :=
  fun x => match x with
    | SLoc x => None
    | GLoc x => h x
  end.

Definition as_gheap' (h : zpheap') : pheap' :=
  fun x => match x with
    | SLoc x => None
    | GLoc x => h x
  end.

Lemma as_gh_is_ph (h : zpheap) : is_pheap (as_gheap' h).
Proof.
  intros [v | v]; unfold as_gheap'; eauto.
  destruct h as [? isph]; simpl; specialize (isph v); auto.
Qed.

Definition as_gheap (h : zpheap) := Pheap (as_gh_is_ph h).

Definition as_sheap (h : simple_heap) : heap :=
  fun x => match x with
    | SLoc x => h x
    | GLoc x => None
  end.    

Definition is_sheap (h : heap) := forall x, h (GLoc x) = None.
Definition is_gheap (h : pheap') := forall x, h (SLoc x) = None.
Lemma as_sh_is_sh (h : simple_heap) : is_sheap (as_sheap h).
Proof.
  unfold is_sheap; simpl; auto.
Qed.
Lemma as_gh_is_gh (h : zpheap') : is_gheap (as_gheap' h).
Proof.
  unfold is_gheap; simpl; auto.
Qed.

Lemma sh_gh_disj (sh : heap) (gh : pheap') : is_sheap sh -> is_gheap gh -> pdisj (htop' sh) gh.
Proof.
  unfold is_sheap, is_gheap, htop, htop'; intros; intros [? | ?]; simpl; auto;
  try rewrite H; try rewrite H0; auto.
  destruct (sh (SLoc z)); auto.
Qed.
Hint Resolve sh_gh_disj as_sh_is_sh as_gh_is_gh.
Lemma sh_gl_is_ph (sh : simple_heap) (gh : zpheap) : pdisj (htop (as_sheap sh)) (as_gheap gh).
Proof.
  simpl; eauto.
Qed.

Definition sh_gl_pheap (sh : simple_heap) (gh : zpheap) : pheap := phplus_pheap (sh_gl_is_ph sh gh).

Definition bdiv_g (gs : glist nblk ntrd) (shs : Vector.t simple_heap nblk) (gh : zpheap) :=
  exists (bid : Fin.t nblk), 
    Bdiv.bdiv (gs[@bid], (sh_gl_pheap shs[@bid] gh)).

Fixpoint safe_ng (n : nat) (gs : glist nblk ntrd)
         (shs : Vector.t simple_heap nblk) (gh : zpheap) (Q : assn) :=
  match n with
    | 0 => True
    | S n =>
      ((forall (bid : Fin.t nblk) (tid : Fin.t ntrd), fst gs[@bid][@tid] = SKIP) ->
         Q default_stack (as_gheap gh)) /\
      (forall (hF : zpheap) (h : simple_heap),
         pdisj gh hF ->
         ptoheap (phplus gh hF) h -> ~abort_g (Gs gs shs h)) /\
      ~ bdiv_g gs shs gh /\ 
      (forall (gs' : g_state nblk ntrd) (hF : zpheap) (h : simple_heap),
         pdisj gh hF ->
         ptoheap (phplus gh hF) h ->
         red_g (Gs gs shs h) gs' ->
         exists (h'' : zpheap),
           pdisj h'' hF /\ ptoheap (phplus h'' hF) (gl_hp gs') /\
           safe_ng n (blks gs') (sh_hp gs') h'' Q)
  end.

Record program : Set := Pr {
  get_sh_decl : list (var * nat);
  get_cmd : cmd}.

Section For_List_Notation.
  Import List.
  Import List.ListNotations.
  Import ZArith.

  Lemma Z_range_dec (x y z : Z) : ({x <= y < z} + {y < x \/ z <= y})%Z.
  Proof.
    destruct (Z_le_dec x y), (Z_lt_dec y z); first [left; omega | right; omega].
  Qed.
    
  Inductive decl_sh : list (var * nat) -> stack -> simple_heap -> Prop :=
  | decl_nil : forall stk, decl_sh nil stk (fun _ => None) 
  | decl_cons : forall ds stk sh v len loc,
      decl_sh ds stk sh ->
      (forall i, i < len -> sh (loc + Z.of_nat i)%Z = None) ->
      decl_sh ((v, len) :: ds) (fun v' => if var_eq_dec v' v then loc else stk v')
              (fun l => if Z_range_dec loc l (loc + Z.of_nat len) then Some 0%Z else sh l).


  Fixpoint sh_spec (sh_decl : list (var * nat)) : assn :=
    match sh_decl with
      | nil => emp
      | (sh, len) :: sh_decl => (Ex f, is_array (Sh sh) len f 0) ** sh_spec sh_decl
    end.
  
  Notation TID := (Var "tid").
  Notation BID := (Var "bid").
  Notation nf i := (nat_of_fin i).
  Notation zf i := (Z.of_nat (nf i)).

  Definition has_no_vars (P : assn) : Prop := indeP (fun (_ _ : stack) => True) P.
  
  Lemma safe_gl (n : nat) :
    forall (gs : glist nblk ntrd) (shs : Vector.t simple_heap nblk) (gh : zpheap) (ghs : Vector.t zpheap nblk) (Q : assn) (sh_decl : list (var * nat) )
           (Qs : Vector.t assn nblk),
      let sinv := sh_spec sh_decl in
      disj_eq ghs gh ->
      (forall bid : Fin.t nblk,
         safe_nk E n gs[@bid] (sh_gl_pheap shs[@bid] ghs[@bid]) (sinv ** Qs[@bid])) ->
      (forall bid : Fin.t nblk, has_no_vars Qs[@bid]) ->
      Aistar_v Qs |= Q -> 
      (forall bid tid, sinv (snd gs[@bid][@tid]) (htop (as_sheap shs[@bid]))) ->
      (forall bid tid, inde sinv (writes_var (fst gs[@bid][@tid]))) ->
      (forall var, List.In var (List.map fst sh_decl) -> E var = Lo) ->
      safe_ng n gs shs gh Q.
  Proof.
    induction n; [simpl; auto|].
    remember (safe_nk E (S n)).
    simpl; intros gs shs gh ghs Q sdec Qs Hdeq Hsafe Hnov HQ Hsinv Hsvar Hslow; repeat split; subst.
    - intros Hskip.
      evar (P : Fin.t nblk -> Prop); assert (Hskipb : forall bid, P bid); [|unfold P in *; clear P].
      { unfold P; intros bid; destruct (Hsafe bid) as (Hskipb & _).
        apply Hskipb in Hskip as (? & ?).
        unfold sat_k in H; simpl in H.
        lazymatch type of H with (let (_, _) := ?X in _) => destruct X as (srep & Hsrep) end.

        Lemma sh_spec_inde (sdec : list (var * nat)) (stk0 stk1 : stack) (E0 : env) : forall h,
          (sh_spec sdec) stk0 h -> low_eq E0 stk0 stk1 ->
          (forall var, List.In var (List.map fst sdec) -> E0 var = Lo) ->
          (sh_spec sdec) stk1 h.
        Proof.
          induction sdec as [|[v n] sdec]; simpl.
          - intros ? H ? ?; apply H.
          - intros h H Hlow Hv.
            destruct H as (ph1 & ph2 & ? & ? & ? & ?); exists ph1 ph2; repeat split; auto.
            destruct H as [f H]; exists f.
            clear IHsdec H1 H2; generalize dependent ph1. 
            generalize 0; induction n; simpl in *; intros st ph1 H; [apply H|].
            destruct H as (ph1' & ph2' & ? & ? & ? & ?); exists ph1' ph2'; repeat split; auto.
            unfold low_eq in Hlow; unfold_conn_all; simpl in *; intros x; rewrite <-Hlow; auto.
        Qed.

        assert ((sh_spec sdec) srep (htop (as_sheap shs[@bid]))).
        { assert (exists nt, ntrd = S nt) as [nt Hnt] by (exists (ntrd - 1); omega).
          generalize dependent gs; rewrite Hnt; intros.
          apply (sh_spec_inde _ (snd gs[@bid][@Fin.F1]) _ E); auto.
          specialize (Hsrep Fin.F1); erewrite nth_map in Hsrep; [apply Hsrep|]; auto. }


        Lemma htop_hplus' (h1 h2 : heap) (H : hdisj h1 h2) :
          htop' (hplus h1 h2) = phplus (htop' h1) (htop' h2).
        Proof.
          unfold htop, htop', hplus, phplus_pheap, phplus(*; simpl; apply pheap_eq *).
          extensionality x; specialize (H x).
          destruct (h1 x), (h2 x); try auto.
          destruct H; congruence.
        Qed.

        Lemma htop_hplus (h1 h2 : heap) (H : hdisj h1 h2) :
          htop (hplus h1 h2) = phplus_pheap (proj1 (hdisj_pdisj _ _) H).
        Proof.
          unfold htop, htop', hplus, phplus_pheap, phplus; simpl; apply pheap_eq.
          extensionality x; specialize (H x).
          destruct (h1 x), (h2 x); try auto.
          destruct H; congruence.
        Qed.

        Require Import Program.
        
        (* Lemma disj_eq_inj n (hs : Vector.t heap n) :forall h, *)
        (*   disj_eq (Vector.map (@htop _) hs) (htop h) -> *)
        (*   is_gheap h -> forall i, is_gheap hs[@i]. *)
        (* Proof. *)
        (*   induction n; simpl; intros h H Hgh i. *)
        (*   - inversion i. *)
        (*   - dependent destruction hs; dependent destruction i; simpl in *. *)
        (*     + intros l. *)
        (*       inversion H; subst; simpl; auto. *)
        (*       apply (f_equal (fun x => x (SLoc l))) in H4; unfold phplus, htop' in H4. *)
        (*       specialize (Hgh l). *)
        (*       destruct ph as [ph ?]; simpl in *. *)
        (*       destruct (h (SLoc l)), (ph (SLoc l)) as [[? ?]|], (h0 (SLoc l)); congruence. *)
        (*     + remember (htop h0) as hh0; inversion H; subst; simpl in *. *)
        (*       apply Eqdep.EqdepTheory.inj_pair2 in H3; subst; eauto. *)
        (*       apply (f_equal (fun x => this x)) in H2; simpl in H2. *)

        (*       Lemma htop_phplus_heap (h1 h2 : heap) (ph : pheap) : *)
        (*         pdisj (htop h1) ph -> *)
        (*         phplus (htop' h1) ph = htop' h2 -> *)
        (*         exists ph', ph = htop ph'. *)
        (*       Proof. *)
        (*         intros;exists (fun x => match PHeap.this ph x with None => None | Some (_,x) => Some x end). *)
        (*         destruct ph as [ph ?]; apply pheap_eq. *)
        (*         unfold phplus, htop, htop' in *; simpl in *; extensionality x; *)
        (*         apply (f_equal (fun f => f x)) in H0. *)
        (*         specialize (is_p x); specialize (H x). *)
        (*         pose proof frac_contra1. *)
        (*         destruct (ph x) as [[? ?]|], (h1 x), (h2 x); first [now auto | congruence | firstorder]. *)
        (*       Qed. *)

        (*       pose proof (@htop_phplus_heap _ _ _ hdis H2) as [ht Hht]; subst; auto. *)
        (*       eapply IHn. *)
        (*       apply H4. *)

        (*       intros x; apply (f_equal (fun f => f (SLoc x))) in H2; specialize (Hgh x). *)
        (*       unfold phplus, htop, htop' in H2; simpl in H2. *)
        (*       repeat lazymatch type of H2 with *)
        (*         | context [match ?X with | Some _ => _ | None => _ end] => destruct X *)
        (*         | context [let (_, _) := ?X in _] => destruct X *)
        (*       end; try congruence. *)
        (* Qed. *)


        assert (pdisj (htop' (as_sheap shs[@bid])) (as_gheap' ghs[@bid])) by auto.
        
        (* rewrite htop_hplus with (H :=H1) in H. *)

        Lemma sc_cancel (P Q : assn) s (hp hq : pheap) (Hdis : pdisj hp hq) :
          precise P ->
          (P ** Q) s (phplus_pheap Hdis) -> P s hp -> Q s hq.
        Proof.
          intros Hprc Hpq Hp; destruct Hpq as (ph1 & ph2 & ? & ? & ? & ?).
          assert (ph1 = hp).
          { specialize (Hprc ph1 ph2 hp hq); simpl in Hprc.
            specialize (Hprc _ H Hp H1 Hdis H2); auto. }
          assert (ph2 = hq).
          { subst; simpl in *.
            apply padd_cancel in H2; auto. }
          subst; auto.
        Qed.

        Require Import Qcanon.
        Lemma precise_ex {T : Type} (P : T -> assn) :
          (forall s x1 x2 h1 h2, P x1 s h1 -> P x2 s h2 ->
                                 (forall l q, (exists v0, PHeap.this h1 l = Some (q, v0)) ->
                                              (exists v1, PHeap.this h2 l = Some (q, v1)))) ->
          precise (Ex x, P x).
        Proof.
          unfold precise; simpl; intros.
          destruct H0 as [x0 H0], H1 as [x1 H1]; pose proof (H _ _ _ _  _ H0 H1); pose proof (H _ _ _ _ _ H1 H0).
          destruct h1 as [h1 ?], h1' as [h1' ?]; apply pheap_eq; extensionality l; simpl in *.
          apply (f_equal (fun f => f l)) in H4;
            specialize (H2 l); specialize (H3 l); specialize (H5 l); specialize (H6 l).
          unfold phplus in *; destruct (h1 l) as [[? ?]|], (h1' l) as [[? ?]|],
            (PHeap.this h2 l) as [[? ?]|], (PHeap.this h2' l) as [[? ?]|]; simpl in *; 
          try congruence;
          try (specialize (H5 q); specialize (H6 q);
               try (destruct H5; [eexists; reflexivity|]; inversion H5; subst);
               try (destruct H6; [eexists; reflexivity|]; inversion H6; subst);
               subst; congruence).
        Qed.
        
        Lemma precise_pts e1 q : precise (Ex e2, e1 -->p (q, Enum e2)).
        Proof.
          apply precise_ex; intros.
          unfold_conn_all; rewrite H, H0 in *; destruct H1; eexists;
          destruct (eq_dec l (ledenot e1 s)); try congruence;
          inversion H1; reflexivity.
        Qed.          
        
        Lemma precise_ex_star {T : Type} (P Q : T -> assn) :
          precise ((Ex x, P x) ** (Ex x, Q x)) ->
          precise (Ex x, P x ** Q x).
        Proof.
          unfold precise; simpl; intros.
          specialize (H h1 h2 h1' h2' s); apply H; auto.
          destruct H0 as (x & ph1 & ph2 & ? & ? & ? & ?).
          exists ph1; exists ph2; (repeat split); (try now (exists x; auto)); auto.
          destruct H1 as (x & ph1 & ph2 & ? & ? & ? & ?).
          exists ph1; exists ph2; (repeat split); (try now (exists x; auto)); auto.
        Qed.

        Lemma precise_is_array e n : forall s, precise (Ex f, is_array e n f s).
        Proof.
          induction n; simpl; intros.
          - apply precise_ex; intros; unfold_conn_all.
            rewrite H, H0 in *; auto.
          - apply precise_ex_star, precise_star.
            + apply precise_ex; intros.
              unfold_conn_all; rewrite H, H0 in *; destruct H1; eexists.
              destruct (eq_dec l (ledenot _ _)); try congruence;
              inversion H1; reflexivity.
            + apply IHn.
        Qed.

        Lemma precise_sh_spec (sh_dc : list (var * nat)) :
          precise (sh_spec sh_dc).
        Proof.
          induction sh_dc as [|[v n] sh_dc]; simpl; auto.
          - apply precise_emp.
          - apply precise_star; auto using precise_is_array.
        Qed.            
      
        apply (sc_cancel (sh_spec sdec) Qs[@bid] srep) in H; auto using precise_sh_spec.
        unfold has_no_vars, indeP in Hnov; simpl in Hnov.
        rewrite (Hnov _ _ default_stack _) in H; auto.
        exact H. }
      simpl in Hskipb.
      apply HQ.


      Lemma aistar_sat {n : nat} : forall (hs : Vector.t pheap n) (h : pheap) (Qs : Vector.t assn n) s ,
        disj_eq hs h -> (forall i, Qs[@i] s hs[@i]) -> Aistar_v Qs s h.
      Proof.
        induction n; dependent destruction hs; dependent destruction Qs; intros.
        - simpl; inversion H; apply emp_emp_ph.
        - simpl.
          inversion H; subst.
          exists h ph; repeat split; auto.
          specialize (H0 Fin.F1); apply H0.
          eapply IHn.
          apply H5.
          intros i; specialize (H0 (Fin.FS i)); simpl in H0.
          apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; auto.
      Qed.

      Lemma as_gheap_pdisj' (h1 h2 : zpheap') :
        pdisj h1 h2 -> pdisj (as_gheap' h1) (as_gheap' h2).
      Proof.
        intros H; intros [l | l]; simpl; auto.
        specialize (H l); auto.
      Qed.
      Lemma as_gheap_pdisj (h1 h2 : zpheap) :
        pdisj h1 h2 -> pdisj (as_gheap h1) (as_gheap h2).
      Proof.
        intros H; intros [l | l]; simpl; auto.
        specialize (H l); auto.
      Qed.
      Hint Resolve as_gheap_pdisj' as_gheap_pdisj.
      
      Lemma phplus_as_gheap (h1 h2 : zpheap') :
        as_gheap' (phplus h1 h2) = phplus (as_gheap' h1) (as_gheap' h2).
      Proof.
        extensionality x; destruct x; unfold hplus; simpl; auto.
      Qed.        

      Lemma disj_eq_as_gh {n : nat} (hs : Vector.t zpheap n) (h : zpheap) :
        disj_eq hs h -> disj_eq (Vector.map as_gheap hs) (as_gheap h).
      Proof.
        dependent induction hs; intros Heq; inversion Heq; subst.
        - assert (as_gheap (emp_ph Z) = emp_ph loc).
          { apply pheap_eq; extensionality l; destruct l as [l | l]; unfold emp_h; eauto. }
          rewrite H; constructor.
        - apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
          assert (Hdis : pdisj (as_gheap h) (as_gheap ph)) by (simpl; auto).
          assert (as_gheap (Pheap (pdisj_is_pheap hdis)) = phplus_pheap Hdis).
          { lets Heq': (>>phplus_as_gheap h ph); unfold phplus_pheap in Heq'.
            apply pheap_eq; simpl; auto. }
          rewrite H; constructor; eauto.
      Qed.          
      apply disj_eq_as_gh in Hdeq.
      eapply aistar_sat; eauto.
      intros; erewrite Vector.nth_map; [|reflexivity]; auto.

    - intros hF h Hdis Heq [bid ?].
      destruct (Hsafe bid) as (_ & Hnabort & _ & _).
      unfold bs_of_gs in H; simpl in H.
      
      Lemma sh_gl_heap_hplus (h1 h2 : simple_heap) :
        sh_gl_heap h1 h2 = hplus (as_sheap h1) (as_npgheap h2).
      Proof.
        extensionality l; destruct l; unfold hplus; simpl; auto.
        destruct (h1 z); auto.
      Qed.

      Lemma phplus_is_gheap (h1 h2 : pheap') :
        is_gheap h1 -> is_gheap h2 -> is_gheap (phplus h1 h2).
      Proof.
        unfold is_gheap, phplus; intros; rewrite H, H0; auto.
      Qed.
        
      Hint Resolve pdisjE1 pdisjE2 sh_gh_disj phplus_is_gheap.
      lets (hrest & _ & Hdis0 & Heq0): (>> disj_tid bid Hdeq).
      assert (HdisrF : pdisj hrest hF).
      { rewrite <-Heq0 in Hdis; apply pdisjC, pdisjE2, pdisjC in Hdis; auto. }
      assert (pdisj (sh_gl_pheap shs[@bid] ghs[@bid]) (as_gheap (phplus_pheap HdisrF))).
      { apply pdisj_padd_expand; simpl; auto; split.
        apply sh_gh_disj; simpl; eauto.
        
        apply as_gheap_pdisj', pdisj_padd_expand; auto.
        rewrite Heq0; auto. }
      lets Hna: (>> Hnabort (sh_gl_heap shs[@bid] h) H0); applys Hna; auto.
      
      Lemma eq_ptoheap {loc : Type} (h : PHeap.heap loc) (ph : gen_pheap' loc) :
        ph = htop h -> ptoheap ph h.
      Proof.
        intros H l; rewrite H; unfold htop, htop'; simpl.
        destruct (h l); eauto.
      Qed.
      apply eq_ptoheap.

      Lemma htop_sh_gl_heap (h1 h2 : simple_heap) :
        htop (sh_gl_heap h1 h2) = sh_gl_pheap h1 (htop h2).
      Proof.
        apply pheap_eq; unfold sh_gl_heap, as_sheap, as_gheap, phplus, htop, htop'.
        extensionality l; destruct l as [l|l]; simpl.
        destruct (h1 l); eauto.
        destruct (h2 l); eauto.
      Qed.
      assert (pdisj ghs[@bid] (phplus hrest hF)).
      { apply pdisj_padd_expand; eauto.
        rewrite Heq0; auto. }
      rewrite sh_gl_heap_hplus in H; eauto.
      rewrite htop_sh_gl_heap; unfold sh_gl_pheap; eauto.
      Notation this := PHeap.this.
      cutrewrite (this (phplus_pheap (sh_gl_is_ph shs[@bid] ghs[@bid])) =
                  phplus (htop (as_sheap shs[@bid])) (as_gheap ghs[@bid])); auto.
      rewrite padd_assoc; eauto.
      cutrewrite (this (phplus_pheap (sh_gl_is_ph shs[@bid] (htop h))) =
                  phplus (htop (as_sheap shs[@bid])) (as_gheap (htop h))); auto.
      f_equal.
      simpl; rewrite <-phplus_as_gheap; eauto.
      f_equal.
      rewrite <-padd_assoc; eauto.
      cutrewrite (phplus gh hF = phplus_pheap Hdis) in Heq; auto.
      rewrite Heq0.
      apply ptoheap_eq in Heq; (* apply (f_equal (fun x => this x)) in Heq;  *)auto.
      
      (* Lemma hplus_assoc {loc : Type} (h1 h2 h3 : PHeap.heap loc) : *)
      (*   hplus (hplus h1 h2) h3 = hplus h1 (hplus h2 h3). *)
      (* Proof. *)
      (*   extensionality l; unfold hplus. *)
      (*   destruct (h1 l); auto. *)
      (* Qed. *)

      (* Lemma hplus_as_gheap (h1 h2 : simple_heap) : *)
      (*   hdisj h1 h2 -> *)
      (*   as_npgheap (hplus h1 h2) = hplus (as_npgheap h1) (as_gheap h2). *)
      (* Proof. *)
      (*   apply pheap_eq. *)
      (*   extensionality x; destruct x; unfold hplus; simpl; auto. *)
      (* Qed.         *)

      (* rewrite hplus_as_gheap, <-hplus_assoc in H. *)
      (* Lemma is_sheap_disj h1 h2 h3 : *)
      (*   is_sheap h1 -> is_gheap h2 -> is_gheap h3 -> *)
      (*   hdisj h2 h3 -> hdisj (hplus h1 h2) h3. *)
      (* Proof. *)
      (*   intros; intros l. *)
      (*   destruct l; specialize (H z); specialize (H0 z); specialize (H1 z). *)
      (*   unfold hplus; auto. *)
      (*   unfold hplus; rewrite H; auto. *)
      (* Qed. *)
      
      (* Lemma hdisjC {loc : Type} (h1 h2 : PHeap.heap loc) : hdisj h1 h2 -> hdisj h2 h1. *)
      (* Proof. *)
      (*   intros; intros l; specialize (H l); tauto. *)
      (* Qed. *)
      
      (* assert (Hgb_gh : is_gheap ghs[@bid]). *)
      (* { eapply disj_eq_inj; eauto using as_gh_is_gh. } *)
      
      (* apply disjeq_phplus with (i := bid) (h' := htop (as_gheap hF)) in Hdeq. *)
      (* 2: apply hdisj_pdisj. *)
      (* 2: apply as_gheap_hdisj; auto. *)
      (* destruct Hdeq as (hF' & Hdis1 & Hdis2 & Heq1 & Hdisj3). *)
      (* erewrite Vector.nth_map in Heq1; [|reflexivity]. *)
      (* assert (exists hhF', hF' = htop hhF') as [hhF' HF']; subst. *)
      (* { eapply htop_phplus_heap. *)
      (*   erewrite Vector.nth_map in Hdis1; [|reflexivity..]. *)
      (*   apply Hdis1. *)
      (*   apply Heq1. } *)
      (* rewrite <-hplus_phplus in Heq1; simpl in Heq1; auto. *)
      (* rewrite <-heap_pheap_eq in Heq1. *)
      (* rewrite <-Heq1 in H.  *)
      Infix "|+|" := hplus (at level 40, left associativity).
      (* assert (as_sheap (sh_hp gs)[@bid] |+| (ghs[@bid] |+| hhF') |+| as_gheap hF = *)
      (*         hplus (hplus (as_sheap (sh_hp gs)[@bid]) ghs[@bid]) (hplus hhF' (as_gheap hF))). *)
      (* { rewrite !hplus_assoc; auto. } *)
      (* rewrite H0 in H; apply Hnabort in H; auto. *)
      (* erewrite Vector.nth_map in Hdisj3; [|reflexivity]. *)
      (* rewrite <-hplus_phplus in Hdisj3. *)

      (* Lemma hplus_is_gheapC (h1 h2 h : heap) : *)
      (*   is_gheap h2 -> h1 |+| h = h2 -> is_gheap h. *)
      (* Proof. *)
      (*   unfold is_gheap; intros. *)
      (*   apply (f_equal (fun f => f (SLoc x))) in H0; unfold hplus in H0; simpl. *)
      (*   specialize (H x). *)
      (*   destruct (h1 (SLoc x)), (h2 (SLoc x)); try rewrite H in *; try congruence. *)
      (* Qed. *)
      
      (* apply is_sheap_disj; auto using as_sh_is_sh, as_gh_is_gh. *)
      (* apply hplus_is_gheap; auto using as_sh_is_sh, as_gh_is_gh. *)
      (* apply hplus_is_gheapC in Heq1; auto using as_gh_is_gh. *)
      (* apply hdisj_pdisj; auto. *)
      (* apply hdisj_pdisj; auto. *)
      (* apply hdisj_pdisj; auto. *)
      (* erewrite Vector.nth_map in Hdis1; [|reflexivity]. *)
      (* auto. *)
      
    - intros Hbdiv; destruct Hbdiv as [bid Hbdiv].
      destruct (Hsafe bid) as (_ & _ & Hbdivi & _).
      
      Definition emp_h : heap := fun x => None.
      Lemma emp_h_unit_r (h : heap) : h |+| emp_h = h.
      Proof.
        unfold hplus;  extensionality x; destruct (h x); auto.
      Qed.
      Lemma emp_h_disj (h : heap) : hdisj h emp_h.
      Proof.
        unfold hdisj; intros; destruct (h x); auto.
      Qed.
      eapply bdiv_weaken in Hbdiv; eauto.
      (* specialize (Hbdivi emp_h); rewrite emp_h_unit_r in Hbdivi; auto; apply Hbdivi in Hbdiv; *)
      (* auto using emp_h_disj. *)

    - intros gs' hF h Hdis Heq Hred.
      inversion Hred; subst; simpl; clear Hred.
      rename H into Hred; rename H0 into Hheq.
      unfold bs_of_gs in Hred; simpl in Hred.
      rewrite sh_gl_heap_hplus in Hred.
      lets (hb & _ & Hdisr & Heqr): (>>disj_tid bid Hdeq).
      (* assert (exists hb, gh = phplus ghs[@bid] hb /\ *)
      (*                    pdisj ghs[@bid] hb) as (hb & Hhb & Hdishb). *)
      (* { apply (disj_tid bid) in Hdeq as (hb & ? & ? & ?). *)
      (*   erewrite Vector.nth_map in H1, H0; [|reflexivity..]. *)
      (*   assert (exists hb', hb = htop hb') as (hb' & ?); subst. *)
      (*   { simpl in H1; apply htop_phplus_heap in H1; auto. } *)
      (*   rewrite <-hdisj_pdisj in H0. *)
      (*   rewrite <-hplus_phplus in H1; simpl in H1; auto. *)
      (*   rewrite <-heap_pheap_eq in H1. *)
      (*   exists hb'; split; auto. } *)
      destruct (Hsafe bid) as (_ & _ & _ & _ & Hsafei).
      assert (HdisbF : pdisj hb hF).
      { rewrite <-Heqr in Hdis; apply pdisjC, pdisjE2, pdisjC in Hdis; eauto. }
      
      lets (ph'' & Hdis'' & Heq'' & Hsafe''): (>> Hsafei (phplus_pheap (as_gheap_pdisj _ _ HdisbF)) Hred).
      (* disjointness *)
      { apply pdisj_padd_expand; (try now simpl; eauto); split; try now simpl; eauto.
        (* apply sh_gh_disj; eauto. *)
        (* apply phplus_is_gheap; eauto. *)
        (* apply phplus_is_gheap; eauto. *)

        apply pdisj_padd_expand; eauto.
        simpl; rewrite <-phplus_as_gheap, Heqr; eauto.
        (* apply as_gheap_pdisj; eauto. *) }
      (* equality: sh_gl_pheap shs[@bid] ghs[@bid] |+|p (hb |+| hF) = shs[@bid] |+| h *)
      { apply eq_ptoheap.
        unfold sh_gl_pheap; simpl.
        (* cutrewrite (this (phplus_pheap (sh_gl_is_ph shs[@bid] ghs[@bid])) = *)
        (*             phplus (htop (as_sheap shs[@bid])) (as_gheap ghs[@bid])); auto. *)
        rewrite padd_assoc; eauto.
        Lemma htop_as_npgheap h:
          htop' (as_npgheap h) = as_gheap (htop h).
        Proof.
          extensionality l; destruct l as [l | l]; unfold htop', as_npgheap, as_gheap';
          eauto.
        Qed.
        assert (hdisj (as_sheap shs[@bid]) (as_npgheap h)).
        { apply hdisj_pdisj; simpl.
          rewrite htop_as_npgheap.
          apply sh_gl_is_ph. }
        rewrite (htop_hplus' _ _ H); eauto.
        simpl; f_equal.
        (* cutrewrite (phplus gh hF = phplus_pheap Hdis) in Heq; auto. *)
        apply ptoheap_eq in Heq; (* apply (f_equal (fun x => this x)) in Heq;  *)simpl in Heq.
        rewrite <-Heqr in Heq.
        rewrite htop_as_npgheap; eauto.
        rewrite <-!phplus_as_gheap; simpl; f_equal; eauto.
        rewrite <-padd_assoc; eauto.

        (* 残り *)
        (* apply pdisj_padd_expand; eauto. *)
        (* rewrite Heqr; eauto. *)
        (* apply pdisj_padd_expand; eauto. *)
        (* rewrite Heqr; eauto. *)
        (* apply sh_gh_disj; eauto. *)
        (* repeat apply phplus_is_gheap; eauto. *)
        (* simpl. *)
        (* rewrite <-phplus_as_gheap; eauto. *)
        (* cutrewrite (phplus hb hF = phplus_pheap HdisbF); auto. *)
        (* apply as_gheap_pdisj. *)
        (* apply pdisj_padd_expand; eauto. *)
        (* rewrite Heqr; eauto. *) }
      
      (* assert (Heq : as_sheap shs[@bid] |+| as_npgheap h = *)
      (*               (as_sheap (sh_hp gs)[@bid] |+| ghs[@bid]) |+| (hb |+| as_gheap hF)). *)
      (* { rewrite hplus_as_gheap, Hhb, !hplus_assoc; auto. } *)
      (* rewrite Heq in Hred; clear Heq. *)
      
      (* assert (hdisj (as_sheap (sh_hp gs)[@bid] |+| ghs[@bid]) (hb |+| as_gheap hF)). *)
      (* { apply is_sheap_disj; auto using as_sh_is_sh, as_gh_is_gh. *)
      (*   eapply disj_eq_inj; eauto using as_sh_is_sh, as_gh_is_gh. *)
      (*   apply hplus_is_gheap; auto using as_gh_is_gh. *)
      (*   symmetry in Hhb; apply hplus_is_gheapC in Hhb; auto. *)
      (*   (* eapply disj_eq_inj; eauto using as_gh_is_gh. *) *)
      (*   apply as_gh_is_gh. *)
        
        Lemma hdisj_hplus_comm {loc : Type} (h1 h2 h3 : PHeap.heap loc) :
          hdisj h1 h2 -> 
          hdisj (h1 |+| h2) h3 -> hdisj h1 (h2 |+| h3).
        Proof.
          unfold hdisj; intros H H1 l.
          specialize (H l); specialize (H1 l); unfold hplus in *;
          destruct (h1 l), (h2 l), (h3 l); try now (destruct H, H1; auto; congruence).
        Qed.
        
        (* apply hdisj_hplus_comm; eauto; rewrite <-Hhb; apply as_gheap_hdisj; eauto. } *)
      (* prove n-safety of bid-th thread*)
      
      Ltac dup H name := let P := type of H in assert (name : P) by auto.
      (* pose proof Hred as Hred'. *)
      (* eapply Hsafei in Hred' as (h' & Hdis' & Heq' & Hsafeb); eauto. *)
      assert (Heq0 : gh' = hplus (as_sheap sh'') (as_npgheap gh'')).
      { rewrite sh_gl_heap_hplus in Hheq; extensionality l; auto. }
      rewrite Heq0 in Heq''; clear Heq0.

      Definition is_psheap (h : pheap') : Prop :=
        forall l, h (GLoc l) = None.
      
      Lemma sh_gl_decomp (h : pheap) :
        exists (hs hg : pheap),
          {Hdis : pdisj hs hg | h = phplus_pheap Hdis /\ is_psheap hs /\ is_gheap hg}.
      Proof.
        set (hs := (fun l => match l with SLoc _ => this h l | _ => None end)).
        assert (is_pheap hs).
        { intros [l | l]; specialize (is_p h (SLoc l)); intros; unfold hs; eauto. }
        set (hg := (fun l => match l with GLoc _ => this h l | _ => None end)).
        assert (is_pheap hg).
        { intros [l | l]; specialize (is_p h (GLoc l)); intros; unfold hg; eauto. }
        exists (Pheap H) (Pheap H0); repeat split; simpl in *.
        assert (pdisj hs hg).
        { intros [l | l]; simpl; eauto.
          destruct (this h (SLoc l)) as [[? ?] | ]; eauto. }
        exists H1; repeat split; simpl in *.
        destruct h as [h ?]; apply pheap_eq; extensionality l; destruct l; unfold phplus; simpl; auto.
        destruct (h (SLoc z)) as [[? ?]|]; auto.
      Qed.

      destruct (sh_gl_decomp ph'') as (sph'' & gph'' & (? & Heqph'' & Hiss & Hisg)); subst.
      simpl in Heq''. rewrite !padd_assoc in Heq''. 
     
      Lemma sh_gl_eq (hs1 hs2 hg1 hg2 : pheap') :
        is_psheap hs1 -> is_psheap hs2 -> is_gheap hg1 -> is_gheap hg2 ->
        phplus hs1 hg1 = phplus hs2 hg2 -> hs1 = hs2 /\ hg1 = hg2.
      Proof.
        intros Hs1 Hs2 Hg1 Hg2 Heq; split; extensionality l; apply (f_equal (fun f => f l)) in Heq;
        destruct l as [l | l]; repeat match goal with [H : _ |- _ ] => specialize (H l) end;
        unfold phplus in *;
        repeat match goal with [H : context [match ?X with _ => _ end] |- _] => destruct X end;
        try congruence.
      Qed.
      apply ptoheap_eq in Heq''; simpl in Heq''.
      rewrite htop_hplus', htop_as_npgheap in Heq''; eauto.

      2: intros [l | l]; unfold as_sheap, as_npgheap; first [now left; eauto | now right; eauto].

      assert (phplus gph'' (phplus (as_gheap' hb) (as_gheap' hF)) = as_gheap (htop gh'')).
      { apply sh_gl_eq in Heq''; auto.
        tauto.
        intros l; cbv; simpl; eauto.
        simpl; eauto.
        (* repeat apply phplus_is_gheap; eauto. *)
        
        (* assert (is_gheap ghs[@bid]). *)
        (* { eapply disj_eq_inj; eauto using as_gh_is_gh. } *)
        (* symmetry in Hhb; apply hplus_is_gheapC in Hhb; auto using as_gh_is_gh. *)
        (* apply as_gh_is_gh. *) }
      rewrite <-padd_assoc in H.
      
      Lemma is_gheap_as_gheap (h : pheap) :
        is_gheap h -> exists h', h = as_gheap h'.
      Proof.
        set (h' := fun l => this h (GLoc l)).
        assert (is_pheap h').
        { unfold h'; intros l; specialize (is_p h (GLoc l)); eauto. }
        intros; exists (Pheap H); simpl; destruct h as [h ?]; apply pheap_eq; extensionality l.
        destruct l as [l | l]; specialize (H0 l); simpl; auto.
      Qed.
      
      apply is_gheap_as_gheap in Hisg as [hg'' ?]; subst.
      simpl in H. rewrite <-!phplus_as_gheap in H; eauto.
      (* assert (Hb : is_gheap hb). *)
      (* { symmetry in Hhb; apply hplus_is_gheapC in Hhb; auto using as_gh_is_gh. } *)
      (* apply is_gheap_as_gheap in Hb as [hb'' ?]; subst. *)
      (* rewrite <-!hplus_as_gheap in H0. *)
      
      Lemma as_gheap_inj h1 h2  : 
        as_gheap' h1 = as_gheap' h2 -> h1 = h2.
      Proof.
        intros; (* destruct h1 as [h1 ?], h2 as [h2 ?]; apply pheap_eq;  *)
        extensionality l.
        apply (f_equal (fun f => f (GLoc l))) in H; auto.
      Qed.
      
      apply as_gheap_inj in H.
      assert (pdisj hg'' hb).
      { cutrewrite (this (phplus_pheap (as_gheap_pdisj hb hF HdisbF)) =
                    phplus (as_gheap hb) (as_gheap hF)) in Hdis''; auto.
        apply pdisjE1 in Hdis''; eauto.
        cutrewrite (this (phplus_pheap x) = phplus sph'' (as_gheap hg'')) in Hdis''; auto.
        apply pdisjC, pdisjE2, pdisjC in Hdis''; auto.
        intros l; specialize (Hdis'' (GLoc l)); unfold as_gheap in Hdis''; eauto. }
      exists (phplus_pheap H0); repeat split; auto.

      { Lemma hdisjE1 {loc : Type} (h1 h2 h3 : PHeap.heap loc) : hdisj (h1 |+| h2) h3 -> hdisj h1 h3.
        Proof.
          unfold hdisj, hplus; intros H l; specialize (H l).
          destruct (h1 l), (h3 l); simpl in *; try congruence; auto.
        Qed.

        Lemma hdisjE2 {loc : Type} (h1 h2 h3 : PHeap.heap loc) : hdisj (h1 |+| h2) h3 -> hdisj h2 h3.
        Proof.
          unfold hdisj, hplus; intros H l; specialize (H l).
          destruct (h1 l), (h2 l), (h3 l); simpl in *; try congruence; auto.
          destruct H; congruence.
        Qed.
        apply pdisj_padd_expand; eauto; split; eauto.
        cutrewrite (this (phplus_pheap x) = phplus sph'' (as_gheap hg'')) in Hdis''; auto.
        apply pdisjC, pdisjE2, pdisjC in Hdis''; auto.

        Lemma pdisj_as_gheap h1 h2 :
          pdisj (as_gheap' h1) (as_gheap' h2) -> pdisj h1 h2.
        Proof.
          intros H l; specialize (H (GLoc l)); eauto.
        Qed.
        
        simpl in Hdis''; rewrite <-phplus_as_gheap in Hdis''; apply pdisj_as_gheap in Hdis''; auto. }

        (* Lemma hdisj_hplus_comm' {loc : Type} (h1 h2 h3 : PHeap.heap loc) : *)
        (*   hdisj h2 h3 ->  *)
        (*   hdisj h1 (h2 |+| h3) -> hdisj (h1 |+| h2) h3. *)
        (* Proof. *)
        (*   unfold hdisj; intros H H1  l. *)
        (*   specialize (H l); specialize (H1 l); unfold hplus in *; *)
        (*   destruct (h1 l), (h2 l), (h3 l); try now (destruct H, H1; auto; congruence). *)
        (* Qed. *)

        (* apply hdisj_hplus_comm'; eauto. *)
        (* assert (exists ghb, ghs[@bid] = as_gheap ghb) as [ghb Heq]. *)
        (* { assert (is_gheap ghs[@bid]). *)
        (*   { eapply disj_eq_inj; eauto using as_gh_is_gh. } *)
        (*   apply is_gheap_as_gheap; auto. } *)
        (* rewrite Heq, <-hplus_as_gheap in Hhb; clear Heq; apply as_gheap_inj in Hhb. *)
        (* rewrite Hhb in Hdis; eauto using hdisjE2. } *)
      { apply eq_ptoheap; simpl; eauto. }
      applys (>> IHn (replace ghs bid hg'') sdec Qs); simpl; eauto.
      + Lemma disj_eq_update {n : nat} (hs : Vector.t zpheap n) (h h' hi : zpheap) (i : Fin.t n)
              (Hdis1 : pdisj hs[@i] h') (Hdis2 : pdisj hi h') :
          disj_eq hs h ->
          h = phplus_pheap Hdis1 ->
          disj_eq (replace hs i hi) (phplus_pheap Hdis2).
        Proof.
          intros Hdeq Heq.
          assert (disj_eq (replace hs i (emp_ph Z)) h').
          { apply (disj_tid i) in Hdeq as (h'' & Hdeq' & Hdis & Heq'); subst.
            simpl in Heq'. apply padd_cancel in Heq'; eauto; subst; auto. }
          apply (disj_upd (hq := hi)) in H; auto.
          destruct H as (? & ? & ?); subst; eauto.
          assert (x = phplus_pheap Hdis2); subst; eauto.
          destruct x; apply pheap_eq; eauto.
        Qed.
        applys (>> (@disj_eq_update)); eauto.
        destruct gh; apply pheap_eq; eauto.
        (* rewrite map_replace. *)
        (* assert (Hd : hdisj (as_gheap hg'') (as_gheap hb'')). *)
        (* { eauto using hdisjE2, hdisjC, hdisjE1. } *)
        (* rewrite hplus_as_gheap, (htop_hplus _ _ Hd). *)
        (* assert (pdisj (Vector.map (@htop loc) ghs)[@bid] (htop (as_gheap hb''))). *)
        (* { erewrite nth_map; [|reflexivity]; apply hdisj_pdisj; eauto. } *)
        (* eapply (disj_eq_update _ _ _ _ _ H1); eauto. *)
        (* apply pheap_eq; erewrite nth_map; [|reflexivity]. *)
        (* rewrite <-hplus_phplus, <-heap_pheap_eq; eauto. *)

      + intros bid'; rewrite !replace_nth; destruct fin_eq_dec; subst; eauto.
        * cutrewrite (sh_gl_pheap sh'' hg'' = phplus_pheap x); auto.
          unfold sh_gl_pheap; apply pheap_eq; f_equal.
          apply sh_gl_eq in Heq''; simpl; jauto.
          intros l; unfold htop'; simpl; auto.
        * Lemma safe_nk_weak ntrd' E' n (ks : klist ntrd') h Q m :
            (m <= n)%nat ->
            safe_nk E' n ks h Q -> safe_nk E' m ks h Q.
          Proof.
            revert ks h n; induction m; simpl in *; eauto; intros.
            destruct n; simpl in *; eauto; intuition; try omega; repeat split; simpl in *; eauto; intros.
            specialize (H5 hF h' h0 ks' H4 H6 H7).
            destruct H5 as (h'' & ? & ? & ?); exists h''; repeat split; eauto.
            eapply IHm; [|apply H9]; try omega.
          Qed.

          eapply safe_nk_weak; [|apply Hsafe]; try omega.

      + intros; rewrite !replace_nth; destruct fin_eq_dec; eauto. 

        Definition dom_eqp (h1 h2 : pheap') :=
          forall (l : loc) p,
            (exists v, h1 l = Some (p, v)) <->
            (exists v, h2 l = Some (p, v)).
        Definition dom_eq (h1 h2 : heap) :=
          dom_eqp (htop h1) (htop h2).
        
        Lemma sh_presrvd C1 C2 st1 st2 :
          ~aborts C1 st1 ->
          C1 / st1 ==>s C2 / st2 ->
          dom_eq (snd st1) (snd st2).
        Proof.
          unfold dom_eq, dom_eqp, htop, htop', full_p in *; simpl in *.
          intros Hna H; induction H; intros; (try now apply IHred; eauto);
          split; intros; subst; eauto; try congruence.
          - apply IHred; auto; intros Ha; apply Hna; constructor; eauto.
          - apply IHred; auto; intros Ha; apply Hna; constructor; eauto.
          - unfold upd; simpl; destruct (eq_dec l (ledenot e1 s)); eauto; try congruence.
            destruct H; simpl in H; destruct (h l); inversion H; subst; eexists; eauto.
          - unfold upd in *; simpl in *; destruct (eq_dec l (ledenot e1 s)); eauto; try congruence.
            destruct H; simpl in H; destruct (h l) eqn:Heq; [inversion H; subst; eexists; eauto|].
            elimtype False; apply Hna; constructor; subst; eauto.
        Qed.

        Lemma pts_dom_eq (h1 h2 : pheap) stk e1 e2 :
          dom_eqp h1 h2 ->
          (e1 -->p (1, e2)) stk h1 ->
          (Ex v : Z, e1 -->p (1, v)) stk h2.
        Proof.
          intros H Hsat; unfold_conn_all; simpl in *.
          assert (exists v, this h1 (ledenot e1 stk) = Some (1, v)) as Hv1.
          { specialize (Hsat (ledenot e1 stk)); destruct (this h1 (ledenot e1 stk)).
            destruct (eq_dec (ledenot e1 stk) (ledenot e1 stk)); try congruence.
            eexists; eauto.
            destruct (eq_dec (ledenot e1 stk) (ledenot e1 stk)); try congruence. }
          assert (exists v, this h2 (ledenot e1 stk) = Some (1, v)) as [v2 Hv2].
          { apply H in Hv1; eauto. }
          Require Import NPeano.
          exists v2%Z; intros.
          unfold htop, htop'; simpl.
          destruct (eq_dec x (ledenot _ _)); subst; eauto.
          - assert (Heq : this h2 x = None); [|rewrite Heq; simpl; eauto].
            specialize (Hsat x); destruct (eq_dec x (ledenot _ _)); try congruence.
            assert (this h1 x = None) by (unfold htop' in *; destruct (this h1 x); try congruence).
            specialize (H x); unfold dom_eq, dom_eqp, htop, htop' in *; simpl in *.
            destruct (this h1 x) as [[? ?]|], (this h2 x) as [[? ?]|]; try congruence.
            specialize (H q); destruct H.
            exploit H1; [eauto|intros [v ?]; congruence].
        Qed.

        Lemma dom_eq_phplus (h1 h2 h h' : pheap) :
          pdisj h1 h2 -> phplus h1 h2 = h -> dom_eqp h h' ->
          exists (h1' h2' : pheap), pdisj h1' h2' /\ phplus h1' h2' = h' /\
                                    dom_eqp h1 h1' /\ dom_eqp h2 h2'.
        Proof.
          intros Hdis Heq Hdomeq.
          set (h1' := fun x => match this h1 x with
                                 | Some (p, _) => match this h' x with
                                                    | Some (_, x) => Some (p, x)
                                                    | None => None
                                                  end
                                 | None => None
                               end).
          assert (Hisp1 : is_pheap h1').
          { intros l; unfold h1'; destruct h1 as [h1 H1]; destruct (h1 l) as [[? ?]|];
            destruct h' as [h' H]; simpl in *; pose proof (H l); pose proof (H1 l);
            destruct (h' l) as [[? ?]|], (h1 l) as [[? ?]|]; eauto. }
          set (h2' := fun x => match this h2 x with
                                 | Some (p, _) => match this h' x with
                                                    | Some (_, x) => Some (p, x)
                                                    | None => None
                                                  end
                                 | None => None
                               end).
          assert (Hisp2 : is_pheap h2').
          { intros l; unfold h2'; destruct h2 as [h2 H1]; destruct (h2 l) as [[? ?]|];
            destruct h' as [h' H]; simpl in *; pose proof (H l); pose proof (H1 l);
            destruct (h' l) as [[? ?]|], (h2 l) as [[? ?]|]; eauto. }
          exists (Pheap Hisp1) (Pheap Hisp2); simpl.
          split.
          { unfold h1', h2'; intros l; specialize (Hdis l).
            destruct (this h1 l) as [[? ?]|], (this h2 l) as [[? ?]|], (this h' l) as [[? ?]|]; eauto.
            repeat split; tauto. }
          split.
          { unfold h1', h2'; extensionality l; unfold phplus in *.
            apply (f_equal (fun f => f l)) in Heq.
            specialize (Hdomeq l).
            destruct (this h1 l) as [[? ?]|], (this h2 l) as [[? ?]|],
                     (this h' l) as [[? ?]|] eqn:Heq'; eauto.
            - destruct (Hdomeq (q + q0)); exploit H; [eexists; eauto|].
              intros [? ?]; congruence.
            - destruct (Hdomeq q); exploit H; [eexists; eauto|].
              intros [? ?]; congruence.
            - destruct (Hdomeq q); exploit H; [eexists; eauto|].
              intros [? ?]; congruence.
            - rewrite <-Heq in Hdomeq; destruct (Hdomeq q) as [? H']; exploit H'; eauto.
              intros [? ?]; congruence. }
          unfold dom_eqp; split; intros; unfold h1', h2'; simpl; 
          apply (f_equal (fun f => f l)) in Heq; unfold phplus in Heq; simpl in Heq;
          specialize (Hdomeq l);
          destruct (this h1 l) as [[? ?]|]; destruct (this h2 l) as [[? ?]|];
          split; intros [? H]; destruct (this h' l) as [[? ?]|]; inversion H;
          (try now (eexists; eauto)); rewrite <-Heq in *.
          - destruct (Hdomeq (q + q0)) as [Hx ?]; exploit Hx; [eexists; eauto|].
            intros [? ?]; congruence.
          - destruct (Hdomeq q) as [Hx ?]; exploit Hx; [eexists; eauto|].
            intros [? ?]; congruence.
          - destruct (Hdomeq (q + q0)) as [Hx ?]; exploit Hx; [eexists; eauto|].
            intros [? ?]; congruence.
          - destruct (Hdomeq q) as [Hx ?]; exploit Hx; [eexists; eauto|].
            intros [? ?]; congruence.
        Qed.
          
        Lemma is_arr_dom_eq stk e n f : forall (h1 h2 : pheap) s,
          dom_eqp h1 h2 ->
          (is_array e n f s) stk h1 ->
          (Ex f, is_array e n f s) stk h2.
        Proof.
          unfold dom_eq.
          induction n; simpl; intros.
          - unfold_conn_all; (exists (fun _:nat => 0%Z)); intros x.
            unfold dom_eqp, dom_eq, htop, htop' in *; simpl in *.
            specialize (H x); destruct (this h2 x) as [[? ?]|]; auto.
            specialize (H0 x); destruct (this h1 x) as [[? ?]|]; try tauto; try congruence.
            destruct (H q) as [? Hx]; exploit Hx; eauto; intros [? ?]; congruence.
          - destruct H0 as (ph1 & ph2 & ? & ? & ? & ?).
            lets (h1' & h2' & Hdis' & Heq' & Heq1' & Heq2'): (>> dom_eq_phplus H2 H3 H).
            lets (v & Hsat1): (>> pts_dom_eq Heq1' H0).
            lets (f' & Hsat2): (>> IHn Heq2' H1).
            exists (fun n => if Nat.eq_dec n s then v else f' n); simpl.
            exists h1' h2'; repeat split; eauto.
            destruct Nat.eq_dec; try congruence; eauto.
            Close Scope Qc_scope.
            Lemma is_array_change (e : loc_exp) (f1 f2 : nat -> Z) n :
              forall s, (forall x, x < n -> f1 (x + s) = f2(x + s)) ->
              forall stc,
                stc ||= is_array e n f1 s <=> is_array e n f2 s.
            Proof.
              induction n; simpl; intros s Hf; try reflexivity.
              intros stc; rewrite IHn.
              cutrewrite (f1 s = f2 s); [reflexivity|].
              pose proof (Hf 0); rewrite plus_O_n in H; rewrite H; omega.
              intros x Hx; rewrite <-Nat.add_succ_comm; apply Hf; omega.
            Qed.
            eapply is_array_change; [|exact Hsat2].
            intros x Hxn; destruct Nat.eq_dec; omega.
        Qed.

        Lemma shspec_dom_eq stk sdec : forall (h1 h2 : pheap),
          dom_eqp h1 h2 ->
          (sh_spec sdec) stk h1 ->
          (sh_spec sdec) stk h2.
        Proof.
          induction sdec as [|[var len] sdec]; simpl; intros h1 h2 Heqb Hsat.
          - unfold_conn_all; unfold dom_eqp in *; intros l; specialize (Hsat l); specialize (Heqb l).
            destruct (this h1 l) as [[? ?]|], (this h2 l) as [[? ?]|]; try congruence.
            destruct (Heqb q) as [_ H]; exploit H; [eauto | intros [? ?]; congruence].
          - destruct Hsat as (ph1 & ph2 & ? & ? & ? & ?).
            lets (ph1' & ph2' & Hdis' & Heq' & Heq1' & Heq2'): (>> dom_eq_phplus H1 H2 Heqb).
            destruct H as (f & H).
            lets Hsat':(>> is_arr_dom_eq Heq1' H).
            exists ph1' ph2'; repeat split; eauto.
        Qed.
          
        Lemma sh_presrvd_b {n : nat} (ks1 ks2 : klist n) h1 h2 :
          ~abort_k (ks1, h1) ->
          (ks1, h1) ==>k (ks2, h2) ->
          dom_eq h1 h2.
        Proof.
          intros Hna Hred; inversion Hred; subst.
          - apply sh_presrvd in H3; simpl in *.
            inversion H1; eauto.
            intros Hc; apply Hna; exists i; simpl in *.
            inversion H1; subst; destruct ss[@i]; inversion H2; eauto.
          - inversion H; inversion H0; unfold dom_eq; intros; split; eauto.
        Qed.

        (* assert (Heq : gh' = as_sheap sh'' |+| as_gheap gh''). *)
        (* { rewrite sh_gl_heap_hplus in *; extensionality l; rewrite Hheq; eauto. } *)
        (* rewrite Heq in Hred. *)

        lets Hdomeq: (>> (@sh_presrvd_b ntrd) Hred).
        { destruct (Hsafe bid) as (_ & Hnaborts & _).
          assert (pdisj (sh_gl_pheap shs[@bid] ghs[@bid]) (as_gheap (phplus_pheap HdisbF))).
          { apply pdisj_padd_expand; simpl; auto; split.
            apply sh_gh_disj; simpl; eauto.
            apply as_gheap_pdisj', pdisj_padd_expand; auto.
            rewrite Heqr; auto. }
          applys (>> Hnaborts H1); auto.
          apply eq_ptoheap; simpl; rewrite htop_hplus'; eauto.
          rewrite padd_assoc; f_equal.
          rewrite <-!phplus_as_gheap, htop_as_npgheap; f_equal.
          rewrite <-padd_assoc, Heqr; simpl.
          apply ptoheap_eq in Heq; rewrite Heq; simpl; auto.

          intros [l | l]; unfold as_sheap, as_npgheap; auto. }
        
        (* assert (pdisj ghs[@bid] (phplus hrest hF)). *)
        (* { apply pdisj_padd_expand; eauto. *)
        (*   rewrite Heq0; auto. } *)
        (* rewrite sh_gl_heap_hplus in H; eauto. *)
        (* rewrite htop_sh_gl_heap; unfold sh_gl_pheap; eauto. *)
        
        (* eapply Hnaborts. *)
        (* apply (Hnaborts (as_gheap hb'' |+| as_gheap hF)); eauto. *)
        (* assert (exists ghb, ghs[@bid] = as_gheap ghb) as [ghb Heq'']. *)
        (* { assert (is_gheap ghs[@bid]). *)
        (*   { eapply disj_eq_inj; eauto using as_gh_is_gh. } *)
        (*   apply is_gheap_as_gheap; auto. } *)
        (* rewrite Heq'' in Hdomeq. *)
        unfold dom_eq in Hdomeq.
        assert (hdisj (as_sheap shs[@bid]) (as_npgheap h)).
        { intros [l | l]; unfold as_sheap, as_npgheap; eauto. }

        Lemma hdisj_as_sh_as_gh h1 h2 : hdisj (as_sheap h1) (as_npgheap h2).
        Proof.
          intros [l | l]; eauto.
        Qed.
        Hint Resolve hdisj_as_sh_as_gh.
        simpl in Hdomeq; rewrite htop_hplus' in Hdomeq; eauto.
        assert (gh' = sh_gl_heap sh'' gh''); [|subst gh'].
        { extensionality l; destruct l as [l | l]; unfold htop'; rewrite Hheq; auto. }

        rewrite sh_gl_heap_hplus, htop_hplus' in Hdomeq; eauto.
        rewrite <-!htop_hplus' in Hdomeq; eauto.

        Lemma dom_eq_sh_gh sh1 sh2 gh1 gh2 :
          dom_eq ((as_sheap sh1) |+| (as_npgheap gh1)) ((as_sheap sh2) |+| (as_npgheap gh2)) ->
          dom_eq (as_sheap sh1) (as_sheap sh2).
        Proof.
          unfold dom_eq, dom_eqp, htop, htop', hplus, as_sheap, as_gheap; simpl; intros H; introv.
          lets~ (H1 & H2): (H l full_p); clear H.
          split; intros [v H'].
          - destruct l as [z | z]; destruct (sh1 z); try congruence.
            exploit H1; [eauto|]; destruct (sh2 z); intros [? H]; inversion H'; eauto.
          - destruct l as [z | z]; destruct (sh2 z); try congruence.
            exploit H2; [eauto|]; destruct (sh1 z); intros [? H]; inversion H'; eauto.
        Qed.

        lets Heqsh: (>> dom_eq_sh_gh Hdomeq).
        pose proof (Hsinv bid tid) as Hsinvi.

        assert (Hsat' : sh_spec sdec (snd gs[@bid][@tid]) (htop (as_sheap sh''))) 
        by (applys shspec_dom_eq; eauto).
        
        Lemma presrv_var {n : nat} (ks1 ks2 : klist n) h1 h2 P :
          (ks1, h1) ==>k (ks2, h2) ->
          (forall tid, inde P (writes_var (fst ks1[@tid]))) ->
          forall tid h, P (snd ks1[@tid]) h -> P (snd ks2[@tid]) h.
        Proof.
          intros H; dependent destruction H; intros.
          - rewrite replace_nth; destruct fin_eq_dec; subst; eauto.
            rewrite H0 in *.
            (* copied from ``CSL.v'' *)
            Lemma writes_agrees (c1 c2 : cmd) (st1 st2 : state) :
              c1 / st1 ==>s c2 / st2 ->
              fst st1 = fst st2 \/
              exists (x : var) (v : Z), In x (writes_var c1) /\ fst st2 = var_upd (fst st1) x v.
            Proof.
              induction 1; try (left; now eauto).
              - destruct IHred as [ ? | [x [ v [Hin Heq] ]] ]; [tauto | right].
                exists x v; split; eauto.
                apply in_app_iff; eauto.
              - right; exists x (edenot e s); split; [constructor | subst]; eauto.
              - right; exists x v; split; [constructor | subst]; eauto.
              - left; subst; eauto.
            Qed.

            Lemma writes_agrees' (c1 c2 : cmd) (st1 st2 : state) (h : pheap) (R : assn):
              c1 / st1 ==>s c2 / st2 ->
              inde R (writes_var c1) ->
              sat (fst st1, h) R -> sat (fst st2, h) R.
            Proof.
              intros hred hinde hsat; apply writes_agrees in hred as [heq | [x [v [Hin Heq]]]].
              - rewrite <-heq; eauto.
              - rewrite Heq; apply hinde; eauto.
            Qed.
            
            specialize (H tid); rewrite H0 in H.
            lets Hwa: (>> writes_agrees' H1 H); apply Hwa; eauto.

          - specialize (H tid); specialize (H1 tid); destructs 6 H1.
            destruct ss[@tid], ks2[@tid]; simpl; eauto.
            inverts H1; inverts * H3.
        Qed.

        applys (@presrv_var ntrd); eauto.

      + intros bid' tid; rewrite replace_nth; destruct fin_eq_dec; eauto.
        subst bid'; specialize (Hsvar bid).

        Lemma writes_inv (c1 c2 : cmd) (st1 st2 : state) :
          c1 / st1 ==>s c2 / st2 -> forall x, In x (writes_var c2) -> In x (writes_var c1).
        Proof.
          induction 1; simpl; eauto.
          - intros x H'; specialize (IHred x); apply in_app_iff. apply in_app_iff in H'; tauto.
          - intros x H; apply in_app_iff; tauto.
          - intros x H; apply in_app_iff; tauto.
          - intros x H; apply in_app_iff in H; destruct H.
            + apply in_app_iff in H; tauto.
            + inversion H.
        Qed.

        Lemma inde_inv1 (c1 c2 : cmd) (st1 st2 : state) (R : assn) :
          c1 / st1 ==>s c2 / st2 -> inde R (writes_var c1) -> inde R (writes_var c2).
        Proof.
          intros H hinde x s h v Hin; specialize (hinde x s h v). 
          lets :  (>> writes_inv H); eauto.
        Qed.

        Lemma presrv_inde {n : nat} (ks1 ks2 : klist n) h1 h2 P :
          (ks1, h1) ==>k (ks2, h2) ->
          (forall tid, inde P (writes_var (fst ks1[@tid]))) ->
          (forall tid, inde P (writes_var (fst ks2[@tid]))).
        Proof.
          intros Hred; dependent destruction Hred.
          - intros; rewrite replace_nth; destruct fin_eq_dec; eauto; subst i.
            applys inde_inv1; eauto.
            specialize (H tid); rewrite H0 in H; eauto.
          - intros.
            Lemma wait_writes (c1 c2 : cmd) (j : nat) :
              wait c1 = Some (j, c2) -> forall x, In x (writes_var c2) -> In x (writes_var c1).
            Proof.
              revert j c2; induction c1; simpl; try now inversion 1.
              intros j c2; destruct (wait c1_1) as [[? ?]|]; intros H; inversion H; inversion H2.
              simpl; intros x H'; apply in_app_iff in H'; apply in_app_iff.
              specialize (IHc1_1 n c eq_refl x); tauto.
            Qed.

            Lemma inde_inv2 (c1 c2 : cmd) (j : nat) (R : assn) :
              wait c1 = Some (j, c2) -> inde R (writes_var c1) -> inde R (writes_var c2).
              intros H hinde x s h v Hin; specialize (hinde x s h v). 
              lets: (>>wait_writes H) ; eauto.
            Qed.
            destructs 6 (H1 tid).
            specialize (H tid).
            repeat match goal with [H:_ |- _] => rewrite H in * end.
            applys inde_inv2; eauto.
        Qed.

        applys (@presrv_inde ntrd); eauto.

        Grab Existential Variables.
        eauto.
Qed.

Definition CSLg (P : assn) (prog : program) (Q : assn) :=
  forall sh gh ks, 
    (forall tid bid, decl_sh (get_sh_decl prog) (snd ks[@bid][@tid]) sh) ->
    (forall tid bid, fst ks[@bid][@tid] = get_cmd prog) ->
    (forall tid bid, snd ks[@bid][@tid] TID = zf tid) ->
    (forall tid bid, snd ks[@bid][@tid] BID = zf bid) ->
    (exists stks, forall tid bid v, v <> TID -> snd ks[@bid][@tid] v = stks[@bid] v) ->
    (exists stk,
       (forall tid bid v, v <> TID -> v <> BID -> snd ks[@bid][@tid] v = stk v) /\
       P stk (as_gheap gh)) ->
  forall n, safe_ng n ks (Vector.const sh nblk) gh Q.

Theorem rule_grid (P : assn) Ps C Qs (Q : assn) sh_decl :
  let sinv := sh_spec sh_decl in
  P |= Aistar_v Ps ->
  (forall bid,
     CSLp ntrd E (Ps[@bid] ** sinv ** !(BID === zf bid)) 
                 C 
                 (sinv ** Qs[@bid])) ->
  Aistar_v Qs |= Q ->
  inde sinv (writes_var C) ->
  (forall bid, inde Ps[@bid] (BID :: TID :: nil)) ->
  (forall bid, low_assn E Ps[@bid]) ->
  (forall bid : Fin.t nblk, has_no_vars Qs[@bid]) ->
  (forall v : var, List.In v (map fst sh_decl) -> E v = Lo) ->
  (E TID = Hi) ->
  (E BID = Lo) ->
  ~In TID (List.map fst sh_decl) ->
  ~In BID (List.map fst sh_decl) ->
  disjoint_list (List.map fst sh_decl) ->
  CSLg P (Pr sh_decl C) Q.
Proof.
  simpl; intros HP Htri HQ Hindsh Hindid Hlow Hnovar Hlo HtidHi HbidLo Htidsh Hbidsh Hdisvars; unfold CSLg; simpl.
  introv Hdec HC HTID HBID (stkb & Hstkb) (stk & Hstk & HsatP); introv.

  (* split h into heaps of each thread block *)
  apply HP in HsatP.
  lets (hs & Hdeq & Hsati): (>>aistar_disj HsatP); simpl in *.
   (* assert (exists hs', hs = Vector.map (@htop loc) hs') as [hs' Heq] by ; subst. *)
  Lemma disj_eq_as_gh' {n : nat} (hs : t pheap n) (h : zpheap) :
    disj_eq hs (as_gheap h) ->
    exists hs', hs = Vector.map as_gheap hs' /\ disj_eq hs' h.
  Proof.
    revert h; induction n; intros h; dependent destruction hs; intros H. 
    - inversion H; subst.
      exists (@Vector.nil zpheap); simpl; split; eauto.
      cutrewrite (h = emp_ph Z); try constructor.
      destruct h as [h ?]; apply pheap_eq; extensionality l; simpl in *.
      apply (f_equal (fun h => h (GLoc l))) in H0.
      unfold PHeap.emp_h, as_gheap' in *; auto.
    - remember (as_gheap h0) as h0'; inverts H.
      Lemma phplus_gheap (h1 h2 : pheap) (h3 : zpheap) :
        phplus h1 h2 = as_gheap h3 ->
        exists h1' h2', h1 = as_gheap h1' /\ h2 = as_gheap h2' /\ phplus h1' h2' = h3.
      Proof.
        intros H.
        Lemma is_gheap_phplus (h1 h2 : pheap) :
          is_gheap (phplus h1 h2) -> is_gheap h1 /\ is_gheap h2.
        Proof.
          unfold phplus; intros H; split; intros l; specialize (H l); simpl in *;
          destruct (this h1 (SLoc l)) as [[? ?]|], (this h2 (SLoc l)) as [[? ?]|]; try congruence.
        Qed.
        assert (is_gheap (phplus h1 h2)) by (rewrite H; simpl; auto).
        apply is_gheap_phplus in H0 as [? ?].
        apply is_gheap_as_gheap in H0; apply is_gheap_as_gheap in H1.
        destruct H0, H1; repeat eexists; eauto.
        subst.
        simpl in H.
        rewrite <-phplus_as_gheap in H; apply as_gheap_inj in H; auto.
      Qed.
      lets phgh : phplus_gheap; simpl in phgh; apply (f_equal (fun h => this h)) in H0; simpl in H0.
      apply phgh in H0 as (h' & ph' & ? & ? & ?); subst.
      lets (hs' & ?): (>> IHn H4); clear IHn; subst.
      exists (Vector.cons _ h' _ hs'); split.
      + apply eq_nth_iff; intros; destruct H; subst; erewrite Vector.nth_map; eauto.
        dependent destruction p2; simpl; jauto.
        erewrite Vector.nth_map; eauto.
      + destruct H; subst.
        assert (pdisj h' ph').
        { intros l; specialize (hdis (GLoc l)); unfold as_gheap, as_gheap' in hdis; simpl in *; auto. }
        cutrewrite (h0 = phplus_pheap H).
        constructor; eauto.
        destruct h0 as [h0 ?]; apply pheap_eq; eauto.
    Qed.
  lets (hs' & ? & Hdeq'): (>> (@disj_eq_as_gh') Hdeq).
  applys* safe_gl; simpl; eauto.
  - intros bid; unfold CSLp in Htri.
    assert (forall tid, fst ks[@bid][@tid] = C) by eauto.
    assert (forall tid, snd ks[@bid][@tid] TID = zf tid) by eauto.
    assert (Hlowl2 : low_eq_l2 E (Vector.map (fun s => snd s) ks[@bid])).
    { apply leq_low_eq_l2; introv Hneq; unfold low_eq; introv Hlox.
      erewrite !nth_map; [|reflexivity..].
      rewrite !Hstkb; eauto; congruence. }
    applys* (>> Htri Hlowl2).
    unfold sat_k;
    lazymatch goal with [|- context [ let (_, _) := ?X in _ ]] => destruct X as [stkr Hstkr] end; simpl.
    Require Import assertions.
    unfold low_eq in Hstkr.
    sep_split.
    { (* BID === bid *)
      unfold_conn; simpl.
      Lemma fin_gt0_inhabit {n : nat} : n <> 0 -> exists (i : Fin.t n), True.
      Proof.
        intros.
        assert (exists n', n = S n') as [n' ?]; subst.
        destruct n; [omega | eauto]. 
        exists (@Fin.F1 n'); eauto.
      Qed.
      destruct (fin_gt0_inhabit ntrd_neq_0) as [i ?].
      specialize (Hstkr i); rewrite <-Hstkr; eauto.
      erewrite nth_map; [|reflexivity]; eauto. }
    specialize (Hsati bid) (* erewrite nth_map in Hsati; [|reflexivity] *).
    assert (Ps[@bid] stkr (hs[@bid])).
    { assert (low_assn (fun v => if var_eq_dec v BID then Hi else E v) Ps[@bid]).
      { unfold low_assn, indeP; simpl.
        introv Hlow12.
        assert (Ps[@bid] s1 h <-> Ps[@bid] (var_upd s1 BID (s2 BID)) h).
        { unfold inde in Hindid; simpl in Hindid.
          apply Hindid; eauto. }
        assert (Ps[@bid] (var_upd s1 BID (s2 BID)) h <-> Ps[@bid] s2 h).
        { unfold low_assn, indeP in Hlow; simpl in Hlow.
          apply Hlow.
            intros x Hx; unfold var_upd; destruct var_eq_dec; try congruence.
            apply Hlow12; destruct var_eq_dec; subst; congruence. }
        rewrite H2, H3; split; eauto. }
      unfold low_assn, indeP in H1; simpl in H1; applys H2; eauto.
      intros x Hx; unfold var_upd; destruct var_eq_dec; try congruence.
      destruct (fin_gt0_inhabit ntrd_neq_0) as [i _].
      specialize (Hstkr i); rewrite <-Hstkr; eauto.
      specialize (Hstk i bid); rewrite <-Hstk; eauto; try congruence.
      erewrite Vector.nth_map; eauto. }
    rewrite Vector.const_nth.

    Lemma decl_sh_spec sdecs stk h :
      disjoint_list (List.map fst sdecs) ->
      decl_sh sdecs stk h ->
      sh_spec sdecs stk (htop (as_sheap h)).
    Proof.
      intros Hdisj; induction 1; simpl.
      - unfold_conn; unfold htop, htop', as_sheap; simpl; intros [|]; eauto.
      - set (ph1' := fun l =>
                       match l with
                         | SLoc l => 
                           if Z_range_dec loc l (loc + Z.of_nat len) then Some (1%Qc, 0%Z) else None
                         | GLoc _ => None
                       end).
        assert (Hph1 : is_pheap ph1').
        { intros x; unfold ph1'; destruct x as [l | l]; [destruct Z_range_dec|]; eauto.
          split; cbv; congruence. }
        set (ph1 := Pheap Hph1 : pheap).
        assert (forall l, (loc <= l < loc + Z.of_nat len)%Z -> sh l = None).
        { intros; assert (exists i, i < len /\ (l = loc + Z.of_nat i)%Z) as [i [? Heq]].
          { exists (Z.to_nat (l - loc)).
            assert (l - loc < Z.of_nat len)%Z by omega.
            split.
            - rewrite Z2Nat.inj_lt in H2; try omega.
              rewrite Nat2Z.id in H2; eauto.
            - rewrite Z2Nat.id; omega. }
          rewrite Heq, H0; eauto. }

        assert (pdisj ph1 (htop (as_sheap sh))).
        { simpl; unfold ph1', htop'; intros [l | l]; simpl; eauto.
          destruct Z_range_dec; eauto.
          rewrite H1; eauto. }
        assert (Heq : phplus ph1 (htop (as_sheap sh)) = 
                      (htop (as_sheap
                               (fun l : Z =>
                                  if Z_range_dec loc l (loc + Z.of_nat len) then Some 0%Z else sh l)))).
        { unfold phplus, htop, htop'; simpl; unfold ph1', as_sheap; extensionality l.
          destruct l as [l | l]; simpl; eauto.
          destruct Z_range_dec.
          rewrite H1; eauto.
          destruct (sh l); eauto. }
        
        exists ph1 (htop (as_sheap sh)); repeat split; eauto.
        
        Lemma is_array_inde v n f s:
          indeP (fun s1 s2 => s1 v = s2 v) (is_array (Sh v) n f s).
        Proof.
          intros s1 s2 h H; split; revert s h; induction n; simpl in *; eauto;
          intros s h (ph1 & ph2 & H1 & H2 & Hdis & Heq); exists ph1 ph2; repeat split; eauto;
          unfold_conn_all; simpl in *; [rewrite <-H | rewrite H]; eauto.
        Qed.          

        Focus 2.
        { assert (low_eq (fun v => if in_dec var_eq_dec v (map fst ds) then Lo else Hi)
                       stk (fun v' => if var_eq_dec v' v then loc else stk v')).
          { intros v' Hlo; destruct var_eq_dec; eauto.
            destruct in_dec; try congruence; subst v'.
            simpl in Hdisj; tauto. }
          applys* sh_spec_inde.
          applys* IHdecl_sh.
          simpl in Hdisj; jauto.
          simpl; intros; destruct in_dec; tauto. } Unfocus.
        exists (fun _ : nat => 0%Z).

        Lemma sh_is_array_sat v len s (stk : stack) loc :
          let h := fun l => match l with
                              | SLoc l0 => 
                                if Z_range_dec (Z.of_nat s + loc) l0 (Z.of_nat s + loc + Z.of_nat len)
                                then Some (1%Qc, 0%Z) else None
                              | GLoc _ => None end in
          forall (H: is_pheap h),
            stk v = loc ->
            is_array (Sh v) len (fun _:nat => 0%Z) s stk (Pheap H).
        Proof.
          revert s; induction len; [simpl|]; intros.
          - unfold_conn; simpl; intros [l | l]; [destruct Z_range_dec; try omega|]; eauto.
          - Arguments Z.of_nat _ : simpl never.
            simpl.
            set (ph1 := fun l => match l with
                         | SLoc l => 
                           if Z.eq_dec l (Z.of_nat s + loc) then Some (1%Qc, 0%Z) else None
                         | GLoc _ => None end).
            set (ph2 := fun l => match l with
                         | SLoc l => 
                           if Z_range_dec (Z.of_nat (S s) + loc) l (Z.of_nat (S s) + loc + Z.of_nat len)
                           then Some (1%Qc, 0%Z) else None
                         | GLoc _ => None end).
            assert (is_pheap ph1).
            { unfold ph1; intros [l|l]; [destruct Z.eq_dec|]; eauto; cbv; split; congruence. }
            assert (is_pheap ph2).
            { unfold ph2; intros [l|l]; [destruct Z_range_dec|]; eauto; cbv; split; congruence. }
            assert (pdisj ph1 ph2).
            { intros [l|l]; unfold ph1, ph2; eauto.
              destruct Z.eq_dec; [destruct Z_range_dec|]; eauto.
              rewrite Nat2Z.inj_succ in a; omega. }
            assert (h = phplus ph1 ph2).
            { unfold ph1, ph2; extensionality l; destruct l as [l | l]; eauto.
              Arguments Z.of_nat n : simpl never.
              Arguments Z.add _ _ : simpl never.
              unfold phplus; simpl; (do 2 destruct Z_range_dec); destruct Z_eq_dec; 
              rewrite !Nat2Z.inj_succ in *; try omega; eauto. }
            exists (Pheap H1) (Pheap H2); repeat split; simpl; eauto.
            unfold_conn; intros [l | l]; simpl; eauto.
            destruct Z.eq_dec, (eq_dec (SLoc _)); try congruence.
            rewrite e, H0 in n; exploit n; [f_equal; omega | tauto].
            inversion e.
            rewrite H6, H0 in n; exploit n; [f_equal; omega|tauto].
        Qed.
        eapply (sh_is_array_sat _ _ 0).
        
        destruct var_eq_dec; congruence.
    Qed.
    destruct (fin_gt0_inhabit ntrd_neq_0) as [i _].
    lets Hsh : (>> decl_sh_spec Hdisvars (Hdec i bid)).

    assert (sh_spec sh_decl stkr (htop (as_sheap sh))).
    { applys sh_spec_inde; eauto.
      unfold low_eq; intros x HElo; specialize (Hstkr i x); erewrite nth_map in Hstkr; [|reflexivity].
      apply Hstkr; eauto. }
    (* assert (is_gheap hs'[@bid]). *)
    (* { applys disj_eq_inj; eauto using as_gh_is_gh. } *)
    (* assert (pdisj (htop hs'[@bid]) (htop (as_sheap sh))). *)
    (* { rewrite <-hdisj_pdisj. *)
    (*   apply hdisjC, sh_gh_disj; eauto using as_sh_is_sh. } *)
    exists (as_gheap hs'[@bid]) (htop (as_sheap sh)); repeat split; eauto.
    + cutrewrite (as_gheap hs'[@bid] = hs[@bid]); auto.
      rewrite H; erewrite Vector.nth_map; eauto.
    + apply pdisjC, sh_gl_is_ph.
    + simpl; rewrite phplus_comm; eauto.
  - introv.
    apply decl_sh_spec; eauto.
    rewrite Vector.const_nth; eauto.
  - intros.
    rewrite HC; eauto.
Qed.

End For_List_Notation.
End GlobalCSL.
