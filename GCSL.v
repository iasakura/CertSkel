Require Export CSL.
Require Import array_dist Bdiv.
Import PHeap Lang assertion_lemmas.

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

Definition bdiv_g (gs : g_state nblk ntrd) :=
  exists bid : Fin.t nblk, 
    Bdiv.bdiv ((blks gs)[@bid], sh_gl_heap (sh_hp gs)[@bid] (gl_hp gs)).

Definition as_gheap (h : simple_heap) : heap :=
  fun x => match x with
    | SLoc x => None
    | GLoc x => h x
  end.

Definition as_sheap (h : simple_heap) : heap :=
  fun x => match x with
    | SLoc x => h x
    | GLoc x => None
  end.    

Fixpoint safe_ng (n : nat) (gs : g_state nblk ntrd) (Q : assn) :=
  match n with
    | 0 => True
    | S n =>
      ((forall (bid : Fin.t nblk) (tid : Fin.t ntrd), fst ((blks gs)[@bid][@tid]) = SKIP) ->
         Q default_stack (htop (as_gheap (gl_hp gs)))) /\
      (forall hF : simple_heap,
         hdisj (gl_hp gs) hF ->
         ~abort_g (Gs (blks gs) (sh_hp gs) (hplus (gl_hp gs) hF))) /\
      ~ bdiv_g gs /\ 
      (forall (gs' : g_state nblk ntrd) (hF : simple_heap),
         hdisj (gl_hp gs) hF ->
         red_g (Gs (blks gs) (sh_hp gs) (hplus (gl_hp gs) hF)) gs' ->
         exists h'' : simple_heap,
           hdisj h'' hF /\ (gl_hp gs') = hplus h'' hF /\
           safe_ng n (Gs (blks gs') (sh_hp gs') h'') Q)
  end.

Record program : Set := Pr {
  get_sh_decl : list (var * nat);
  get_args : list var;
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
  
  Notation TID := (Var 0).
  Notation BID := (Var 1).
  Notation nf i := (nat_of_fin i).
  Notation zf i := (Z.of_nat (nf i)).

  Definition CSLg (P : assn) (prog : program) (Q : assn) :=
    forall sh gh ks, 
      (forall tid bid, decl_sh (get_sh_decl prog) (snd ks[@bid][@tid]) sh) ->
      (forall tid bid, fst ks[@bid][@tid] = get_cmd prog) ->
      (forall tid bid, snd ks[@bid][@tid] TID = zf tid) ->
      (forall tid bid, snd ks[@bid][@tid] BID = zf bid) ->
      (exists stk,
         (forall tid bid v, v <> TID -> v <> BID -> snd ks[@bid][@tid] v = stk v) /\
         P stk (htop (as_gheap gh))) ->
    forall n, safe_ng n (Gs ks (const sh nblk) gh) Q.

  Definition has_no_vars (P : assn) : Prop := indeP (fun (_ _ : stack) => True) P.
  
  Lemma safe_gl (n : nat) :
    forall (gs : g_state nblk ntrd) (ghs : Vector.t heap nblk) (Q : assn) (sh_decl : list (var * nat) )
           (Qs : Vector.t assn nblk),
      let sinv := sh_spec sh_decl in
      disj_eq (Vector.map (@htop loc) ghs) (htop (as_gheap (gl_hp gs))) ->
      (forall bid : Fin.t nblk,
         safe_nk E n (fst (bs_of_gs gs bid))
                 (hplus (as_sheap (sh_hp gs)[@bid]) ghs[@bid]) (sinv ** Qs[@bid])) ->
      (forall bid : Fin.t nblk, has_no_vars Qs[@bid]) ->
      Aistar_v Qs |= Q -> 
      (forall bid tid, sinv (snd (blks gs)[@bid][@tid]) (htop (as_sheap (sh_hp gs)[@bid]))) ->
      (forall bid tid, inde sinv (writes_var (fst (blks gs)[@bid][@tid]))) ->
      (forall var, List.In var (List.map fst sh_decl) -> E var = Lo) ->
      safe_ng n gs Q.
  Proof.
    induction n; simpl; auto.
    intros gs ghs Q sdec Qs Hdeq Hsafe Hnov HQ Hsinv Hsvar Hslow; repeat split.
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
            destruct H as (ph1 & ph2 & ? & ? & ? & ?); exists ph1, ph2; repeat split; auto.
            destruct H as [f H]; exists f.
            clear IHsdec H1 H2; generalize dependent ph1. 
            generalize 0; induction n; simpl in *; intros st ph1 H; [apply H|].
            destruct H as (ph1' & ph2' & ? & ? & ? & ?); exists ph1', ph2'; repeat split; auto.
            unfold low_eq in Hlow; unfold_conn_all; simpl in *; intros x; rewrite <-Hlow; auto.
        Qed.

        assert ((sh_spec sdec) srep (htop (as_sheap (sh_hp gs)[@bid]))).
        { assert (exists nt, ntrd = S nt) as [nt Hnt] by (exists (ntrd - 1); omega).
          generalize dependent gs; rewrite Hnt; intros.
          apply (sh_spec_inde _ (snd (blks gs)[@bid][@Fin.F1]) _ E); auto.
          specialize (Hsrep Fin.F1); erewrite nth_map in Hsrep; [apply Hsrep|]; auto. }

        Definition is_sheap (h : heap) := forall x, h (GLoc x) = None.
        Definition is_gheap (h : heap) := forall x, h (SLoc x) = None.
        Lemma as_sh_is_sh (h : simple_heap) : is_sheap (as_sheap h).
        Proof.
          unfold is_sheap; simpl; auto.
        Qed.
        Lemma as_gh_is_gh (h : simple_heap) : is_gheap (as_gheap h).
        Proof.
          unfold is_gheap; simpl; auto.
        Qed.

        Lemma sh_gh_disj (sh gh : heap) : is_sheap sh -> is_gheap gh -> hdisj sh gh.
        Proof.
          unfold is_sheap, is_gheap; intros; intros [? | ?]; auto.
        Qed.

        Lemma htop_hplus (h1 h2 : heap) (H : hdisj h1 h2) :
          (htop (hplus h1 h2)) = phplus_pheap (proj1 (hdisj_pdisj h1 h2) H).
        Proof.
          unfold htop, htop', hplus, phplus_pheap, phplus; simpl; apply pheap_eq.
          extensionality x; specialize (H x).
          destruct (h1 x), (h2 x); try auto.
          destruct H; congruence.
        Qed.

        Require Import Program.
        
        Lemma disj_eq_inj n (hs : Vector.t heap n) :forall h,
          disj_eq (Vector.map (@htop _) hs) (htop h) ->
          is_gheap h -> forall i, is_gheap hs[@i].
        Proof.
          induction n; simpl; intros h H Hgh i.
          - inversion i.
          - dependent destruction hs; dependent destruction i; simpl in *.
            + intros l.
              inversion H; subst; simpl; auto.
              apply (f_equal (fun x => x (SLoc l))) in H4; unfold phplus, htop' in H4.
              specialize (Hgh l).
              destruct ph as [ph ?]; simpl in *.
              destruct (h (SLoc l)), (ph (SLoc l)) as [[? ?]|], (h0 (SLoc l)); congruence.
            + remember (htop h0) as hh0; inversion H; subst; simpl in *.
              apply Eqdep.EqdepTheory.inj_pair2 in H3; subst; eauto.
              apply (f_equal (fun x => this x)) in H2; simpl in H2.

              Lemma htop_phplus_heap (h1 h2 : heap) (ph : pheap) :
                pdisj (htop h1) ph ->
                phplus (htop' h1) ph = htop' h2 ->
                exists ph', ph = htop ph'.
              Proof.
                intros;exists (fun x => match PHeap.this ph x with None => None | Some (_,x) => Some x end).
                destruct ph as [ph ?]; apply pheap_eq.
                unfold phplus, htop, htop' in *; simpl in *; extensionality x;
                apply (f_equal (fun f => f x)) in H0.
                specialize (is_p x); specialize (H x).
                pose proof frac_contra1.
                destruct (ph x) as [[? ?]|], (h1 x), (h2 x); first [now auto | congruence | firstorder].
              Qed.

              pose proof (@htop_phplus_heap _ _ _ hdis H2) as [ht Hht]; subst; auto.
              eapply IHn.
              apply H4.

              intros x; apply (f_equal (fun f => f (SLoc x))) in H2; specialize (Hgh x).
              unfold phplus, htop, htop' in H2; simpl in H2.
              repeat lazymatch type of H2 with
                | context [match ?X with | Some _ => _ | None => _ end] => destruct X
                | context [let (_, _) := ?X in _] => destruct X
              end; try congruence.
        Qed.

        assert (hdisj (as_sheap (sh_hp gs)[@bid]) ghs[@bid]).
        { apply sh_gh_disj; [apply as_sh_is_sh|].
          apply disj_eq_inj with (as_gheap (gl_hp gs)); auto.
          apply as_gh_is_gh. }
        
        rewrite htop_hplus with (H :=H1) in H.

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

      eapply aistar_sat; eauto.
      intros; erewrite Vector.nth_map; [|reflexivity]; auto.

    - intros hF Hdis [bid ?].
      destruct (Hsafe bid) as (_ & Hnabort & _ & _).
      unfold bs_of_gs in H; simpl in H.
      
      Lemma sh_gl_heap_hplus (h1 h2 : simple_heap) :
        sh_gl_heap h1 h2 = hplus (as_sheap h1) (as_gheap h2).
      Proof.
        extensionality l; destruct l; unfold hplus; simpl; auto.
        destruct (h1 z); auto.
      Qed.

      rewrite sh_gl_heap_hplus in H.
      
      Lemma hplus_assoc {loc : Type} (h1 h2 h3 : PHeap.heap loc) :
        hplus (hplus h1 h2) h3 = hplus h1 (hplus h2 h3).
      Proof.
        extensionality l; unfold hplus.
        destruct (h1 l); auto.
      Qed.

      Lemma hplus_as_gheap (h1 h2 : simple_heap) :
        as_gheap (hplus h1 h2) = hplus (as_gheap h1) (as_gheap h2).
      Proof.
        extensionality x; destruct x; unfold hplus; simpl; auto.
      Qed.        

      rewrite hplus_as_gheap, <-hplus_assoc in H.
      Lemma is_sheap_disj h1 h2 h3 :
        is_sheap h1 -> is_gheap h2 -> is_gheap h3 ->
        hdisj h2 h3 -> hdisj (hplus h1 h2) h3.
      Proof.
        intros; intros l.
        destruct l; specialize (H z); specialize (H0 z); specialize (H1 z).
        unfold hplus; auto.
        unfold hplus; rewrite H; auto.
      Qed.

      Lemma as_gheap_hdisj (h1 h2 : simple_heap) :
        hdisj h1 h2 -> hdisj (as_gheap h1) (as_gheap h2).
      Proof.
        intros; intros [l | l]; simpl; auto.
      Qed.
      
      Lemma hdisjC {loc : Type} (h1 h2 : PHeap.heap loc) : hdisj h1 h2 -> hdisj h2 h1.
      Proof.
        intros; intros l; specialize (H l); tauto.
      Qed.
      
      assert (Hgb_gh : is_gheap ghs[@bid]).
      { eapply disj_eq_inj; eauto using as_gh_is_gh. }
      
      apply disjeq_phplus with (i := bid) (h' := htop (as_gheap hF)) in Hdeq.
      2: apply hdisj_pdisj.
      2: apply as_gheap_hdisj; auto.
      destruct Hdeq as (hF' & Hdis1 & Hdis2 & Heq1 & Hdisj3).
      erewrite Vector.nth_map in Heq1; [|reflexivity].
      assert (exists hhF', hF' = htop hhF') as [hhF' HF']; subst.
      { eapply htop_phplus_heap.
        erewrite Vector.nth_map in Hdis1; [|reflexivity..].
        apply Hdis1.
        apply Heq1. }
      rewrite <-hplus_phplus in Heq1; simpl in Heq1; auto.
      rewrite <-heap_pheap_eq in Heq1.
      rewrite <-Heq1 in H. 
      Infix "|+|" := hplus (at level 40, left associativity).
      assert (as_sheap (sh_hp gs)[@bid] |+| (ghs[@bid] |+| hhF') |+| as_gheap hF =
              hplus (hplus (as_sheap (sh_hp gs)[@bid]) ghs[@bid]) (hplus hhF' (as_gheap hF))).
      { rewrite !hplus_assoc; auto. }
      rewrite H0 in H; apply Hnabort in H; auto.
      erewrite Vector.nth_map in Hdisj3; [|reflexivity].
      rewrite <-hplus_phplus in Hdisj3.

      Lemma hplus_is_gheapC (h1 h2 h : heap) :
        is_gheap h2 -> h1 |+| h = h2 -> is_gheap h.
      Proof.
        unfold is_gheap; intros.
        apply (f_equal (fun f => f (SLoc x))) in H0; unfold hplus in H0; simpl.
        specialize (H x).
        destruct (h1 (SLoc x)), (h2 (SLoc x)); try rewrite H in *; try congruence.
      Qed.
      
      Lemma hplus_is_gheap (h1 h2 : heap) :
        is_gheap h1 -> is_gheap h2 -> is_gheap (h1 |+| h2).
      Proof.
        unfold is_gheap, hplus; intros; rewrite H, H0; auto.
      Qed.
        
      apply is_sheap_disj; auto using as_sh_is_sh, as_gh_is_gh.
      apply hplus_is_gheap; auto using as_sh_is_sh, as_gh_is_gh.
      apply hplus_is_gheapC in Heq1; auto using as_gh_is_gh.
      apply hdisj_pdisj; auto.
      apply hdisj_pdisj; auto.
      apply hdisj_pdisj; auto.
      erewrite Vector.nth_map in Hdis1; [|reflexivity].
      auto.
      
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
      specialize (Hbdivi emp_h); rewrite emp_h_unit_r in Hbdivi; auto; apply Hbdivi in Hbdiv;
      auto using emp_h_disj.

    - intros gs' hF Hdis Hred.
      inversion Hred; subst; simpl in *; clear Hred.
      rename H into Hred; rename H0 into Hheq.
      unfold bs_of_gs in Hred; simpl in Hred.
      rewrite sh_gl_heap_hplus in Hred.
      assert (exists hb, as_gheap (gl_hp gs) = hplus ghs[@bid] hb /\
                         hdisj ghs[@bid] hb) as (hb & Hhb & Hdishb).
      { apply (disj_tid bid) in Hdeq as (hb & ? & ? & ?).
        erewrite Vector.nth_map in H1, H0; [|reflexivity..].
        assert (exists hb', hb = htop hb') as (hb' & ?); subst.
        { simpl in H1; apply htop_phplus_heap in H1; auto. }
        rewrite <-hdisj_pdisj in H0.
        rewrite <-hplus_phplus in H1; simpl in H1; auto.
        rewrite <-heap_pheap_eq in H1.
        exists hb'; split; auto. }
      assert (Heq : as_sheap (sh_hp gs)[@bid] |+| as_gheap (gl_hp gs |+| hF) =
                    (as_sheap (sh_hp gs)[@bid] |+| ghs[@bid]) |+| (hb |+| as_gheap hF)).
      { rewrite hplus_as_gheap, Hhb, !hplus_assoc; auto. }
      rewrite Heq in Hred; clear Heq.
      destruct (Hsafe bid) as (_ & _ & _ & _ & Hsafei); clear Hsafe.
      
      assert (hdisj (as_sheap (sh_hp gs)[@bid] |+| ghs[@bid]) (hb |+| as_gheap hF)).
      { apply is_sheap_disj; auto using as_sh_is_sh, as_gh_is_gh.
        eapply disj_eq_inj; eauto using as_sh_is_sh, as_gh_is_gh.
        apply hplus_is_gheap; auto using as_gh_is_gh.
        symmetry in Hhb; apply hplus_is_gheapC in Hhb; auto.
        (* eapply disj_eq_inj; eauto using as_gh_is_gh. *)
        apply as_gh_is_gh.
        
        Lemma hdisj_hplus_comm {loc : Type} (h1 h2 h3 : PHeap.heap loc) :
          hdisj h1 h2 -> 
          hdisj (h1 |+| h2) h3 -> hdisj h1 (h2 |+| h3).
        Proof.
          unfold hdisj; intros H H1 l.
          specialize (H l); specialize (H1 l); unfold hplus in *;
          destruct (h1 l), (h2 l), (h3 l); try now (destruct H, H1; auto; congruence).
        Qed.
        
        apply hdisj_hplus_comm; eauto; rewrite <-Hhb; apply as_gheap_hdisj; eauto. }

      eapply Hsafei in Hred as (h' & Hdis' & Heq' & Hsafeb); eauto.
      assert (Heq : gh' = hplus (as_sheap sh'') (as_gheap gh'')).
      { rewrite sh_gl_heap_hplus in Hheq; extensionality l; auto. }
      rewrite Heq in Heq'; clear Heq.
      
      Lemma sh_gl_decomp (h : heap) :
        exists hs hg, h = hs |+| hg /\ is_sheap hs /\ is_gheap hg.
      Proof.
        exists (fun l => match l with SLoc _ => h l | _ => None end)
               (fun l => match l with GLoc _ => h l | _ => None end); repeat split.
        extensionality l; destruct l; unfold hplus; simpl; auto.
        destruct (h (SLoc z)); auto.
      Qed.

      destruct (sh_gl_decomp h') as (hs & h'' & Heq & Hiss & Hisg); subst.
      rewrite !hplus_assoc in Heq'.
      
      Lemma sh_gl_eq (hs1 hs2 hg1 hg2 : heap) :
        is_sheap hs1 -> is_sheap hs2 -> is_gheap hg1 -> is_gheap hg2 ->
        hs1 |+| hg1 = hs2 |+| hg2 -> hs1 = hs2 /\ hg1 = hg2.
      Proof.
        intros Hs1 Hs2 Hg1 Hg2 Heq; split; extensionality l; apply (f_equal (fun f => f l)) in Heq;
        destruct l as [l | l]; repeat match goal with [H : _ |- _ ] => specialize (H l) end;
        unfold "|+|" in *;
        repeat match goal with [H : context [match ?X with _ => _ end] |- _] => destruct X end;
        try congruence.
      Qed.

      assert (as_gheap gh'' = h'' |+| (hb |+| as_gheap hF)).
      { apply sh_gl_eq in Heq'; auto using as_sh_is_sh, as_gh_is_gh, hplus_is_gheap.
        tauto.
        repeat apply hplus_is_gheap; auto.
        assert (is_gheap ghs[@bid]).
        { eapply disj_eq_inj; eauto using as_gh_is_gh. }
        symmetry in Hhb; apply hplus_is_gheapC in Hhb; auto using as_gh_is_gh.
        apply as_gh_is_gh. }
      rewrite <-hplus_assoc in H0.

      Lemma is_gheap_as_gheap (h : heap) :
        is_gheap h -> exists h', h = as_gheap h'.
      Proof.
        intros; exists (fun l => h (GLoc l)); extensionality l.
        destruct l as [l | l]; specialize (H l); simpl; auto.
      Qed.

      apply is_gheap_as_gheap in Hisg as [hg'' ?]; subst.
      assert (Hb : is_gheap hb).
      { symmetry in Hhb; apply hplus_is_gheapC in Hhb; auto using as_gh_is_gh. }
      apply is_gheap_as_gheap in Hb as [hb'' ?]; subst.
      rewrite <-!hplus_as_gheap in H0.

      Lemma as_gheap_inj h1 h2 : 
        as_gheap h1 = as_gheap h2 -> h1 = h2.
      Proof.
        intros; extensionality l; apply (f_equal (fun f => f (GLoc l))) in H; auto.
      Qed.

      apply as_gheap_inj in H0.

      exists (hg'' |+| hb''); repeat split; auto.
      
      Lemma hdisjE1 (h1 h2 h3 : heap) : hdisj (h1 |+| h2) h3 -> hdisj h1 h3.
      Proof.
        unfold hdisj, hplus; intros H l; specialize (H l).
        destruct (h1 l), (h3 l); simpl in *; try congruence; auto.
      Qed.

      Lemma hdisjE2 (h1 h2 h3 : heap) : hdisj (h1 |+| h2) h3 -> hdisj h2 h3.
      Proof.
        unfold hdisj, hplus; intros H l; specialize (H l).
        destruct (h1 l), (h2 l), (h3 l); simpl in *; try congruence; auto.
        destruct H; congruence.
      Qed.

      apply hdisjE2 in Hdis'.

      Lemma hdisj_as_gheap h1 h2 :
        hdisj (as_gheap h1) (as_gheap h2) -> hdisj h1 h2.
      Proof.
        unfold hdisj; intros; specialize (H (GLoc x)); eauto.
      Qed.

      rewrite <-hplus_as_gheap in Hdis'; apply hdisj_as_gheap in Hdis'.

      Lemma hdisj_hplus_comm' {loc : Type} (h1 h2 h3 : PHeap.heap loc) :
        hdisj h2 h3 -> 
        hdisj h1 (h2 |+| h3) -> hdisj (h1 |+| h2) h3.
      Proof.
        unfold hdisj; intros H H1  l.
        specialize (H l); specialize (H1 l); unfold hplus in *;
        destruct (h1 l), (h2 l), (h3 l); try now (destruct H, H1; auto; congruence).
      Qed.

      apply hdisj_hplus_comm'; eauto.
      