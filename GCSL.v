Require Export CSL array_dist.
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

Definition hdisj_sim (h1 h2 : simple_heap) :=
  forall x, h1 x = None \/ h2 x = None.

Definition hplus_sim (h1 h2 : simple_heap) :=
  fun x => match h1 x with
    | Some x => Some x
    | None => h2 x
  end.

Definition bdiv_g (gs : g_state nblk ntrd) :=
  exists bid : Fin.t nblk, 
    Bdiv.bdiv ((blks gs)[@bid], sh_gl_heap (sh_hp gs)[@bid] (gl_hp gs)).

Fixpoint safe_ng (n : nat) (gs : g_state nblk ntrd) (Q : assn) :=
  match n with
    | 0 => True
    | S n =>
      ((forall (bid : Fin.t nblk) (tid : Fin.t ntrd), fst ((blks gs)[@bid][@tid]) = SKIP) ->
         Q default_stack (htop (heap_of_sheap (gl_hp gs)))) /\
      (forall hF : simple_heap,
         hdisj_sim (gl_hp gs) hF ->
         ~abort_g (Gs (blks gs) (sh_hp gs) (hplus_sim (gl_hp gs) hF))) /\
      ~ bdiv_g gs /\
      (forall (gs' : g_state nblk ntrd) (hF : simple_heap),
         hdisj_sim (gl_hp gs) hF ->
         red_g (Gs (blks gs) (sh_hp gs) (hplus_sim (gl_hp gs) hF)) gs' ->
         exists h'' : simple_heap,
           hdisj_sim h'' hF /\ (gl_hp gs') = hplus_sim h'' hF /\
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
      | (sh, len) :: sh_decl => is_array (Sh sh) len (fun _ => 0%Z) 0 ** sh_spec sh_decl
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
         P stk (htop (heap_of_sheap gh))) ->
    forall n, safe_ng n (Gs ks (const sh nblk) gh) Q.
  
  Lemma safe_gl (C : cmd) (Q : assn) (Qs : Vector.t assn nblk) 
  :
    