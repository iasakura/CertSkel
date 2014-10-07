(** ex 15 *)

Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Inductive Tree:Set :=
  | Node: seq Tree -> Tree.

Fixpoint Tree_ind' (P : Tree -> Set) (Q : seq Tree -> Set)
  (pn : (forall l, Q l -> P (Node l)))
  (qnil : (Q [::]))
  (qcons : forall t ts, P t -> Q ts -> Q ([:: t & ts]))
  (t : Tree) : P t :=
  match t return P t with
    | Node ts =>
      let q_ts := (fix t_ind ts :=
         match ts return Q ts with
           | [::] => qnil
           | [:: t & ts'] => qcons t ts' (Tree_ind' P Q pn qnil qcons t) (t_ind ts')
          end) ts in
      pn ts q_ts
  end.

Fixpoint Tree_eq (t1 t2 : Tree) :=
  match t1, t2 with
    | Node l1, Node l2 =>
      (fix ts_eq l1 l2 :=
         match l1, l2 with
           | [::], [::] => true
           | [:: x & xs], [:: y & ys] => Tree_eq x y && ts_eq xs ys
           | _, _ => false
         end) l1 l2
  end.
Fixpoint Tree_eq_seq (ts1 ts2 : seq Tree) :=
  match ts1, ts2 with
    | [::], [::] => true
    | [:: x & ts1], [:: y & ts2] => Tree_eq x y && Tree_eq_seq ts1 ts2
    | _, _ => false
  end.

Lemma Tree_eqP : Equality.axiom Tree_eq.
Proof.
  rewrite / Equality.axiom.
  pose P x := forall y, reflect (x = y) (Tree_eq x y).
  apply (Tree_ind' P (fun x => forall y, reflect (x = y) (Tree_eq_seq x y))); rewrite/P; move=>{P}. 
  - move=>l IH [] l0.
    move:(IH l0)=>{IH}IH.
    move=>/=; rewrite -/ Tree_eq_seq.
    case: IH.
    + by move=>->; apply: ReflectT.
      by move=>H; apply:ReflectF=>H'; apply: H; case: H'.
  - case.
    + by apply: ReflectT. 
    + by move=> a l; apply: ReflectF.
  - move=> t ts Ht Hts.
    case.
    + by apply: ReflectF.
      move=> a l.
      move: (Ht a)=>{Ht}Ht; move: (Hts l)=>{Hts}Hts /=.
      case: (Tree_eq t a) Ht; case: (Tree_eq_seq ts) Hts; move=>Hts Ht.
      * by apply ReflectT; congr (_ :: _); [apply/Ht | apply/Hts].
      * by apply ReflectF; move=>H; inversion H; subst; clear H; inversion Hts.
      * by apply ReflectF; move=>H; inversion H; subst; clear H; inversion Ht.
      * by apply ReflectF; move=>H; inversion H; subst; clear H; inversion Ht.
Qed.

Theorem Tree_dec: forall a b:Tree, {a=b} + {a<>b}.
Proof.
  move=> a b.
  case: (Tree_eqP a b).
  by left; done.
  by right; done.
Qed.