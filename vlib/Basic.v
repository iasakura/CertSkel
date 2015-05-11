(* from http://www.mpi-sws.org/~viktor/cslsound/coq/Basic.html *)
Require Import VVlib.

Set Implicit Arguments.
Unset Strict Implicit.

Definition heap := Z -> option Z.

(* upd f x y = f [x |-> y] *)
Definition upd A (f: Z -> A) x y a := if Z.eq_dec a x then y else f a.

(* h1 _|_ h2 *)
Definition hdef (h1 h2 : heap) := forall x, h1 x = None \/ h2 x = None.

(* h1 + h2 *)
Definition hplus (h1 h2 : heap) : heap := 
  (fun x => match h1 x with None => h2 x | Some y => Some y end).

(* commutative *)
Lemma hdefC : forall h1 h2, hdef h1 h2 -> hdef h2 h1.
Proof. unfold hdef; firstorder. Qed.

Lemma hdef_hplus : 
  forall h1 h2 h3, hdef h1 (hplus h2 h3) <-> hdef h1 h2 /\ hdef h1 h3.
Proof.
 unfold hdef, hplus.
 intuition repeat match goal with H: forall _ : Z, _ |- _ => specialize (H x) end;
 desf; vauto.
Qed.

Lemma hdef_hplus2 : 
  forall h1 h2 h3, hdef (hplus h2 h3) h1 <-> hdef h1 h2 /\ hdef h1 h3.
Proof.
 unfold hdef, hplus; intuition
   repeat match goal with H: _ |- _ => specialize (H x) end; 
     desf; vauto.
Qed.

Corollary hdef_hplus_a : 
  forall h1 h2 h3, hdef h1 h2 -> hdef h1 h3 -> hdef h1 (hplus h2 h3).
Proof. by intros; apply hdef_hplus. Qed.

Corollary hdef_hplus_b : 
  forall h1 h2 h3, hdef h1 h2 -> hdef h1 h3 -> hdef (hplus h2 h3) h1.
Proof. by intros; apply hdef_hplus2. Qed.

Hint Resolve hdef_hplus_a hdef_hplus_b.
Hint Immediate hdefC.

Lemma hplusA : 
 forall h1 h2 h3, hplus (hplus h1 h2) h3 = hplus h1 (hplus h2 h3).
Proof.
  by unfold hplus; ins; extensionality x; ins; desf.
Qed.

Lemma hplusC : 
 forall h1 h2, hdef h1 h2 -> hplus h2 h1 = hplus h1 h2.
Proof.
  unfold hplus; ins; extensionality x; desf.
  destruct (H x); clarify.
Qed.

Lemma hplusAC : 
 forall h1 h2 h3,
   hdef h1 h2 ->
   hplus h2 (hplus h1 h3) = hplus h1 (hplus h2 h3).
Proof.
  unfold hplus; ins; extensionality x; desf.
  destruct (H x); clarify.
Qed.

Lemma hplusKl :
  forall h h1 h2,
    hplus h h1 = hplus h h2 -> hdef h h1 -> hdef h h2 ->
    h1 = h2.
Proof.
  unfold hplus, hdef; ins; extensionality x.
  apply (f_equal (fun f => f x)) in H.
  specialize (H0 x). specialize (H1 x). desf. congruence.
Qed.

Lemma hplusKr :
  forall h h1 h2,
    hplus h1 h = hplus h2 h -> hdef h1 h -> hdef h2 h ->
    h1 = h2.
Proof.
  unfold hplus, hdef; ins; extensionality x.
  apply (f_equal (fun f => f x)) in H;
  specialize (H0 x); specialize (H1 x); desf; congruence.
Qed.

(* リストの要素がどの2つも異なる *)
Fixpoint disjoint_list A (l : list A) :=
  match l with
    | nil => True
    | x :: l => ~ In x l /\ disjoint_list l
  end.
(* xl ∩ yl = ∅ *)
Fixpoint disjoint A (xl yl : list A) :=
  match xl with
    | nil => True
    | x :: xl => ~ In x yl /\ disjoint xl yl
  end.
(* remove all y in l *)
Fixpoint removeAll A (eq_dec : forall x y : A, {x = y} + {x <> y}) l y :=
  match l with
    | nil => nil
    | x :: l => 
      if eq_dec x y then removeAll eq_dec l y
      else x :: removeAll eq_dec l y
  end.
(* xl - yl *)
Fixpoint list_minus A eq_dec (xl yl : list A) :=
  match yl with 
    | nil => xl
    | y :: yl => list_minus eq_dec (removeAll eq_dec xl y) yl
  end.

(* x ∉ l -> removeAll l x = l *)
Lemma removeAll_notin :
 forall A dec (x : A) l (NIN: ~ In x l), 
   removeAll dec l x = l.
Proof.
  induction l; ins; desf; [exfalso | f_equal]; eauto.
Qed.

(* removeAll _ xはidempotent *)
Lemma removeAllK : forall A dec l (x : A),
  removeAll dec (removeAll dec l x) x = removeAll dec l x.
Proof.
  induction l; ins; desf; ins; desf; f_equal; auto.
Qed.

(* removeAll _ xは順番入れ替えても同じ *)
Lemma removeAllC : forall A dec l (x y : A),
  removeAll dec (removeAll dec l y) x = removeAll dec (removeAll dec l x) y.
Proof.
  induction l; ins; desf; ins; desf; f_equal; auto.
Qed.

(* l - {y} - l' = l - l' - {y} *)
Lemma removeAll_list_minus : forall A dec l l' (y : A),
  removeAll dec (list_minus dec l l') y = 
  list_minus dec (removeAll dec l y) l'.
Proof.
  by induction[l] l'; ins; rewrite IHl', removeAllC.
Qed.

(* x ∈ l - {y} ⇔ x ∈ l /\ x <> y *)
Lemma In_removeAll : forall A dec l (x y : A),
  In x (removeAll dec l y) <-> In x l /\ x <> y.
Proof.
  induction l; ins; desf; simpl; rewrite ?IHl; 
    split; ins; des; clarify; auto.
Qed.

(* x ∈ l - l' ⇔ x ∈ l /\ x ∉ l' *)
Lemma In_list_minus : forall A dec l l' (x : A),
  In x (list_minus dec l l') <-> In x l /\ ~ In x l'.
Proof.
  induction[l] l'; ins; desf; rewrite ?IHl', ?In_removeAll; intuition.
Qed.

(* disjoint l1 -> disjoint l2 -> l1 ∩ l2 = ∅ -> disjoint (l1 ++ l2) *)
Lemma disjoint_list_app :
  forall A (l1 l2 : list A), disjoint_list l1 -> disjoint_list l2 -> disjoint l1 l2 -> 
    disjoint_list (l1 ++ l2).
Proof.
  induction l1; ins; rewrite In_app in *; intuition.
Qed.

(* disjoint l -> disjoint (l - {y}) *)
Lemma disjoint_list_removeAll : forall A dec l (y : A),
  disjoint_list l -> disjoint_list (removeAll dec l y).
Proof.
  induction l; ins; desf; simpl; try rewrite In_removeAll; intuition.
Qed.

(* disjoint l -> disjoint (l - l') *)
Lemma disjoint_list_list_minus : forall A dec (l l' : list A),
  disjoint_list l -> disjoint_list (list_minus dec l l').
Proof.
  induction[l] l'; ins; desf; auto using disjoint_list_removeAll.
Qed.

(* x ∉ l -> l - {x} = l *)
Lemma removeAll_irr: forall A dec l (x: A) (NIN: ~ In x l),
  removeAll dec l x = l.
Proof.
  induction l; ins; desf; [exfalso|f_equal]; eauto.
Qed.

(* (l ++ l') - {x} = l - {x} ++ l' - {y} *)
Lemma removeAll_app: forall A dec l l' (x: A),
  removeAll dec (l ++ l') x = removeAll dec l x ++ removeAll dec l' x.
Proof.
  induct l.
Qed.

(* x - (y ++ z) = x - y - z *)
Lemma list_minus_app:
  forall A dec (x y z: list A), 
    list_minus dec x (y ++ z) = list_minus dec (list_minus dec x y) z.
Proof.
  induction[x] y.
  - by simpl.
  - intros x z; simpl; apply IHy.
(*  by induction[x] y; ins.*)
Qed.

(* (x - z) - y = (x - y) - z *)
Lemma list_minusC:
  forall A dec (x y z: list A), 
    list_minus dec (list_minus dec x z) y = list_minus dec (list_minus dec x y) z.
Proof.
  by induction[x] y; ins; rewrite removeAll_list_minus, IHy.
Qed.

(* x ∩ z = ∅ -> x + (z - w) - z = x *)
Lemma list_minus1:
  forall A (x z: list A) (D: disjoint x z) dec w, 
    list_minus dec (x ++ list_minus dec z w) z = x.
Proof.
  induction z; ins; [by induction w; ins; apply appl0|].
  rewrite removeAll_app, removeAll_list_minus; simpl; desf.
  rewrite <- removeAll_list_minus, <- removeAll_app, <- removeAll_list_minus, IHz.
  (* Dのみのこしてxについての帰納法
     - x = [] のとき, removeAll _ [] _ = []より自明
     - x = y :: ysのとき,
       IH : disjoint ys (a :: z) -> removeAll dec ys a = ys
       D : disjoint (y :: ys) (a :: z) = ~ (y ∈ (a :: z)) /\ disjoint ys z
                                       =  ~ (y = a ‌\/ y ∈ z) /\ disjoint ys (a :: z)
       (LHS) = removeAll dec (y :: ys) a
             = if y == a then ys else y :: removeAll dec ys a
        case y == a. Dより矛盾
        case y <> a.
            disjoint ys (a :: z)なので
            LHS = y :: ys = y :: ys
   *)
  clear -D; induction x; ins; desf; [exfalso|f_equal]; eauto.
  by clear -D; induction x; ins; intuition.
Qed.

(*
z ∩ x = ∅ -> ((z - w) ++ x) - z = x
*)
Lemma list_minus2:
  forall A (x z: list A) (D: disjoint z x) dec w, 
    list_minus dec (list_minus dec z w ++ x) z = x.
Proof.
  induction z; ins; [by induction w; ins; apply appl0|].
  rewrite removeAll_app, removeAll_list_minus; simpl; desf.
  rewrite <- removeAll_list_minus, <- removeAll_app, <- removeAll_list_minus, IHz; try done.
  by clear -D; induction x; ins; desf; [exfalso|f_equal]; eauto.
Qed.

(* (x ++ z) - (y ++ z) = x - y *)
Lemma list_minus_appr:
  forall A dec (x y z : list A), disjoint x z -> 
    list_minus dec (x ++ z) (y ++ z) = list_minus dec x y.
Proof.
  ins; rewrite list_minus_app, list_minusC; f_equal.
  apply (list_minus1 H dec nil).
Qed.

(* (z ++ x) - (z ++ y) = x - y *)
Lemma list_minus_appl:
  forall A dec (x y z : list A), disjoint z x -> 
    list_minus dec (z ++ x) (z ++ y) = list_minus dec x y.
Proof.
  ins; rewrite list_minus_app; f_equal; apply (list_minus2 H dec nil).
Qed.

(* x - {a} - y - {a} = x - y - {a} *)
Lemma list_minus_removeAll2:
  forall A dec x y (a: A), 
    list_minus dec (removeAll dec x a) (removeAll dec y a)
    = removeAll dec (list_minus dec x y) a.
Proof.
  induction[x] y; ins; desf; simpls.
  by rewrite IHy, <- !removeAll_list_minus, removeAllK.
  by rewrite removeAllC, IHy.
Qed.

(* a ∉ x -> x - (y - {a}) = x - y *)
Lemma list_minus_removeAll_irr: 
  forall A dec (a: A) x (NIN: ~ In a x) y, 
    list_minus dec x (removeAll dec y a) = list_minus dec x y.
Proof.
  induction[x NIN] y; ins; desf; simpls; try rewrite IHy; eauto.
  by rewrite removeAll_irr.
  rewrite In_removeAll; intuition.
Qed.

(* (∀x, p x ⇔ q x) -> (∃ x, p x) ⇔ (∃ x, q x)  *)
Lemma ex_iff : forall A p q (EQ: forall x : A, p x <-> q x),
  (exists x, p x) <-> (exists x, q x).
Proof. firstorder. Qed.

(* (∀x, p x ⇔ q x) -> (∀ x, p x) ⇔ (∀ x, q x)  *)
Lemma all_iff : forall A p q (EQ: forall x : A, p x <-> q x),
  (forall x, p x) <-> (forall x, q x).
Proof. firstorder. Qed.

(* ∀ (f1, f2 : T1 -> T2), (s : list T1), ((∀x, x ∈ s -> f1 x = f2 x) -> map f1 s = map f2 s *)
Lemma Eq_in_map:
  forall (T1 T2 : Type) (f1 f2 : T1 -> T2) (s : list T1),
  (forall x (IN: In x s), f1 x = f2 x) -> map f1 s = map f2 s.
Proof.
  induction s; ins; f_equal; auto.
Qed.
