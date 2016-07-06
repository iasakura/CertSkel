Require Import Omega List Monad SkelLib.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
      | HNil => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => B elm
                                          | _ :: _ => unit
                                        end) with
          | HFirst _ => tt
          | HNext _ _ _ => tt
        end
      | HCons _ _ x mls' => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => Empty_set
                                          | x' :: ls'' =>
                                            B x' -> (member ls'' -> B elm)
                                            -> B elm
                                        end) with
          | HFirst _ => fun x _ => x
          | HNext _ _ mem' => fun _ get_mls' => get_mls' mem'
        end x (hget _ mls')
    end.
End hlist.

Implicit Arguments hlist [A].
Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].
Implicit Arguments hget [A B elm ls].

Implicit Arguments HFirst [A elm ls].
Implicit Arguments HNext [A elm x ls].

Implicit Arguments member [A].

Module Skel.
  Inductive Typ := TBool | TZ | TTup (typ1 typ2 : Typ).

  Fixpoint typDenote (t : Typ) := 
    match t with
    | TBool => bool
    | TZ => Z
    | TTup t1 t2 => (typDenote t1 * typDenote t2)%type
    end.

  Definition aTypDenote (t : Typ) := list (typDenote t).

  Inductive BinOp : Typ -> Typ -> Typ -> Type :=
  | Eplus : BinOp TZ TZ TZ
  | Emult : BinOp TZ TZ TZ
  | Emin : BinOp TZ TZ TZ
  | BEq : BinOp TZ TZ TBool
  | Blt : BinOp TZ TZ TBool.

  Fixpoint opDenote t1 t2 t3 (op : BinOp t1 t2 t3) :
    typDenote t1 -> typDenote t2 -> typDenote t3 :=
    match op with
    | Eplus => Z.add
    | Emult => Z.mul
    | Emin  => Z.min
    | BEq   => Z.eqb
    | Blt   => Z.ltb
    end.

  Inductive SExp : list Typ -> list Typ -> Typ -> Type :=
  | EVar : forall GA GS t, member t GS -> SExp GA GS t
  | ENum : forall GA GS, Z -> SExp GA GS TZ
  | EBin : forall GA GS t1 t2 t3,
      BinOp t1 t2 t3 -> SExp GA GS t1 -> SExp GA GS t2 -> SExp GA GS t3
  | EA : forall GA GS t, member t GA -> SExp GA GS TZ -> SExp GA GS t
  | ELen : forall GA GS t, member t GA -> SExp GA GS TZ
  | EIf : forall GA GS t,
      SExp GA GS TBool -> SExp GA GS t -> SExp GA GS t -> SExp GA GS t
  | ECons : forall GA GS t1 t2, SExp GA GS t1 -> SExp GA GS t2 -> SExp GA GS (TTup t1 t2)
  | EPrj1 : forall GA GS t1 t2, SExp GA GS (TTup t1 t2) -> SExp GA GS t1
  | EPrj2 : forall GA GS t1 t2, SExp GA GS (TTup t1 t2) -> SExp GA GS t2
  | ELet : forall GA GS t1 t2, SExp GA GS t1 -> SExp GA (t1 :: GS) t2 -> SExp GA GS t2.    

  Fixpoint sexpDenote GA GS t (e : SExp GA GS t) :
    hlist aTypDenote GA -> hlist typDenote GS -> comp (typDenote t) :=
    match e with
    | EVar _ _ _ x => fun sa se => ret (hget se x)
    | ENum _ _ n => fun sa se => ret n
    | EBin _ _ _ _ _ op t1 t2 => fun sa se =>
      do! x := sexpDenote _ _ _ t1 sa se in
      do! y := sexpDenote _ _ _ t2 sa se in
      ret (opDenote _ _ _ op x y)
    | EA _ _ _ x e => fun sa se =>
      do! v := sexpDenote _ _ _ e sa se in
      let arr := hget sa x in
      nth_error arr v
    | ELen _ _ _ x => fun sa se =>
      let arr := hget sa x in
      ret (Z.of_nat (length arr))
    | EIf _ _ _ t1 t2 t3 => fun sa se =>
      do! b := sexpDenote _ _ _ t1 sa se in
      do! th := sexpDenote _ _ _ t2 sa se in
      do! el := sexpDenote _ _ _ t3 sa se in
      ret (if b then th else el)
    | ECons _ _ _ _ t1 t2 => fun sa se =>
      do! v1 := sexpDenote _ _ _ t1 sa se in
      do! v2 := sexpDenote _ _ _ t2 sa se in
      ret (v1, v2)
    | EPrj1 _ _ _ _ t => fun sa se =>
      do! v1 := sexpDenote _ _ _ t sa se in
      ret (fst v1)
    | EPrj2 _ _ _ _ t => fun sa se =>
      do! v1 := sexpDenote _ _ _ t sa se in
      ret (snd v1)
    | ELet _ _ _ _ e1 e2 => fun sa se =>
      do! v1 := sexpDenote _ _ _ e1 sa se in
      sexpDenote _ _ _ e2 sa (HCons v1 se)
    end.

  Inductive FTyp :=
    Fun1 : Typ -> Typ -> FTyp 
  | Fun2 : Typ -> Typ -> Typ -> FTyp.

  Fixpoint ftypDenote (t : FTyp) :=
    match t with
    | Fun1 t1 t2 => typDenote t1 -> comp (typDenote t2)
    | Fun2 t1 t2 t3 => typDenote t1 -> typDenote t2 -> comp (typDenote t3)
    end.

  Inductive Func : list Typ -> FTyp -> Type :=
    F1 : forall (GA : list Typ) (dom cod : Typ),
      SExp GA (dom :: nil) cod -> Func GA (Fun1 dom cod) 
  | F2 : forall (GA : list Typ) (dom1 dom2 cod : Typ),
      SExp GA (dom2 :: dom1 :: nil) cod -> Func GA (Fun2 dom1 dom2 cod).

  Definition funcDenote GA ft (f : Func GA ft) : hlist aTypDenote GA -> ftypDenote ft :=
    match f with
    | F1 _ _ _ e => fun sa => fun x => sexpDenote _ _ _ e sa (HCons x HNil)
    | F2 _ _ _ _ e => fun sa => fun x y => 
      sexpDenote _ _ _ e sa (HCons y (HCons x HNil))
    end.

  Inductive LExp : list Typ -> Typ -> Type := 
  | LNum GA (n : Z) : LExp GA TZ
  | LLen GA t : member t GA -> LExp GA TZ
  | LMin GA : LExp GA TZ -> LExp GA TZ -> LExp GA TZ.

  Fixpoint lexpDenote GA t (le : LExp GA t) :
    hlist aTypDenote GA -> typDenote t :=
    match le with
    | LNum _ n => fun _ => (n : typDenote TZ)
    | LLen _ GA x => fun sa => 
      let arr := hget sa x in Z.of_nat (length arr)
    | LMin _ a1 a2 => fun sa => 
      Z.min (lexpDenote _ _ a1 sa) (lexpDenote _ _ a1 sa) 
    end.

  Inductive AE : list Typ -> Typ -> Type :=
  | VArr GA t : member t GA -> AE GA t
  | DArr GA cod : Func GA (Fun1 TZ cod) -> LExp GA TZ -> AE GA cod.

  Definition aeDenote GA t (ae : AE GA t) :
    hlist aTypDenote GA -> comp (aTypDenote t).
      refine(
    match ae with
    | VArr _ _ x => fun sa => ret (hget sa x)
    | DArr _ _ f len => fun sa => _
    end).
      pose (fun i => funcDenote _ _ f sa i) as f'.
      pose (lexpDenote _ _ len sa) as n.
      apply (mapM f' (seq 0 (Z.to_nat n))).
  Defined.
  
  Inductive SkelE : list Typ -> Typ -> Type  :=
  | Map GA dom cod : Func GA (Fun1 dom cod) -> (AE GA dom) -> SkelE GA cod
  | Reduce GA t : Func GA (Fun2 t t t) -> (AE GA t) -> SkelE GA t
  | Seq GA : LExp GA TZ -> LExp GA TZ -> SkelE GA TZ
  | Zip GA t1 t2 : AE GA t1 -> AE GA t2 -> SkelE GA (TTup t1 t2).

  Definition skelDenote GA t (skel : SkelE GA t) :
    hlist aTypDenote GA -> comp (aTypDenote t) :=
    match skel with
    | Map _ _ _ f e => fun sa =>
      do! arr := aeDenote _ _ e sa in
      mapM (funcDenote _ _ f sa) arr
    | Reduce _ _ f e => fun sa =>
      do! arr := aeDenote _ _ e sa in
      reduceM (funcDenote _ _ f sa) arr
    | Seq _ start len => fun sa => 
      ret (seq (lexpDenote _ _ start sa) (Z.to_nat (lexpDenote _ _ len sa)))
    | Zip _ _ _ a1 a2 => fun sa =>
      do! a1 := aeDenote _ _ a1 sa in
      do! a2 := aeDenote _ _ a2 sa in
      ret (zip a1 a2)
    end.

  Inductive AS : list Typ -> Typ -> Type := 
  | ALet GA t1 t2 : SkelE GA t1 -> AS (t1 :: GA) t2 -> AS GA t2
  | ARet GA t : member t GA -> AS GA t.

  Fixpoint asDenote GA t (as_ : AS GA t) :
    hlist aTypDenote GA -> comp (aTypDenote t) :=
      match as_ with
      | ALet _ _ _ skel e => fun sa =>
        do! x := skelDenote _ _ skel sa in
        asDenote _ _ e (HCons x sa) 
      | ARet _ _ x => fun sa => ret (hget sa x)
      end.
End Skel.