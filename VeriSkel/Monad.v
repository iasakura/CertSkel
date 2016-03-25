Require Import List.

Class Monad (f : Type -> Type) := {ret : forall {A}, A -> f A; bind : forall {A B}, f A -> (A -> f B) -> f B}.

Infix ">>=" := bind(at level 60).

Definition bind_opt A B (a : option A) (f : A -> option B) : option B :=
  match a with
  | None => None
  | Some a => f a
  end.

Instance option_monad : Monad option :=
  {ret := fun _ x => (Some x);
   bind := bind_opt}.

Fixpoint bind_list A B (a : list A) (f : A -> list B) : list B :=
  match a with
  | nil => nil
  | a :: l => f a ++ bind_list _ _ l f
  end.

Instance list_monad : Monad list := {ret := fun _ x => x :: nil; bind := bind_list}.

Fixpoint sequence {m a} `{Monad m} (xs : list (m a)) : m (list a) :=
  match xs with
  | nil => ret nil
  | x :: xs => x >>= fun y =>
               sequence xs >>= fun ys =>
               ret (y :: ys)
  end.

Notation "'let!' x := e1 'in' e2" := (bind e1 (fun x => e2)) (at level 200, x ident, e1 at level 100, e2 at level 200).
