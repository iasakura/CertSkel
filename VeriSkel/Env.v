Require Import PHeap.

(* general enviroment *)
Section Environment.
  Definition Env (A B : Type) (eqt : eq_type A) := A -> B.
  
  Definition upd {A B eqt} (env : Env A B eqt) x v : Env A B eqt :=
    fun y => if eq_dec x y then v else env y.
  Definition upd_opt {A B eqt} (env : Env A (option B) eqt) x v : Env A (option B) eqt :=
    fun y => if eq_dec x y then Some v else env y.
  Definition emp_opt {A B eqt} : Env A (option B) eqt := fun (_ : A) => @None B.
  Definition emp_def {A B eqt} (d : B) : Env A B eqt := fun (_ : A) => d.
End Environment.