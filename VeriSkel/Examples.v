Require Import Compiler MyEnv SimplSkel Ext.
Require Import List.

Definition aty_env := (upd_opt emp_opt (VarA "arr") Sx.TZ).
Definition ntrd := 1024.
Definition nblk := 24.
Definition avar_env := (upd (emp_def (0, nil)) (VarA "arr") (0, 1 :: nil)).

Import SimplSkel.
Import Sx.
Definition prog1 :=
  (* let t := map (fun x -> x * x) arr in *)
  (* let t1 := reduce (fun x y -> x + y) t in *)
  (* t1 *)
  ALet (VarA "t") TZ "map" ((F ((VarE "x", TZ) :: nil)
                               (EBin Emult
                                     (EVar (VarE "x") TZ)
                                     (EVar (VarE "x") TZ) TZ)) :: nil)
       ((VArr (VarA "arr"), TZ) :: nil) (
  ALet (VarA "t1") TZ "reduce" ((F ((VarE "x", TZ) :: (VarE "y", TZ) :: nil)
                                   (EBin Eplus
                                         (EVar (VarE "x") TZ)
                                         (EVar (VarE "y") TZ) TZ)) :: nil)
       ((VArr (VarA "t"), TZ) :: nil) (
  ARet (VarA "t1"))).

Definition gen1 := Compiler.compile_prog 1024 24 2 aty_env avar_env prog1.

Definition res1 := save_to_file gen1 "test1.cu".

Definition prog2 :=
  (* let idxs := map (fun x -> x) (Darr n (fun i -> i)) in *)
  (* let arrIdx := map (fun i -> (i, arr[i])) idxs in *)
  (* let maxIdx := reduce (fun (i, x) (j, y) -> if x < y then i else j) arrIdx in *)
  (* maxIdx *)
  ALet (VarA "idxs") TZ
       "map" (F ((VarE "x", TZ) :: nil) (EVar (VarE "x") TZ) :: nil)
       ((DArr (F ((VarE "i", TZ) :: nil) (EVar (VarE "i") TZ)) (LLen (VarA "arr")), TZ) :: nil) (
  ALet (VarA "arrIdx") (TTup (TZ :: TZ :: nil))
       "map" (F ((VarE "i", TZ) :: nil)
                (ECons ((EVar (VarE "i") TZ) :: (EA (VarA "arr") (EVar (VarE "i") TZ) TZ) :: nil)
                       (TTup (TZ :: TZ :: nil))) :: nil)
       ((VArr (VarA "idxs"), TZ) :: nil) (
  ALet (VarA "maxIdx") (TTup (TZ :: TZ :: nil))
       "reduce" (F ((VarE "ix", TTup (TZ :: TZ :: nil)) ::
                     (VarE "iy", TTup (TZ :: TZ :: nil)) :: nil)
                    (EIf (EBin Blt
                               (EPrj (EVar (VarE "ix") (TTup (TZ :: TZ :: nil))) 1 TZ)
                               (EPrj (EVar (VarE "iy") (TTup (TZ :: TZ :: nil))) 1 TZ) TBool)
                         (EVar (VarE "ix") (TTup (TZ :: TZ :: nil)))
                         (EVar (VarE "iy") (TTup (TZ :: TZ :: nil))) (TTup (TZ :: TZ :: nil)))
                    :: nil)
       ((VArr (VarA "arrIdx"), (TTup (TZ :: TZ :: nil))) :: nil) (
  ARet (VarA "maxIdx")))).

Definition gen2 := Compiler.compile_prog 1024 24 2 aty_env avar_env prog2.
Eval compute in gen2.

Definition res2 := save_to_file gen2 "test2.cu".