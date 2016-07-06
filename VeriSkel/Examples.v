Require Import Compiler MyEnv TypedTerm Ext Extract.
Require Import List.

Definition aty_env := Skel.TZ :: nil.
Definition ntrd := 1024.
Definition nblk := 24.

Import Skel.
Arguments ALet {GA t1 t2} _ _.
Arguments Map {GA dom cod} _ _ .
Arguments F1 {GA dom cod} _.
Arguments F2 {GA dom1 dom2 cod} _.
Arguments EBin {GA GS t1 t2 t3} _ _ _.
Arguments EVar {GA GS t} _.
Arguments VArr {GA t} _.
Arguments Reduce {GA t} _ _.
Arguments ARet {GA t} _.
Arguments DArr {GA cod} _ _.
Arguments LLen {GA t} _.
Arguments ECons {GA GS t1 t2} _ _.
Arguments EA {GA GS t} _ _.
Arguments EPrj1 {GA GS t1 t2} _.
Arguments EPrj2 {GA GS t1 t2} _.
Arguments EIf {GA GS t} _ _ _.
Definition prog1 : Skel.AS (TZ :: nil) TZ :=
  (* let t := map (fun x -> x * x) arr in *)
  (* let t1 := reduce (fun x y -> x + y) t in *)
  (* t1 *)
  ALet
    (Map (F1 (EBin Emult (EVar HFirst) (EVar HFirst))) (VArr HFirst)) (
  ALet (Reduce (F2 (EBin Eplus (EVar (HNext HFirst)) (EVar (HFirst)))) (VArr HFirst)) (
  ARet HFirst)).

Definition gen1 := Compiler.compile_prog 1024 24 prog1.
(* Toplevel input, characters 32-36: *)
(* > Definition res1 := save_to_file gen1 "test1.cu". *)
(* >                                 ^^^^ *)
(* Error: The term "gen1" has type *)
(*  "(list (Lang.CTyp * Host.hostVar) * *)
(*    (list Host.instr * (Host.hostVar * list Host.hostVar)) * *)
(*    list Host.kernel)%type" while it is expected to have type *)
(*  "(list (Lang.CTyp * Host.hostVar) * Host.Prog)%type". *)

Definition res1 := save_to_file gen1 "test1.cu".

Definition prog2 : Skel.AS (TZ :: nil) (TTup TZ TZ) :=
  (* let idxs := map (fun x -> x) (Darr n (fun i -> i)) in *)
  (* let arrIdx := map (fun i -> (i, arr[i])) idxs in *)
  (* let maxIdx := reduce (fun (i, x) (j, y) -> if x < y then i else j) arrIdx in *)
  (* maxIdx *)
  ALet
    (Map (F1 (EVar HFirst)) (DArr (F1 (EVar HFirst)) (LLen HFirst))) (
  ALet
    (Map (F1 (ECons (EA (HNext HFirst) (EVar HFirst)) (EVar HFirst) )) (VArr HFirst)) (
  ALet
    (Reduce (F2 (EIf (EBin Blt (EPrj1 (EVar (HNext HFirst))) (EPrj1 (EVar HFirst)))
                     (EVar (HNext HFirst)) (EVar HFirst))) (VArr HFirst)) (
  ARet HFirst))).

 
Definition gen2 := Compiler.compile_prog 1024 24 prog2.
Eval compute in gen2.

Definition res2 := save_to_file gen2 "test2.cu".

Cd "extracted".

Separate Extraction res1 res2.
