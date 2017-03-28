Require Import PeanoNat Nat LibTactics Psatz.
Require Import GPUCSL SkelLib CSLTactics.
Require Import CUDALib TypedTerm.
Require Import Host.
Require Import CodeGen CUDALib Correctness Grid CSLTactics CSLLemma Utils.
Import List.

Section mkScan.

Variable typ : Skel.Typ.

Variable ntrd nblk : nat.
Variable e_b : nat.

Hypothesis ntrd_neq_0: ntrd <> 0.
Hypothesis nblk_neq_0: nblk <> 0.

Notation sarr0 := (locals "_sarr0" typ 0).
Notation sarr1 := (locals "_sarr1" typ 0).

Notation xs := (locals "xs" typ 0).
Notation ys := (locals "ys" typ 0).
Notation zs := (locals "zs" typ 0).
Notation out := (outArr typ).

Definition in_sarr n := if (n mod 2 =? 0) then v2sh sarr0 else v2sh sarr1.
Definition out_sarr n := if (n mod 2 =? 0) then v2sh sarr1 else v2sh sarr0.

Variable arr_c : var -> (cmd * vars typ).
Variable func_c : vars typ -> vars typ -> (cmd * vars typ).

Definition scan_body n offset :=
  Cbarrier n ;;
  Cif ("tid" <C Zn offset) (
    writes (out_sarr n +os "tid") (v2e xs)
  ) (
    reads ys (ty2ctys typ) (in_sarr n +os ("tid" -C Zn offset)) ;;
    assigns_call2 zs func_c ys xs ;;
    assigns xs (ty2ctys typ) (v2e zs) ;;
    writes (out_sarr n +os "tid") (v2e zs)
  ).

Fixpoint scan_aux n off :=
  match n with
  | O => Cskip
  | S n => 
    scan_body n off ;; scan_aux n (off * 2)
  end.

Definition scan_loop nt := scan_aux (log2 nt) 1.

Definition scan_block nt :=
  assigns_get xs arr_c "ix" ;;
  writes (out_sarr (log2 nt)) (v2e xs) ;;
  scan_loop nt ;;
  writes (v2gl out +os "ix") (v2e xs).

Goal False. 
  pose (scan_block 16).
  unfold scan_block, scan_loop, scan_aux, scan_body, log2, out_sarr, in_sarr in c; simpl in c.
Abort.

Definition scan_prog nt : program :=
  {| get_sh_decl := sh_decl ntrd typ "_sarr0" 0 ++ sh_decl ntrd typ "_sarr1" 0;
     get_cmd := scan_block nt |}.

Definition mkScan GA typ ntrd : kernel :=
  let arr_vars := gen_params GA in
  let params_in := flatten_avars arr_vars in
  let params_out := (inp_len_name, Int) :: flatTup (out_name typ) in
  {| params_of := params_out ++ params_in;
     body_of := scan_prog ntrd |}.