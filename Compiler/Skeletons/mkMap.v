Require Import LibTactics Psatz.
Require Import GPUCSL scan_lib CSLTactics.
Require Import CUDALib TypedTerm.
Require Import CSLLemma CodeGen CUDALib Correctness CSLTactics.
Require Import Host.

Section mkMap.

Variable ntrd nblk : nat.

Variable GA : list Skel.Typ.
Variable dom cod : Skel.Typ.
Variable arr : var -> (cmd * vars dom).
Variable func : vars dom -> (cmd * vars cod).

Definition out : vars cod := maptys fst (out_name cod).
Definition len : vars Skel.TZ := out_len_name.
Definition t := locals "t" dom 0.

Definition mkMap_cmd inv :=
  "i" :T Int ::= "tid" +C "bid" *C Zn ntrd ;;
  WhileI inv ("i" <C len) (
    fst (arr "i") ;;
    assigns t (ty2ctys dom) (v2e (snd (arr "i"))) ;;
    fst (func t) ;;
    writes (v2gl out +os "i") (v2e (snd (func t))) ;;
    "i" ::= Zn ntrd *C Zn nblk +C "i"
  )%exp.

Definition mkMap : kernel :=
  let arr_vars := gen_params GA in
  let params_in := flatten_avars arr_vars in
  let params_out := (out_len_name, Int) :: flatTup (out_name cod) in
  {| params_of := params_out ++ params_in;
     body_of := Pr nil (mkMap_cmd FalseP) |}.

Variable avar_env : AVarEnv GA.
Variable aptr_env : APtrEnv GA.
Variable aeval_env : AEvalEnv GA.

Lemma mkMap_cmd_ok BS (tid : Fin.t ntrd) : 
  CSL BS tid
      (kernelInv avar_env aptr_env aeval_env Emp True nil 1)
      (mkMap_cmd FalseP)
      (kernelInv avar_env aptr_env aeval_env Emp True nil 1).
Abort.
End mkMap.