Require Import LibTactics Psatz.
Require Import GPUCSL SkelLib scan_lib CSLTactics.
Require Import CUDALib TypedTerm.
Require Import Host.
Require Import Skel_lemma CodeGen CUDALib Correctness Grid CSLTactics CSLLemma.

Section mkReduce.

Variable typ : Skel.Typ.

Variable ntrd nblk : nat.
Variable e_b : nat.

Hypothesis ntrd_neq_0: ntrd <> 0.
Hypothesis nblk_neq_0: nblk <> 0.

Hypothesis max_th_size : ntrd <= 2 ^ e_b.
Hypothesis eb_neq_0 : e_b <> 0.

Variable GA : list Skel.Typ.
Variable avar_env : AVarEnv GA.
Variable aptr_env : APtrEnv GA.
Variable aeval_env : AEvalEnv GA.
Hypothesis Haok : aenv_ok avar_env.

Variable arr : Skel.AE GA typ.
Variable arr_c : var -> (cmd * vars typ).
Hypothesis arr_ok : ae_ok avar_env arr arr_c.

Variable func : Skel.Func GA (Skel.Fun2 typ typ typ).
Variable func_c : vars typ -> vars typ -> (cmd * vars typ).
Hypothesis f_ok : func_ok avar_env func func_c.

Variable f : Skel.typDenote typ -> Skel.typDenote typ -> Skel.typDenote typ.
Infix "\op" := f (at level 50, left associativity).

Hypothesis f_total :
  forall x y, Skel.funcDenote _ _ func aeval_env x y = Some (x \op y).

Hypothesis f_comm : 
  forall x y, x \op y = y \op x.
Hypothesis f_assoc :
  forall x y z, x \op y \op z = x \op (y \op z).

Variable result : Skel.aTypDenote typ.
Hypothesis eval_reduce_ok :
  Skel.skelDenote _ _ (Skel.Reduce _ _ func arr) aeval_env = Some result.

Lemma eval_arr_ok :
  { arr_res | Skel.aeDenote _ _ arr aeval_env = Some arr_res}.
Proof.
  simpl in *; unfold Monad.bind_opt in *.
  destruct Skel.aeDenote; simpl in *; inverts eval_reduce_ok; eexists; eauto.
Qed.

Definition arr_res : Skel.aTypDenote typ := let (a, _) := eval_arr_ok in a.

Definition eval_arr_ok' : Skel.aeDenote _ _ arr aeval_env = Some arr_res.
Proof.
  unfold arr_res; destruct eval_arr_ok; eauto.
Qed.

Hint Resolve eval_arr_ok' : pure_lemma.

Notation xs := (locals "xs" typ 0).
Notation ys := (locals "ys" typ 0).
Notation zs := (locals "zs" typ 0).
Notation t := (locals "t" typ 0).
Notation sarr := (locals "sarr" typ 0).
Definition outArr ty := locals "_arrOut" ty 0.
Notation out := (outArr typ).
Notation len := out_len_name.

Definition reduce_body n s :=
  (Cbarrier (n - 1) ;;
   Cif (Band ("tid" +C Zn s <C "slen") ("tid" <C Zn s)) (
     reads xs (ty2ctys typ) (v2sh sarr +os ("tid" +C Zn s)) ;;
     assigns_call2 zs func_c ys xs ;;
     assigns ys (ty2ctys typ) (v2e zs) ;;
     writes (v2sh sarr +os "tid") (v2e ys)
   ) Cskip
  )%exp.

Definition st n := 2 ^ (e_b - n).

Fixpoint reduce_aux t m :=
  match m with
  | O => Cskip    
  | S m =>
    reduce_body t (st t) ;; reduce_aux (S t) m 
  end.

Definition reduceBlock := reduce_aux 1 e_b.

Fixpoint vals2es {ty} (v : val) :=
  match ty return exps ty with
  | Skel.TBool | Skel.TZ => Enum v
  | Skel.TTup t1 t2 => (@vals2es t1 v, @vals2es t2 v)
  end.

Definition seq_reduce inv :=
  assigns ys (ty2ctys typ) (vals2es 0%Z) ;;
  writes (v2sh sarr +os "tid") (vals2es 0%Z) ;;
  "ix" :T Int ::= ("tid" +C "bid" *C Zn ntrd) ;;
  Cif ("ix" <C len) (
    assigns_get ys arr_c "ix" ;;
    "ix" ::= "ix" +C Zn ntrd *C Zn nblk ;;
    WhileI inv ("ix" < len) (
      assigns_get xs arr_c "ix" ;;
      assigns_call2 zs func_c ys xs ;;
      assigns ys (ty2ctys typ) (v2e zs) ;;
      "ix" ::= "ix" +C Zn ntrd *C Zn nblk
    );;
    writes (v2sh sarr +os "tid") (v2e ys)
  ) Cskip.

Definition setToLen :=
  Cif (len <C "bid" *C Zn ntrd) (
    "slen" :T Int ::= 0%Z 
  ) (Cif (len <C ("bid" +C 1%Z) *C Zn ntrd) (
    "slen" :T Int ::= len -C "bid" *C Zn ntrd 
  ) (
    "slen" :T Int ::= Zn ntrd
  )).

Definition mkReduce_cmd :=
  seq_reduce FalseP ;;
  setToLen ;;
  reduceBlock ;;
  Cif ("tid" == 0%Z) (
    reads t (ty2ctys typ) (v2sh sarr +os 0%Z) ;;
    writes (v2gl out +os "bid") (v2e t) 
  ) Cskip.

Section blockReduce.
Variable tid : Fin.t ntrd.
Variable inp : list (Skel.typDenote typ).
Hypothesis inp_length : length inp = ntrd.
Variable l : nat.
Hypothesis l_le_ntrd : l <= ntrd.
Variable inpp : vals typ.

Arguments Sumbool.sumbool_and {A B C D} _ _.

(* the elements of sarr after the n-th iteration *)
Fixpoint f_sim n i :=
  match n with
  | O => gets' inp i
  | S m => 
    if Sumbool.sumbool_and (lt_dec (i + st (S n)) l) (lt_dec i (st (S n))) then
      f_sim m i \op f_sim m (i + st (S n))
    else 
      f_sim m i
  end.

Definition dist n i :=
  if Sumbool.sumbool_and (lt_dec (i + st (S n)) l) (lt_dec i (st (S n))) then i
  else i - st (S n).

Definition dist_pre (i : nat) := i.

Notation cvals f := (arr2CUDA (ls_init 0 ntrd f)).

Definition Binv f n i := (arrays' (val2sh inpp) (ith_vals (dist n) (cvals f) i 0) 1).

Definition BSpre n i :=
  match n with
  | O => (arrays' (val2sh inpp) (ith_vals dist_pre (arr2CUDA inp) i 0 ) 1)
  | S n => Binv (f_sim (S n)) n i
  end.

Definition BSpost n i := Binv (f_sim n) n i.

Definition BS n := (MyVector.init (fun i : Fin.t ntrd => Assn (BSpre n (nf i)) True nil),
                    MyVector.init (fun i : Fin.t ntrd => Assn (BSpost n (nf i)) True nil)).

Lemma reduceBlock_ok n :
  CSL BS tid
      (Assn (BSpre n (nf tid)) True
            ("tid" |-> Zn (nf tid) ::
             "slen" |-> Zn l :: 
             sarr |=> inpp ++
             ys |=> sc2CUDA (f_sim n (nf tid))))
      (reduce_body (S n) (st (S n)))
      (Assn (BSpre (S n) (nf tid)) True
            ("tid" |-> Zn (nf tid) ::
             "slen" |-> Zn l :: 
             sarr |=> inpp ++
             ys |=> sc2CUDA (f_sim (S n) (nf tid)))).
Proof.
  unfold reduce_body, BS.
  cutrewrite (S n - 1 = n); [|omega].
  hoare_forward; eauto.
  unfold BSpost, Binv.
  do 2 hoare_forward.
  - hoare_forward.
    unfold arr2CUDA; rewrite map_length, init_length; lia.
    unfold dist.
    destruct Sumbool.sumbool_and; try lia.
    simplify_remove_var.
    
    

End mkReduce.
