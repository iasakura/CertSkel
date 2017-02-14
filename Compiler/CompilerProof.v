Require Import LibTactics assertion_lemmas GPUCSL TypedTerm Monad
        Host DepList CUDALib CSLLemma CSLTactics CodeGen Compiler mkMap mkReduce
        Correctness CodeGenM SeqCompilerProof.

Definition main_spec GA :=
  let ps := gen_params GA in
  let params := flatten_avars (hmap (fun ty x => ((fst (fst x), Int), toPtr (snd x))) ps) in
  {| fs_tag := Hfun; fs_params := map fst params;
     fs_tri := (All (apEnv : APtrEnv GA) (aeEnv : AEvalEnv GA),
                FDbl (kernelInv (remove_typeinfo ps) apEnv aeEnv Emp True nil 1)
                     ((fun _ _ => True) ** (kernelInv (remove_typeinfo ps) apEnv aeEnv Emp True nil 1))) |}.

Lemma compile_map_ok GA dom cod ntrd nblk
      (avenv : AVarEnv GA) (apenv : APtrEnv GA) (aeenv : AEvalEnv GA)
      (f : Skel.Func GA (Skel.Fun1 dom cod))
      (arr : Skel.AE GA dom) (result : Skel.aTypDenote cod)
      xs fns Gp :
  Skel.skelDenote GA cod (Skel.Map GA dom cod f arr) aeenv = Some result
  -> ST_ok (preST xs fns (kernelInv avenv apenv aeenv Emp True nil 1) Gp)
           (compile_map ntrd nblk avenv f arr)
           (fun res => postST xs fns (kernelInv avenv apenv aeenv Emp True nil 1)
                              (Ex ps len, kernelInv avenv apenv aeenv
                                                    (arrays (val2gl ps) (arr2CUDA result) 1%Qc)
                                                    True
                                                    (fst res |-> len :: snd res |=> ps) 1%Qc) Gp nil).
Proof.
  intros Heval.
  unfold compile_map; simpl.
  eapply rule_backward.
  evar (ftri : FTri).
  eapply rule_bind.
  { applys (>>rule_gen_kernel).
    skip. skip.
    intros.
    Definition interp_program_n_simp p fs n :=
      interp_ftri (fs_tri fs) (fun P Q => forall ntrd nblk, CSLg_n ntrd nblk P p Q n).
    Definition interp_program M G p fs :=
      with_ctx M G (fun n => interp_program_n_simp p fs n).

    Lemma interp_fd_kfun M G k fs :
      interp_program M G (body_of k) fs -> interp_kfun M G k fs.
    Proof.
      unfold interp_program, interp_kfun, with_ctx; intros Hsat n Hctx.
      forwards* Hsat': Hsat.
      unfold interp_program_n_simp, interp_kfun_n_simp, CSLkfun_n_simp, CSLg_n in *.
      destruct fs as [? ? ftri]; simpl in *.
      destruct k; simpl in *.
      induction ftri; simpl in *; eauto.
    Qed.
    Lemma mkMap_ok M G GA dom cod arr_c f_c pars tag :
      interp_kfun M G (mkMap GA dom cod arr_c f_c)
                     (FS pars tag
                         (All ntrd nblk avar_env aptr_env aeval_env arr f result eval_map_ok outp outs,
                          FDbl (kernelInv avar_env aptr_env aeval_env (arrays (val2gl outp) outs 1)
                                          True
                                          ("nblk" |-> Zn nblk :: "ntrd" |-> Zn ntrd :: inp_len_name |-> G.Zn
                                                  (Datatypes.length (mkMap.arr_res GA aeval_env dom cod arr f result eval_map_ok)) :: mkMap.outArr cod |=> outp) 1)
                               (kernelInv' aptr_env aeval_env (arrays (val2gl outp) (arr2CUDA result) 1) True 1))).
        apply interp_fd_kfun.
        unfold interp_program, interp_program_n_simp; simpl.
        intros n Hctx ntrd nblk avar_env aptr_env aeval_env arr f result eval_map_ok outp outs.
        introv. 

        Lemma CSLg_CSLg_n ntrd nblk P p Q : CSLg ntrd nblk P p Q -> forall n, CSLg_n ntrd nblk P p Q n.
        Proof. unfold CSLg, CSLg_n; eauto. Qed.
        apply CSLg_CSLg_n.





          

        apply mkMap_prog_ok.

    apply interp_fd_kfun.
    unfold mkMap; simpl.



Theorem compile_AS_ok GA ty ntrd nblk (p : Skel.AS GA ty) :
  let M := compile_prog ntrd nblk p in
  sat_FC M nil (("__main", main_spec GA) :: nil).
Proof.
  admit.
Qed.