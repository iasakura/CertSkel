# CertSkel: A DSL for Verified GPGPU Programming in Coq

[![wercker status](https://app.wercker.com/status/782385b9d3161dee3e164f316999f6da/m/master "wercker status")](https://app.wercker.com/project/byKey/782385b9d3161dee3e164f316999f6da)

```coq
(* DSL source code: dot product *)
Definition dot (xs ys : list Z) : comp (list Z)
  := do! t <- mapM (fun xy => ret (fst xy * snd xy)) (zip xs ys) in
     reduceM (fun x y => ret (x + y)) t.

(* Compilation by theorem proving: there exists a GPGPU program which is equivalent to the source program *)
Definition dot_fused_GPGPU :
  {p : GModule | @equivGC (Skel.TZ :: Skel.TZ :: nil) (Skel.TZ) dot p}.
Proof.
  unfold dot; simpl.
  (* Reification *)
  reifyFunc.
  eapply equivIC_weaken.
  { (* Fusion transformation *)
    introv Heq; applys (>>simple_fusion_correct Heq).
    repeat econstructor; simpl.
    - intros; omega.
    - intros; omega. }
  (* GPGPU code generation *)
  apply compileOk.
  repeat econstructor; simpl.
  - intros; omega.
  - intros; omega.
Defined.

Definition res := save_to_file (`dot_fused_GPGPU) "./dot_fused.cu".

Cd "extracted".

Separate Extraction res.
```
For more examples, see `./examples`.

## Prerequisite

- Coq 8.7.2
- CUDA toolkit (tested only with CUDA 7.0, 8.0)

## Build

- For CertSkel, run `make`
- For examples, run `make examples`
