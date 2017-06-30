Require Import Monad SkelLib Computation ZArith TypedTerm Program.
Require Import Compiler Ext Extract Host CompilerProof LibTactics.
Open Scope Z_scope.

Require Import DepList.
Import Skel.

Definition dot_fused_IR : AS (TZ :: TZ :: nil) TZ :=
  ALet _ _ _ (
    Reduce _ _  (F2 _ TZ TZ TZ (EBin _ _ _ _ _ Eplus (EVar _ _ _ (HNext HFirst)) (EVar _ _ _ HFirst)))
      (DArr _ _ (F1 _ TZ TZ (EBin _ _ _ _ _ Emult 
                                  (EA _ _ _ (HNext HFirst) (EVar _ _ _ HFirst) )
                                  (EA _ _ _ HFirst (EVar _ _ _ HFirst)))) (LLen _ _ HFirst))
  ) (
  ARet _ _ HFirst).

Goal False.
  pose (asDenote _ _ dot_fused_IR) as D.
  simpl in D.
Abort.

Definition res := save_to_file (compile_prog 1024 24 dot_fused_IR) "./dot_fused.cu".

Cd "extracted".

Separate Extraction res.