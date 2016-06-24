Require Import Compiler MyEnv SimplSkel.
Require Import List.

Parameter save_to_file :
  Host.CUDA * (Host.hostVar * list Host.hostVar) * list Host.kernel ->
  String.string -> 
  unit.