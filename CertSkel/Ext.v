Require Import Compiler MyEnv String.
Require Import List.

Parameter save_to_file :
  Host.Prog -> String.string -> unit.