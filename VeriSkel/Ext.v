Require Import Compiler MyEnv SimplSkel.
Require Import List.

Parameter save_to_file :
  (list (Lang.CTyp * Host.hostVar) *
   Host.Prog) ->
  String.string -> 
  unit.