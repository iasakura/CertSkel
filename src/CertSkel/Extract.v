Require Import Compiler Ext.

Require Import ExtrOcamlBasic ExtrOcamlBigIntConv ExtrOcamlIntConv ExtrOcamlNatBigInt
        ExtrOcamlNatInt  ExtrOcamlString ExtrOcamlZBigInt ExtrOcamlZInt.
Extraction Blacklist List String Int.
(* Extract Inductive list => "([])" ["[]" "(:)"]. *)
(* Extract Inductive bool => "Bool" ["True" "False"]. *)
(* Extract Inductive nat => int ["0" "succ"] "(\fO fS n -> if n == 0 then fO () else fS (n-1))". *)
(* Extract Inductive prod => "(,)" ["(,)"]. *)

Extract Constant save_to_file => "Printer.save_to_file".
