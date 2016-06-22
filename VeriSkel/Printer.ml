open Lang
open GCSL
open Host

let (!%) = Printf.sprintf ;;

let var_printer vs = List.fold_right (fun c acc -> Char.escaped c ^ acc) vs "";;

let rec exp_printer = function
  | Evar v -> var_printer v
  | Enum i -> !% "%d" i
  | Eplus (e1, e2) -> !% "(%s) + (%s)" (exp_printer e1) (exp_printer e2)
  | Emin (e1, e2) -> !% "min(%s, %s)" (exp_printer e1) (exp_printer e2)
  | Eeq (e1, e2) -> !% "(%s) == (%s)" (exp_printer e1) (exp_printer e2)
  | Emult (e1, e2) -> !% "(%s) * (%s)" (exp_printer e1) (exp_printer e2)
  | Esub (e1, e2) -> !% "(%s) - (%s)" (exp_printer e1) (exp_printer e2)
  | Ediv2 e1 -> !% "(%s) / 2" (exp_printer e1)
  | Elt (e1, e2) -> !% "(%s) < (%s)" (exp_printer e1) (exp_printer e2)
;;

let rec bexp_printer = function
  | Beq (e1, e2) -> !% "(%s) == (%s)" (exp_printer e1) (exp_printer e2)
  | Blt (e1, e2) -> !% "(%s) < (%s)" (exp_printer e1) (exp_printer e2)
  | Band (e1, e2) -> !% "(%s) && (%s)" (bexp_printer e1) (bexp_printer e2)
  | Bnot e1 -> !% "!(%s)" (bexp_printer e1)
;;

let rec loc_exp_printer = function
  | Sh e | Gl e -> exp_printer e
  | Coq_loc_offset (l, e) -> !% "%s[%s]" (loc_exp_printer l) (exp_printer e)
;;

let rec cmd_printer = function
  | Cskip -> ""
  | Cassign (x, e) -> !% "%s = %s" (var_printer x) (exp_printer e)
  | Cread (x, l) -> !% "%s = %s" (var_printer x) (loc_exp_printer l)
  | Cwrite (l, e) -> !% "%s = %s" (loc_exp_printer l) (exp_printer e)
  | Cseq (c1, c2) -> !% "%s;\n%s" (cmd_printer c1) (cmd_printer c2)
  | Cif (b, c1, c2) -> !% "if (%s) {%s} {%s}" (bexp_printer b) (cmd_printer c1) (cmd_printer c2)
  | Cwhile (b, c) -> !% "while (%s) {%s}" (bexp_printer b) (cmd_printer c)
  | Cbarrier _ -> "__syncthreads()"
;;

let program_printer p =
  let sdecl =
    List.fold_left (fun acc (x, n) ->
      acc ^ "\n" ^ !% "__shared__ %s[%d];\n" (var_printer x) n) "" p.get_sh_decl in
  !% "%s\n%s" sdecl (cmd_printer p.get_cmd)
;;

let rec kernel_printer k = 
  let params =
    (List.fold_left (fun acc x -> acc ^ ", " ^ (var_printer x)) " " k.params_of) in
    !% "__global__ void (%s) {%s}" params (program_printer k.body_of)
;;

let hostVar_printer x = !% "x%d" x;;

let expr_printer = function
  | Const n -> !% "%d" n
  | VarE x -> hostVar_printer x
;;

let instr_printer = function
  | Coq_alloc (i, e) -> !% "%s = alloc(%s)" (hostVar_printer i) (expr_printer e)
  | Coq_iLet (i, e) -> !% "%s = %s" (hostVar_printer i) (expr_printer e)
  | Coq_invoke (ker, n, m, es) -> 
     let args = List.fold_left (fun acc e -> acc ^ ", " ^ expr_printer e) "" es in
     !% "ker%d<<<%d, %d>>>(%s)" ker n m args
;;

let instrs_printer is =
    List.fold_left (fun acc e -> acc ^ instr_printer e ^ ";\n") "" is 

let cuda_printer ((is, (resLen, res)), kers) = 
  "??? f() {\n" ^
    instrs_printer is ^ "\n" ^
    !% "return (%s, %s);\n" (hostVar_printer resLen) 
      (List.fold_left (fun acc e -> acc ^ ", " ^ hostVar_printer e) "" res) ^
  "}\n\n" ^
  List.fold_left (fun acc k -> acc ^ "\n" ^ kernel_printer k) "" kers 
;;

let () =
  let file = Sys.argv.(1) in
  let out = open_out file in
  output_string out @@
    cuda_printer (Compiler.(compile_prog aty_env ntrd nblk 2 avar_env prog));
  close_out out
;;
