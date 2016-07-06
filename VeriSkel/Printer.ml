open Lang
open GCSL
open Host

module SV = Set.Make(struct
  type t = var * coq_CTyp 
  let compare = compare
end)

let (!%) = Printf.sprintf ;;

let var_printer vs = List.fold_right (fun c acc -> Char.escaped c ^ acc) vs "";;

let rec exp_printer = function
  | Evar v -> var_printer v
  | Enum i -> !% "%d" i
  | Eplus (e1, e2) -> !% "(%s + %s)" (exp_printer e1) (exp_printer e2)
  | Emin (e1, e2) -> !% "min(%s, %s)" (exp_printer e1) (exp_printer e2)
  | Eeq (e1, e2) -> !% "(%s == %s)" (exp_printer e1) (exp_printer e2)
  | Emult (e1, e2) -> !% "(%s * %s)" (exp_printer e1) (exp_printer e2)
  | Esub (e1, e2) -> !% "(%s - %s)" (exp_printer e1) (exp_printer e2)
  | Ediv2 e1 -> !% "(%s / 2)" (exp_printer e1)
  | Elt (e1, e2) -> !% "(%s < %s)" (exp_printer e1) (exp_printer e2)
;;

let rec bexp_printer = function
  | Beq (e1, e2) -> !% "(%s == %s)" (exp_printer e1) (exp_printer e2)
  | Blt (e1, e2) -> !% "(%s < %s)" (exp_printer e1) (exp_printer e2)
  | Band (e1, e2) -> !% "(%s && %s)" (bexp_printer e1) (bexp_printer e2)
  | Bnot e1 -> !% "(!%s)" (bexp_printer e1)
;;

let rec loc_exp_printer = function
  | Sh e | Gl e -> exp_printer e
  | Coq_loc_offset (l, e) -> !% "%s[%s]" (loc_exp_printer l) (exp_printer e)
;;

let rec cmd_printer = function
  | Cskip -> ""
  | Cassign (ty, x, e) -> !% "%s = %s;" (var_printer x) (exp_printer e)
  | Cread (ty, x, l) -> !% "%s = %s;" (var_printer x) (loc_exp_printer l)
  | Cwrite (l, e) -> !% "%s = %s;" (loc_exp_printer l) (exp_printer e)
  | Cseq (c1, c2) -> !% "%s\n%s" (cmd_printer c1) (cmd_printer c2)
  | Cif (b, c1, c2) -> !% "if (%s) {\n%s\n} else {\n%s\n}"
     (bexp_printer b) (cmd_printer c1) (cmd_printer c2)
  | Cwhile (b, c) -> !% "while (%s) {\n%s\n}" (bexp_printer b) (cmd_printer c)
  | Cbarrier _ -> "__syncthreads();"
;;

let rec collect_vars = function
  | Cassign (Some ty, x, e) -> SV.singleton (x, ty)
  | Cread (Some ty, x, e) -> SV.singleton (x, ty)
  | Cseq (c1, c2) -> SV.union (collect_vars c1) (collect_vars c2)
  | Cif (b, c1, c2) -> SV.union (collect_vars c1) (collect_vars c2)
  | Cwhile (b, c) -> collect_vars c
  | _ -> SV.empty
;;

let rec ctyp_printer = function
  | Int -> "int"
  | Bool -> "bool"
  | Ptr ty -> ctyp_printer ty ^ "*"

let program_printer p =
  let sdecl = 
    List.map (fun dec ->
      !% "__shared__ %s %s[%d];"
        (ctyp_printer dec.coq_SD_ctyp) (var_printer dec.coq_SD_var) (dec.coq_SD_len)) p.get_sh_decl
    |> String.concat ";\n" in
  let iddec = "int tid = threadIdx.x;\nint bid = blockIdx.x;" in
  !% "%s\n%s\n%s" sdecl iddec (cmd_printer p.get_cmd)
;;

let rec kernel_printer name k = 
  let params =
    List.map (fun (x, cty) -> !% "%s %s" (ctyp_printer cty) (var_printer x)) k.params_of 
    |> String.concat ", " in
  let fvars = SV.diff (collect_vars k.body_of.get_cmd) (SV.of_list (k.params_of @ k.params_of)) in
  let var_decl = List.map (fun (x, ty) -> !%"%s %s;" (ctyp_printer ty) (var_printer x)) (SV.elements fvars)
    |> String.concat "\n" in
  !% "__global__ void %s(%s) {\n%s\n%s\n}"
    name params var_decl (program_printer k.body_of)
;;

let hostVar_printer x = !% "x%d" x;;

let rec expr_printer = function
  | Const n -> !% "%d" n
  | VarE x -> hostVar_printer x
  | Min (x, y) -> !% "min(%s, %s)" (expr_printer x) (expr_printer y)
  | Add (x, y) -> !% "(%s + %s)" (expr_printer x) (expr_printer y)
  | Sub (x, y) -> !% "(%s - %s)" (expr_printer x) (expr_printer y)
  | Div (x, y) -> !% "(%s / %s)" (expr_printer x) (expr_printer y)
;;

let instr_printer = function
  | Coq_alloc (i, e) -> !% "int* %s = alloc(%s)" (hostVar_printer i) (expr_printer e)
  | Coq_iLet (i, e) -> !% "int %s = %s" (hostVar_printer i) (expr_printer e)
  | Coq_invoke (ker, n, m, es) ->
     let args =
       List.map expr_printer es 
       |> String.concat ", " in
     !% "__ker%d<<<%d, %d>>>(%s); cudaDeviceSynchronize();" ker m n args
;;

let instrs_printer is =
    List.fold_left (fun acc e -> acc ^ instr_printer e ^ ";\n") "" is 

let pars_printer pars =
  String.concat "," @@
    List.map (fun (ty, p) -> !% "%s %s" (ctyp_printer ty) (hostVar_printer p)) pars
;;

let cuda_printer {prog_params = pars; prog_hostprog = is; prog_res = (resLen, res); prog_kernels = kers} =
  "#include \"certskel.h\"\n" ^ 
  (List.mapi (fun i -> kernel_printer (!% "__ker%d" i)) kers |> String.concat "\n\n") ^
  !% "\n\nT f(%s) {\n" (pars_printer pars) ^ 
    instrs_printer is ^ "\n" ^
    !% "return makeT(%s, %s);\n" (hostVar_printer resLen) 
    (List.map hostVar_printer res |> String.concat ",") ^
  "}"
;;

let save_to_file res name =
  let out = open_out (var_printer name) in
  output_string out @@ cuda_printer res;
  close_out out
;;
