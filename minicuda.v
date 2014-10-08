(**
  Coq Implementation of
  "A Sound and Complete Abstraction for Reasoning about Parallel Prefix Sums"
 *)

Module Minicuda.
  Require Import ssreflect ssrbool ssrnat seq.
  
  Inductive var := Var of nat.

  Inductive type :=
  | Int | Bool.
  Inductive a_type :=
  | Array of type.
  
  Inductive op2 : type -> type -> type -> Set :=
  | And : op2 Bool Bool Bool | Or : op2 Bool Bool Bool | Not : op2 Bool Bool Bool
  | Plus : op2 Int Int Int | Mult : op2 Int Int Int | Le : op2 Int Int Bool.

  Inductive expr := 
  | e_bool of bool 
  | e_nat of nat
  | e_var of var
  | e_arr of var & expr
  | e_op2 : forall {typ1 typ2 typ3}, expr -> op2 typ1 typ2 typ3 -> expr -> expr.
  
  Inductive stmt :=
  | s_var_ass of var & expr
  | s_arr_ass of var & expr & expr
  | s_if of expr & stmts & stmts
  | s_while of expr & stmts
  with stmts :=
  | snil
  | sseq of stmt & stmts.

  Scheme stmt_ind' := Induction for stmt Sort Prop
  with   stmts_ind' := Induction for stmts Sort Prop.
  
  Combined Scheme stmt_ind_mul from stmt_ind', stmts_ind'.
  
  Definition context := var -> option type.
  
  Inductive expr_typing (g : context) (ga : context) : expr -> type -> Prop := 
  | T_bool : forall b : bool, expr_typing g ga (e_bool b) Bool
  | T_nat : forall n : nat, expr_typing g ga (e_nat n) Int
  | T_var : forall (v : var) (ty : type), g v = Some ty -> expr_typing g ga (e_var v) ty
  | T_arr : forall (arr : var) (e_i : expr) (typ : type),
              ga arr = Some typ ->
              expr_typing g ga e_i Int ->
              expr_typing g ga (e_arr arr e_i) typ
  | T_op2 : forall (e1 e2  : expr) (typ1 typ2 typ3 : type) (op : op2 typ1 typ2 typ3),
                   expr_typing g ga e1 typ1 -> expr_typing g ga e2 typ2 ->
                   expr_typing g ga (e_op2 e1 op e2) typ3.

  Inductive stmt_typing (g : context) (ga : context) : stmt -> Prop :=
  | T_ass : forall (v : var) (e : expr), stmt_typing g ga (s_var_ass v e)
  | T_arr_ass : forall (v : var) (e1 e2 : expr) (T : type),
      ga v = Some T ->
      expr_typing g ga e1 Int ->
      expr_typing g ga e2 T ->
      stmt_typing g ga (s_arr_ass v e1 e2)
  | T_ite : forall (e : expr) (ss1 ss2 : stmts),
      expr_typing g ga e Bool ->
      stmts_typing g ga ss1 ->
      stmts_typing g ga ss2 ->
      stmt_typing g ga (s_if e ss1 ss2)
  | T_loop : forall (e : expr) (ss : stmts),
      expr_typing g ga e Bool ->
      stmts_typing g ga ss ->
      stmt_typing g ga (s_while e ss)
  with stmts_typing (g : context) (ga : context) : stmts -> Prop :=
  | T_nil : stmts_typing g ga snil
  | T_seq : forall (s : stmt) (ss : stmts),
              stmt_typing g ga s -> stmts_typing g ga ss -> stmts_typing g ga (sseq s ss).

  Inductive value :=
  | V_bool of bool
  | V_nat of nat.

  Definition array_store := nat -> value.
  
  Definition store_v := var -> option value.
  Definition store_a := var -> option (nat -> value).

  Reserved Notation "sv '/' sta '/' e '||' v" (at level 40, sta at level 39, e at level 39, v at level 39).

  Inductive eval_expr (sv : store_v) (sa : store_a) : expr -> value -> Prop :=
  | E_bool : forall b,  sv / sa / (e_bool b) || (V_bool b)
  | E_nat : forall n, sv / sa / (e_nat n) || (V_nat n)
  | E_var : forall v val, sv v = Some val ->
                          sv / sa / (e_var v) || val
  | E_arr : forall arr a_v e_i idx val,
              sa arr = Some a_v ->
              sv / sa / e_i || (V_nat idx) ->
              a_v idx = val ->
              sv / sa / (e_arr arr e_i) || val
  | E_and : forall (e1 e2 : expr) (v1 v2 : bool),
              sv / sa / e1 || (V_bool v1) ->
              sv / sa / e2 || (V_bool v2) ->
              sv / sa / (e_op2 e1 And e2) || (V_bool (andb v1 v2))
  | E_or : forall (e1 e2 : expr) (v1 v2 : bool),
              sv / sa / e1 || (V_bool v1) ->
              sv / sa / e2 || (V_bool v2) ->
              sv / sa / (e_op2 e1 Or e2) || (V_bool (orb v1 v2))
  | E_not : forall (e1 e2 : expr) (v1 v2 : bool),
              sv / sa / e1 || (V_bool v1) ->
              sv / sa / e2 || (V_bool v2) ->
              sv / sa / (e_op2 e1 Not e2) || (V_bool (negb v1))
  | E_plus : forall (e1 e2 : expr) (v1 v2 : nat),
              sv / sa / e1 || (V_nat v1) ->
              sv / sa / e2 || (V_nat v2) ->
              sv / sa / (e_op2 e1 Plus e2) || (V_nat (addn v1 v2))
  | E_mult : forall (e1 e2 : expr) (v1 v2 : nat),
               sv / sa / e1 || (V_nat v1) ->
               sv / sa / e2 || (V_nat v2) ->
               sv / sa / (e_op2 e1 Mult e2) || (V_nat (muln v1 v2))
  | E_le : forall (e1 e2 : expr) (v1 v2 : bool),
              sv / sa / e1 || (V_nat v1) ->
              sv / sa / e2 || (V_nat v2) ->
              sv / sa / (e_op2 e1 Le e2) || (V_nat (leq v1 v2))
  where "sv '/' sta '/' e '||' v" := (eval_expr sv sta e v).

  Inductive value_typing : value -> type -> Prop :=
  | same_bool : forall b, value_typing (V_bool b) Bool
  | same_nat : forall n, value_typing (V_nat n) Int.

  Definition array_typing (arr : array_store) (typ : type) : Prop :=
    forall (idx : nat) (v : value), arr idx = v -> value_typing v typ.

  Definition store_typing (g : context) (sv : store_v) :=
    forall (v : var) (typ : type),
      g v = Some typ -> exists val, sv v = Some val /\ value_typing val typ.

  Definition store_a_typing (ga : context) (sa : store_a) : Prop :=
    forall (v : var) (typ : type),
      ga v = Some typ -> exists arr, sa v = Some arr /\ array_typing arr typ.

  Lemma expr_progress : forall (e : expr) (g ga : context) (sv : store_v) (sa : store_a) (typ : type),
    expr_typing g ga e typ -> store_typing g sv -> store_a_typing ga sa ->
    exists (v : value), sv / sa / e || v.
  Proof.
    move=> e g ga sv sa typ; elim.
    - by move=>b _ _; exists (V_bool b); apply E_bool.
    - by move=>n _ _; exists (V_nat n); apply E_nat.
    - rewrite / store_typing; move=> v ty Hty Hstore _.
      pose H := (Hstore v ty Hty).
      case: H=> val [Hsv _].
      by exists val; apply E_var.
    - move=> arr idx typ0 Htyarr Hidx IH _ Hsa.
  Abort.
  
  Reserved Notation "stv / sta / s1 '==>s' stv' / sta'/ s2" (at level 40).

