(**
  Coq Implementation of
  "A Sound and Complete Abstraction for Reasoning about Parallel Prefix Sums"
 *)

Module Minicuda.
  Require Import ssreflect ssrbool ssrnat eqtype seq.

  (* variable = nat *)
  Inductive var := Var of nat.
  (* (==) のための証明 *)
  Definition var_eq (v1 v2 : var) :=
    match v1, v2 with
      | Var n1, Var n2 => n1 == n2
    end.

  Lemma var_eqP : Equality.axiom var_eq.
  Proof.
    rewrite / Equality.axiom.
    case=>x [] y.
    case: (@eqP _ x y).
    by move=>-> /=; rewrite eq_refl; apply: ReflectT.
    move=>H /=.
    suff: (x == y = false).
    - by move=>->; apply: ReflectF; case.
      by case:eqP.
  Qed.

  Canonical var_eqMixin := EqMixin var_eqP.
  Canonical nat_eqType := EqType var var_eqMixin.

  (* currently, supported type is only nat, bool or array *)
  Inductive type :=
  | Int | Bool.
  Inductive a_type :=
  | Array of type.

  (* operators, carry parameter type and return type  *)
  Inductive op2 : type -> type -> type -> Set :=
  | And : op2 Bool Bool Bool | Or : op2 Bool Bool Bool | Not : op2 Bool Bool Bool
  | Plus : op2 Int Int Int | Mult : op2 Int Int Int | Le : op2 Int Int Bool.

  (* pure expression *)
  Inductive expr := 
  | e_bool of bool 
  | e_nat of nat
  | e_var of var
  | e_arr of var & expr
  | e_op2 : forall {typ1 typ2 typ3}, expr -> op2 typ1 typ2 typ3 -> expr -> expr.

  (* statements *)
  Inductive stmt :=
  | s_var_ass of var & expr
  | s_arr_ass of var & expr & expr
  | s_if of expr & stmts & stmts
  | s_while of expr & stmts
  | s_barrier
  with stmts :=
  | snil
  | sseq of stmt & stmts.

  (* generate induction for stmt and stmts *)
  Scheme stmt_ind' := Induction for stmt Sort Prop
  with   stmts_ind' := Induction for stmts Sort Prop.
  
  Combined Scheme stmt_ind_mul from stmt_ind', stmts_ind'.
  
  (* value *)
  Inductive value :=
  | V_bool of bool
  | V_nat of nat.

  (* array is function of nat to value *)
  Definition array_store := nat -> value.

  (* store, distinguish between normal value and array value *)
  Definition store_v := var -> option value.
  Definition store_a := var -> option array_store.
  
  (* number of threads *)
  Parameter D : nat.

  (* state per threads *)
  Definition local_state  := (store_v * stmts)%type.
  (* thread map *)
  Definition state_map := forall i, i < D -> local_state.

  (* program variable ``tid'' *)
  Definition tid := Var 0.

  (* variable tid is thread number 
  Definition tid_is_tid (m : state_map) :=
    forall (i : nat) (H : i < D), fst (m i H) tid = Some (V_nat i).
   *)
  
  (* kernel is array and local state *)
  Definition kernel_state := (store_a * state_map)%type.

  (* typing context *)
  Definition context := var -> option type.

  (* typing rules for expression *)
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

  (* typing rules for statement *)
  Inductive stmt_typing (g : context) (ga : context) : stmt -> Prop :=
  | T_ass : forall (v : var) (e : expr) (typ : type),
      expr_typing g ga e typ ->
      g v = Some typ ->
      stmt_typing g ga (s_var_ass v e)
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
  | T_barrier : stmt_typing g ga s_barrier
  with stmts_typing (g : context) (ga : context) : stmts -> Prop :=
  | T_nil : stmts_typing g ga snil
  | T_seq : forall (s : stmt) (ss : stmts),
              stmt_typing g ga s -> stmts_typing g ga ss -> stmts_typing g ga (sseq s ss).

  (* generate induction for statement *)
  Scheme stmt_typing_ind' := Induction for stmt_typing Sort Prop
  with   stmts_typing_ind' := Induction for stmts_typing Sort Prop.
  
  Combined Scheme stmt_typing_ind_mul from stmt_typing_ind', stmts_typing_ind'.

  Inductive arr_acc := R | W.
  Definition location := (arr_acc * var * nat)%type.
  
  (* evaluation rule *)
  Reserved Notation "sv '/' sta '/' e '||' '(' v ',' l ')'" (at level 40, sta at level 39, e at level 39, v at level 39).

  Inductive eval_expr (sv : store_v) (sa : store_a) : expr -> value -> list location -> Prop :=
  | E_bool : forall b,  sv / sa / (e_bool b) || (V_bool b,  [::])
  | E_nat : forall n, sv / sa / (e_nat n) || (V_nat n, [::])
  | E_var : forall v val, sv v = Some val ->
                          sv / sa / (e_var v) || (val, [::])
  | E_arr : forall arr a_v e_i idx val ls,
              sa arr = Some a_v ->
              sv / sa / e_i || (V_nat idx, ls) ->
              a_v idx = val ->
              sv / sa / (e_arr arr e_i) || (val, [:: (R, arr, idx) & ls])
  | E_and : forall (e1 e2 : expr) (v1 v2 : bool) l1 l2,
              sv / sa / e1 || (V_bool v1, l1) ->
              sv / sa / e2 || (V_bool v2, l2) ->
              sv / sa / (e_op2 e1 And e2) || (V_bool (andb v1 v2), app l1 l2)
  | E_or : forall (e1 e2 : expr) (v1 v2 : bool) l1 l2,
              sv / sa / e1 || (V_bool v1, l1) ->
              sv / sa / e2 || (V_bool v2, l2) ->
              sv / sa / (e_op2 e1 Or e2) || (V_bool (orb v1 v2), app l1 l2)
  | E_not : forall (e1 e2 : expr) (v1 v2 : bool) l1 l2,
              sv / sa / e1 || (V_bool v1, l1) ->
              sv / sa / e2 || (V_bool v2, l2) ->
              sv / sa / (e_op2 e1 Not e2) || (V_bool (negb v1), app l1 l2)
  | E_plus : forall (e1 e2 : expr) (v1 v2 : nat) l1 l2,
              sv / sa / e1 || (V_nat v1, l1) ->
              sv / sa / e2 || (V_nat v2, l2) ->
              sv / sa / (e_op2 e1 Plus e2) || (V_nat (addn v1 v2), app l1 l2)
  | E_mult : forall (e1 e2 : expr) (v1 v2 : nat) l1 l2,
               sv / sa / e1 || (V_nat v1, l1) ->
               sv / sa / e2 || (V_nat v2, l2) ->
               sv / sa / (e_op2 e1 Mult e2) || (V_nat (muln v1 v2), app l1 l2)
  | E_le : forall (e1 e2 : expr) (v1 v2 : nat) l1 l2,
              sv / sa / e1 || (V_nat v1, l1) ->
              sv / sa / e2 || (V_nat v2, l2) ->
              sv / sa / (e_op2 e1 Le e2) || (V_bool (leq v1 v2), app l1 l2)
  where "sv '/' sta '/' e '||' '(' v ',' l ')'" := (eval_expr sv sta e v l).

  (* typing rule for value *)
  Inductive value_typing : value -> type -> Prop :=
  | TV_bool : forall b, value_typing (V_bool b) Bool
  | TV_nat : forall n, value_typing (V_nat n) Int.

  (* array is well typed ⇔ all elements have same type *)
  Definition array_typing (arr : array_store) (typ : type) : Prop :=
    forall (idx : nat) (v : value), arr idx = v -> value_typing v typ.

  (* store is well typed ⇔ all valid variables are typed *)
  Definition store_typing (g : context) (sv : store_v) :=
    forall (v : var) (typ : type),
      g v = Some typ -> exists val, sv v = Some val /\ value_typing val typ.

  (* store of array is well typed ⇔ all valid variables are typed as array *)
  Definition store_a_typing (ga : context) (sa : store_a) : Prop :=
    forall (v : var) (typ : type),
      ga v = Some typ -> exists arr, sa v = Some arr /\ array_typing arr typ.

  (* progress lemma for expression *)
  Lemma expr_progress (e : expr) (g ga : context) (sv : store_v) (sa : store_a) (typ : type):
    expr_typing g ga e typ -> store_typing g sv -> store_a_typing ga sa ->
    exists (v : value) (l : list location), sv / sa / e || (v, l) /\ value_typing v typ.
  Proof.
    elim.
    - move=>b _ _; exists (V_bool b); exists [::]; split; [apply: E_bool | apply: TV_bool].
    - by move=>n _ _; exists (V_nat n); exists [::]; split; [apply: E_nat | apply: TV_nat].
    - rewrite / store_typing; move=> v ty Hty Hstore _.
      pose H := (Hstore v ty Hty).
      case: H=> val [Hsv Htyp].
      exists val; exists [::]; split; first by apply E_var.
      by done.
    - move=> arr idx typ0 Htyarr Hidx IH Hs Hsa.
      move: (IH Hs Hsa)=> H.
      case: H=> idx_v [l [Hi Hity]].
      inversion Hity; subst.
      case: (Hsa arr typ0 Htyarr)=> arr_v [H' Ha].
      rewrite / array_typing in Ha.
      by exists (arr_v n); exists [:: (R, arr, n) & l]; split; [apply: E_arr | apply: Ha].
    - move=> e1 e2 typ1 typ2 typ3; case;
      move=> Hty1 IH1 Hty2 IH2 Hs Hsa;
      case: (IH1 Hs Hsa)=> v1 [l1 [Hv1 Htyv1]];
      case: (IH2 Hs Hsa)=> v2 [l2 [Hv2 Htyv2]];
      inversion Htyv1; subst; inversion Htyv2; subst.
      + exists (V_bool (andb b b0)); exists (cat l1 l2); split; first by apply: E_and.
        by apply: TV_bool.
      + exists (V_bool (orb b b0)); exists (cat l1 l2); split; first by apply: E_or.
        by apply: TV_bool.
      + exists (V_bool (negb b)); exists (cat l1 l2); split; first by apply: E_not.
        by apply: TV_bool.
      + exists (V_nat (n + n0)); exists (cat l1 l2); split; first by apply: E_plus.
        by apply: TV_nat.
      + exists (V_nat (n * n0)); exists (cat l1 l2); split; first by apply: E_mult.
        by apply: TV_nat.
      + exists (V_bool (leq n n0)); exists (cat l1 l2); split; first by apply E_le.
        by apply: TV_bool.
  Qed.

  (* value update*)
  Definition update_v (var : var) (v : value) (store : store_v) := fun var' =>
    if var' == var then Some v else store var'.

  (* array update *)
  Definition update_a (arr : var) (i : nat) (v : value) (store_a : store_a) := fun arr' =>
    if arr == arr' then
      if store_a arr is Some val_a then
        Some (fun i' => if i' == i then v
                  else val_a i)
      else None
    else store_a arr'.

  (* append sequences *)
  Fixpoint sapp (ss1 ss2 : stmts) :=
    match ss1 with
      | snil => ss2
      | sseq s ss1 => sseq s (sapp ss1 ss2)
    end.

  Reserved Notation "'[' '==>s' '(' stv ',' sta ',' s1 ')'  '(' stv' ',' sta' ',' s2 ')' 'at' loc ']'".
  
  Inductive stmt_step (stv : store_v) (sta : store_a) :
    stmts -> store_v -> store_a -> stmts -> list location -> Prop :=
  | S_Assign : forall (var : var) (e : expr) (val : value) (rest : stmts) l, 
      stv / sta / e || (val, l) ->
      [ ==>s (stv, sta, (sseq (s_var_ass var e) rest))
             ((update_v var val stv), sta, rest) at l]
  | S_Array : forall (e_idx e : expr) (idx : nat) (val : value) (a_var : var) (rest : stmts) lidx lv,
      stv / sta / e_idx || (V_nat idx, lidx) ->
      stv / sta / e     || (val, lv) ->
      [ ==>s (stv, sta, (sseq (s_arr_ass a_var e_idx e) rest))
             (stv, update_a a_var idx val sta, rest) at
             [:: (W, a_var, idx) & lidx ++ lv ]]
  | S_Ife_T : forall (e_cond : expr) (s_then s_else : stmts) (rest : stmts) l,
      stv / sta / e_cond || (V_bool true, l) ->
      [ ==>s (stv, sta, sseq (s_if e_cond s_then s_else) rest)
             (stv, sta, sapp s_then rest) at l]
  | S_Ife_F : forall (e_cond : expr) (s_then s_else rest : stmts) l,
      stv / sta / e_cond || (V_bool false, l) ->
      [ ==>s (stv, sta, sseq (s_if e_cond s_then s_else) rest)
             (stv, sta, sapp s_else rest) at l]
  | S_loop_T : forall (e_cond : expr) (s_body rest : stmts) l,
      stv / sta / e_cond || (V_bool true, l) ->
      [ ==>s (stv, sta, sseq (s_while e_cond s_body) rest)
            (stv, sta, sapp s_body (sseq (s_while e_cond s_body) rest)) at l]
  | S_loop_F : forall (e_cond : expr) (s_body rest : stmts) l,
      stv / sta / e_cond || (V_bool false, l) ->
      [ ==>s (stv, sta, sseq (s_while e_cond s_body) rest)
            (stv, sta, rest) at l]
    where "'[' '==>s' '(' stv ',' sta ',' ss1 ')' '(' stv' ',' sta' ',' ss2 ')' 'at' l ']'" :=
    (stmt_step stv sta ss1 stv' sta' ss2 l).
  
  (* This lemma is true, but barrier
  Lemma stmt_progress (ss : stmts) (g ga : context) (stv : store_v) (sta : store_a) :
    stmts_typing g ga ss -> store_typing g stv -> store_a_typing ga sta ->
    ss = snil \/ exists (stv' : store_v) (sta' : store_a) (ss' : stmts) l,
                   [ ==>s (stv, sta, ss) (stv', sta', ss') at l].
  Proof.
    elim; first by move=> _ _; left.
    move=> s rest.
    elim.
    - move=> var e typ Hety Hgty Htyss IH Htysv Htysa; right. 
      move: (expr_progress e g ga stv sta typ Hety Htysv Htysa)=>[val [Hval Hty]].
      exists (update_v var val stv); exists sta; exists rest.
      by apply: S_Assign.
    - move=> arr_var e_idx e typ HgaT Hidxty Hety Htyss IH Htysv Htysa; right.
      move: (expr_progress e_idx g ga stv sta Int Hidxty Htysv Htysa)=>[v_idx [Hv_idx Hty_idx]].
      move: (expr_progress e g ga stv sta typ Hety Htysv Htysa)=>[v_e [Hv_e Hty_e]].
      inversion Hty_idx; subst.
      exists stv; exists (update_a arr_var n v_e sta); exists rest.
      by apply: S_Array.
    - move=> e_cond s_then s_else Hty_cond Hty_then Hty_else _ _ Htysv Htysa; right.
      move: (expr_progress e_cond g ga stv sta Bool Hty_cond Htysv Htysa)=>[v_cond [Hv_cond Htyv_cond]].
      exists stv; exists sta.
      inversion Htyv_cond as [b_cond H |]; subst.
      case: b_cond Hv_cond {Htyv_cond}.
      + by exists (sapp s_then rest); apply: S_Ife_T.
      + by exists (sapp s_else rest); apply: S_Ife_F.
    - move=> e_cond s_body Hty_cond Hty_body _ _ Htysv Htysa; right.
      exists stv; exists sta.
      move: (expr_progress e_cond g ga stv sta Bool Hty_cond Htysv Htysa)=>[v_cond [Hv_cond Htyv_cond]].
      inversion Htyv_cond as [b_cond H|]; subst.
      case: b_cond Hv_cond {Htyv_cond}.
      + by exists (sapp s_body (sseq (s_while e_cond s_body) rest)); apply S_loop_T.
        by exists rest; apply S_loop_F.
  Abort.
   *)
  
  Lemma expr_deterministic (e : expr) (sv : store_v) (sa : store_a) (v v' : value) l l' :
    sv / sa / e || (v, l) -> sv / sa / e || (v', l') -> v = v'.
  Proof.
    move=> H; move: H v'; elim.
    - by move=> b v' H; inversion H; subst.
    - by move=> n v' H; inversion H; subst.
    - move=> var val Hst v' H; inversion H; subst.
      by rewrite H1 in Hst; case: Hst.
  Abort.

  Definition update_state (m : state_map) (i : nat) (H : i < D) (st : local_state) :=
    fun j (Hj : j < D) =>
      if i == j then st
      else m i H.

  Inductive acc_log := Acc of nat & seq location | Barrier.

  Reserved Notation "'[' '==>k' '(' sta ',' m ')' '(' sta' ',' m' ')' 'at' l ']'".

  Inductive kernel_step : kernel_state -> kernel_state -> acc_log -> Prop :=
  | K_Step : forall (i : nat) (H : i < D) (m : state_map)
                    (sta : store_a)  (stv : store_v) (ss : stmts) 
                    (sta' : store_a) (stv' : store_v) (ss' : stmts) (l : list location),
               m i H = (stv, ss) -> [==>s (stv, sta, ss) (stv', sta', ss') at l] ->
               [ ==>k (sta, m) (sta', update_state m i H (stv', ss')) at Acc i l ]
  | K_Barrier : forall (m : state_map) (m' : state_map) (sta : store_a),
                  (forall (t : nat) (Ht : t < D), exists stv,
                     (exists ss, m  t Ht = (stv, sseq s_barrier ss) /\
                                 m' t Ht = (stv, ss)) \/
                     (m t Ht = (stv, snil) /\ m' t Ht = (stv, snil))) ->
                  (exists (t : nat) (Ht : t < D) (stv : store_v) (ss : stmts),
                     m t Ht = (stv, sseq s_barrier ss)) ->
                  [ ==>k (sta, m) (sta, m') at Barrier ]
    where "'[' '==>k' '(' sta ',' m ')' '(' sta' ',' m' ')' 'at' l ']'" :=
       (kernel_step (sta, m) (sta', m') l).

  Reserved Notation " '[' '==>k*' '(' sta ',' m ')' '(' sta' ',' m' ')' 'log' l ']'".

  Inductive kernel_multi_step : kernel_state -> kernel_state -> list acc_log -> Prop :=
  | KM_Nil : forall (sta : store_a) (m : state_map),
               [ ==>k* (sta, m) (sta, m) log [::] ]
  | KM_Step : forall (sta sta' sta'' : store_a) (m m' m'' : state_map) l l',
               [ ==>k* (sta, m) (sta', m') log l ] -> [ ==>k (sta', m') (sta'', m'') at l'] ->
               [ ==>k* (sta, m) (sta'', m'') log [:: l' & l]]
    where " '[' '==>k*' '(' sta ',' m ')' '(' sta' ',' m' ')' 'log' l ']'" :=
      (kernel_multi_step (sta, m) (sta', m') l).  