
module Formula = AtlasFormula
module Id = AtlasFormula.Id
module Expr = AtlasFormula.Expr
open !Formula

(** Substitution expression *)
type subst_expr = Var of Id.t | Ptr of { base: Id.t ; offset: Int64.t }

(** State status *)
type status = Ok | Error of IssueType.t option * Location.t * Sil.instr

(** Abstract state *)
type t = {
  current: Formula.t;             (** Current part of formula *)
  missing: Formula.t;             (** Missing part of formula *)
  vars: Var.t VarIdMap.t;      (** Sil variable map *)
  types: Typ.t VarIdMap.t;        (** Type map *)
  subst: subst_expr VarIdMap.t;   (** Substitution map *)
  status: status;                 (** State status *)
}

(** Empty state *)
let empty_ = {
  current = Formula.empty;
  missing = Formula.empty;
  vars = VarIdMap.empty;
  types = VarIdMap.empty;
  subst = VarIdMap.empty;
  status = Ok;
}

(** State initialized with local, formal, return variables and their types *)
let rec empty analysis =
  let open IntraproceduralAnalysis in
  let open ProcAttributes in
  let s = empty_ in
  let proc_name = Procdesc.get_proc_name analysis.proc_desc in
  let locals = Procdesc.get_locals analysis.proc_desc in
  let formals = Procdesc.get_pvar_formals analysis.proc_desc in
  let ret_var = Procdesc.get_ret_var analysis.proc_desc in
  let ret_typ = Procdesc.get_ret_type analysis.proc_desc in
  let with_locals = List.fold ~init:s locals
    ~f:(fun state var -> 
      let pvar = Pvar.mk var.name proc_name in
      add_variable pvar var.typ state)
  in
  let with_formals = List.fold ~init:with_locals formals
    ~f:(fun state (pvar, typ) ->
      add_variable pvar typ state)
  in
  { with_formals with 
    vars = VarIdMap.add 0 (Var.of_pvar ret_var) with_formals.vars;
    types = VarIdMap.add 0 ret_typ with_formals.types }

(** Adds variable [v] with type [t] into state [s]. If [id] is present, it is used, otherwise a fresh id is generated *)
and add_variable ?id v t s =
  let id' = match id with
  | Some id -> id
  | None -> Id.fresh ()
  in
  { s with 
    vars = VarIdMap.add id' (Var.of_pvar v) s.vars;
    types = VarIdMap.add id' t s.types }


(* ==================== equality substitution helpers ==================== *)

(** Searches for the canonical [Id.t] of SIL variable [v] by looking it up in [s.vars]
    and following the substitution chain to its root *)
let rec get_canonical_var_id v s =
  match Formula.lookup_variable_id v s.vars with
  | None -> None
  | Some id -> Some (canonical_id s.subst id)

(** Follows the substitution chain from [id] to its canonical root [Id.t] *)
and canonical_id subst id =
  match VarIdMap.find_opt id subst with
  | None -> id
  | Some Var id' -> canonical_id subst id'
  | Some Ptr { base } -> canonical_id subst base

(** Searches for the canonical [subst_expr] of SIL variable [v], following substitution chains
    and accumulating pointer offsets *)
let rec get_canonical_expr v s =
  match Formula.lookup_variable_id v s.vars with
  | None -> None
  | Some id -> Some (canonical_expr s.subst id 0L)

(** Follows the substitution chain from [id], accumulating [rel_offset] through [Ptr] nodes.
    Returns [Var id] if offset is zero, or [Ptr { base; offset }] otherwise *)
and canonical_expr subst id rel_offset =
  match VarIdMap.find_opt id subst with
  | None ->
    if Int64.equal rel_offset 0L then
      Var id
    else
      Ptr { base = id; offset = rel_offset }
  | Some Var id' -> canonical_expr subst id' rel_offset
  | Some Ptr { base; offset } ->
    let abs_offset = Stdlib.Int64.add rel_offset offset in
    canonical_expr subst base abs_offset

(** Converts a [subst_expr] to its [Expr.t] representation *)
let subst_expr_to_formula_expr = function
  | Var id -> Expr.Var id
  | Ptr { base; offset } -> Expr.BinOp (Pplus, Var base, Const (Int offset))

(** Applies substitution [~from_] [~to_] over current and missing parts of [state].
    If [~to_] expression is found within a pure constraint or a heap predicate, a synthetic variable will take it's place *)
let subst_apply ~from_ ~to_ state =
  let current_pure = subst_apply_to_pure ~from_:from_ ~to_:to_ state.current.pure in
  let missing_pure = subst_apply_to_pure ~from_:from_ ~to_:to_ state.missing.pure in
  let current_spatial = subst_apply_to_spatial ~from_:from_ ~to_:to_ state.current.spatial in
  let missing_spatial = subst_apply_to_spatial ~from_:from_ ~to_:to_ state.missing.spatial in
  { state with 
    current = { pure = current_pure; spatial = current_spatial };
    missing = { pure = missing_pure; spatial = missing_spatial} }

(** Prepares [state] for an address substitution targeting [id].
    Must be called before [subst_apply] when [id] is being reassigned to a new address.
    Two-step process:
    1. Removes stale [Base(id)==0] and [End(id)==0] constraints from both current and
       missing pure — these were set on declaration and are no longer true after assignment.
       New Base/End constraints will be established by the subsequent substitution.
    2. Replaces all remaining occurrences of [Var id] in the formula with a fresh placeholder
       variable via [subst_apply]. This preserves references to the old value of [id]
       (e.g. memory that was reachable through [id] but not yet freed) so the formula
       stays satisfiable after [id] is rebound to a new address. *)
let clear_before_subst id state =
  let is_base_or_end_zero_expr = function
    | Expr.BinOp (Peq, UnOp (Base, Var id'), Const (Int 0L))
      when Id.equal id id' -> true
    | Expr.BinOp (Peq, UnOp (End, Var id'), Const (Int 0L))
      when Id.equal id id' -> true
    | _ -> false
  in
  let current_pure = List.filter
    ~f:(fun exp -> not (is_base_or_end_zero_expr exp))
    state.current.pure
  in
  let missing_pure = List.filter
    ~f:(fun exp -> not (is_base_or_end_zero_expr exp))
    state.missing.pure
  in
  let state = { state with
    current = { state.current with pure = current_pure };
    missing = { state.missing with pure = missing_pure } }
  in
  let placeholder = Id.fresh () in
  subst_apply ~from_:(Expr.Var id) ~to_:(Expr.Var placeholder) state


(* ==================== Exp.t helpers ==================== *)

(** Checks whether SIL [Exp.t] suggests a dereference (contains a temporary variable [Exp.Var]) *)
let rec is_sil_dereference exp =
  match Exp.ignore_cast exp with
    Exp.Var _ ->
      true
  | Exp.Lfield ({ exp = e }, _, _) ->
    is_sil_dereference e
  | Exp.Lindex (e, _) ->
    is_sil_dereference e
  | Exp.UnOp (_, e, _) ->
    is_sil_dereference e
  | Exp.BinOp (_, e1, e2) ->
    is_sil_dereference e1 ||
    is_sil_dereference e2
  | _ ->
    false

(** Checks whether SIL [Exp.t] suggests an address assignment (contains a program variable [Exp.Lvar]) *)
let rec is_sil_address_assign exp =
  match Exp.ignore_cast exp with
  | Exp.Lvar _ ->
    true
  | Exp.Lfield ({ exp = e }, _, _) ->
    is_sil_address_assign e
  | Exp.Lindex (e, _) ->
    is_sil_address_assign e
  | Exp.UnOp (_, e, _) ->
    is_sil_address_assign e
  | Exp.BinOp (_, e1, e2) ->
    is_sil_address_assign e1 ||
    is_sil_address_assign e2
  | _ ->
    false

(* ==================== Expr.t helpers ==================== *)

(** Extracts the single pointer-typed variable id and its evaluated byte offset from [expr].
    Filters variable ids by pointer type in [state.types]. Returns [None] if zero or multiple
    pointer variables are found. Used during dereference to identify the base pointer *)
let rec base_and_offset_of_expr expr state =
  let var_ids = variable_ids_of_expr expr in
  let pointers = List.filter var_ids
    ~f:(fun id ->
      match VarIdMap.find_opt id state.types with
      | Some t -> is_pointer_type t
      | None -> false)
  in
  match pointers with
  | [base] ->
    Some (base, eval_expr_offset expr base state)
  | _ ->
    None

(** Determines whether provided type [t] is a C pointer *)
and is_pointer_type t =
  let open Typ in
  match t.desc with
  | Typ.Tptr _ -> true
  | Typ.Tarray { elt } -> is_pointer_type elt
  | _ -> false

(** Extracts all variable ids from given [expr] *)
and variable_ids_of_expr expr =
  let rec extract ids = function
    | Expr.Undef -> ids
    | Expr.Var id -> id :: ids
    | Expr.Const _ -> ids
    | Expr.UnOp (_, e) -> extract ids e
    | Expr.BinOp (_, e1, e2) ->
      let ids = extract ids e1 in
      extract ids e2
  in
  extract [] expr

(** Evaluates the byte offset of [expr] relative to base variable [skip_id].
    Skips [skip_id] itself during evaluation, resolves other variables through
    pure constraints, and computes arithmetic. Falls back to 0L for unresolvable parts *)
and eval_expr_offset expr skip_id state =
  let lookup_pure id =
    Formula.lookup_pure_const_exp_of_id id state.current.pure
  in
  let rec eval off = function
    | Expr.Undef -> off
    | Expr.Var id when Id.equal id skip_id -> off
    | Expr.Var id ->
      begin match lookup_pure id with
      | Some e -> eval off (normalize_expr e state)
      | None -> off
      end
    | Expr.Const (Int i) -> Stdlib.Int64.add off i
    | Expr.Const _ -> off
    | Expr.UnOp (op, e) ->
      let inner = eval 0L e in
      begin match op with
      | Puminus ->
        Stdlib.Int64.sub off inner
      | Lnot | BVnot | Base | End | Freed -> off
      end
    | Expr.BinOp (op, e1, e2) ->
      let lhs = eval 0L e1 in
      let rhs = eval 0L e2 in
      let res = match op with
        | Pplus ->
          Stdlib.Int64.add lhs rhs
        | Pminus ->
          Stdlib.Int64.sub lhs rhs
        | Pmult ->
          Stdlib.Int64.mul lhs rhs
        | Pdiv when (Int64.compare rhs 0L) <> 0 ->
          Stdlib.Int64.div lhs rhs
        | Pmod when (Int64.compare rhs 0L) <> 0 ->
          Stdlib.Int64.rem lhs rhs
        | BVlshift | BVrshift
        | Pless | Plesseq | Peq | Pneq
        | BVand | BVor | BVxor
        | Land | Lor | _ -> 0L
      in
      Stdlib.Int64.add off res
  in
  eval 0L (normalize_expr expr state)

(** Normalizes [expr] by folding constant arithmetic, eliminating identity operations
    (e.g. x+0, x*1), and simplifying double negation. Does not resolve variables *)
and normalize_expr expr _state =
  let open Expr in 
  let norm = normalize_expr in
  match expr with
    Var _ | Const _ | Undef ->
      expr
  | UnOp (op, e) ->
    let e' = norm e _state in
    begin match op, e' with
      Puminus, Const (Int i) ->
      Const (Int (Int64.neg i))
    | Lnot, Const (Int i) ->
      Const (Int (if (Int64.compare i 0L) <> 0 then 0L else 1L))
    | BVnot, Const (Int i) ->
      Const (Int (Stdlib.Int64.lognot i))
    | Puminus, UnOp (Puminus, e_inner) ->
      e_inner
    | _ ->
      UnOp (op, e')
    end
  | BinOp (op, e1, e2) ->
    let e1' = norm e1 _state in
    let e2' = norm e2 _state in
    begin match op, e1, e2 with
      Pplus, Const (Int i1), Const (Int i2) ->
      Const (Int (Stdlib.Int64.add i1 i2))
    | Pminus, Const (Int i1), Const (Int i2) ->
      Const (Int (Stdlib.Int64.sub i1 i2))
    | Pmult, Const (Int i1), Const (Int i2) ->
      Const (Int (Stdlib.Int64.mul i1 i2))
    | Pdiv, Const (Int i1), Const (Int i2)
      when (Int64.compare i2 0L) <> 0 ->
      Const (Int (Stdlib.Int64.div i1 i2))
    | Pmod,   Const (Int i1), Const (Int i2)
      when (Int64.compare i2 0L) <> 0 ->
      Const (Int (Int64.rem i1 i2))

    | Pplus, e, Const (Int 0L)
    | Pplus, Const (Int 0L), e ->
      e
    | Pminus, e, Const (Int 0L) ->
      e
    | Pmult, e, Const (Int 1L)
    | Pmult, Const (Int 1L), e ->
      e
    | Pmult, _, Const (Int 0L)
    | Pmult, Const (Int 0L), _ ->
      Const (Int 0L)

    | Land, Const (Int 0L), _
    | Land, _, Const (Int 0L) ->
      Const (Int 0L)
    | Lor, Const (Int 1L), _
    | Lor, _, Const (Int 1L) ->
      Const (Int 1L)

    | _ ->
      BinOp (op, e1', e2')
    end

(** Evaluates [expr] to Int64, resolving variables through pure constraints.
    Handles arithmetic operations (+, -, *, /, %), unary minus, and normalizes first.
    Returns [None] if any subexpression cannot be fully resolved *)
let eval_expr_to_int64_opt expr state =
  let lookup_pure id =
    Formula.lookup_pure_const_exp_of_id id state.current.pure
  in
  let rec eval = function
    | Expr.Const (Int i) -> Some i
    | Expr.Var id ->
      begin match lookup_pure id with
      | Some e -> eval (normalize_expr e state)
      | None -> None
      end
    | Expr.UnOp (Puminus, e) ->
      Option.map (eval e) ~f:Stdlib.Int64.neg
    | Expr.BinOp (Pplus, e1, e2) ->
      Option.bind (eval e1) ~f:(fun v1 ->
      Option.map (eval e2) ~f:(fun v2 ->
        Stdlib.Int64.add v1 v2))
    | Expr.BinOp (Pminus, e1, e2) ->
      Option.bind (eval e1) ~f:(fun v1 ->
      Option.map (eval e2) ~f:(fun v2 ->
        Stdlib.Int64.sub v1 v2))
    | Expr.BinOp (Pmult, e1, e2) ->
      Option.bind (eval e1) ~f:(fun v1 ->
      Option.map (eval e2) ~f:(fun v2 ->
        Stdlib.Int64.mul v1 v2))
    | Expr.BinOp (Pdiv, e1, e2) ->
      Option.bind (eval e1) ~f:(fun v1 ->
      Option.bind (eval e2) ~f:(fun v2 ->
        if Int64.equal v2 0L then None
        else Some (Stdlib.Int64.div v1 v2)))
    | Expr.BinOp (Pmod, e1, e2) ->
      Option.bind (eval e1) ~f:(fun v1 ->
      Option.bind (eval e2) ~f:(fun v2 ->
        if Int64.equal v2 0L then None
        else Some (Stdlib.Int64.rem v1 v2)))
    | _ -> None
  in
  eval (normalize_expr expr state)


(* ==================== pure constraint helpers ==================== *)

(** Traverses both current and missing pure constraints of [state], looking for ([unop](Var [id])==exp)
    Returns (Some exp, is_current) | None *)
let lookup_pure_unop_eq_expr id unop state =
  match unop with
  | Expr.Base ->
    begin match Formula.lookup_pure_base_expr id state.current.pure with
    | Some b -> Some (b, true)
    | None ->
      begin match Formula.lookup_pure_base_expr id state.missing.pure with
      | Some b -> Some (b, false)
      | None -> None
      end
    end
  | Expr.End ->
    begin match Formula.lookup_pure_end_expr id state.current.pure with
    | Some b -> Some (b, true)
    | None ->
      begin match Formula.lookup_pure_end_expr id state.missing.pure with
      | Some b -> Some (b, false)
      | None -> None
      end
    end
  | _ -> None

(** Traverses both current and missing pure constraints of [state], looking for (Freed(Var [id])) *)
let is_freed_expr id state =
  let curr_freed, miss_freed =
    Formula.has_freed_expr id state.current.pure,
    Formula.has_freed_expr id state.missing.pure
  in
  curr_freed || miss_freed

(** Assigns [rhs_expr] to [lhs_expr] during store dereference.
    For non-pointer types: adds (lhs == rhs) equality and zero Base/End constraints to pure.
    For pointer types: delegates to [store_dereference_address_assign] which updates substitutions.
    Targets current or missing formula based on [to_missing] *)
let rec store_dereference_assign ?to_missing:(to_missing=false) state lhs_typ lhs_id lhs_expr rhs_expr =
  let types = VarIdMap.add lhs_id lhs_typ state.types in
  if is_pointer_type lhs_typ then
    store_dereference_address_assign { state with types } lhs_id lhs_expr rhs_expr
  else
    let pure_part =
      Expr.BinOp (Peq, lhs_expr, rhs_expr) ::
      Expr.BinOp (Peq, UnOp (Base, Var lhs_id), Const (Int 0L)) ::
      [ Expr.BinOp (Peq, UnOp (End, Var lhs_id), Const (Int 0L)) ]
    in
    let pure = List.append
      pure_part
      (if to_missing then state.missing.pure else state.current.pure)
    in
    if to_missing then
      { state with types; missing = { state.missing with pure } }
    else
      { state with types; current = { state.current with pure } }

(** Handles pointer-typed store dereference. Extracts the RHS base+offset,
    canonicalizes it, then calls [clear_before_subst] on [lhs_id] to remove stale
    Base/End==0 constraints and preserve old references via a placeholder.
    Finally applies the substitution so the RHS expression maps to the LHS *)
and store_dereference_address_assign state lhs_id lhs_expr rhs_expr =
  match base_and_offset_of_expr rhs_expr state with
  | Some (rhs_id, rhs_offset) ->
    let rhs_canonical = canonical_expr state.subst rhs_id rhs_offset in
    let rhs_norm = normalize_expr (subst_expr_to_formula_expr rhs_canonical) state in
    let lhs_norm = normalize_expr lhs_expr state in
    let state = clear_before_subst lhs_id state in
    subst_apply ~from_:rhs_norm ~to_:lhs_norm state
  | None ->
    Logging.die InternalError
      "[Error] store_dereference_address_assign - failed to found base pointer variable"


(* ==================== heap predicate helpers ==================== *)

type block_split_args = { to_remove: heap_pred ; to_add: heap_pred list ; new_dest_id: Id.t }

(** Intermediate result of block splitting *)
type block_split_res =
  | ExpExactMatch of { block_split_args: block_split_args ; old_dest: Expr.t } (* new cell matched some existing ExpPointsTo with destination expression *)
  | BlockExactMatch of block_split_args (* new cell matched exactly some BlockPointsTo | UniformBlockPointsTo *)
  | BlockEdgeMatch of block_split_args (* new cell matched the edge of some BlockPointsTo | UniformBlockPointsTo *)
  | BlockMiddleMatch of block_split_args (* new cell matched the middle of some BlockPointsTo | UniformBlockPointsTo *)

(** Result of heap match (used by load dereference) *)
type heap_match_res =
  | MatchExpExact of { matched: heap_pred; dest: Expr.t } (* exact ExpPointsTo match, dest is the existing value *)
  | MatchBlockSplit of block_split_res (* block contains our cell, needs splitting *)

(** Attempts to split a heap predicate from [hps] to carve out a cell at [lhs_var_id]+[lhs_offset]
    of size [cell_size]. Tries in order: exact ExpPointsTo match, exact block match,
    left edge match, right edge or middle match. Creates a fresh destination id for the new cell.
    Returns [Some block_split_res] with the matched predicate to remove and new predicates to add *)
let heap_try_block_split hps lhs_var_id lhs_offset cell_size =
  let eval_exp_exact_match to_remove src size dest =
    let new_dest_id = Id.fresh () in
    let to_add = 
      [ ExpPointsTo (src, size, Expr.Var (new_dest_id)) ]
    in
    let block_split_args =
      { to_remove; to_add; new_dest_id }
    in 
    Some (ExpExactMatch { block_split_args; old_dest = dest })
  in
  let try_exp_exact_match hp src size dest =
    match src, size with
    | Expr.BinOp (Pplus, Var _, Const (Int off)),
      Expr.Const (Int size')
        when Int64.equal off lhs_offset &&
          Int64.equal size' cell_size ->
            eval_exp_exact_match hp src size dest
    | Expr.Var _,
      Expr.Const (Int size')
        when Int64.equal 0L lhs_offset &&
          Int64.equal size' cell_size ->
            eval_exp_exact_match hp src size dest
    | _ -> None
  in
  let eval_block_exact_match to_remove =
    let new_dest_id = Id.fresh () in
    let to_add = [
      ExpPointsTo (
        Expr.BinOp (Pplus, Var lhs_var_id, Const (Int lhs_offset)),
        Expr.Const (Int cell_size),
        Expr.Var new_dest_id) ]
    in
    Some (BlockExactMatch { to_remove; to_add; new_dest_id})
  in
  let try_block_exact_match hp src size =
    match src, size with
    | Expr.BinOp (Pplus, Var _, Const (Int off)),
      Expr.Const (Int size)
        when Int64.equal off lhs_offset &&
          Int64.equal size cell_size ->
            eval_block_exact_match hp
    | Expr.Var _,
      Expr.Const (Int size)
        when Int64.equal 0L lhs_offset && 
          Int64.equal size cell_size ->
            eval_block_exact_match hp
    | _ -> None
  in
  let eval_block_left_edge_match to_remove fragment_size =
    let new_dest_id = Id.fresh () in
    let to_add = [
      ExpPointsTo (
        Expr.BinOp (Pplus, Var lhs_var_id, Const (Int lhs_offset)),
        Expr.Const (Int cell_size),
        Expr.Var new_dest_id) ;
      BlockPointsTo (
        Expr.BinOp (Pplus, Var lhs_var_id, Const (Int (Stdlib.Int64.add lhs_offset cell_size))),
        Expr.Const (Int (Stdlib.Int64.sub fragment_size cell_size))) ]
    in
    Some (BlockEdgeMatch { to_remove; to_add; new_dest_id })
  in
  let try_block_left_edge_match hp src size =
    match src, size with
    | Expr.BinOp (Pplus, Var _, Const (Int off)),
      Expr.Const (Int size)
        when Int64.equal off lhs_offset &&
          (Int64.compare size cell_size ) >= 0 ->
            eval_block_left_edge_match hp size
    | Expr.Var _,
      Expr.Const (Int size)
        when Int64.equal 0L lhs_offset &&
          (Int64.compare size cell_size ) >= 0 ->
            eval_block_left_edge_match hp size
    | _ -> None
  in
  let eval_block_right_edge_or_middle_match to_remove fragment_size fragment_offset =
    let new_dest_id = Id.fresh () in
    let to_add_new_cell = ExpPointsTo (
      Expr.BinOp (Pplus, Var lhs_var_id, Const (Int lhs_offset)),
      Expr.Const (Int cell_size),
      Expr.Var new_dest_id)
    in
    let to_add_left_block = BlockPointsTo (
      Expr.BinOp (Pplus, Var lhs_var_id, Const (Int fragment_offset)),
      Expr.Const (Int (Stdlib.Int64.sub lhs_offset fragment_offset)))
    in
    let lef_and_middle_size =
      Stdlib.Int64.add (Stdlib.Int64.sub lhs_offset fragment_offset) cell_size
    in
    if (Int64.compare fragment_size lef_and_middle_size) > 0 then
      let to_add = [
        to_add_new_cell;
        to_add_left_block;
        BlockPointsTo (
          Expr.BinOp (Pplus, Var lhs_var_id, Const (Int (Stdlib.Int64.add lhs_offset fragment_offset))),
          Expr.Const (Int (Stdlib.Int64.sub fragment_size lef_and_middle_size))) ]
      in
      Some (BlockMiddleMatch { to_remove; to_add; new_dest_id })
    else
      let to_add = [ to_add_new_cell; to_add_left_block ] in
      Some (BlockEdgeMatch { to_remove; to_add; new_dest_id })
  in
  let try_block_right_edge_or_middle_match hp src size =
    match src, size with
    | Expr.BinOp (Pplus, Var _, Const (Int off)),
      Expr.Const (Int size)
        when (Int64.compare size (Stdlib.Int64.add cell_size (Stdlib.Int64.sub lhs_offset off))) >= 0 ->
          eval_block_right_edge_or_middle_match hp size off
    | Expr.Var _,
      Expr.Const (Int size)
        when (Int64.compare size (Stdlib.Int64.add cell_size lhs_offset)) >= 0 ->
          eval_block_right_edge_or_middle_match hp size 0L
    | _ -> None
  in
  let rec try_block_split = function
    | [] -> None
    | (ExpPointsTo (src, size, dest)) as hp :: rest ->
      begin match try_exp_exact_match hp src size dest with
      | Some res -> Some res
      | None -> try_block_split rest
      end
    | (BlockPointsTo (src, size)) as hp :: rest ->
      begin match try_block_exact_match hp src size with
      | Some res -> Some res
      | None -> begin match try_block_left_edge_match hp src size with
        | Some res -> Some res
        | None -> begin match try_block_right_edge_or_middle_match hp src size with
          | Some res -> Some res
          | None -> try_block_split rest
          end
        end
      end
    | _ :: rest -> try_block_split rest
  in
  try_block_split hps

(** Traverses heap predicates [hps], looking for a match at [var_id]+[offset] of size [cell_size].
    First tries to find an exact ExpPointsTo match (same offset and size), returning its destination directly.
    If no exact match, falls back to block splitting via [heap_try_block_split]. *)
let heap_try_match hps var_id offset cell_size =
  let try_exp_exact_match hp src size dest =
    match src, size with
    | Expr.BinOp (Pplus, Var _, Const (Int off)),
      Expr.Const (Int size')
        when Int64.equal off offset &&
          Int64.equal size' cell_size ->
            Some (MatchExpExact { matched = hp; dest })
    | Expr.Var _,
      Expr.Const (Int size')
        when Int64.equal 0L offset &&
          Int64.equal size' cell_size ->
            Some (MatchExpExact { matched = hp; dest })
    | _ -> None
  in
  let rec try_match = function
    | [] -> None
    | (ExpPointsTo (src, size, dest)) as hp :: rest ->
      begin match try_exp_exact_match hp src size dest with
      | Some res -> Some res
      | None -> try_match rest
      end
    | _ :: rest -> try_match rest
  in
  match try_match hps with
  | Some _ as res -> res
  | None ->
    match heap_try_block_split hps var_id offset cell_size with
    | Some split_res -> Some (MatchBlockSplit split_res)
    | None -> None

(** Traverses both current and missing heap predicates of [state], looking for:
    ExpPointsTo (src, size, _) | BlockPointsTo (src, size) | UniformBlockPointsTo (src, size, _)
    where src = (Var [var_id] + (num <= [var_offset])) and size >= [cell_size].
    Resulting lists are ordered by src offset descending *)
let heap_find_block_fragments state var_id var_offset cell_size =
  let current, current_rest = Formula.heap_find_block_fragments
    state.current.spatial var_id var_offset cell_size
  in
  let missing, missing_rest = Formula.heap_find_block_fragments
    state.missing.spatial var_id var_offset cell_size
  in
  let sorted_current =
    Formula.sort_heap_preds_by_offset_desc current
  in
  let sorted_missing =
    Formula.sort_heap_preds_by_offset_desc missing
  in
  sorted_current, current_rest, sorted_missing, missing_rest


(* ==================== Exp.t -> Expr.t conversion ==================== *)

(** Converts SIL Exp.t [e] to custom Expr.t interpretation.
    If a known variable is encountered, it's canonical Id
    is used in the conversion. If the variable is unknown,
    it is converted as Expr.Undef *)
let rec sil_exp_to_expr ?typ e tenv s =
  match e with
    Exp.Cast (_, inner) -> sil_exp_to_expr inner tenv s
  | Exp.Const c -> sil_const_exp_to_expr c
  | Exp.Sizeof sz -> sil_sizeof_exp_to_expr sz
  | Exp.Lvar pvar -> begin match
    get_canonical_expr (Var.of_pvar pvar) s with
    | Some exp -> subst_expr_to_formula_expr exp
    | None ->
      if Pvar.is_return pvar then Expr.ret
      else Expr.Undef (* TODO could be a global variable *)
    end
  | Exp.Var ident -> begin match
    get_canonical_expr (Var.of_id ident) s with
    | Some exp -> subst_expr_to_formula_expr exp
    | None -> Expr.Undef
    end
  | Exp.UnOp (op, exp, _) ->
    let exp' = sil_exp_to_expr exp tenv s in
    let op' = sil_unop_exp_to_expr op in
    Expr.UnOp (op', exp')
  | Exp.BinOp ((Binop.PlusPI | Binop.MinusPI) as op, e1, e2)
    when Option.is_some typ ->
      let typ_size = match typ with
        | Some t -> typ_size_of tenv t
        | None -> 1L
      in
      let lhs = sil_exp_to_expr e1 tenv s in
      let rhs = sil_exp_to_expr e2 tenv s in
      let op' = sil_binop_exp_to_expr op in
      (* if lhs is pointer then TODO make sure pointer is always lhs *)
      Expr.BinOp (op', lhs, Expr.BinOp (Expr.Pmult, rhs, Const (Int typ_size)))
  | Exp.BinOp ((Binop.Gt | Binop.Ge) as op, e1, e2) ->
    let lhs = sil_exp_to_expr e1 tenv s in
    let rhs = sil_exp_to_expr e2 tenv s in
    let op' = sil_binop_exp_to_expr op in
    Expr.BinOp (op', rhs, lhs)
  | Exp.BinOp (op, e1, e2) ->
    let lhs = sil_exp_to_expr e1 tenv s in
    let rhs = sil_exp_to_expr e2 tenv s in
    let op' = sil_binop_exp_to_expr op in
    Expr.BinOp (op', lhs, rhs)
  | Exp.Lfield ({ exp; is_implicit = _ }, fieldname, typ) ->
      let base = sil_exp_to_expr exp tenv s in
      let offset = sil_struct_field_offset_bytes tenv fieldname typ in
      Expr.BinOp (Pplus, base, Const (Int offset))
  | Exp.Lindex (base, index) ->
      let base' = sil_exp_to_expr base tenv s in
      let index' = sil_exp_to_expr index tenv s in
      let offset = sil_array_offset_bytes base index' tenv s in
      Expr.BinOp (Pplus, base', offset)
  | _ -> Expr.Undef

and sil_const_exp_to_expr c =
  match c with
    Const.Cint i -> Expr.Const (Int (Z.to_int64 (IntLit.to_big_int i)))
  | Const.Cstr str -> Expr.Const (String str)
  | Const.Cfloat f -> Expr.Const (Float f)
  | Const.Cfun _ | Const.Cclass _ -> Expr.Undef

and sil_sizeof_exp_to_expr sz =
  let open Exp in
  match sz with
  | { nbytes = Some i } -> Expr.Const (Int (Int.to_int64 i))
  (* | { nbytes = Some i; dynamic_length = exp } *)
  | _ -> Expr.Undef

and sil_struct_field_offset_bytes tenv target_field struct_typ =
  let open Typ in
  let open Struct in
  match struct_typ.desc with
  | Typ.Tstruct name ->
    begin match Tenv.lookup tenv name with
    | Some { fields } ->
      let rec aux acc = function
        | [] -> acc
        | { name; typ } :: rest ->
          if Fieldname.equal name target_field then
            acc
          else
            let size = typ_size_of tenv typ in
            aux (Stdlib.Int64.add acc size) rest
      in
      aux 0L fields
    | _ ->
      0L
    end
  | _ ->
    0L

and sil_array_offset_bytes base index tenv s =
  let temp_vars =
    Sequence.map ~f:(fun id -> Var.of_id id) (Exp.free_vars base)
  in
  let pvars =
    Sequence.map ~f:(fun p -> Var.of_pvar p) (Exp.program_vars base)
  in
  let vars = Sequence.append temp_vars pvars |> Sequence.to_list in
  let var_ids = List.map vars
    ~f:(fun var ->
      get_canonical_var_id var s)
  in
  match List.filter_opt var_ids with
  | [id] ->
    begin match VarIdMap.find_opt id s.types with
    | Some t ->
      let size_of_t = typ_size_of tenv t in
      Expr.BinOp (Expr.Pmult, index, Const (Int size_of_t))
    | None -> index
    end
  | _ -> index  (* TODO maybe not the best fallback *)

and typ_size_of tenv typ =
  let open Typ in
  let open Struct in
  match typ.desc with
  (* for now assume 64bit architecture *)
  (* TODO wire up to infer's runtime info -- i did not find any *)
  | Tint ikind ->
      begin match ikind with
      | IChar | ISChar | IUChar | IBool -> 1L
      | IInt | IUInt -> 4L
      | IShort | IUShort -> 2L
      | ILong | IULong | ILongLong | IULongLong -> 8L
      | I128 | IU128 -> 16L
      end
  | Tfloat fkind ->
    begin match fkind with
    | FFloat -> 4L
    | FDouble | FLongDouble -> 8L
    end
  | Tvoid -> 0L
  | Tfun _ -> 8L
  | Tptr (_, _) -> 8L
  | Tstruct name ->
    begin match Tenv.lookup tenv name with
    | Some { fields } ->
      let rec sum acc = function
        | [] -> acc
        | { name = _; typ } :: rest ->
          let size = typ_size_of tenv typ in
          sum (Stdlib.Int64.add acc size) rest
      in
      sum 0L fields
    | _ ->
      0L
    end
  | Tarray {elt; length = _; stride = _} ->
    typ_size_of tenv elt
  | TVar _ -> 0L (* C++ template variables *)

and sil_unop_exp_to_expr op =
  match op with
    Unop.LNot -> Expr.Lnot
  | Unop.Neg -> Expr.Puminus
  | Unop.BNot -> Expr.BVnot

and sil_binop_exp_to_expr op =
  match op with
    Binop.PlusA _ | Binop.PlusPI -> Expr.Pplus
  | Binop.MinusA _ | Binop.MinusPI | Binop.MinusPP -> Expr.Pminus
  | Binop.Mult _ -> Expr.Pmult
  | Binop.DivI | Binop.DivF -> Expr.Pdiv
  | Binop.Mod -> Expr.Pmod
  | Binop.Shiftlt -> Expr.BVlshift
  | Binop.Shiftrt -> Expr.BVrshift
  | Binop.Lt | Binop.Gt -> Expr.Pless
  | Binop.Le | Binop.Ge -> Expr.Plesseq
  | Binop.Eq -> Expr.Peq
  | Binop.Ne -> Expr.Pneq
  | Binop.BAnd -> Expr.BVand
  | Binop.BXor -> Expr.BVxor
  | Binop.BOr -> Expr.BVor
  | Binop.LAnd -> Expr.Land
  | Binop.LOr -> Expr.Lor


(* ==================== pretty printing ==================== *)

let rec to_string state =
  status_to_string state.status ^
  "Current:\n" ^
  Formula.to_string state.vars state.current 
  ^ "\n----------------\nMissing:\n"
  ^ Formula.to_string state.vars state.missing
  ^ "\n----------------\nVars:\n"
  ^ vars_to_string state.vars
  ^ "\n----------------\nSubstitutions:\n"
  ^ subst_to_string state.vars state.subst
  ^ "\n----------------\nTypes:\n"
  ^ types_to_string state.types
  ^ "\n================"

and subst_to_string vars subst =
  let traversal =
    VarIdMap.fold
    (fun from_ to_ traversal ->
      traversal ^ Expr.var_to_string vars from_ ^ "==" ^ subst_expr_to_string vars to_ ^ ";")
    subst
    "{"
  in
  traversal ^ "}"

and subst_expr_to_string vars = function
  | Var id -> 
    Expr.var_to_string vars id
  | Ptr { base; offset } ->
    "(" ^ Expr.var_to_string vars base ^ "+" ^ Int64.to_string offset ^ ")"

and status_to_string s =
  match s with
    Ok ->
      "OK\n"
  | Error (Some issue, loc, instr) ->
    "ERROR\n" ^
    "ISSUE=" ^ issue.unique_id ^ "\n" ^
    "LOCATION=" ^ loc_to_string loc ^ "\n" ^
    "SIL_INSTR=" ^ sil_instr_to_string instr ^ "\n"
  | Error (None, loc, instr) ->
    "ERROR\nISSUE=\n" ^
    "LOCATION=" ^ loc_to_string loc ^ "\n" ^
    "SIL_INSTR=" ^ sil_instr_to_string instr ^ "\n"

and loc_to_string loc = 
  let open Location in
  "[line " ^
  Int.to_string (loc.line) ^
  "; column " ^
  Int.to_string (loc.col) ^
  "]"

and sil_instr_to_string instr =
  Format.asprintf "%a"
    (Sil.pp_instr ~print_types:true Pp.text)
    instr

and vars_to_string vars =
  let bindings = VarIdMap.bindings vars in
  String.concat (
    List.map bindings
    ~f:(fun (id, var) ->
      let var_str = match var with
      | Var.ProgramVar pvar ->
        Pvar.get_simplified_name pvar
      | Var.LogicalVar ident ->
        Ident.to_string ident
      in
      "(" ^ var_str ^ ";" ^ Int.to_string id ^ ") "))

and types_to_string types =
  String.concat (
    List.map (VarIdMap.bindings types)
    ~f:(fun (id, typ) ->
      "(" ^ Typ.to_string typ ^ ";" ^ Int.to_string id ^ ") "))


let rec sil_exp_to_string e =
  let open Exp in
  match e with
    Var id -> "Var(" ^ Ident.to_string id ^ ")"
  | Lvar pvar -> "Lvar(" ^ Pvar.to_string pvar ^ ")"
  | Const c -> "Const(" ^ sil_const_to_string c ^ ")"
  | Cast (typ, e1) -> "Cast(" ^ Typ.to_string typ ^ ", " ^ sil_exp_to_string e1 ^ ")"
  | UnOp (op, e1, typ) -> "UnOp(" ^ sil_unop_to_string op ^ ", " ^ sil_exp_to_string e1 ^ ", " ^ typ_opt_to_string typ ^ ")"
  | BinOp (op, e1, e2) -> "BinOp(" ^ sil_binop_to_string op ^ ", " ^ sil_exp_to_string e1 ^ ", " ^ sil_exp_to_string e2 ^ ")"
  | Lfield ({ exp }, field, typ) -> "Lfield(" ^ sil_exp_to_string exp ^ ", " ^ Fieldname.to_string field ^ ", " ^ Typ.to_string typ ^ ")"
  | Lindex (e1, e2) -> "Lindex(" ^ sil_exp_to_string e1 ^ ", " ^ sil_exp_to_string e2 ^ ")"
  | Sizeof { typ; nbytes; dynamic_length } ->
      let nbytes_str =
        match nbytes with
        | None -> "None"
        | Some n -> "Some(" ^ Int.to_string n ^ ")"
      in
      let dyn_str =
        match dynamic_length with
        | None -> "None"
        | Some e -> "Some(" ^ sil_exp_to_string e ^ ")"
      in
      "Sizeof(" ^ Typ.to_string typ ^ ", " ^ nbytes_str ^ ", " ^ dyn_str ^ ")"
  | Closure _ -> "Closure()"
  | _ -> "Undef"

  and sil_const_to_string = function
    Const.Cint i ->
      "Cint(" ^ IntLit.to_string i ^ ")"
  | Const.Cfloat f ->
      "Cfloat(" ^ string_of_float f ^ ")"
  | Const.Cstr s ->
      "Cstr(\"" ^ s ^ "\")"
  | Const.Cfun pn ->
      "Cfun(" ^ Procname.to_string pn ^ ")"
  | Const.Cclass _ ->
      "Cclass()"

  and sil_unop_to_string = function
  | Unop.Neg -> "Neg"
  | Unop.BNot -> "BNot"
  | Unop.LNot -> "LNot"

  and sil_binop_to_string = function
    Binop.PlusA _ -> "PlusA"
  | Binop.PlusPI -> "PlusPI"
  | Binop.MinusA _ -> "MinusA"
  | Binop.MinusPI -> "MinusPI"
  | Binop.MinusPP -> "MinusPP"
  | Binop.Mult _ -> "Mult"
  | Binop.DivI -> "DivI"
  | Binop.DivF -> "DivF"
  | Binop.Mod -> "Mod"
  | Binop.Shiftlt -> "Shiftlt"
  | Binop.Shiftrt -> "Shiftrt"
  | Binop.Lt -> "Lt"
  | Binop.Gt -> "Gt"
  | Binop.Le -> "Le"
  | Binop.Ge -> "Ge"
  | Binop.Eq -> "Eq"
  | Binop.Ne -> "Ne"
  | Binop.BAnd -> "BAnd"
  | Binop.BXor -> "BXor"
  | Binop.BOr -> "BOr"
  | Binop.LAnd -> "LAnd"
  | Binop.LOr -> "LOr"

  and typ_opt_to_string = function
      Some t -> "Some(" ^ Typ.to_string t ^ ")"
    | None -> "None"
