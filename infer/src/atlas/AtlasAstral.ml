
(** Translation layer from AtlasFormula to Astral's LowLevelSeplog.
    Instantiates the solver with 64-bit address width and provides
    translation functions for expressions, heap predicates, and formulas.

    The translation requires the full abstract state ([AtlasState.t]) because:
    - Variable types determine Astral term width (pointers are 64-bit, integers
      use their actual bit width from [state.types])
    - Substitution entries ([state.subst]) encode aliasing relationships that
      must appear as equalities in the Astral formula

    Limitations:
    - [Pdiv] / [Pmod] must be statically evaluable to integer constants.
    - [Freed] has no spatial encoding in Astral — tracked externally by Atlas.
    - [String] / [Float] constants are not translatable. *)

module Formula = AtlasFormula
module Expr = Formula.Expr
module Id = Formula.Id
module VarIdMap = Formula.VarIdMap

open !Stdlib

(** Astral LowLevelSeplog instance with 64-bit pointer width *)
module LL = Astral.LowLevelSeplog.Make(struct let width = 64 end)()

(** Returns the bit width for a variable based on its type in [state.types].
    Pointer types are 64-bit. Integer types use their actual size in bits.
    Falls back to 64 for unknown types *)
let var_width_of_id id (types : Typ.t VarIdMap.t) : int =
  match VarIdMap.find_opt id types with
  | Some t ->
    begin match t.Typ.desc with
    | Tptr _ | Tarray _ -> 64
    | Tint IChar | Tint ISChar | Tint IUChar | Tint IBool -> 8
    | Tint IShort | Tint IUShort -> 16
    | Tint IInt | Tint IUInt -> 32
    | Tint ILong | Tint IULong | Tint ILongLong | Tint IULongLong -> 64
    | Tint I128 | Tint IU128 -> 128
    | Tfloat FFloat -> 32
    | Tfloat FDouble | Tfloat FLongDouble -> 64
    | _ -> 64
    end
  | None -> 64

(** Translates an AtlasFormula expression to an Astral LowLevelSeplog term.
    Uses [state.types] to determine variable widths. Constants are 64-bit
    bitvectors. Arithmetic ([Pplus], [Pminus], [Pmult]) maps directly to
    Astral's [mk_plus], [mk_minus], [mk_mult] *)
let rec translate_expr (types : Typ.t VarIdMap.t) (expr : Expr.t) : LL.Term.t =
  match expr with
  | Var id ->
    (* All variables use 64-bit width regardless of their C type.
       Bitwuzla requires matching widths on both sides of a comparison term,
       and our model does not support integer overflow semantics anyway —
       sizes, offsets, and addresses all live in the same 64-bit space *)
    LL.Term.mk_var 64 (Int.to_string id)
  | Const (Int n) ->
    LL.Term.mk_const ~size:64 (Int64.to_int n)
  | Const Null ->
    LL.Term.null
  | Const (String _) | Const (Float _) | Undef ->
    LL.Term.mk_fresh_var 64 "unsupported"
  | UnOp (Base, e) ->
    LL.Term.mk_block_begin (translate_expr types e)
  | UnOp (End, e) ->
    LL.Term.mk_block_end (translate_expr types e)
  | UnOp (Puminus, e) ->
    LL.Term.mk_minus (LL.Term.mk_const ~size:64 0) (translate_expr types e)
  | UnOp (Freed, _) | UnOp (Lnot, _) | UnOp (BVnot, _) ->
    LL.Term.mk_fresh_var 64 "unsupported"
  | BinOp (Pplus, e1, e2) ->
    LL.Term.mk_plus (translate_expr types e1) (translate_expr types e2)
  | BinOp (Pminus, e1, e2) ->
    LL.Term.mk_minus (translate_expr types e1) (translate_expr types e2)
  | BinOp (Pmult, e1, e2) ->
    LL.Term.mk_mult (translate_expr types e1) (translate_expr types e2)
  | BinOp ((Peq | Pneq | Pless | Plesseq), _, _) ->
    (* Boolean-valued comparisons as terms — LowLevelSeplog has no boolean
       term type (mk_eq2/mk_distinct2 return formulas, not terms), so these
       cannot be nested inside spatial predicates. Fresh 1-bit variable *)
    LL.Term.mk_fresh_var 64 "unsupported_bool"
  | BinOp ((Pdiv | Pmod | Land | Lor
           | BVlshift | BVrshift | BVand | BVor | BVxor), _, _) ->
    LL.Term.mk_fresh_var 64 "unsupported"


(** Translates a heap predicate to an Astral formula atom.
    [BlockPointsTo] and [UniformBlockPointsTo] become [mk_pto_array] (allocated region).
    [ExpPointsTo] becomes [mk_pto] (single cell with known destination value) *)
let translate_heap_pred types (hp : Formula.heap_pred) : LL.t =
  match hp with
  | BlockPointsTo (src, size) ->
    LL.mk_pto_array (translate_expr types src) ~size:(translate_expr types size)
  | ExpPointsTo (src, _size, dest) ->
    LL.mk_pto (translate_expr types src) (translate_expr types dest)
  | UniformBlockPointsTo (src, size, _value) ->
    LL.mk_pto_array (translate_expr types src) ~size:(translate_expr types size)

(** Negates an expression at the formula level.
    [Peq] ↔ [Pneq], [Lnot] unwraps, everything else wraps in [Lnot] *)
let negate_expr (expr : Expr.t) : Expr.t =
  match expr with
  | BinOp (Peq, e1, e2) -> BinOp (Pneq, e1, e2)
  | BinOp (Pneq, e1, e2) -> BinOp (Peq, e1, e2)
  | BinOp (Pless, e1, e2) -> BinOp (Plesseq, e2, e1)
  | BinOp (Plesseq, e1, e2) -> BinOp (Pless, e2, e1)
  | UnOp (Lnot, inner) -> inner
  | _ -> UnOp (Lnot, expr)

(** Translates a pure constraint to an Astral formula atom.
    Returns [None] for constraints that cannot be expressed in LowLevelSeplog
    (freed markers, unsupported operations).
    Handles [Lnot]-wrapped conditions from SIL false branches by negating
    the inner expression and retrying *)
let rec translate_pure_constraint types (expr : Expr.t) : LL.t option =
  match expr with
  | BinOp (Peq, e1, e2) ->
    Some (LL.mk_eq2 (translate_expr types e1) (translate_expr types e2))
  | BinOp (Pneq, e1, e2) ->
    Some (LL.mk_distinct2 (translate_expr types e1) (translate_expr types e2))
  | BinOp (Pless, e1, e2) ->
    Some (LL.mk_lesser (translate_expr types e1) (translate_expr types e2))
  | BinOp (Plesseq, e1, e2) ->
    Some (LL.mk_lesser_or_eq (translate_expr types e1) (translate_expr types e2))
  | UnOp (Lnot, inner) ->
    (* SIL false branches wrap conditions in Lnot: !(e1 == e2).
       Unwrap by negating the inner expression and retrying *)
    translate_pure_constraint types (negate_expr inner)
  | UnOp (Freed, _) ->
    None
  | _ ->
    None

(** Translates substitution entries to Astral equality atoms.
    Each [subst] binding [id ↦ target] becomes [id == translate(target)].
    [Var rhs_id] becomes [id == rhs_id].
    [Ptr { base; offset }] becomes [id == base + offset] *)
let translate_subst types (subst : AtlasState.subst_expr VarIdMap.t) : LL.t list =
  VarIdMap.fold (fun id target acc ->
    let lhs = translate_expr types (Expr.Var id) in
    let rhs = match target with
      | AtlasState.Var rhs_id -> translate_expr types (Expr.Var rhs_id)
      | AtlasState.Ptr { base; offset } ->
        translate_expr types (Expr.BinOp (Pplus, Var base, Const (Int offset)))
    in
    LL.mk_eq2 lhs rhs :: acc
  ) subst []

(** Translates a complete state to an Astral LowLevelSeplog formula.
    Combines current spatial predicates, current pure constraints, and
    substitution entries into a single separating conjunction *)
let translate_state (state : AtlasState.t) : LL.t =
  let types = state.types in
  let spatial_atoms = List.map (translate_heap_pred types) state.current.spatial in
  let pure_atoms = List.filter_map (translate_pure_constraint types) state.current.pure in
  let subst_atoms = translate_subst types state.subst in
  match spatial_atoms @ pure_atoms @ subst_atoms with
  | [] -> LL.emp
  | atoms -> LL.mk_star atoms

(** Checks satisfiability of the current state via Astral *)
let check_sat (state : AtlasState.t) : [`Sat | `Unsat | `Unknown] =
  let ll_formula = translate_state state in
  LL.check_sat ll_formula

(** Checks satisfiability of the current state conjoined with an additional
    condition. Used for prune condition strengthening: when [eval_prune_condition]
    returns Unknown, we check whether the conjunction of the state with the
    condition (or its negation) is satisfiable *)
let check_sat_with_condition (state : AtlasState.t) (condition : Expr.t) : [`Sat | `Unsat | `Unknown] =
  let base = translate_state state in
  match translate_pure_constraint state.types condition with
  | Some cond_atom ->
    let query = LL.mk_star [base; cond_atom] in
    Format.printf "[ASTRAL] query: %s\n" (LL.show query);
    let result = LL.check_sat query in
    Format.printf "[ASTRAL] result: %s\n"
      (match result with `Sat -> "SAT" | `Unsat -> "UNSAT" | `Unknown -> "UNKNOWN");
    result
  | None ->
    Format.printf "[ASTRAL] condition not translatable, returning Unknown\n";
    `Unknown

(** Evaluates a prune condition using Astral. Checks both the condition and
    its negation against the current state:
    - [UNSAT(state ∧ cond)] → condition impossible → [Unsat]
    - [UNSAT(state ∧ ¬cond)] → condition must hold → [Sat]
    - Otherwise → [Unknown] *)
let eval_prune (state : AtlasState.t) (condition : Expr.t) : AtlasState.prune_result =
  Format.printf "[ASTRAL] eval_prune called\n";
  match check_sat_with_condition state condition with
  | `Unsat -> Unsat
  | `Sat | `Unknown ->
    match check_sat_with_condition state (negate_expr condition) with
    | `Unsat -> Sat
    | `Sat | `Unknown -> Unknown
