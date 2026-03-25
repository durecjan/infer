
(** Unique variable identifier module.
    Uses OCaml 5 Domain-Local Storage (DLS) via [AnalysisGlobalState.make_dls]
    for thread-safe fresh id generation — each analysis domain gets its own
    counter, and the state is automatically saved/restored when ondemand
    analysis suspends a procedure to analyze a dependency. *)
module Id = struct
  type t = int [@@deriving compare, equal, hash]

  let initial_next_fresh = 1

  let next_fresh = AnalysisGlobalState.make_dls ~init:(fun () -> initial_next_fresh)

  (** Generates a fresh unique identifier, incrementing the domain-local counter *)
  let fresh () =
    let l = DLS.get next_fresh in
    DLS.set next_fresh (l + 1) ;
    l

  let pp = Format.pp_print_int

end

(** Map keyed by variable [Id.t], used for vars, types, and substitutions in the abstract state *)
module VarIdMap = Stdlib.Map.Make (Id)

(** Set of variable [Id.t], used for cycle detection in pure constraint resolution *)
module VarIdSet = Stdlib.Set.Make (Id)

(** Looks up a variable by its [Id.t] in the variable map. Returns [Some Var.t] or [None] *)
let lookup_variable id vars =
  VarIdMap.find_opt id vars

(** Finds the [Id.t] of the first variable in [vars] that equals [v].
    Performs a linear scan over all bindings, returning the first match *)
let lookup_variable_id v vars =
  let rec find_var = function
    | [] -> None
    | (a, b) :: l -> if Var.equal b v then Some a else find_var l
  in
  find_var (VarIdMap.bindings vars)

(** Expression language for pure constraints and heap predicate arguments.
    [Var] holds an [Id.t], [Base]/[End]/[Freed] are special unary operators
    for memory block bounds and deallocation tracking *)
module Expr = struct
  type t =
      Var of int
    | Const of const_val
    | UnOp of (unop * t)
    | BinOp of (binop * t * t)
    | Undef  (** Unknown or unresolvable expression *)

  and unop =
    | Base   (** Lower bound of a memory block *)
    | End    (** Upper bound (exclusive) of a memory block *)
    | Freed  (** Marks a memory block as deallocated *)
    | BVnot  (** bitwise complement *)  
    | Lnot  (** logical not *)
    | Puminus  (** unary minus *)

  and binop =
    | Pplus
    | Pminus
    | Pmult
    | Pdiv
    | Pmod
    | BVlshift  (** shift left *)
    | BVrshift  (** shift right *)
    | Pless
    | Plesseq
    | Peq
    | Pneq
    | BVand  (** bitwise AND *)
    | BVor  (** bitwise OR *)
    | BVxor  (** bitwise XOR *)
    | Land  (** logical AND *)
    | Lor  (** logical OR *)
  
  and const_val =
    | Int of Int64.t
    | Null  (** Null pointer constant — distinct from integer zero *)
    | String of string
    | Float of float

  let one = Const (Int 1L)
  let zero = Const (Int 0L)
  let null = Const Null

  (** Return variable is always Id 0 *)
  let ret = Var 0

  let unop_equal op1 op2 =
    match op1, op2 with
    | Base, Base
    | End, End
    | BVnot, BVnot
    | Lnot, Lnot
    | Puminus, Puminus -> true
    | _ -> false

  let binop_equal op1 op2 =
    match op1, op2 with
    | Pplus, Pplus
    | Pminus, Pminus
    | Pmult, Pmult
    | Pdiv, Pdiv
    | Pmod, Pmod
    | BVlshift, BVlshift
    | BVrshift, BVrshift
    | Pless, Pless
    | Plesseq, Plesseq
    | Peq, Peq
    | Pneq, Pneq
    | BVand, BVand
    | BVor, BVor
    | BVxor, BVxor
    | Land, Land
    | Lor, Lor -> true
    | _ -> false

  let rec equal e1 e2 =
    match e1, e2 with
    | Var id1, Var id2 ->
      Id.equal id1 id2
    | Const (Int i1), Const (Int i2) ->
      Int64.equal i1 i2
    | Const Null, Const Null -> true
    | Const (String s1), Const (String s2) ->
      String.equal s1 s2
    | Const (Float f1), Const (Float f2) ->
      Float.equal f1 f2
    | UnOp (op1, e1'), UnOp (op2, e2') ->
      unop_equal op1 op2 && equal e1' e2'
    | BinOp (op1, e1', e2'), BinOp (op2, e1'', e2'') ->
      binop_equal op1 op2 && equal e1' e1'' && equal e2' e2''
    | Undef, Undef -> true
    | _ -> false

  let rec var_to_string vars v =
    if Id.equal v 0 then
      "%ret"
    else
      match lookup_variable v vars with
        Some var -> var_string var
      | None -> "Var(" ^ (Int.to_string v) ^ ")"

  and var_string = function
      Var.ProgramVar pvar -> Pvar.get_simplified_name pvar
    | Var.LogicalVar id -> Ident.to_string id

  let const_to_string c =
    match c with
    | Int i -> Int64.to_string i
    | Null -> "null"
    | String s -> "\"" ^ String.escaped s ^ "\""
    | Float f -> Float.to_string f

  let unop_to_string o =
    match o with
    | Base -> "Base"
    | End -> "End"
    | Freed -> "Freed"
    | Puminus -> "-"
    | BVnot -> "~"
    | Lnot -> "!"

  let binop_to_string o =
    match o with
    | Pplus -> "+"
    | Pminus -> "-"
    | Pmult -> "*"
    | Pdiv -> "/"
    | Pmod -> "%"
    | BVlshift -> "<<"
    | BVrshift -> ">>"
    | Pless -> "<"
    | Plesseq -> "<="
    | Peq -> "=="
    | Pneq -> "!="
    | BVand -> "&"
    | BVxor -> "^"
    | BVor -> "|"
    | Land -> "&&"
    | Lor -> "||"

  let rec to_string vars exp =
  match exp with
  | Var a -> var_to_string vars a
  | Const a -> const_to_string a
  | UnOp (op,a) -> unop_to_string op ^ "(" ^ to_string vars a ^ ")"
  | BinOp (op,a,b) -> "(" ^ to_string vars a ^ binop_to_string op ^ to_string vars b ^ ")"
  | Undef -> "Undef"

end

(** Separation logic formula consisting of spatial (heap) and pure (constraint) parts.
    The spatial part is a separating conjunction of heap predicates.
    The pure part is a conjunction of expression constraints. *)
type t = {
  spatial: spatial;
  pure: pure;
}

(** Heap predicates describing memory regions:
    - [BlockPointsTo]: allocated block of [size] bytes at [source], contents unknown
    - [ExpPointsTo]: single cell of [size] bytes at [source] with known [destination] value
    - [UniformBlockPointsTo]: block of [size] bytes at [source], every byte has [value] *)
and heap_pred =
  | BlockPointsTo of Expr.t * Expr.t
  | ExpPointsTo of Expr.t * Expr.t * Expr.t
  | UniformBlockPointsTo of Expr.t * Expr.t * Expr.t

and spatial = heap_pred list

and pure = Expr.t list

let empty = { spatial = []; pure = [] }

let rec pure_to_string vars p =
  match p with
  | [] -> ""
  | first::[] -> Expr.to_string vars first
  | first::rest -> Expr.to_string vars first ^ " & " ^ pure_to_string vars rest

let rec spatial_to_string vars s =
  match s with
  | [] -> ""
  | first::[] -> points_to_to_string vars first
  | first::rest -> points_to_to_string vars first ^ " * " ^ spatial_to_string vars rest

  and points_to_to_string vars points_to =
  match points_to with
  | ExpPointsTo (source, size, dest) ->
    Expr.to_string vars source ^ " -(" ^ Expr.to_string vars size ^ ")-> " ^ Expr.to_string vars dest
  | BlockPointsTo (source, size) ->
    Expr.to_string vars source ^ " -(" ^ Expr.to_string vars size ^ ")-> block"
  | UniformBlockPointsTo (source, size, value) ->
    Expr.to_string vars source ^ " -(" ^ Expr.to_string vars size ^ ")-> block[" ^ Expr.to_string vars value ^ "]"

let to_string vars f =
  spatial_to_string vars f.spatial ^ "\n" ^ pure_to_string vars f.pure


(* ==================== pure constraint helpers ==================== *)

(** Resolves a variable [id] through pure equality constraints to a constant expression.
    Follows chains of (Var id == Var id') and (Var id == Const _) equalities,
    checking both LHS and RHS positions. Uses [VarIdSet] to detect cycles.
    Only resolves to [Const] values — returns [None] for non-constant results *)
let lookup_pure_const_exp_of_id id pure =
  let rec resolve visited id =
    if VarIdSet.mem id visited then
      None
    else
      let visited = VarIdSet.add id visited in
      match
        Stdlib.List.find_opt
        (function
        | Expr.BinOp (Expr.Peq, Expr.Var lhs, _) when Id.equal lhs id ->
          true
        | Expr.BinOp (Expr.Peq, _, Expr.Var rhs) when Id.equal rhs id ->
          true
        | _ -> false)
        pure
      with
      | None -> None
      | Some (Expr.BinOp (Expr.Peq, Expr.Var lhs, rhs)) when Id.equal lhs id ->
        resolve_rhs visited rhs
      | Some (Expr.BinOp (_, lhs, Expr.Var rhs)) when Id.equal rhs id ->
        resolve_rhs visited lhs
      | _ -> None
    and resolve_rhs visited = function
      | Expr.Const _ as c -> Some c
      | Expr.Var id' -> resolve visited id'
      | _ -> None
    in
    resolve VarIdSet.empty id

(** Looks up the first pure constraint matching (Base(Var [id]) == exp), returns [Some exp] *)
let rec lookup_pure_base_expr id = function
  | [] -> None
  | Expr.BinOp (Expr.Peq, Expr.UnOp (Expr.Base, Expr.Var id'), exp) :: _
    when Id.equal id id' -> Some exp
  | _ :: rest -> lookup_pure_base_expr id rest

(** Looks up the first pure constraint matching (End(Var [id]) == exp), returns [Some exp] *)
let rec lookup_pure_end_expr id = function
  | [] -> None
  | Expr.BinOp (Expr.Peq, Expr.UnOp (Expr.End, Expr.Var id'), exp) :: _
    when Id.equal id id' -> Some exp
  | _ :: rest -> lookup_pure_end_expr id rest

(** Checks whether the pure constraint list contains a (Freed(Var [id])) expression *)
let rec has_freed_expr id = function
  | [] -> false
  | Expr.UnOp (Freed, Var id') :: _
    when Id.equal id id' -> true
  | _ :: rest -> has_freed_expr id rest

(** Tries to evaluate [expr] to an Int64 value. Handles [Const (Int _)] and arithmetic
    binary operations ([+], [-], [*], [/], [%], unary [-]). Returns [None] if the expression
    contains variables or other non-evaluable subexpressions — no state access is available
    at this level, so variable resolution must happen before calling this *)
and eval_expr_to_int64 e =
  let open Expr in
  match e with
    Const (Int i) ->
      Some i
  | Const Null ->
      Some 0L
  | UnOp (Puminus, e1) ->
    Option.map (eval_expr_to_int64 e1) ~f:(fun v ->
      Stdlib.Int64.neg v)
  | BinOp (Pplus, e1, e2) ->
    Option.bind (eval_expr_to_int64 e1) ~f:(fun v1 ->
    Option.map (eval_expr_to_int64 e2) ~f:(fun v2 ->
      Stdlib.Int64.add v1 v2))
  | BinOp (Pminus, e1, e2) ->
    Option.bind (eval_expr_to_int64 e1) ~f:(fun v1 ->
    Option.map (eval_expr_to_int64 e2) ~f:(fun v2 ->
      Stdlib.Int64.sub v1 v2))
  | BinOp (Pmult, e1, e2) ->
    Option.bind (eval_expr_to_int64 e1) ~f:(fun v1 ->
    Option.map (eval_expr_to_int64 e2) ~f:(fun v2 ->
      Stdlib.Int64.mul v1 v2))
  | BinOp (Pdiv, e1, e2) ->
    Option.bind (eval_expr_to_int64 e1) ~f:(fun v1 ->
    Option.bind (eval_expr_to_int64 e2) ~f:(fun v2 ->
      if Int64.equal v2 0L then None
      else Some (Stdlib.Int64.div v1 v2)))
  | BinOp (Pmod, e1, e2) ->
    Option.bind (eval_expr_to_int64 e1) ~f:(fun v1 ->
    Option.bind (eval_expr_to_int64 e2) ~f:(fun v2 ->
      if Int64.equal v2 0L then None
      else Some (Stdlib.Int64.rem v1 v2)))
  | _ ->
      None

(** Evaluates [expr] to Int64 and checks whether the result is zero.
    Limited to constant arithmetic — expressions containing variables return false *)
let is_zero_expr expr =
  match eval_expr_to_int64 expr with
  | Some i when Int64.equal i 0L -> true
  | _ -> false

(** Checks whether [expr] is a null pointer constant *)
let is_null_expr = function
  | Expr.Const Null -> true
  | _ -> false


(* ==================== heap predicate helpers ==================== *)

(** Prepends heap predicate [p] to the spatial part of formula [f] *)
let add_heap_pred p f =
  { f with spatial = p :: f.spatial }

(** Looks up the first [BlockPointsTo] with source [Var id] in the heap predicate list *)
let rec lookup_heap_pred_block_points_to id = function
  | [] -> None
  | (BlockPointsTo (Expr.Var id', _)) as hp :: _
    when Id.equal id' id ->
      Some hp
  | _ :: rest ->
    lookup_heap_pred_block_points_to id rest

(** Looks up the first [ExpPointsTo] whose source equals [src] in the heap predicate list *)
let rec lookup_heap_pred_exp_points_to src = function
  | [] -> None
  | (ExpPointsTo (src', _, _)) as hp :: _
    when Expr.equal src' src ->
      Some hp
  | _ :: rest ->
    lookup_heap_pred_exp_points_to src rest

(** Structural equality for heap predicates, comparing all fields via [Expr.equal] *)
let heap_pred_equal a b =
  match a, b with
  | BlockPointsTo (src1, size1), BlockPointsTo (src2, size2) ->
    Expr.equal src1 src2 && Expr.equal size1 size2
  | ExpPointsTo (src1, size1, dest1), ExpPointsTo (src2, size2, dest2) ->
    Expr.equal src1 src2 && Expr.equal size1 size2 && Expr.equal dest1 dest2
  | UniformBlockPointsTo (src1, size1, value1), UniformBlockPointsTo (src2, size2, value2) ->
    Expr.equal src1 src2 && Expr.equal size1 size2 && Expr.equal value1 value2
  | _ -> false

(** Partitions [spatial] into (matching, rest) where matching heap predicates have
    source rooted at [Var var_id] with offset <= [var_offset] and size >= [cell_size].
    Used to find candidate fragments for block splitting during dereference *)
let heap_find_block_fragments spatial var_id var_offset cell_size =
  let is_block_fragment src size =
    match src, size with
    | Expr.BinOp (Pplus, Var id, Const (Int off)),
      Expr.Const (Int size) ->
        Id.equal id var_id &&
        (Int64.compare off var_offset) <= 0 &&
        (Int64.compare size cell_size) >= 0
    | Expr.Var id,
      Expr.Const (Int size) ->
        Id.equal id var_id &&
        (Int64.compare 0L var_offset) <= 0 &&
        (Int64.compare size cell_size) >= 0
    | _ -> false
  in
  Stdlib.List.partition
    (fun hp ->
      match hp with
      | ExpPointsTo (src, size, _)
        when is_block_fragment src size -> true
      | BlockPointsTo (src, size)
        when is_block_fragment src size -> true
      | UniformBlockPointsTo (src, size, _)
        when is_block_fragment src size -> true
      | _ -> false)
    spatial

(** Sorts heap predicates by source offset in descending order.
    Expects source to be [BinOp (Pplus, Var _, Const (Int offset))] or [Var _] (offset 0).
    Raises [InternalError] if source does not match either pattern *)
let rec sort_heap_preds_by_offset_desc hps =
  hps
  |> List.map ~f:(fun hp -> (points_to_src_offset hp, hp))
  |> List.sort ~compare:(fun (o1, _) (o2, _) -> Int64.compare o2 o1)
  |> List.map ~f:snd

and points_to_src_offset hp =
  let src =
    match hp with
    | BlockPointsTo (src, _)
    | ExpPointsTo (src, _, _)
    | UniformBlockPointsTo (src, _, _) -> src
  in
  match src with
  | Expr.BinOp (Pplus, Var _, Const (Int i)) -> i
  | Expr.Var _ -> 0L
  | _ -> Logging.die InternalError "unexpected src format"


(* ==================== expression substitution ==================== *)

(** Replaces every occurrence of [~old_] with [~new_] within [expr], using [Expr.equal] for matching *)
let expr_replace ~old_ ~new_ expr =
  let rec replace e =
    if Expr.equal e old_ then new_
    else
      match e with
      | Expr.Var _
      | Expr.Const _
      | Expr.Undef -> e
      | Expr.UnOp (op, e1) ->
        Expr.UnOp (op, replace e1)
      | Expr.BinOp (op, e1, e2) ->
        Expr.BinOp (op, replace e1, replace e2)
  in
  replace expr

(** Applies substitution [~from_] -> [~to_] over every pure constraint in the list *)
let subst_apply_to_pure ~from_ ~to_ pure =
  let rec apply acc = function
    | [] -> acc
    | constr :: rest ->
      let subst = expr_replace ~old_:from_ ~new_:to_ constr in
      apply (subst :: acc) rest
  in
  apply [] pure

(** Applies substitution [~from_] -> [~to_] over every heap predicate in the list,
    replacing within all fields (source, size, and destination/value where applicable) *)
let subst_apply_to_spatial ~from_ ~to_ spatial =
  let rec apply acc = function
  | [] -> acc
  | BlockPointsTo (src, size) :: rest ->
      let subst = BlockPointsTo (
        expr_replace ~old_:from_ ~new_:to_ src,
        expr_replace ~old_:from_ ~new_:to_ size)
      in
      apply (subst :: acc) rest
  | UniformBlockPointsTo (src, size, value) :: rest ->
      let subst = UniformBlockPointsTo (
        expr_replace ~old_:from_ ~new_:to_ src,
        expr_replace ~old_:from_ ~new_:to_ size,
        expr_replace ~old_:from_ ~new_:to_ value)
      in
      apply (subst :: acc) rest
  | ExpPointsTo (src, size, dest) :: rest ->
      let subst = ExpPointsTo (
        expr_replace ~old_:from_ ~new_:to_ src,
        expr_replace ~old_:from_ ~new_:to_ size,
        expr_replace ~old_:from_ ~new_:to_ dest) in
      apply (subst :: acc) rest
  in apply [] spatial
