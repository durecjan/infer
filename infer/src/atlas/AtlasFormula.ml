
module Id = struct
  type t = int [@@deriving compare, equal, hash]

  let initial_next_fresh = 1

  let next_fresh = AnalysisGlobalState.make_dls ~init:(fun () -> initial_next_fresh)

  let fresh () =
  let l = DLS.get next_fresh in
  DLS.set next_fresh (l + 1) ;
  l

  let pp = Format.pp_print_int

end

(** Variable Id map *)
module VarIdMap = Stdlib.Map.Make (Id)

let lookup_variable id vars =
  VarIdMap.find_opt id vars

let lookup_variable_id v vars =
  let rec find_var = function
    | [] -> None
    | (a, b) :: l -> if Var.equal b v then Some a else find_var l 
  in
  find_var (VarIdMap.bindings vars)

module Expr = struct
  type t =
      Var of int
    | Const of const_val
    | UnOp of (unop * t)
    | BinOp of (binop * t * t)
    | Undef

  and unop =
    | Base
    | End
    | Freed
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
    | String of string
    | Float of float

  let one = Const (Int 1L)
  let zero = Const (Int 0L)
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

type t = {
  spatial: spatial;
  pure: pure;
}

and heap_pred =
  | BlockPointsTo of Expr.t * Expr.t (* source, size *)
  | ExpPointsTo of Expr.t * Expr.t * Expr.t (* source, size, destination *)
  | UniformBlockPointsTo of Expr.t * Expr.t * Expr.t (* source, size, value of every byte *)

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

module IdSet = Stdlib.Set.Make (Id)

let lookup_pure_const_exp_of_id id pure =
  let rec resolve visited id =
    if IdSet.mem id visited then
      None
    else
      let visited = IdSet.add id visited in
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
    resolve IdSet.empty id

let add_heap_pred p f =
  let { spatial } = f in
  { f with spatial = p :: spatial }

(** Only takes PointsToBlock predicates. [id] must be a canonical identifier of a pointer typed variable. *)
let rec heap_pred_take_opt id spatial =
  let rec traverse acc = function
    [] -> None
  | (BlockPointsTo (src, _) as hp) :: l
    when expr_contains_var_with_id id src ->
      Some (hp, List.rev_append acc l)
  | (UniformBlockPointsTo (src, _, _) as hp) :: l
    when expr_contains_var_with_id id src ->
      Some (hp, List.rev_append acc l)
  | hp :: l ->
    traverse (hp :: acc) l
  in
  traverse [] spatial

and expr_base_var_find_opt e =
  let open Expr in
  match e with
    (Var _) as v -> Some v
  | UnOp (_, e) -> expr_base_var_find_opt e
  | BinOp (_, e1, e2) ->
    begin
      match expr_base_var_find_opt e1 with
        Some v -> Some v
      | None -> expr_base_var_find_opt e2
    end
  | Const _ -> None
  | Undef -> None

and expr_contains_var_with_id id e =
  let open Expr in
  match expr_base_var_find_opt e with
    Some (Var id') -> Id.equal id' id
  | _ -> false

(** Traverses pure constraints and looks for (Base(Var [id])==exp) *)
let rec find_pure_base_expr id = function
  | [] -> None
  | Expr.BinOp (Expr.Peq, Expr.UnOp (Expr.Base, Expr.Var id'), exp) :: _
    when Id.equal id id' -> Some exp
  | _ :: rest -> find_pure_base_expr id rest

(** Traverses pure constraints and looks for (End(Var [id])==exp) *)
let rec find_pure_end_expr id = function
  | [] -> None
  | Expr.BinOp (Expr.Peq, Expr.UnOp (Expr.Base, Expr.Var id'), exp) :: _
    when Id.equal id id' -> Some exp
  | _ :: rest -> find_pure_end_expr id rest

(** Determines whether the given expression list contains (Freed(Var [id]) expression *)
let rec has_freed_expr id = function
  | [] -> false
  | Expr.UnOp (Freed, Var id') :: _ 
    when Id.equal id id' -> true
  | _ :: rest -> has_freed_expr id rest

(** Evaluates [expr] to Int64 and compares it to 0L *)
let rec is_zero_expr expr =
  match eval_expr_to_int64 expr with
  | Some i when Int64.equal i 0L ->
    true
  | _ ->
    false

and eval_expr_to_int64 e =
  let open Expr in
  match e with
    Const (Int i) ->
      Some i
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
  | _ ->
      None

(** Traverses heap predicates and looks for PointsToBlock (Var [id], size, dest) *)
let rec heap_pred_find_block_points_to id = function
  | [] -> None
  | (BlockPointsTo (Expr.Var id', _)) as hp :: _
    when Id.equal id' id ->
      Some hp
  | _ :: rest ->
    heap_pred_find_block_points_to id rest

(** Traverses heap predicates and looks for PointsToExp ([src], size, dest) *)
let rec heap_pred_find_exp_points_to src = function
  | [] -> None
  | (ExpPointsTo (src', _, _)) as hp :: _
    when Expr.equal src' src ->
      Some hp
  | _ :: rest ->
    heap_pred_find_exp_points_to src rest

(** Replaces every occurence of [~old_] with [~new] within given [expr] *)
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

(** Applies substitution [~from_] [~to_] over a list of pure constraints [pure] *)
let subst_apply_to_pure ~from_ ~to_ pure =
  let rec apply acc = function
    | [] -> acc
    | constr :: rest ->
      let subst = expr_replace ~old_:from_ ~new_:to_ constr in
      apply (subst :: acc) rest
  in
  apply [] pure

(** Applies substitution [~from_] [~to_] over a list of heap predicates [spatial] *)
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
