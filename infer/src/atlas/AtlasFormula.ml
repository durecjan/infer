
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

let rec lookup_variable id vars =
  match vars with
    [] -> None
  | (a,b)::l -> if Id.equal b id then Some a else lookup_variable id l

let rec lookup_variable_id v vars =
  match vars with
    [] -> None
  | (a,b)::l -> if Var.equal a v then Some b else lookup_variable_id v l

module Expr = struct
  type t =
      Var of int
    | Const of const_val
    | UnOp of (unop * t)
    | BinOp of (binop * t * t)
    | Undef

  and unop =
      Base
    | End
    | BVnot  (** bitwise complement *)  
    | Lnot  (** logical not *)
    | Puminus  (** unary minus *)

  and binop =
      Pplus
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
      Ptr of int
    | Int of Int64.t
    | String of string
    | Float of float

  let one = Const (Int 1L)
  let zero = Const (Int 0L)
  let null = Const (Ptr 0)
  let ret = Var 0

  let rec var_to_string vars v =
    if Id.equal v 0 then
      "%ret"
    else
      match lookup_variable v vars with
        Some var -> var_string var
      | None -> Int.to_string v

  and var_string = function
      Var.ProgramVar pvar -> Pvar.get_simplified_name pvar
    | Var.LogicalVar id -> Ident.to_string id

  let const_to_string c =
    match c with
    | Ptr p -> if Int.equal p 0 then "NULL" else Printf.sprintf "0x%x" p
    | Int i -> Int64.to_string i
    | String s -> "\"" ^ String.escaped s ^ "\""
    | Float f -> Float.to_string f

  let unop_to_string o =
    match o with
    | Base -> "base"
    | End -> "end"
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

and block = {
  id : int;
  base : Int64.t;
  end_ : Int64.t;
  freed : bool
}

and heap_pred =
  | PointsToExp of Expr.t * Expr.t * Expr.t (* source, size_of_field, destination *)
  | PointsToBlock of Expr.t * Expr.t * block (* source, size_of_field, memory_block *)
  | PointsToUniformBlock of Expr.t * Expr.t * block * Expr.const_val (* source, size_of_field, memory_block, uniform_value *)

and spatial = heap_pred list

and pure = Expr.t list

let empty = {spatial = []; pure = []}

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
  | PointsToExp (source, size, dest) ->
    Expr.to_string vars source ^ " -(" ^ Expr.to_string vars size ^ ")-> " ^ Expr.to_string vars dest
  | PointsToBlock (source, size, block) ->
    Expr.to_string vars source ^ " -(" ^ Expr.to_string vars size ^ ")-> " ^ block_to_string block
  | PointsToUniformBlock (source, size, block, value) ->
    Expr.to_string vars source ^ " -(" ^ Expr.to_string vars size ^ ")-> " ^ uniform_block_to_string block value

and block_to_string b =
  "[id=" ^ Int.to_string b.id ^ ";base=" ^ Int64.to_string b.base ^ ";end=" ^ Int64.to_string b.end_ ^ ";freed=" ^ Bool.to_string b.freed ^ "]"

and uniform_block_to_string b v =
  "[id=" ^ Int.to_string b.id ^ ";base=" ^ Int64.to_string b.base ^ ";end=" ^ Int64.to_string b.end_ ^ ";freed=" ^ Bool.to_string b.freed ^ ";uniform_value=" ^ Expr.const_to_string v ^ "]"

let to_string vars f =
  spatial_to_string vars f.spatial ^ "\n" ^ pure_to_string vars f.pure

module IdSet = Stdlib.Set.Make (Int)

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

let is_heap_pred_source id f =
  let rec traverse l =
    match l with
      [] -> false
    | (PointsToExp (Var v, _, _)) :: _
      when Id.equal v id -> true
    | (PointsToBlock (Var v, _, _)) :: _
      when Id.equal v id -> true
    | (PointsToUniformBlock (Var v, _, _, _)) :: _
      when Id.equal v id -> true
    | _ :: l ->
      traverse l
  in
  traverse f.spatial

let is_heap_pred_dest id f =
  let rec traverse l =
    match l with
      [] -> false
    | (PointsToExp (_, _, Var v)) :: _
      when Id.equal v id -> true
    | _ :: l ->
      traverse l
  in
  traverse f.spatial

let is_heap_pred id f =
  let rec traverse l =
    match l with
      [] -> false
    | (PointsToExp (Var v, _, _)) :: _
      when Id.equal v id -> true
    | (PointsToBlock (Var v, _, _)) :: _
      when Id.equal v id -> true
    | (PointsToUniformBlock (Var v, _, _, _)) :: _
      when Id.equal v id -> true
    | (PointsToExp (_, _, Var v)) :: _
      when Id.equal v id -> true
    | _ :: l ->
      traverse l
  in
  traverse f.spatial

let add_heap_pred p f =
  let { spatial } = f in
  { f with spatial = p :: spatial }

let heap_pred_find_src_of_dest id f =
  let rec traverse l =
    match l with
      [] -> None
    | (PointsToExp (source, _, Var v)) :: _
      when Id.equal v id -> Some source
    | _ :: l ->
      traverse l
  in
  traverse f.spatial

(** traverse looking via source, if not then via dest, until you find some block *)
let rec heap_pred_find_block id spatial =
  match spatial with
  | [] -> None
  | PointsToBlock (Var v, _, b) :: rest ->
      if Id.equal v id then Some b else heap_pred_find_block id rest
  | PointsToUniformBlock (Var v, _, b, _) :: rest ->
      if Id.equal v id then Some b else heap_pred_find_block id rest
  | PointsToExp (Var src, _, Var dest) :: rest
    when Id.equal dest id ->
      (match heap_pred_find_block src spatial with
       | Some b -> Some b
       | None -> heap_pred_find_block id rest)
  | _ :: rest -> heap_pred_find_block id rest

(** Finds size of block with [id] inside [spatial] *)
let rec heap_pred_block_size_find_opt id spatial =
  match spatial with
    [] -> None
  | PointsToBlock (_, size, block) :: rest ->
    if Id.equal block.id id
    then eval_expr_to_int64 size
    else heap_pred_block_size_find_opt id rest
  | PointsToUniformBlock (_, size, block, _) :: rest ->
    if Id.equal block.id id
    then eval_expr_to_int64 size
    else heap_pred_block_size_find_opt id rest
  | _ :: rest -> heap_pred_block_size_find_opt id rest

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

(** Searches for PointsToBlock | PointsToUniformBlock predicates,
    if none found, searches for PointsToExp predicates.
    [id] must be a canonical identifier of a pointer typed variable *)
let rec heap_pred_find_opt id f =
  let rec traverse l found_exp =
    match l with
      [] -> None
    | (PointsToBlock (src, _, _)) as p :: _
      when expr_contains_var_with_id id src ->
        Some p
    | (PointsToUniformBlock (src, _, _, _)) as p :: _
      when expr_contains_var_with_id id src ->
        Some p
    | (PointsToExp (src, _, _)) as p :: rest
      when expr_contains_var_with_id id src ->
        traverse rest (Some p)
    | (PointsToExp (_, _, dest)) as p :: rest
      when expr_contains_var_with_id id dest ->
        traverse rest (Some p)
    | _ :: rest ->
      traverse rest found_exp
  in
  traverse f.spatial None

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

(** Only takes PointsToBlock predicates. [id] must be a canonical identifier of a pointer typed variable. *)
let heap_pred_take_opt id spatial =
  let rec traverse acc = function
    [] -> None
  | (PointsToBlock (src, _, _) as hp) :: l
    when expr_contains_var_with_id id src ->
      Some (hp, List.rev_append acc l)
  | (PointsToUniformBlock (src, _, _, _) as hp) :: l
    when expr_contains_var_with_id id src ->
      Some (hp, List.rev_append acc l)
  | hp :: l ->
    traverse (hp :: acc) l
  in
  traverse [] spatial
