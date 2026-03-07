
module Formula = AtlasFormula
module Id = AtlasFormula.Id
module Expr = AtlasFormula.Expr

module VarIdMap = Stdlib.Map.Make (Id)

type status = Ok | Error of IssueType.t option * Location.t option

type t = {
  current: Formula.t;             (* current formula *)
  missing: Formula.t;             (* missing part of formula *)
  vars: (Var.t * Id.t) list;      (* variable association list *)
  types: Typ.t VarIdMap.t;        (* type map *)
  subst: Id.t VarIdMap.t;         (* variable id substitution map *)
  status: status;                 (* status = Ok | Error *)
}

let empty = {
  current = Formula.empty;
  missing = Formula.empty;
  vars = [];
  types = VarIdMap.empty;
  subst = VarIdMap.empty;
  status = Ok;
}


(** Searches for canonical Id of variable [v], using state [s] *)
let rec get_canonical_var_id v s =
  match Formula.lookup_variable_id v s.vars with
  | None -> None
  | Some id -> Some (canonical_id s.subst id)

and canonical_id subst id =
  match VarIdMap.find_opt id subst with
  | None -> id
  | Some id' -> canonical_id subst id'

(** Adds substitution between Ids [~from], [~to] to state [s] *)
let subst_add ~from_ ~to_ s =
  let from_canonical = canonical_id s.subst from_ in
  let to_canonical = canonical_id s.subst to_ in
  if Id.equal from_canonical to_canonical then
    s
  else
    { s with subst = VarIdMap.add from_canonical to_canonical s.subst }

(** Converts SIL Exp.t [e] to custom Expr.t interpretation.
    If a known variable is encountered, it's canonical Id
    is used in the conversion. If the variable is unknown,
    it is converted as Expr.Undef *)
let rec sil_exp_to_expr e tenv s =
  match e with
    Exp.Cast (_, inner) -> sil_exp_to_expr inner tenv s
  | Exp.Const c -> sil_const_exp_to_expr c
  | Exp.Sizeof sz -> sil_sizeof_exp_to_expr sz
  | Exp.Lvar pvar -> begin match
    get_canonical_var_id (Var.of_pvar pvar) s with
      Some id ->
      Expr.Var id
    | None ->
      if Pvar.is_return pvar then
        Expr.ret
      else
        (* TODO could be a global variable *)
        Expr.Undef
    end
  | Exp.Var ident -> begin match
    get_canonical_var_id (Var.of_id ident) s with
      Some id ->
      Expr.Var id
    | None ->
      Expr.Undef
    end
  | Exp.UnOp (op, exp, _) ->
    let exp' = sil_exp_to_expr exp tenv s in
    let op' = sil_unop_exp_to_expr op in
    Expr.UnOp (op', exp')
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


let sil_get_pointer_variable_id exp s =
  let vars = Exp.free_vars exp |> Sequence.to_list in
  let var_ids = List.map vars
    ~f:(fun ident ->
      get_canonical_var_id (Var.of_id ident) s)
  in
  let pointers = List.filter var_ids
    ~f:(fun id ->
      match id with
      | None -> false (* should not really happen, unless global variable *)
      | Some id ->
        begin match VarIdMap.find_opt id s.types with
        | Some typ -> Typ.is_pointer typ
        | None -> false
      end)
  in
  match pointers with
  | [Some base] -> Some base
  | _ -> None


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
      traversal ^ Formula.Expr.var_to_string vars from_ ^ "==" ^ Formula.Expr.var_to_string vars to_ ^ ";")
    subst
    "{"
  in
  traversal ^ "}"

and status_to_string s =
  match s with
    Ok ->
      "OK\n"
  | Error (Some issue, Some loc) ->
    "ERROR\n" ^
    "ISSUE=" ^ issue.unique_id ^ "\n" ^
    "LOCATION=" ^ loc_to_string loc ^ "\n"
  | Error (Some issue, None) ->
    "ERROR\n" ^
    "ISSUE=" ^ issue.unique_id ^ "\n"
  | Error (None, Some loc) ->
    "ERROR\n" ^
    "LOCATION=" ^ loc_to_string loc ^ "\n"
  | Error (None, None) ->
    "ERROR\n"

and loc_to_string loc = 
  let open Location in
  "[line " ^
  Int.to_string (loc.line) ^
  "; column " ^
  Int.to_string (loc.col) ^
  "]"

and vars_to_string vars =
  String.concat (
    List.map vars
    ~f:(fun (var, id) ->
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

(* debugging prints *)

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

(** TODO: for now aggregating arithmetic operations should be enough *)
let rec expr_normalize expr state =
  let open Expr in 
  let norm = expr_normalize in
  match expr with
    Var _ | Const _ | Undef ->
      expr
  | UnOp (op, e) ->
    let e' = norm e state in
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
    let e1' = norm e1 state in
    let e2' = norm e2 state in
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

(** Evaluates [expr], handling BinOp | Const | Var ,
    where Var must have a chain of pure constraints,
    eventually leading to Const. If any part fails
    to evaluate, method returns None *)
let eval_state_expr_to_int64_opt expr state = (* atp i have a milion eval_to_int64, need to refactor again *)
  let open Formula in
  let open Expr in
  (* TODO a lot of None cases, revisit *)
  let rec eval acc = function
      Var id -> begin match
        lookup_pure_const_exp_of_id id state.current.pure with
          Some e -> eval acc e
        | None -> None 
      end
    | BinOp (Pplus, e1, e2) ->
      begin match eval acc e1 with
        Some acc1 -> eval acc1 e2
      | None ->
          match eval acc e2 with
            Some acc2 -> eval acc2 e1
          | None -> None
      end
    | BinOp (Pminus, e, Const (Int i)) ->
        eval (Stdlib.Int64.sub acc i) e
    | Const (Int i) ->
        Some (Stdlib.Int64.add acc i)
    | _ ->
      None
  in
  eval 0L expr

(** Searches through [state] heap predicates (both current and missing) and looks for PointsToExp with [dest],
    then proceeeds to look for PointsToBlock | PointsToUniformBlock using the obtained src. Returns everything
    that was found, meaning (PointsToExp option * (PointsToBlock | PointsToUniformBlock) option). [dest] expression
    must be normalized! *)
let rec heap_pred_find_opt_block_points_to_by_dest dest state =
  match find_points_to_exp dest state.missing.spatial,
    find_points_to_exp dest state.current.spatial
  with
  | Some (src, points_to_exp), None
  | None, Some (src, points_to_exp) ->
    begin match find_points_to_block src state.missing.spatial,
      find_points_to_block src state.current.spatial
    with
    | Some points_to_block, None
    | None, Some points_to_block ->
      (Some points_to_exp, Some points_to_block)
    | _ ->
      (Some points_to_exp, None)
    end
  | _ ->
    (None, None)

  and find_points_to_exp dest = function
  | [] -> None
  | Formula.PointsToExp (src, _, dest') as hp :: _
    when Expr.equal dest' dest ->
      Some (src, hp)
  | _ :: rest ->
    find_points_to_exp dest rest

  and find_points_to_block src = function
  | [] -> None
  | Formula.PointsToBlock (src', _, _) as hp :: _
    when Expr.equal src' src ->
      Some hp
  | Formula.PointsToUniformBlock (src', _, _, _) as hp :: _
    when Expr.equal src' src ->
      Some hp
  | _ :: rest ->
    find_points_to_block src rest

(** Traverses both current and missing pure constraints of [state], looking for (Base(Var [id])==exp) *)
let state_find_pure_base_expr id state =
  let curr_base, miss_base =
    Formula.find_pure_base_expr id state.current.pure,
    Formula.find_pure_base_expr id state.missing.pure
  in
  match curr_base, miss_base with
  | Some b, None | None, Some b ->
    Some b
  | _ ->
    None

(** Traverses both current and missing heap predicates of [state], looking for PointsToBlock (Var [id], size, dest) *)
let state_heap_pred_find_block_points_to id state =
  let curr_hp, miss_hp =
    Formula.heap_pred_find_block_points_to id state.current.spatial,
    Formula.heap_pred_find_block_points_to id state.missing.spatial
  in
  match curr_hp, miss_hp with
  | Some hp, None | None, Some hp ->
    Some hp
  | _ ->
    None

(** Traverses both current and missing heap predicates of [state], looking for PointsToExp ([src], size, dest) *)
let state_heap_pred_find_exp_points_to src state =
  let curr_hp, miss_hp =
    Formula.heap_pred_find_exp_points_to src state.current.spatial,
    Formula.heap_pred_find_exp_points_to src state.missing.spatial
  in
  match curr_hp, miss_hp with
  | Some hp, None | None, Some hp ->
    Some hp
  | _ ->
    None
