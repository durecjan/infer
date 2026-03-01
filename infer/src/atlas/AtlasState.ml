
module Formula = AtlasFormula
module Id = AtlasFormula.Id
module Expr = AtlasFormula.Expr

module VarIdMap = Stdlib.Map.Make (Id)

type status = Ok | Error

type t = {
  current: Formula.t;             (* current formula *)
  missing: Formula.t;             (* missing part of formula *)
  vars: (Var.t * Id.t) list;      (* variable association list *)
  types: Typ.t VarIdMap.t;           (* type map *)
  subst: Id.t VarIdMap.t;            (* variable id substitution map *)
  status: status;                 (* status = Ok | Error *)
  err_loc: Location.t option;     (* location of error *)
  err_issue: IssueType.t option;  (* issue type of error *)
}

let empty = {
  current = Formula.empty;
  missing = Formula.empty;
  vars = [];
  types = VarIdMap.empty;
  subst = VarIdMap.empty;
  status = Ok;
  err_loc = None;
  err_issue = None;
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
let rec sil_exp_to_expr e s =
  match Exp.ignore_cast e with
    Exp.Cast (_, inner) -> sil_exp_to_expr inner s
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
    let exp' = sil_exp_to_expr exp s in
    let op' = sil_unop_exp_to_expr op in
    Expr.UnOp (op', exp')
  | Exp.BinOp ((Binop.Gt | Binop.Ge) as op, e1, e2) ->
    let lhs = sil_exp_to_expr e1 s in
    let rhs = sil_exp_to_expr e2 s in
    let op' = sil_binop_exp_to_expr op in
    Expr.BinOp (op', rhs, lhs)
  | Exp.BinOp (op, e1, e2) ->
    let lhs = sil_exp_to_expr e1 s in
    let rhs = sil_exp_to_expr e2 s in
    let op' = sil_binop_exp_to_expr op in
    Expr.BinOp (op', lhs, rhs)
  | Exp.Lfield ({ exp; is_implicit = _ }, _fieldname, typ) ->
      let base = sil_exp_to_expr exp s in
      begin match sil_lfield_offset_bytes (*fieldname*) typ with
        Some off ->
        Expr.BinOp (Expr.Pplus, base, Const (Int off))
      | None ->
        (* TODO rethink this fallback idea vs. Expr.Undef offset *)
        base
      end
  | Exp.Lindex (base, index) ->
      let base' = sil_exp_to_expr base s in
      let index' = sil_exp_to_expr index s in
      Expr.BinOp (Pplus, base', index')
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

and sil_lfield_offset_bytes (*tenv*) (*fieldname*) typ =
  sil_lindex_element_size typ

and sil_lindex_element_size typ =
  let open Typ in
  match typ.desc with
  (* for now assume 64bit architecture *)
  (* TODO wire up to infer's runtime info *)
    Tint ikind ->
      begin match ikind with
        IChar -> Some 1L
      | ISChar -> Some 1L
      | IUChar -> Some 1L
      | IBool -> Some 1L
      | IInt -> Some 4L
      | IUInt -> Some 4L
      | IShort -> Some 2L
      | IUShort -> Some 2L
      | ILong -> Some 8L
      | IULong -> Some 8L
      | ILongLong -> Some 16L
      | IULongLong -> Some 16L
      | I128 -> Some 32L
      | IU128 -> Some 32L
      end
  | Tfloat _ -> None
  | Tvoid -> None
  | Tfun _ -> None
  | Tptr (_, _) -> None
  | Tstruct _ -> None
  | TVar _ -> None
  | Tarray _ -> None

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


let rec to_string state =
  status_to_string state.status ^
  "Current:\n" ^
  Formula.to_string state.vars state.current 
  ^ "\n----------------\nMissing:\n"
  ^ Formula.to_string state.vars state.missing
  ^ "\n----------------\nSubstitutions:\n"
  ^ subst_to_string state.vars state.subst
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
    Ok -> "" | Error -> "ERROR_STATE\n"


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