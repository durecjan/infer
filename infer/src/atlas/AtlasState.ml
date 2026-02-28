
module Formula = AtlasFormula
module Id = AtlasFormula.Id
module Expr = AtlasFormula.Expr

module SubstMap = Stdlib.Map.Make (Id)

type status = Ok | Error

type t = {
  current: Formula.t;             (* current formula *)
  missing: Formula.t;             (* missing part of formula *)
  vars: (Var.t * Id.t) list;      (* variable association list *)
  subst: Id.t SubstMap.t;         (* variable id substitution map *)
  status: status;                 (* status = Ok | Error *)
  err_loc: Location.t option;     (* location of error *)
  err_issue: IssueType.t option;  (* issue type of error *)
}

let empty = {
  current = Formula.empty;
  missing = Formula.empty;
  vars = [];
  subst = SubstMap.empty;
  status = Ok;
  err_loc = None;
  err_issue = None;
}


(** Searches for canonical Id of variable [v], using state [s],
    if not found, makes fresh Id *)
let rec get_existing_canonical_or_mk_fresh_id_of_var v s =
  match Formula.lookup_variable_id v s.vars with
  | Some id ->
    let canonical = canonical_id s.subst id in
    (canonical, s)
  | None ->
    let id = Id.fresh () in
    (id, { s with vars = (v, id) :: s.vars })

and canonical_id subst id =
  match SubstMap.find_opt id subst with
  | None -> id
  | Some id' -> canonical_id subst id'

(** Searches for canonical Id of variable [v], using state [s] *)
let get_variable_id v s =
  match Formula.lookup_variable_id v s.vars with
  | None -> None
  | Some id -> Some (canonical_id s.subst id)

(** Adds substitution between Ids [~from], [~to] to state [s] *)
let subst_add ~from_ ~to_ s =
  let from_canonical = canonical_id s.subst from_ in
  let to_canonical = canonical_id s.subst to_ in
  if Id.equal from_canonical to_canonical then
    s
  else
    { s with subst = SubstMap.add from_canonical to_canonical s.subst }

(** Converts SIL Exp.t [e] to custom Expr.t interpretation.
    If a known variable is encountered, it's canonical Id
    is used in the conversion. If the variable is unknown,
    a new Id is created and the state [s] is modified. *)
let rec sil_exp_to_expr e s =
  match e with
    Exp.Cast (_, inner) -> sil_exp_to_expr inner s
  | Exp.Const c -> sil_const_exp_to_expr c s
  | Exp.Sizeof sz -> sil_sizeof_exp_to_expr sz s
  | Exp.Lvar pvar ->
    let (id, state) =
      get_existing_canonical_or_mk_fresh_id_of_var (Var.of_pvar pvar) s
    in (Expr.Var id, state)
  | Exp.Var ident ->
    let (id, state) =
      get_existing_canonical_or_mk_fresh_id_of_var (Var.of_id ident) s
    in (Expr.Var id, state)
  | Exp.UnOp (op, exp, _) ->
    let (exp', state) = sil_exp_to_expr exp s in
    let op' = sil_unop_exp_to_expr op in
    (Expr.UnOp (op', exp'), state)
  | Exp.BinOp ((Binop.Gt | Binop.Ge) as op, e1, e2) ->
    let (lhs, state) = sil_exp_to_expr e1 s in
    let (rhs, state) = sil_exp_to_expr e2 state in
    let op' = sil_binop_exp_to_expr op in
    (Expr.BinOp (op', rhs, lhs), state)
  | Exp.BinOp (op, e1, e2) ->
    let (lhs, state) = sil_exp_to_expr e1 s in
    let (rhs, state) = sil_exp_to_expr e2 state in
    let op' = sil_binop_exp_to_expr op in
    (Expr.BinOp (op', lhs, rhs), state)
  | Exp.Lfield ({ exp; is_implicit = _ }, _, _) ->
      sil_exp_to_expr exp s
  | Exp.Lindex (base, index) ->
      let (base', state) = sil_exp_to_expr base s in
      let (index', state) = sil_exp_to_expr index state in
      (Expr.BinOp (Pplus, base', index'), state)
  | _ -> (Expr.Undef, s)

and sil_const_exp_to_expr c s =
  let e = match c with
    Const.Cint i -> Expr.Const (Int (Z.to_int64 (IntLit.to_big_int i)))
  | Const.Cstr str -> Expr.Const (String str)
  | Const.Cfloat f -> Expr.Const (Float f)
  | Const.Cfun _ | Const.Cclass _ -> Expr.Undef
  in (e, s)

and sil_sizeof_exp_to_expr sz s =
  let open Exp in
  let e = match sz with
  | { nbytes = Some i } -> Expr.Const (Int (Int.to_int64 i))
  (* | { nbytes = Some i; dynamic_length = exp } *)
  | _ -> Expr.Undef
  in (e, s)

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
  "Current:\n" ^
  Formula.to_string state.vars state.current 
  ^ "\n---------------\nMissing:"
  ^ Formula.to_string state.vars state.missing
  ^ "\n---------------\nSubstitutions:"
  ^ subst_to_string state.vars state.subst
  ^ "\n---------------"

and subst_to_string vars subst =
  let traversal =
    SubstMap.fold
    (fun from_ to_ traversal ->
      traversal ^ Formula.Expr.var_to_string vars from_ ^ "=" ^ Formula.Expr.var_to_string vars to_ ^ ";")
    subst
    "{"
  in
  traversal ^ "}"


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