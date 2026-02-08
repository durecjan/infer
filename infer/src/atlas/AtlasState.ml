
module Formula = AtlasFormula
module Id = AtlasFormula.Id

module SubstMap = Stdlib.Map.Make (Id)

type t = {
  formula: Formula.t;
  vars: (Var.t * Id.t) list;
  subst: Id.t SubstMap.t
}

let empty = {
  formula = Formula.empty;
  vars = [];
  subst = SubstMap.empty;
}

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

let get_variable_id v s =
  match Formula.lookup_variable_id v s.vars with
  | None -> None
  | Some id -> Some (canonical_id s.subst id)

let subst_add ~from_ ~to_ s =
  let from_canonical = canonical_id s.subst from_ in
  let to_canonical = canonical_id s.subst to_ in
  if Id.equal from_canonical to_canonical then
    s
  else
    { s with subst = SubstMap.add from_canonical to_canonical s.subst }

let subst_to_string vars subst =
  let traversal =
    SubstMap.fold
    (fun from_ to_ traversal ->
      traversal ^ Formula.Expr.var_to_string vars from_ ^ "=" ^ Formula.Expr.var_to_string vars to_ ^ ";")
    subst
    "{"
  in
  traversal ^ "}"

let to_string state = 
  Formula.to_string state.vars state.formula ^ "\n---------------\n" ^ subst_to_string state.vars state.subst ^ "\n---------------"