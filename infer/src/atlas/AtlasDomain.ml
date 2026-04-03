
module Formula = AtlasFormula
module Expr = Formula.Expr
module Id = Formula.Id
module State = AtlasState

open !Formula

(* ==================== State equality ==================== *)

let rec state_equal s1 s2 =
  let open State in
  status_equal s1.status s2.status &&
  spatial_equal s1.current.spatial s2.current.spatial &&
  spatial_equal s1.missing.spatial s2.missing.spatial &&
  pure_equal s1.current.pure s2.current.pure &&
  pure_equal s1.missing.pure s2.missing.pure &&
  VarIdMap.equal subst_expr_equal s1.subst s2.subst &&
  VarIdMap.equal Var.equal s1.vars s2.vars &&
  VarIdMap.equal Typ.equal s1.types s2.types

and spatial_equal s1 s2 =
  List.equal heap_pred_equal s1 s2

and pure_equal p1 p2 =
  List.equal Expr.equal p1 p2

and status_equal s1 s2 =
  let open State in
  match s1, s2 with
  | Ok, Ok -> true
  | Error (mess1, loc1, instr1), Error (mess2, loc2, instr2) ->
    Sil.equal_instr instr1 instr2 &&
    Location.equal loc1 loc2 &&
    String.equal mess1 mess2
  | Ok, Error _ | Error _, Ok -> false

and subst_expr_equal se1 se2 =
  let open State in
  match se1, se2 with
  | Var id1, Var id2 -> Id.equal id1 id2
  | Ptr { base = b1; offset = 0L }, Var b2 -> Id.equal b1 b2
  | Var b1, Ptr { base = b2; offset = 0L } -> Id.equal b1 b2
  | Ptr { base = b1; offset = off1 }, Ptr { base = b2; offset = off2 } ->
    Id.equal b1 b2 && Int64.equal off1 off2
  | _ -> false

(* ==================== Disjunctive domain ==================== *)

(** Disjunctive domain — each disjunct is a single abstract state.
    Satisfies [AbstractDomain.Disjunct] for use with [MakeDisjunctive] *)
module DisjDomain = struct
  type t = State.t

  let pp fmt state =
    Format.fprintf fmt "%s" (State.to_string state)

  (** Structural implication — identical states.
      TODO: implement proper State.leq as subset check on spatial/pure *)
  let leq ~lhs ~rhs = state_equal lhs rhs

  (** Fast structural equality for deduplication at CFG join points *)
  let equal_fast = state_equal

  (** All states represent concrete states *)
  let is_normal _ = true

  (** C has no exceptions *)
  let is_exceptional _ = false

  (** All states are executable *)
  let is_executable _ = true

  (** Should never be called for C — no exceptional states to convert *)
  let exceptional_to_normal s = s
end

(** Trivial non-disjunctive domain — we track nothing across disjuncts *)
module NonDisjDomain = AbstractDomain.BottomTopLifted (AbstractDomain.Empty)
