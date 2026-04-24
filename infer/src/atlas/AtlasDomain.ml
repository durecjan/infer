
module Formula = AtlasFormula
module Expr = Formula.Expr
module Id = Formula.Id
module State = AtlasState

open !Formula

(* ==================== Alpha-equality ==================== *)

(** Bijective mapping between cell ids for alpha-equivalence.
    Maps ids from state1 to state2 (forward) and state2 to state1 (backward).
    Returns [None] if a conflict is detected (same id mapped to different partners) *)
type bijection = {
  forward: int VarIdMap.t;   (** state1 id → state2 id *)
  backward: int VarIdMap.t;  (** state2 id → state1 id *)
}

let empty_bijection = { forward = VarIdMap.empty; backward = VarIdMap.empty }

(** Extends the bijection with a new pair [(id1, id2)].
    Returns [Some bijection] on success, [None] on conflict *)
let extend_bijection bij id1 id2 =
  match VarIdMap.find_opt id1 bij.forward, VarIdMap.find_opt id2 bij.backward with
  | Some id2', _ when not (Id.equal id2 id2') -> None
  | _, Some id1' when not (Id.equal id1 id1') -> None
  | Some _, Some _ -> Some bij  (* already recorded *)
  | _ ->
    Some { forward = VarIdMap.add id1 id2 bij.forward;
           backward = VarIdMap.add id2 id1 bij.backward }

(** Checks whether [id] is a cell id (not a program variable).
    Cell ids are not present in the vars map *)
let is_cell_id id (s : State.t) =
  not (VarIdMap.mem id s.vars)

(** Checks whether types match for two ids across states *)
let types_match id1 (s1 : State.t) id2 (s2 : State.t) =
  match VarIdMap.find_opt id1 s1.types, VarIdMap.find_opt id2 s2.types with
  | Some t1, Some t2 -> Typ.equal t1 t2
  | None, None -> true
  | _ -> false

(** Compares two ids under the bijection. If both are pvars (same id expected),
    compares directly. If both are cell ids, extends the bijection and checks types.
    Returns [Some updated_bijection] on match, [None] on mismatch *)
let match_ids bij id1 (s1 : State.t) id2 (s2 : State.t) =
  let cell1 = is_cell_id id1 s1 in
  let cell2 = is_cell_id id2 s2 in
  match cell1, cell2 with
  | false, false ->
    (* Both pvars — must be same id *)
    if Id.equal id1 id2 then Some bij else None
  | true, true ->
    (* Both cell ids — extend bijection + check types *)
    begin match extend_bijection bij id1 id2 with
    | Some bij' ->
      if types_match id1 s1 id2 s2 then Some bij' else None
    | None -> None
    end
  | _ -> None  (* one cell, one pvar — mismatch *)

(** Compares two expressions under the bijection, extending it as needed.
    Returns [Some updated_bijection] on match, [None] on mismatch *)
let rec match_expr bij (s1 : State.t) (s2 : State.t) e1 e2 =
  match e1, e2 with
  | Expr.Var id1, Expr.Var id2 ->
    match_ids bij id1 s1 id2 s2
  | Expr.Const c1, Expr.Const c2 ->
    if Expr.equal (Const c1) (Const c2) then Some bij else None
  | Expr.UnOp (op1, e1'), Expr.UnOp (op2, e2') ->
    if Expr.unop_equal op1 op2 then match_expr bij s1 s2 e1' e2'
    else None
  | Expr.BinOp (op1, l1, r1), Expr.BinOp (op2, l2, r2) ->
    if Expr.binop_equal op1 op2 then
      match match_expr bij s1 s2 l1 l2 with
      | Some bij' -> match_expr bij' s1 s2 r1 r2
      | None -> None
    else None
  | Expr.Undef, Expr.Undef -> Some bij
  | _ -> None

(** Status equality — Ok matches Ok, Error matches Error with same message/location/instr *)
let status_equal s1 s2 =
  let open State in
  match s1, s2 with
  | Ok, Ok -> true
  | Error (_, _, instr1), Error (_, _, instr2) ->
    Sil.equal_instr instr1 instr2
  | Ok, Error _ | Error _, Ok -> false

(** Step 1: Compare substitutions under alpha-equivalence.
    Iterates both subst maps in key order. Keys (pvar ids) must match.
    Values are compared structurally, building the cell id bijection.
    Returns [Some bijection] on success, [None] on mismatch *)
let match_subst (s1 : State.t) (s2 : State.t) bij =
  let open State in
  let bindings1 = VarIdMap.bindings s1.subst in
  let bindings2 = VarIdMap.bindings s2.subst in
  if List.length bindings1 <> List.length bindings2 then None
  else let rec aux bij = function
    | [], [] -> Some bij
    | (k1, v1) :: rest1, (k2, v2) :: rest2 ->
      if not (Id.equal k1 k2) then None
      else begin match v1, v2 with
      | Var id1, Var id2 ->
        begin match match_ids bij id1 s1 id2 s2 with
        | Some bij' -> aux bij' (rest1, rest2)
        | None -> None
        end
      | Ptr { base = b1; offset = off1 }, Ptr { base = b2; offset = off2 } ->
        if not (Int64.equal off1 off2) then None
        else begin match match_ids bij b1 s1 b2 s2 with
        | Some bij' -> aux bij' (rest1, rest2)
        | None -> None
        end
      | Var id1, Ptr { base = b2; offset = 0L } ->
        begin match match_ids bij id1 s1 b2 s2 with
        | Some bij' -> aux bij' (rest1, rest2)
        | None -> None
        end
      | Ptr { base = b1; offset = 0L }, Var id2 ->
        begin match match_ids bij b1 s1 id2 s2 with
        | Some bij' -> aux bij' (rest1, rest2)
        | None -> None
        end
      | _ -> None
      end
    | _ -> None  (* different number of entries *)
  in
  aux bij (bindings1, bindings2)

(** Compares two heap predicates under the bijection.
    Returns [Some updated_bijection] on match, [None] on mismatch *)
let match_heap_pred bij (s1 : State.t) (s2 : State.t) hp1 hp2 =
  match hp1, hp2 with
  | ExpPointsTo (src1, sz1, dst1), ExpPointsTo (src2, sz2, dst2) ->
    begin match match_expr bij s1 s2 src1 src2 with
    | Some bij' ->
      begin match match_expr bij' s1 s2 sz1 sz2 with
      | Some bij'' -> match_expr bij'' s1 s2 dst1 dst2
      | None -> None
      end
    | None -> None
    end
  | BlockPointsTo (src1, sz1), BlockPointsTo (src2, sz2) ->
    begin match match_expr bij s1 s2 src1 src2 with
    | Some bij' -> match_expr bij' s1 s2 sz1 sz2
    | None -> None
    end
  | UniformBlockPointsTo (src1, sz1, v1), UniformBlockPointsTo (src2, sz2, v2) ->
    begin match match_expr bij s1 s2 src1 src2 with
    | Some bij' ->
      begin match match_expr bij' s1 s2 sz1 sz2 with
      | Some bij'' -> match_expr bij'' s1 s2 v1 v2
      | None -> None
      end
    | None -> None
    end
  | _ -> None

(** Step 2: Compare spatial predicates under alpha-equivalence.
    Lists must have the same length and predicates must match pairwise.
    Returns [Some updated_bijection] on success, [None] on mismatch *)
let match_spatial bij (s1 : State.t) (s2 : State.t) sp1 sp2 =
  let rec aux bij = function
    | [], [] -> Some bij
    | hp1 :: rest1, hp2 :: rest2 ->
      begin match match_heap_pred bij s1 s2 hp1 hp2 with
      | Some bij' -> aux bij' (rest1, rest2)
      | None -> None
      end
    | _ -> None
  in
  aux bij (sp1, sp2)

(** Step 3: Compare pure constraints under alpha-equivalence.
    Lists must have the same length and constraints must match pairwise.
    Returns [Some updated_bijection] on success, [None] on mismatch *)
let match_pure bij (s1 : State.t) (s2 : State.t) p1 p2 =
  let rec aux bij = function
    | [], [] -> Some bij
    | e1 :: rest1, e2 :: rest2 ->
      begin match match_expr bij s1 s2 e1 e2 with
      | Some bij' -> aux bij' (rest1, rest2)
      | None -> None
      end
    | _ -> None
  in
  aux bij (p1, p2)

(** Alpha-equality: two states are equal if there exists a bijective mapping
    between their cell ids such that status, vars, subst, spatial, and pure
    all match under that mapping. Types are checked inline during id matching.
    Short-circuits on cheap structural checks before attempting the mapping.

    Known limitation: spatial and pure lists are compared positionally —
    predicates must appear in the same order in both states. Order-independent
    matching would require bipartite permutation search. In practice this is
    sufficient because both states are produced by the same transfer functions
    traversing the same CFG path, so predicate order is deterministic *)
let state_alpha_equal s1 s2 =
  let open State in
  (* Quick structural checks first *)
  if not (status_equal s1.status s2.status) then false
  else if not (VarIdMap.equal Var.equal s1.vars s2.vars) then false
  else if List.length s1.current.spatial <> List.length s2.current.spatial then false
  else if List.length s1.missing.spatial <> List.length s2.missing.spatial then false
  else if List.length s1.current.pure <> List.length s2.current.pure then false
  else if List.length s1.missing.pure <> List.length s2.missing.pure then false
  else
    (* Build bijection through subst → spatial → pure *)
    match match_subst s1 s2 empty_bijection with
    | None -> false
    | Some bij ->
      match match_spatial bij s1 s2 s1.current.spatial s2.current.spatial with
      | None -> false
      | Some bij ->
        match match_spatial bij s1 s2 s1.missing.spatial s2.missing.spatial with
        | None -> false
        | Some bij ->
          match match_pure bij s1 s2 s1.current.pure s2.current.pure with
          | None -> false
          | Some bij ->
            match match_pure bij s1 s2 s1.missing.pure s2.missing.pure with
            | None -> false
            | Some _ -> true

(* ==================== State subset ==================== *)

(** Subset matching for substitutions under alpha-equivalence.
    Every binding in [s1.subst] must find a matching binding in [s2.subst].
    [s2.subst] may contain additional entries not present in [s1.subst].
    Both binding lists are sorted by key, so s2-only entries are skipped.
    Returns [Some bijection] on success, [None] on mismatch *)
let match_subst_subset (s1 : State.t) (s2 : State.t) bij =
  let open State in
  let bindings1 = VarIdMap.bindings s1.subst in
  let bindings2 = VarIdMap.bindings s2.subst in
  if List.length bindings1 > List.length bindings2 then None
  else let rec aux bij = function
    | [], _ -> Some bij  (* all s1 entries matched *)
    | _, [] -> None      (* s1 has unmatched entries *)
    | (k1, v1) :: rest1, (k2, v2) :: rest2 ->
      let cmp = Id.compare k1 k2 in
      if cmp > 0 then
        (* k2 < k1: s2 has extra entry, skip it *)
        aux bij ((k1, v1) :: rest1, rest2)
      else if cmp < 0 then
        (* k1 < k2: s1 entry not found in s2 *)
        None
      else begin match v1, v2 with
      | Var id1, Var id2 ->
        begin match match_ids bij id1 s1 id2 s2 with
        | Some bij' -> aux bij' (rest1, rest2)
        | None -> None
        end
      | Ptr { base = b1; offset = off1 }, Ptr { base = b2; offset = off2 } ->
        if not (Int64.equal off1 off2) then None
        else begin match match_ids bij b1 s1 b2 s2 with
        | Some bij' -> aux bij' (rest1, rest2)
        | None -> None
        end
      | Var id1, Ptr { base = b2; offset = 0L } ->
        begin match match_ids bij id1 s1 b2 s2 with
        | Some bij' -> aux bij' (rest1, rest2)
        | None -> None
        end
      | Ptr { base = b1; offset = 0L }, Var id2 ->
        begin match match_ids bij b1 s1 id2 s2 with
        | Some bij' -> aux bij' (rest1, rest2)
        | None -> None
        end
      | _ -> None
      end
  in
  aux bij (bindings1, bindings2)

(** Subset matching for spatial predicates under alpha-equivalence.
    Every predicate in [sp_rhs] must find a matching predicate in [sp_lhs].
    [sp_lhs] may contain additional unmatched predicates.
    Matched predicates are removed from candidates to prevent double-matching.
    Returns [Some updated_bijection] on success, [None] on mismatch *)
let match_spatial_subset bij (s1 : State.t) (s2 : State.t) sp_lhs sp_rhs =
  let rec find_match bij hp_rhs checked = function
    | [] -> None
    | hp_lhs :: rest ->
      begin match match_heap_pred bij s1 s2 hp_lhs hp_rhs with
      | Some bij' -> Some (bij', List.rev_append checked rest)
      | None -> find_match bij hp_rhs (hp_lhs :: checked) rest
      end
  in
  let rec aux bij candidates = function
    | [] -> Some bij
    | hp_rhs :: rest_rhs ->
      begin match find_match bij hp_rhs [] candidates with
      | Some (bij', remaining) -> aux bij' remaining rest_rhs
      | None -> None
      end
  in
  aux bij sp_lhs sp_rhs

(** Subset matching for pure constraints under alpha-equivalence.
    Every constraint in [p_rhs] must find a matching constraint in [p_lhs].
    [p_lhs] may contain additional unmatched constraints.
    Returns [Some updated_bijection] on success, [None] on mismatch *)
let match_pure_subset bij (s1 : State.t) (s2 : State.t) p_lhs p_rhs =
  let rec find_match bij e_rhs checked = function
    | [] -> None
    | e_lhs :: rest ->
      begin match match_expr bij s1 s2 e_lhs e_rhs with
      | Some bij' -> Some (bij', List.rev_append checked rest)
      | None -> find_match bij e_rhs (e_lhs :: checked) rest
      end
  in
  let rec aux bij candidates = function
    | [] -> Some bij
    | e_rhs :: rest_rhs ->
      begin match find_match bij e_rhs [] candidates with
      | Some (bij', remaining) -> aux bij' remaining rest_rhs
      | None -> None
      end
  in
  aux bij p_lhs p_rhs

(** State subset: [state_leq s1 s2] holds when [s1]'s formula is contained
    within [s2]'s — every substitution, spatial predicate, and pure constraint
    in [s1] has a matching counterpart in [s2] (under the cell id bijection),
    but [s2] may contain additional entries not present in [s1].

    Same known limitations as [state_alpha_equal]: greedy matching without
    backtracking. Sufficient in practice for the same reasons *)
let state_leq s1 s2 =
  let open State in
  if not (status_equal s1.status s2.status) then false
  else if not (VarIdMap.equal Var.equal s1.vars s2.vars) then false
  else if List.length s1.current.spatial > List.length s2.current.spatial then false
  else if List.length s1.missing.spatial > List.length s2.missing.spatial then false
  else if List.length s1.current.pure > List.length s2.current.pure then false
  else if List.length s1.missing.pure > List.length s2.missing.pure then false
  else
    match match_subst_subset s1 s2 empty_bijection with
    | None -> false
    | Some bij ->
      match match_spatial_subset bij s1 s2 s2.current.spatial s1.current.spatial with
      | None -> false
      | Some bij ->
        match match_spatial_subset bij s1 s2 s2.missing.spatial s1.missing.spatial with
        | None -> false
        | Some bij ->
          match match_pure_subset bij s1 s2 s2.current.pure s1.current.pure with
          | None -> false
          | Some bij ->
            match match_pure_subset bij s1 s2 s2.missing.pure s1.missing.pure with
            | None -> false
            | Some _ -> true

(* ==================== Disjunctive domain ==================== *)

(** Disjunctive domain — each disjunct is a single abstract state.
    Satisfies [AbstractDomain.Disjunct] for use with [MakeDisjunctive] *)
module DisjDomain = struct
  type t = State.t

  let pp fmt state =
    Format.fprintf fmt "%s" (State.to_string state)

  (** State implication — lhs is subsumed by rhs if rhs's spatial/pure
      predicates are a subset of lhs's (lhs is at least as specific) *)
  let leq ~lhs ~rhs = state_leq lhs rhs

  (** Fast structural equality for deduplication at CFG join points *)
  let equal_fast = state_alpha_equal

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
