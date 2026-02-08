open! IStd

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

let get_fresh_id = Id.fresh


module HeapCursor = struct
  type t = int [@@deriving compare, equal, hash]

  let cursor = Atomic.make 1

  let get = Atomic.get cursor

  let update (n : int) =
    let rec loop () =
      let current = Atomic.get cursor in
      let next = current + n in
      if Atomic.compare_and_set cursor current next
      then current
      else loop ()
    in
    loop ()

end

let get_heap_cursor = HeapCursor.get

let update_heap_cursor = HeapCursor.update


module Address = struct

  type t =
    | NonTop of int
    | Top
  let of_int (n: int) = NonTop n

  let lt x y =
    match x, y with
    | _, Top | Top, _ ->
      Top
    | NonTop a, NonTop b ->
      if a < b then NonTop 1 else NonTop 0

  let gt x y =
    match x, y with
    | _, Top | Top, _->
      Top
    | NonTop a, NonTop b ->
      if a > b then NonTop 1 else NonTop 0
  
  let le x y =
    match x, y with
    | _, Top | Top, _->
      Top
    | NonTop a, NonTop b ->
      if a <= b then NonTop 1 else NonTop 0

  let ge x y =
    match x, y with
    | _, Top | Top, _->
      Top
    | NonTop a, NonTop b ->
      if a >= b then NonTop 1 else NonTop 0

  let eq x y =
    match x, y with
    | _, Top | Top, _->
      Top
    | NonTop a, NonTop b ->
      if Int.equal a b then NonTop 1 else NonTop 0

  let ne x y =
    match x, y with
    | _, Top | Top, _->
      Top
    | NonTop a, NonTop b ->
      if Int.equal a b then NonTop 0 else NonTop 1

  let add x y =
    match x, y with
    | _, Top | Top, _ -> Top
    | NonTop a, NonTop b -> NonTop (a + b)

  let sub x y =
    match x, y with
    | _, Top | Top, _ -> Top
    | NonTop a, NonTop b -> NonTop (a - b)

  let equal x y =
    match x, y with
    | _, Top | Top, _ ->
      false
    | NonTop a, NonTop b ->
      Int.equal a b

  let leq ~lhs ~rhs =
    match (lhs, rhs) with
    | _, Top -> true
    | Top, NonTop _ -> false
    | NonTop a, NonTop b -> a <= b

  let join a b =
    match (a, b) with
    | Top, _ | _, Top -> Top
    | NonTop x, NonTop y -> NonTop (max x y)

  let widening_threshold = 5

  let widen ~prev ~next ~num_iters =
    match (prev, next) with
    | Top, _ | _, Top -> Top
    | NonTop prev, NonTop next
      when num_iters < widening_threshold ->
        NonTop (max prev next)
    | NonTop _, NonTop _ -> Top

  let pp fmt = function
    | Top -> Format.pp_print_string fmt "Top"
    | NonTop n -> Format.pp_print_int fmt n
end

module Value = struct
  type t =
      Ptr of { block : Id.t; offset : Address.t }
    | Int of int
    | String of string
    | Float of float
    | Top

  let of_int n = Int n

  let of_ptr block offset = Ptr { block = block; offset = offset }

  let of_addr addr = 
    match addr with
    | Address.NonTop n -> Int n
    | Address.Top -> Top

  let leq ~lhs ~rhs =
    match lhs, rhs with
    | _, Top -> true
    | Top, _ -> false
    | Int a, Int b -> a <= b
    | Ptr id1, Ptr id2
      when Id.equal id1.block id2.block ->
        Address.leq ~lhs:id1.offset ~rhs:id2.offset
    | _, _ -> false

  let join v1 v2 =
    match v1, v2 with
    | Top, _ | _, Top -> Top
    | Int a, Int b -> Int (max a b)
    | Ptr id1, Ptr id2
      when Id.equal id1.block id2.block ->
        Ptr 
          { block = id1.block
          ; offset = Address.join id1.offset id2.offset }
    | Ptr _, Ptr _ -> Top
    | _, _ -> Top

  let widening_threshold = 5

  let widen ~prev ~next ~num_iters =
    match prev, next with
    | Top, _ | _, Top -> Top
    | Int a, Int b
      when num_iters < widening_threshold ->
        Int (max a b)
    | Int _, Int _ -> Top
    | Ptr id1, Ptr id2
      when Id.equal id1.block id2.block ->
        Ptr
          { block = id1.block
          ; offset = 
            Address.widen
              ~prev:id1.offset
              ~next:id2.offset
              ~num_iters }
    | _, _ -> Top

  let pp fmt = function
    | Top -> Format.pp_print_string fmt "Top"
    | Int n -> Format.fprintf fmt "Int(%d)" n
    | Float f -> Format.fprintf fmt "Float(%f)" f
    | String s -> Format.fprintf fmt "String(%s)" s
    | Ptr { block; offset } ->
      Format.fprintf fmt "Ptr(block=%a, off=%a)"
      Id.pp block
      Address.pp offset

end

module Block = struct
  type t = 
    { base : Address.t
    ; end_ : Address.t
    ; freed : bool }
  
  let pp fmt block =
    Format.fprintf fmt "{base=%a; end=%a; freed=%b}"
      Address.pp block.base
      Address.pp block.end_
      block.freed

  let leq ~lhs ~rhs =
    Address.leq ~lhs:lhs.base ~rhs:rhs.base &&
    Address.leq ~lhs:lhs.end_ ~rhs:rhs.end_

  let join block1 block2 =
    { base = Address.join block1.base block2.base
    ; end_ = Address.join block1.end_ block2.end_
    ; freed = block1.freed || block2.freed }
  
  let widen ~prev ~next ~num_iters =
    { base = Address.widen ~prev:prev.base ~next:next.base ~num_iters
    ; end_ = Address.widen ~prev:prev.end_ ~next:next.end_ ~num_iters
    ; freed = prev.freed || next.freed }
end

module Heap = AbstractDomain.Map (Id) (Block)

module Stack = struct
  module VarMap = Stdlib.Map.Make(Var)

  type t = Id.t VarMap.t
end

module Env = struct
  module IdMap = Stdlib.Map.Make(Id)

  type t = Value.t IdMap.t
end

module Formula = AtlasFormula

module Domain = struct
  type t =
    { env: Env.t
    ; stack: Stack.t
    ; heap: Heap.t
    ; formula: Formula.t }
  let init =
    { env = Env.IdMap.empty
    ; stack = Stack.VarMap.empty
    ; heap = Heap.empty
    ; formula = Formula.empty }

  let leq ~lhs ~rhs = 
    Heap.leq ~lhs:lhs.heap ~rhs:rhs.heap (* && Formula.leq TODO *)

  let join _lhs _rhs =
    Logging.die Die.InternalError "join not supported yet: domain is path-sensitive"

  let widen ~_prev ~_next ~_num_iters =
    Logging.die Die.InternalError "join not supported yet: domain is path-sensitive"

  let pp_stack_env fmt (stack : Stack.t) (env : Env.t) =
    Format.fprintf fmt "@[<v>Stack/Env:@," ;
    Stack.VarMap.iter
      (fun var av ->
        let value =
          match Env.IdMap.find_opt av env with
          | Some v -> v
          | None -> Value.Top
        in
        Format.fprintf fmt "  %a ↦ %a ↦ %a@,"
          Var.pp var
          Id.pp av
          Value.pp value
      )
      stack ;
    Format.fprintf fmt "@]"

  let pp_heap fmt (heap : Heap.t) =
    Format.fprintf fmt "@[<v>Heap:@," ;
    Heap.iter
      (fun bid block ->
        Format.fprintf fmt
          "  %a: base=%a end=%a freed=%b@,"
          Id.pp bid
          Address.pp block.base
          Address.pp block.end_
          block.freed
      )
      heap ;
    Format.fprintf fmt "@]"

  let pp fmt (astate : t) =
    Format.fprintf fmt "@[<v 0>" ;
    pp_stack_env fmt astate.stack astate.env ;
    pp_heap fmt astate.heap ;
    Format.fprintf fmt "@]"
end

type t = Domain.t

let empty = Domain.init

let leq ~lhs ~rhs = Domain.leq ~lhs ~rhs

let join = Domain.join

let widen ~prev ~next ~num_iters = Domain.widen ~_prev:prev ~_next:next ~_num_iters:num_iters

let pp fmt astate = Domain.pp fmt astate

let alloc_block (size: Value.t) (astate: t) : t * Value.t =
  let id = Id.fresh () in
  let base', end' =
    match size with
    | Value.Int s ->
      let base = HeapCursor.update (s + 1) in
      Address.NonTop base, Address.NonTop (base + s)
    | Value.Ptr _ | Value.Top | Value.Float _ | Value.String _ ->
      Address.Top, Address.Top
  in
  let block =
    let open Block in
    { base = base'
    ; end_ = end'
    ; freed = false }
  in
  let new_blocks = Heap.add id block astate.heap in
  { astate with heap = new_blocks },
  Value.Ptr { block = id; offset = Address.NonTop 0 }

let free_block (id: Id.t) (astate: t) : t =
  let heap' =
    (Heap.update id
      (function 
        | Some block ->
          Some { block with freed = true }
        | None -> None)
      astate.heap)
  in
  { astate with heap = heap' }

let is_freed (id: Id.t) (astate: t) : bool =
  let block = Heap.find_opt id astate.heap in
  match block with
  | Some { base = _; end_ = _; freed = true } ->
    true
  | _ ->
    false 

let base (loc: Address.t) (astate: t) : Address.t option =
  Heap.fold
    (fun _ block acc ->
      match acc with
      | Some _ -> acc
      | None ->
        match (block.base, block.end_, loc) with
        | (Address.NonTop b, Address.NonTop e, Address.NonTop l)
          when b <= l && l <= e ->
            Some block.base
        | _ ->
          None)
    astate.heap
    None

let end_ (loc:Address.t) (astate: t) : Address.t option =
  Heap.fold
    (fun _ block acc ->
      match acc with
      | Some _ -> acc
      | None ->
        match (block.base, block.end_, loc) with
        | (Address.NonTop b, Address.NonTop e, Address.NonTop l)
          when b <= l && l <= e ->
            Some block.end_
        | _ ->
          None)
    astate.heap
    None

let lookup_var (var : Var.t) (astate : t) : Value.t =
  match Stack.VarMap.find_opt var astate.stack with
    | Some av ->
      begin
        match Env.IdMap.find_opt av astate.env with
        | Some v -> v
        | None -> Value.Top (* this should not happen - every AV in stack must be bound in env *)
      end
    | None -> Value.Top

let store_var (var : Var.t) (value: Value.t) (astate: t) : t =
  let av = Id.fresh () in
  { astate with env = Env.IdMap.add av value astate.env
  ; stack = Stack.VarMap.add var av astate.stack }

module ExpEvalRes = struct
  type t =
    | Ok of Value.t
    | PtrSubDifferentBlocks
    | PtrComparisonError
    | Unknown

  let eval_unop (op: Unop.t) (v: Value.t) : t =
    match op, v with
    | Neg, Int i ->
      Ok (Int (-i))
    | BNot, Int i ->
      Ok (Int (lnot i))
    | LNot, Int i ->
      Ok (Int (if Int.equal i 0 then 1 else 0))
    | (Neg | BNot | LNot), Ptr _ ->
      Unknown
    | (Neg | BNot | LNot), Top ->
      Ok Top
    | _ -> Unknown

  let eval_binop (op: Binop.t) (v1: Value.t) (v2: Value.t) : t =
    match op, v1, v2 with
    | PlusA _, Int a, Int b ->
      Ok (Int (a + b))
    | MinusA _, Int a, Int b ->
      Ok (Int (a - b))
    | Mult _, Int a, Int b ->
      Ok (Int (a * b))
    | DivI, Int a, Int b ->
      Ok (Int (a / b))
    | DivF, Float a, Float b ->
      Ok (Float (a /. b))
    | Mod, Int a, Int b ->
      Ok (Int (a mod b))
    | Shiftlt, Int a, Int b ->
      Ok (Int (a lsl b))
    | Shiftrt, Int a, Int b ->
      Ok (Int (a lsr b))
    | (PlusA _ | MinusA _ | Mult _ | DivI | Mod | Shiftlt | Shiftrt), Top, Int _
    | (PlusA _ | MinusA _ | Mult _ | DivI | Mod | Shiftlt | Shiftrt), Int _, Top
    | (PlusA _ | MinusA _ | Mult _ | DivI | Mod | Shiftlt | Shiftrt), Top, Top ->
      Ok Top
    | PlusPI, Ptr p, Int x ->
      Ok (Ptr { p with offset = Address.add p.offset (NonTop x) })
    | MinusPI, Ptr p, Int x ->
      Ok (Ptr { p with offset = Address.sub p.offset (NonTop x) })
    | PlusPI, Ptr p, Top
    | MinusPI, Ptr p, Top ->
      Ok (Ptr { p with offset = Top })
    | MinusPP, Ptr { block = b1; offset = off1}, Ptr { block = b2; offset = off2} ->
      if Id.equal b1 b2 then
        Ok (Value.of_addr (Address.sub off1 off2))
      else
        PtrSubDifferentBlocks
    | Lt, Int a, Int b ->
      Ok (Int (if a < b then 1 else 0))
    | Gt, Int a, Int b ->
      Ok (Int (if a > b then 1 else 0))
    | Le, Int a, Int b ->
      Ok (Int (if a <= b then 1 else 0))
    | Ge, Int a, Int b ->
      Ok (Int (if a >= b then 1 else 0))
    | Eq, Int a, Int b ->
      Ok (Int (if Int.equal a b then 1 else 0))
    | Ne, Int a, Int b ->
      Ok (Int (if Int.equal a b then 0 else 1))
    | (Lt | Gt | Le | Ge | Eq | Ne), Top, Int _
    | (Lt | Gt | Le | Ge | Eq | Ne), Int _, Top
    | (Lt | Gt | Le | Ge | Eq | Ne), Top, Top ->
      Ok Top
    | Lt, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when Id.equal id1 id2 ->
        Ok (Value.of_addr (Address.lt off1 off2))
    | Gt, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when Id.equal id1 id2 ->
        Ok (Value.of_addr (Address.gt off1 off2))
    | Le, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when Id.equal id1 id2 ->
        Ok (Value.of_addr (Address.le off1 off2))
    | Ge, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when Id.equal id1 id2 ->
        Ok (Value.of_addr (Address.ge off1 off2))
    | Eq, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when Id.equal id1 id2 ->
        Ok (Value.of_addr (Address.eq off1 off2))
    | Eq, Ptr _, Int 0 | Eq, Int 0, _ -> (* ptr == NULL *)
      Ok (Int 0)
    | Ne, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when Id.equal id1 id2 ->
        Ok (Value.of_addr (Address.ne off1 off2))
    | Ne, Ptr _, Int 0 | Ne, Int 0, _ -> (* ptr != NULL *)
      Ok (Int 1)
    | (Lt | Gt | Le | Ge | Eq | Ne), Ptr _, Ptr _
    | (Lt | Gt | Le | Ge | Eq | Ne), Ptr _, Int _
    | (Lt | Gt | Le | Ge | Eq | Ne), Int _, Ptr _ ->
      PtrComparisonError
    | BAnd, Int a, Int b ->
      Ok (Int (a land b))
    | BXor, Int a, Int b ->
      Ok (Int (a lxor b))
    | BOr, Int a, Int b ->
      Ok (Int (a lor b))
    | (BAnd | BXor | BOr), Top, Int _
    | (BAnd | BXor | BOr), Int _, Top
    | (BAnd | BXor | BOr), Top, Top ->
      Ok Top
    | LAnd, Int a, Int b ->
      Ok (Int (if a <> 0 && b <> 0 then 1 else 0))
    | LOr, Int a, Int b ->
      Ok (Int (if a <> 0 || b <> 0 then 1 else 0))
    | (LAnd | LOr), Top, Int _
    | (LAnd | LOr), Int _, Top
    | (LAnd | LOr), Top, Top ->
        Ok Top
    | LAnd, Ptr _, Int a
    | LAnd, Int a, Ptr _->
      Ok (Int (if a <> 0 then 1 else 0))
    | LAnd, Ptr _, Ptr _ ->
      Ok (Int 1)
    | LOr, Ptr _, Int _
    | LOr, Int _, Ptr _ ->
      Ok (Int 1)
    | _ -> Unknown
end

let rec eval_exp (astate : Domain.t) (exp : Exp.t) : ExpEvalRes.t =
  match exp with
  | Var id ->
    Ok (lookup_var (Var.of_id id) astate)
  | UnOp (op, e, _typ) ->
    begin
      match eval_exp astate e with
      | Ok v -> ExpEvalRes.eval_unop op v
      | err -> err (* UnOp involving pointer *)
    end
  | BinOp (op, e1, e2) ->
    Format.print_newline () ;
    let res1 = eval_exp astate e1 in
    let res2 = eval_exp astate e2 in
    begin
      match res1, res2 with
      | Ok v1, Ok v2 ->
        ExpEvalRes.eval_binop op v1 v2
      | Unknown, Ok _ | Ok _, Unknown | Unknown, Unknown ->
        Unknown
      | Ok _, err | err, Ok _ | Unknown, err  | err, Unknown ->
        err
      | err1, _ -> (* for now report only the lhs issue *)
        err1
    end
  | Const (Const.Cint i) ->
    let z = IntLit.to_big_int i in
    Ok (Int (Z.to_int z))
  | Const (Const.Cstr s) ->
    Ok (String s)
  | Const (Const.Cfloat f) ->
    Ok (Float f)
  | Cast (_typ, e) ->
    eval_exp astate e
  | Lvar pvar ->
    Ok (lookup_var (Var.of_pvar pvar) astate)
  (* Lfield *)
  (* Lindex *)
  | Sizeof { nbytes = Some n } ->
    Ok (Int n)
  (* Sizeof for [dynamic_length] *)
  | _ ->
    Unknown
