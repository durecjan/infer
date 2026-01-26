open! IStd

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

module BlockId = struct

    type t = int

    let counter = ref 0

    let fresh () = incr counter; !counter

    let compare : t -> t -> int = Int.compare

    let equal (x : t) (y : t) : bool = Int.equal x y

    let pp = Format.pp_print_int
  end

module Value = struct
  type t =
    | Int of int
    | Ptr of { block : BlockId.t; offset : Address.t }
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
      when BlockId.equal id1.block id2.block ->
        Address.leq ~lhs:id1.offset ~rhs:id2.offset
    | _, _ -> false

  let join v1 v2 =
    match v1, v2 with
    | Top, _ | _, Top -> Top
    | Int a, Int b -> Int (max a b)
    | Ptr id1, Ptr id2
      when BlockId.equal id1.block id2.block ->
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
      when BlockId.equal id1.block id2.block ->
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
    | Ptr { block; offset } ->
      Format.fprintf fmt "Ptr(block=%a, off=%a)"
      BlockId.pp block
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

module Heap = AbstractDomain.Map (BlockId) (Block)

(* Define VarKey since Var does not satisfy IStdlib.PrettyPrintable.PrintableOrderedType *)
module VarKey : PrettyPrintable.PrintableOrderedType = struct
  type t = Var.t

  let compare = Var.compare
  let pp = Var.pp
end

module Env : AbstractDomain.MapS
  with type key = VarKey.t
  and type value = Value.t =
  AbstractDomain.Map (VarKey) (Value)

module Domain = struct
  type t =
    { env: Env.t
    ; heap: Heap.t 
    ; heap_cursor : Address.t}
  
  let init =
    { env = Env.empty
    ; heap = Heap.empty
    ; heap_cursor = Address.of_int 0 }

  let leq ~lhs ~rhs = 
    Env.leq ~lhs:lhs.env ~rhs:rhs.env &&
    Heap.leq ~lhs:lhs.heap ~rhs:rhs.heap

  let join lhs rhs =
    { env = Env.join lhs.env rhs.env
    ; heap = Heap.join lhs.heap rhs.heap
    ; heap_cursor = Address.join lhs.heap_cursor rhs.heap_cursor}

  let widen ~prev ~next ~num_iters =
    { env = Env.widen ~prev:prev.env ~next:next.env ~num_iters
    ; heap= Heap.widen ~prev:prev.heap ~next:next.heap ~num_iters 
    ; heap_cursor = Address.widen ~prev:prev.heap_cursor ~next:next.heap_cursor ~num_iters }

  let pp fmt {env; heap; heap_cursor} =
    Format.fprintf fmt "@[<v2>Env=%a@;Blocks=%a@;Cursor=%a@]" Env.pp env Heap.pp heap Address.pp heap_cursor
end

type t = Domain.t

let empty = Domain.init

let leq ~lhs ~rhs = Domain.leq ~lhs ~rhs

let join = Domain.join

let widen ~prev ~next ~num_iters = Domain.widen ~prev ~next ~num_iters

let pp fmt astate = Domain.pp fmt astate

let alloc_block (size: Value.t) (astate: t) : t * Value.t =
  let id = BlockId.fresh () in
  let size' =
    match size with
    | Value.Int s -> Address.NonTop s
    | Value.Ptr _ | Value.Top -> Address.Top
  in
  let base = astate.heap_cursor in
  let new_cursor =
    match base, size' with
    | Address.NonTop b, Address.NonTop s ->
      Address.of_int (b + s + 1)
    | Address.Top, _ | _, Address.Top ->
      Address.Top
  in
  let block =
    let open Block in
    { base = base
    ; end_ =
      (match base, size' with
      | Address.NonTop b, Address.NonTop s ->
        Address.of_int (b + s)
      | Address.Top, _ | _, Address.Top ->
        Address.Top )
    ; freed = false }
  in
  let new_blocks = Heap.add id block astate.heap in
  { astate with heap = new_blocks; heap_cursor = new_cursor },
  Value.Ptr { block = id; offset = Address.NonTop 0 }

let free_block (id: BlockId.t) (astate: t) : t =
  let heap' =
    (Heap.update id
      (function 
        | Some block ->
          Some { block with freed = true }
        | None -> None)
      astate.heap)
  in
  { astate with heap = heap' }

let is_freed (id: BlockId.t) (astate: t) : bool =
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

let key_of_var (var : Var.t) : Env.key =
  Obj.magic var

let lookup_var (var : Var.t) (astate : t) : Value.t =
  let key = key_of_var var in
  match Env.find_opt key astate.env with
    | Some v -> v
    | None -> Value.Top

let store_var (var : Var.t) (value: Value.t) (astate: t) : t =
  let key = key_of_var var in
  { astate with env= Env.add key value astate.env }

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
    (* | DivF  (** / for floats *) *)
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
      if BlockId.equal b1 b2 then
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
      when BlockId.equal id1 id2 ->
        Ok (Value.of_addr (Address.lt off1 off2))
    | Gt, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when BlockId.equal id1 id2 ->
        Ok (Value.of_addr (Address.gt off1 off2))
    | Le, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when BlockId.equal id1 id2 ->
        Ok (Value.of_addr (Address.le off1 off2))
    | Ge, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when BlockId.equal id1 id2 ->
        Ok (Value.of_addr (Address.ge off1 off2))
    | Eq, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when BlockId.equal id1 id2 ->
        Ok (Value.of_addr (Address.eq off1 off2))
    | Eq, Ptr _, Int 0 | Eq, Int 0, _ -> (* ptr == NULL *)
      Ok (Int 0)
    | Ne, Ptr { block = id1; offset = off1 }, Ptr { block = id2; offset = off2 }
      when BlockId.equal id1 id2 ->
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
  | Const (Const.Cint c) ->
    begin
      match IntLit.to_int c with
      | Some n -> Ok (Int n)
      | None -> Ok Top
    end
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
