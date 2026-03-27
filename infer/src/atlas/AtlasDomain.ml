
module State = AtlasState

module Domain = struct
  type t = State.t list

  (** [lhs ⊆ rhs] — every state in [lhs] exists in [rhs] *)
  let leq ~lhs ~rhs =
    List.for_all lhs ~f:(fun s ->
      List.exists rhs ~f:(State.equal s))

  let join x y =
    List.fold
    ~init:[]
    ~f:(fun acc a ->
      if List.exists ~f:(State.equal a) acc then acc
      else a :: acc)
    (List.append x y)

  let widen ~prev ~next ~num_iters:_ =
    join prev next

  let pp fmt astate =
    List.iter astate ~f:(fun state ->
      Format.fprintf fmt "%s\n" (State.to_string state))
end

type t = Domain.t