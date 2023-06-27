module type EventType =
  sig
    type event
    type channel
    val equal_event : event -> event -> bool
    val equal_channel : channel -> channel -> bool
    val hash_event : event -> int
    val hash_channel : channel -> int
    val compare_event : event -> event -> int
    val event_to_channel : event -> channel
    val show_event : event -> string
    val show_channel : channel -> string
    val pp_event : Format.formatter -> event -> unit
    val pp_channel : Format.formatter -> channel -> unit
    val hash_fold_event : Base.Hash.state -> event -> Base.Hash.state
  end

module type ProcessModel =
  sig
    type event
    type channel
    val equal_event : event -> event -> bool
    val equal_channel : channel -> channel -> bool
    val hash_event : event -> int
    val hash_channel : channel -> int
    val compare_event : event -> event -> int
    val event_to_channel : event -> channel
    val show_event : event -> string
    val show_channel : channel -> string
    val pp_event : Format.formatter -> event -> unit
    val pp_channel : Format.formatter -> channel -> unit
    val hash_fold_event : Base.Hash.state -> event -> Base.Hash.state

    module H : sig
      type t = Tau | ITick | Hid of event
      val pp : Format.formatter -> t -> unit
      val show : t -> string
    end

    type trans =
      Event of event * process
    | Receive of channel * (event -> bool) * (event -> process)

    and tau_trans = H.t * process

    and anatomy =
      Alone
    | Choice of process list
    | InternalChoice of process list
    | ConcurrentComposition of process list
    | Interleave of process list
    | SequentialComposition of process * process
    | Hide of process
    | Rename of process

    and transf_res =  trans list * tau_trans list

    and process =
      < transitions : transf_res;
      tick : bool;
      class_id : int;
      compare : process -> int;
      equal : process -> bool;
      set_state : unit;
      hash : int;
      anatomy : anatomy;
      pwalk : unit;
      show : string >

    val transitions : process -> transf_res
    val equal_process : process -> process -> bool
    val compare_process : process -> process -> int
    val hash_process : process -> int
    val show_process : process -> string
    val pwalk : process -> unit

    type 'state process_class = {
      transf : ('state -> process) -> 'state -> transf_res;
      compare : 'state -> 'state -> int;
      hash : 'state -> int;
      show : 'state -> string;
      pwalk : 'state -> unit;
      mutable state : 'state;
    }

    val make_process_class :
      (('s -> process) -> 's -> trans list) ->
      ('s -> 's -> int) ->
      ('s -> int) -> ('s -> string) -> ?pwalk:('s -> unit) -> 's ->
      's process_class
    val make_process_class_tau :
      (('s -> process) -> 's -> trans list * tau_trans list) ->
      ('s -> 's -> int) ->
      ('s -> int) -> ('s -> string) -> ?pwalk:('s -> unit) -> 's ->
      's process_class
    val make_process : 's process_class -> 's -> process

    val omega : process
    val stop : process
    val skip : process

    val choice : process list -> process
    val internal_choice : process list -> process
    val composition : (channel -> bool) -> process list -> process
    val interleave : process list -> process
    val hide : (channel -> bool) -> process -> process
    val sequential_composition : process -> process -> process

  end

module Make (E : EventType) : ProcessModel
       with type event = E.event
       with type channel = E.channel
