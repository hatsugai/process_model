open Process

module type Verification =
  sig
    type event
    type channel
    type ievent
    type process

    module A :
      sig
        type t = Tau | Tick | Event of event | Hid of event | ITick
        val pp : Format.formatter -> t -> unit
        val show : t -> string
        val equal : t -> t -> bool
        val compare : t -> t -> int
      end

    module V :
    sig
      type t = Tick | Event of event 
      val pp : Format.formatter -> t -> unit
      val show : t -> string
      val equal : t -> t -> bool
      val compare : t -> t -> int
    end

    type lts = {
      vis_transv : (event * int) list array;
      tau_transv : (ievent * int) list array;
      tickv : bool array;
    }

    type 'state ltsx = {
      lts : lts;
      statev : 'state array;
      show : int -> string;
    }

    module IntSet : Set.S
    module ES : Set.S
    module ESS : Set.S

    type check_traces_result =
        CT_Violation of ((int * int) * A.t) list
      | CT_Ok

    type check_failures_result =
        CF_TraceViolation of ((int * int) * A.t) list
      | CF_RefusalViolation of ESS.t * ES.t * int * int *
          ((int * int) * A.t) list
      | CF_Ok

    val unfold : (channel -> event list) -> process -> process ltsx
    val det : lts -> IntSet.t ltsx
    val check_traces : lts -> lts -> check_traces_result
    val min_acceptances : lts -> IntSet.t ltsx -> ESS.t array
    val check_failures : lts -> ESS.t array -> lts -> check_failures_result

    val print_trace_violation :
      IntSet.t ltsx -> 'a ltsx -> 'b ltsx ->
      int * ((int * int) * A.t) list ->
      unit
    val print_refusals_violation :
      IntSet.t ltsx ->
      'a ltsx ->
      'b ltsx -> ESS.t -> ES.t -> int -> int -> ((int * int) * A.t) list -> unit
  end

module Make (P : ProcessModel) : Verification
       with type event = P.event
       with type channel = P.channel
       with type ievent = P.H.t
       with type process = P.process
