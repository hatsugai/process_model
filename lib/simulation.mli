open Process

module type Simulation =
  sig
    type event
    type channel
    type process
    val simulation : (channel -> event list) -> process -> unit
  end

module Make(P : ProcessModel) : Simulation
       with type event = P.event
       with type channel = P.channel
       with type process = P.process
