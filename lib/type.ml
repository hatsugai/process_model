module TransitionLabel =
  struct
    type 'event ievent = Tau | Hid of 'event | ITick
    type 'event revent = Vis of 'event | Internal of 'event ievent | Tick

    let show_ievent show = function
        Tau -> "tau"
      | Hid e -> "*" ^ (show e)
      | ITick -> "*tick"

    let show_revent show = function
        Vis e -> show e
      | Internal i -> show_ievent show i
      | Tick -> "tick"
  end

module type EventType =
  sig
    type t
    val show : t -> string
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
  end

module type ChannelType =
  sig
    type t
    val show : t -> string
    val equal : t -> t -> bool
    val hash : t -> int
  end
