import Init.Data.List.Find

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Erasure

universe u v w

variable {Packet : Type u} {Accepted : Type v}

/-- Erasure keeps the order and identity of every admitted submission. -/
theorem filterMap_filter_of_rejected
    (check : Packet → Option Accepted) (keep : Packet → Bool)
    (rejected : ∀ packet, keep packet = false → check packet = none)
    (packets : List Packet) :
    (packets.filter keep).filterMap check = packets.filterMap check := by
  induction packets with
  | nil => rfl
  | cons packet packets ih =>
    cases retained : keep packet with
    | false => simp [retained, rejected packet retained, ih]
    | true => simp [List.filterMap_cons, retained, ih]

theorem findSome_filter_of_rejected
    (check : Packet → Option Accepted) (keep : Packet → Bool)
    (rejected : ∀ packet, keep packet = false → check packet = none)
    (packets : List Packet) :
    (packets.filter keep).findSome? check = packets.findSome? check := by
  simpa only [List.head?_filterMap] using
    congrArg List.head? (filterMap_filter_of_rejected check keep rejected packets)

/-- Insert any number of rejected submissions anywhere in a batch. -/
inductive InsertsRefused (check : Packet → Option Accepted) :
    List Packet → List Packet → Prop where
  | nil : InsertsRefused check [] []
  | keep (packet : Packet) {original presented : List Packet} :
      InsertsRefused check original presented →
      InsertsRefused check (packet :: original) (packet :: presented)
  | insert (packet : Packet) {original presented : List Packet} :
      check packet = none → InsertsRefused check original presented →
      InsertsRefused check original (packet :: presented)

theorem first_stutter {check : Packet → Option Accepted} {original presented : List Packet}
    (same : InsertsRefused check original presented) :
    presented.findSome? check = original.findSome? check := by
  induction same with
  | nil => rfl
  | keep packet _ ih => simp [List.findSome?_cons, ih]
  | insert packet refused _ ih => simp [refused, ih]

variable {State : Type u} {Reply : Type v} {Command : Type w}

/-- An adaptive strategy sees the due ordinal and the public replies,
most recent first. A single command may be a whole coalition's batch. -/
def run (advance : State → Command → State × Reply) (initial : State)
    (strategy : Nat → List Reply → Command) : Nat → State × List Reply
  | 0 => (initial, [])
  | n + 1 =>
    let (current, replies) := run advance initial strategy n
    let (next, reply) := advance current (strategy n replies)
    (next, reply :: replies)

/-- Only the reached currents are needed. The complete state and reply
history agree, so every observer of the authoritative trace agrees. -/
theorem run_eq_of_same_effect_along (advance : State → Command → State × Reply)
    (initial : State) (left right : Nat → List Reply → Command)
    (same : ∀ n, let current := run advance initial left n
      advance current.1 (left n current.2) = advance current.1 (right n current.2)) :
    run advance initial left = run advance initial right := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ← ih, same n]

variable {Noise : Type w}

/-- Parallel ingress has no place in the due queue. Its traffic can
itself be an arbitrary infinite stream at each ordinal. -/
theorem run_ignores_parallel_traffic (advance : State → Command → State × Reply)
    (initial : State) (strategy : Nat → List Reply → Command)
    (traffic : Nat → List Reply → Nat → Noise) :
    run (fun current (input : Command × (Nat → Noise)) => advance current input.1)
        initial (fun n replies => (strategy n replies, traffic n replies)) =
      run advance initial strategy := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih]

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Erasure
