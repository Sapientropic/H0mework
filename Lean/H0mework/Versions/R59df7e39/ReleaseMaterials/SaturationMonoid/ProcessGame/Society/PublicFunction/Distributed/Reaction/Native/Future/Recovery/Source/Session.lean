import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source.Stepper
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Stepper
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
  {pricing : Pricing (Action old)} {point : Point (old := old) (oldDepth := oldDepth) (word := word)}
structure Session (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  private mk ::
  current : Cursor pricing point
  work : List (Event (old := old) (oldDepth := oldDepth) (word := word))
  history : History (Stepper.initial pricing point) current work
def Session.initial (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) : Session pricing point :=
  ⟨Stepper.initial pricing point,[],.nil _⟩
noncomputable def Session.rank (session : Session pricing point) := session.current.rank
def Session.move (session : Session pricing point) : Option (Event (old := old) (oldDepth := oldDepth) (word := word) × Session pricing point) :=
  match actual : session.current.move with
  | none => none
  | some (event,next) => some (event,⟨next,session.work++[event],session.history.append (.step actual (.nil next))⟩)
def Session.completed (session : Session pricing point) : Option (Execution pricing point) :=
  match actual : session.current.completed with
  | none => none
  | some made => some (Execution.fromHistory session.current session.work session.history made actual)
theorem Session.initial_rank : (Session.initial pricing point).rank = steps (pricing.execute point) := rfl
theorem Session.move_decreases {before after : Session pricing point}
    {event : Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · rename_i emitted next moved
    cases actual
    exact Cursor.move_decreases moved
theorem Session.move_appends {before after : Session pricing point}
    {event : Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : after.work = before.work++[event] := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · cases actual;rfl
theorem Session.completed_iff_stopped (session : Session pricing point) : session.completed.isSome = true ↔ session.move = none := by
  have native := Cursor.completed_iff_stopped session.current
  unfold Session.completed Session.move
  split <;> split <;> simp_all
theorem Session.stopped_iff_zero (session : Session pricing point) : session.move = none ↔ session.rank = 0 := by
  unfold Session.move Session.rank
  have native := Cursor.stopped_iff_zero session.current
  split <;> simp_all
theorem Session.conservation (session : Session pricing point) : session.rank+session.work.length = steps (pricing.execute point) := by
  have native := session.history.conservation
  rw [Stepper.initial_rank] at native
  exact native
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Stepper
