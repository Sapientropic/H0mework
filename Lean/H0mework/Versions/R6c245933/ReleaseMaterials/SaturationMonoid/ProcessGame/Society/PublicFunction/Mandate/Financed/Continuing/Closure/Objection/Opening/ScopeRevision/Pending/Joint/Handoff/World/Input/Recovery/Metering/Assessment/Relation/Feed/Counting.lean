import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Quiet

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

universe u v
private theorem constant_pi_length {Key : Type u} [DecidableEq Key] {Move : Type v}
    (keys : List Key) (choices : List Move) :
    (List.pi keys (fun _ => choices)).length = choices.length ^ keys.length := by
  induction keys with
  | nil => simp
  | cons key tail ih =>
    simp [List.pi_cons, List.length_flatMap, ih, Nat.pow_succ, Nat.mul_comm]

variable {code : Code Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit}

/-- Count the original Pi catalogue without allocating its function values.
Repeated positions are retained by the same product formula. -/
def tableCount (point : Continuation.Cursor code) : Nat :=
  (moves code).length ^
    (Residual.keys code (Residual.seed point.source point.entry point.cut)
      (Residual.schedules point.source point.entry point.cut)).length

theorem tableCount_exact (point : Continuation.Cursor code) :
    tableCount point = (Cut.tables point.source point.entry point.cut).length :=
  (constant_pi_length _ _).symm

variable (model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit)) (domain : List (Continuation.Cursor model.source.code))

def rowCount : Nat := ((Replanning.points model domain).map fun world => tableCount world.val).sum

theorem rowCount_exact : rowCount model domain = (Selection.rows model domain).length := by
  unfold rowCount Selection.rows Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.rows
  simp only [List.length_flatMap, List.length_map, List.length_attach, tableCount_exact]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
