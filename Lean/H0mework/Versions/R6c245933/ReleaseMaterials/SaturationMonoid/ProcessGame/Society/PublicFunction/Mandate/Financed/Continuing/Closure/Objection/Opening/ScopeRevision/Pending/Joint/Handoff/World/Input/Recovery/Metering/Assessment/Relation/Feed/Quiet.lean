import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Selection

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
noncomputable section

variable (model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)) (point : Continuation.Cursor model.source.code)
  (reference : Rule model.source.code) {fuel : Nat} (program : Whole.Program model.source.code fuel)
  (quiet : PublicDomain.quiet (code := model.source.code) = true) (rival : Opponent model.source.code)

include quiet

theorem quiet_source : source model point reference program rival =
    source model point reference program PublicDomain.silent := by
  unfold source
  have same := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.quiet_controllers
    model point reference program quiet rival
  change Whole.controller point reference program rival = Whole.controller point reference program PublicDomain.silent at same
  exact congrArg (fun driver => Future.target point.source point.entry point.cut
    (Future.jointOpponent point.source point.entry point.cut driver) (Whole.schedule point reference program).val) same

theorem quiet_window {epoch : Epoch} (inventory : Inventory epoch) :
    window model point reference program rival inventory =
      window model point reference program PublicDomain.silent inventory := by
  unfold window words
  rw [quiet_source model point reference program quiet rival]

theorem quiet_present {epoch : Epoch} (inventory : Inventory epoch) (tariff : Restoration.Tariff
    (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit)) :
    present model point reference program rival inventory tariff =
      present model point reference program PublicDomain.silent inventory tariff := by
  unfold present
  rw [Restoration.quiet_tensor model point reference program quiet rival tariff,
    quiet_window model point reference program quiet rival inventory]

theorem quiet_tensor {epoch : Epoch} (inventory : Inventory epoch) (tariff : Restoration.Tariff
    (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit)) :
    tensor model point reference program rival inventory tariff =
      tensor model point reference program PublicDomain.silent inventory tariff := by
  unfold tensor
  rw [quiet_present model point reference program quiet rival inventory tariff]

namespace Selection
variable (domain : List (Continuation.Cursor model.source.code))

def silentRow (world : Replanning.Point model domain) : Row model domain :=
  ⟨world,⟨externalTable world.val PublicDomain.silent,Residual.restriction_is_generated _ _ _ _⟩⟩

theorem quiet_holds {epoch : Epoch} (inventory : Inventory epoch) (tariff : Restoration.Tariff
    (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
    (requested : List (List Action)) (previous : Whole.Program model.source.code fuel)
    (row : Row model domain) :
    holds inventory model domain reference tariff requested previous program row ↔
      holds inventory model domain reference tariff requested previous program (silentRow model domain row.world) := by
  dsimp only [holds, silentRow, Accepts]
  rw [Feed.quiet_tensor model row.world.val reference program quiet
    (Cut.opponent row.world.val.source row.world.val.entry row.world.val.cut row.table.val) inventory tariff,
    Feed.quiet_tensor model row.world.val reference previous quiet
    (Cut.opponent row.world.val.source row.world.val.entry row.world.val.cut row.table.val) inventory tariff]
  rw [Feed.the_common_table_keeps_the_complete_joint_tensor model row.world.val reference inventory tariff
      (program := program) (rival := PublicDomain.silent),
    Feed.the_common_table_keeps_the_complete_joint_tensor model row.world.val reference inventory tariff
      (program := previous) (rival := PublicDomain.silent)]

end Selection
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
