import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
noncomputable section

private theorem all_positions {Item : Type} (items : List Item) (property : Item → Prop) :
    (∀ index : Fin items.length,property items[index]) ↔ ∀ item ∈ items,property item := by
  constructor
  · intro all item member
    obtain ⟨index,inside,same⟩ := List.mem_iff_getElem.mp member
    rw [←same]
    exact all ⟨index,inside⟩
  · intro all index
    exact all items[index] (List.getElem_mem index.isLt)

variable {epoch : Epoch} (inventory : Inventory epoch)
  (model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit))
  (domain : List (Continuation.Cursor model.source.code)) (original : Rule model.source.code)
  (requested : List (List Action))
  (tariff : Restoration.Tariff (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit))
  (row : Feed.Selection.Row model domain)
  (new previous : Whole.Program model.source.code (horizon domain))
  (current : Cell original requested inventory tariff (⟨row,new⟩ : Job model domain))
  (old : Cell original requested inventory tariff (⟨row,previous⟩ : Job model domain))

def Cell.scopeNoWorse (index : Fin (Restoration.required model row.world.val requested).length) : Prop :=
  ScopeForecast.NoWorse (current.scopeForecast index) (old.scopeForecast index)

instance (index : Fin (Restoration.required model row.world.val requested).length) :
    Decidable (Cell.scopeNoWorse inventory model domain original requested tariff row new previous current old index) := by
  unfold Cell.scopeNoWorse;infer_instance

private theorem scope_noWorse_exact (index : Fin (Restoration.required model row.world.val requested).length) :
    Cell.scopeNoWorse inventory model domain original requested tariff row new previous current old index ↔
      ScopeNoWorse current.actual.2 old.actual.2 (Restoration.required model row.world.val requested)[index]
        (Runtime.read current.actual.2.packet.2 (Restoration.required model row.world.val requested)[index])
        (Runtime.read old.actual.2.packet.2 (Restoration.required model row.world.val requested)[index]) := by
  unfold Cell.scopeNoWorse
  rw [Cell.every_forecast_is_the_original_scope_call,Cell.every_forecast_is_the_original_scope_call]
  change ScopeNoWorse current.actual.2 old.actual.2 (Restoration.required model row.world.val requested)[index]
    (current.report index) (old.report index) ↔ _
  exact Iff.of_eq (congrArg₂ (ScopeNoWorse current.actual.2 old.actual.2
    (Restoration.required model row.world.val requested)[index])
    (current.every_report_is_the_original_source_call index) (old.every_report_is_the_original_source_call index))

def Cell.NoWorse : Prop :=
  Feed.PresentNoWorse model row.world.val inventory requested current.actual old.actual ∧
  ∀ index : Fin (Restoration.required model row.world.val requested).length,
    (ReportNoWorse current.actual.2 old.actual.2 (Restoration.required model row.world.val requested)[index]
      (current.report index) (old.report index) ∧ Window.NoWorse (current.jointWindow index) (old.jointWindow index) ∧
        Cell.scopeNoWorse inventory model domain original requested tariff row new previous current old index) ∧
    Native.Future.Recovery.Funding.NoWorse (current.funding index) (old.funding index)

instance : Decidable (Cell.NoWorse inventory model domain original requested tariff row new previous current old) := by
  unfold Cell.NoWorse Native.Future.Recovery.Funding.NoWorse
  infer_instance

/-- Both tests consume the same cached report pair at every original query
position, including duplicated registrations. No tensor fallback is evaluated. -/
def Cell.compare : Bool := decide (Cell.NoWorse inventory model domain original requested tariff row new previous current old)

theorem Cell.compare_is_the_complete_original_history_relation :
    Cell.compare inventory model domain original requested tariff row new previous current old = true ↔
    Feed.Accepts model row.world.val original inventory requested new previous
      (Cut.opponent row.world.val.source row.world.val.entry row.world.val.cut row.table.val) tariff := by
  rw [Cell.compare,decide_eq_true_eq]
  unfold Cell.NoWorse
  dsimp only [Job.queries] at *
  simp_rw [scope_noWorse_exact,
    Cell.funding_uses_the_same_generated_report,Cell.every_report_is_the_original_source_call,
    Cell.every_joint_window_is_the_original_source_call]
  rw [current.generated,old.generated]
  dsimp only [Feed.Accepts,Restoration.Family.Accepts,Restoration.Family.futureNoWorse,
    Restoration.Family.Tensor.future,Restoration.Family.Tensor.funding,Feed.tensor,
    Option.map_some,Option.bind_some,Restoration.Family.ReportsNoWorse,Feed.FutureNoWorse,JointNoWorse,ScopeNoWorse]
  dsimp only [Job.queries]
  let now := Feed.present model row.world.val original new
    (Cut.opponent row.world.val.source row.world.val.entry row.world.val.cut row.table.val) inventory tariff
  let prior := Feed.present model row.world.val original previous
    (Cut.opponent row.world.val.source row.world.val.entry row.world.val.cut row.table.val) inventory tariff
  let property := fun word : List Action =>
    (ReportNoWorse now.2 prior.2 word (Runtime.read now.2.packet.2 word) (Runtime.read prior.2.packet.2 word) ∧
      Window.NoWorse (Relation.jointWindow now.2 word (Runtime.read now.2.packet.2 word))
        (Relation.jointWindow prior.2 word (Runtime.read prior.2.packet.2 word)) ∧
      ScopeForecast.NoWorse (Relation.scopeForecast now.2 word (Runtime.read now.2.packet.2 word))
        (Relation.scopeForecast prior.2 word (Runtime.read prior.2.packet.2 word))) ∧
    Native.Future.Recovery.Funding.NoWorse (Runtime.read now.2.packet.2 word).funding
      (Runtime.read prior.2.packet.2 word).funding
  have positions := all_positions (Restoration.required model row.world.val requested) property
  constructor
  · rintro ⟨present,reports⟩
    have all := positions.mp reports
    exact ⟨present,fun word member => (all word member).1,fun word member => (all word member).2⟩
  · rintro ⟨present,reports,funding⟩
    exact ⟨present,positions.mpr (fun word member => ⟨reports word member,funding word member⟩)⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work
