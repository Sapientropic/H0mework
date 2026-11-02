import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding.Order
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Funding
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Funding
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Transport

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Event.Future.Expiry.Progress
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (word : List Action)

/-- The report's cache is the original root's one generated Stage. Its native
window is read from that Stage and its own response, never from a reset account. -/
structure Report where
  private mk ::
  staged : Stage (Recovery.begin inventory word)
  generated : staged = Metering.Runtime.read inventory word

def produce : Report inventory word := ⟨Metering.Runtime.read inventory word,rfl⟩

/-- Execute the same actual Stage directly; the facade read remains its specification. -/
def nativeProduce : Report inventory word :=
  ⟨Metering.stage (Recovery.begin inventory word),(Metering.Runtime.read_exact inventory word).symm⟩

theorem nativeProduce_exact : nativeProduce inventory word = produce inventory word := rfl

@[csimp] theorem produce_codegen : @produce = @nativeProduce := rfl

private theorem cost_append {first middle last : Packet}
    (front : Event.Evolution first middle) (back : Event.Evolution middle last) (bearer : Bool) :
    Event.Costs.cost (.append front back) bearer = Event.Costs.cost front bearer + Event.Costs.cost back bearer :=
  PublicFunction.Costs.Visits.total_append sources (Event.Costs.records front) (Event.Costs.records back) bearer

namespace Report
variable {inventory word} (report : Report inventory word)
def funding := Funding.ofResult report.staged.result
abbrev consumed := report.staged.endpoint.consumed
abbrev residual := report.staged.endpoint.residual
def response := Event.produce report.staged.endpoint.saved []
def packet := report.response.packet

def recovery {first : Packet} (earlier : Event.Evolution first ⟨epoch,inventory⟩) :=
  Event.Evolution.append earlier report.staged.endpoint.native

def native {first : Packet} (earlier : Event.Evolution first ⟨epoch,inventory⟩) :=
  Event.Evolution.append (report.recovery earlier) report.response.native

def rows := Responsibility.census report.packet

def originalRow {first : Packet} (earlier : Event.Evolution first ⟨epoch,inventory⟩)
    (row : Responsibility.Row first) := Responsibility.transport (report.native earlier) row

def costs {first : Packet} (earlier : Event.Evolution first ⟨epoch,inventory⟩) :=
  Event.Costs.cost (report.native earlier)

def accounts {first : Packet} (earlier : Event.Evolution first ⟨epoch,inventory⟩) :=
  Event.Funding.account (report.native earlier)

def preservesFunding {otherEpoch : Epoch} {previous : Inventory otherEpoch}
    (old : Report previous word) : Bool :=
  Distributed.Reaction.Native.Future.Recovery.Funding.check report.funding old.funding

theorem financeReceipt {first : Packet} (earlier : Event.Evolution first ⟨epoch,inventory⟩) :
    Event.Funding.Receipt (report.native earlier) := Event.Funding.receive (report.native earlier)

theorem is_the_original_billed_response : report.packet = Metering.Runtime.packet inventory word := by
  unfold packet response
  rw [report.generated]
  rfl

theorem funding_status_is_the_original_actual_source_observation :
    report.funding.isNone = Funding.isFunded (Metering.Projection.produce epoch inventory.inputs word).kind := by
  unfold funding
  rw [Funding.status_is_the_actual_result,report.generated,
    Metering.Projection.the_observation_is_consumed_by_the_original_root]

theorem every_final_native_row_is_present (row : Responsibility.Row report.packet) : row ∈ report.rows :=
  Responsibility.every_original_row_is_in_the_census row

theorem every_original_row_keeps_its_admission_history_and_complete_run
    {first : Packet} (earlier : Event.Evolution first ⟨epoch,inventory⟩) (row : Responsibility.Row first) :
    (report.originalRow earlier row).row.origin = row.origin ∧
    row.state.history <+: (report.originalRow earlier row).state.history ∧
    Nonempty ((report.originalRow earlier row).native.Run row.origin.initial (report.originalRow earlier row).state) :=
  ⟨(Responsibility.every_actual_step_retains_its_original_admission_and_history (report.native earlier) row).1,
    (Responsibility.every_actual_step_retains_its_original_admission_and_history (report.native earlier) row).2,
    ⟨(report.originalRow earlier row).complete⟩⟩

theorem all_registration_bills_repair_and_response_costs_are_kept
    {first : Packet} (earlier : Event.Evolution first ⟨epoch,inventory⟩) (bearer : Bool) :
    report.costs earlier bearer = Event.Costs.cost earlier bearer +
      Event.Costs.cost report.staged.endpoint.native bearer + Event.Costs.cost report.response.native bearer := by
  change Event.Costs.cost (.append (.append earlier report.staged.endpoint.native) report.response.native) bearer = _
  rw [cost_append,cost_append]

theorem material_balance_in_each_original_good {first : Packet}
    (earlier : Event.Evolution first ⟨epoch,inventory⟩) (bearer : Bool) (good : Good) :
    (current report.packet.1 report.packet.2.inputs).stock bearer good +
      report.costs earlier bearer (.operating good) + report.costs earlier bearer (.debtPayment good) =
    (current first.1 first.2.inputs).stock bearer good + Event.Costs.credits (report.native earlier) bearer good :=
  Event.Costs.material_balance (report.native earlier) bearer good

theorem cash_and_all_original_financial_slots_share_the_actual_net_window {first : Packet}
    (earlier : Event.Evolution first ⟨epoch,inventory⟩) (bearer : Bool) (good : Good) :
    report.accounts earlier true bearer good + report.accounts earlier false bearer good =
      Event.FinancialBalance.quotedNet first bearer good - Event.FinancialBalance.quotedNet report.packet bearer good :=
  Event.Funding.actual_net_position_change (report.native earlier) bearer good

theorem original_request_split : report.consumed ++ report.residual = pending inventory word := report.staged.endpoint.split

theorem funding_failure_keeps_an_actual_source_obstruction (failed : Funding.Failure (Recovery.begin inventory word))
    (_recorded : report.funding = some failed) :
    (∃ head tail, (Recovery.begin inventory word).residual = head::tail ∧ quote (Recovery.begin inventory word) head.signer = none) ∨
    ∃ (saved : Recovery.Cursor inventory word) (fee : Action) (count : Nat),
      ∃ item ∈ (Mandate.law base epoch.scope).rawItems saved.before (attempt fee count saved).output,
        item.index = (attempt fee count saved).consumed.length ∧
        ¬ (Mandate.law base epoch.scope).Valid item.before item.request :=
  Funding.every_failed_bill_retains_its_actual_raw_item failed
end Report
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment
