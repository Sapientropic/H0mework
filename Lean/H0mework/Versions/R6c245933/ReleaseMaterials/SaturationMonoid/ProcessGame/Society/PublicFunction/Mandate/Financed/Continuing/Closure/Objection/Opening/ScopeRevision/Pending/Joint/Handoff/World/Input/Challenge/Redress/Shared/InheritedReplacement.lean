import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.ControlPayments
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.InheritedResponse

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.InheritedReplacement

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Input.Event Input.Event.Future.Expiry.Progress
noncomputable section
variable {first : Packet} {epoch : Epoch} {inventory : Inventory epoch}

/-- This is the already executed prefix of the shared root's response. -/
def beforeTrace (inventory : Inventory epoch) : Evolution ⟨epoch,inventory⟩ ⟨epoch,Iteration.staged inventory⟩ :=
  .append (.submit inventory (Shared.word inventory))
    (Event.inputEvolution (Shared.after inventory) (Responsibility.Dispatch.intent (Shared.after inventory)))

def incoming (earlier : Evolution first ⟨epoch,inventory⟩) := Evolution.append earlier (beforeTrace inventory)

abbrev trace (inventory : Inventory epoch) := Shared.Runtime.answer inventory

def path (earlier : Evolution first ⟨epoch,inventory⟩) := InheritedResponse.combined (incoming earlier) (trace inventory)

def replacement (earlier : Evolution first ⟨epoch,inventory⟩) := InheritedResponse.classify (incoming earlier) (trace inventory)

def financeRun (earlier : Evolution first ⟨epoch,inventory⟩) :=
  first.2.finance.generated.concatRuns _ (Response.financeAlong (path earlier))

def births (earlier : Evolution first ⟨epoch,inventory⟩) := Financial.Family.Migration.Exposure.admissions sources (financeRun earlier)

theorem every_new_and_old_financial_address_is_present_once (earlier : Evolution first ⟨epoch,inventory⟩) :
    (births earlier).map Financial.Family.Migration.Exposure.Birth.index =
      List.range (trace inventory).packet.2.finance.current.slots.length := by
  simpa only [births,ResponsibilityState.empty,List.length_nil,List.range_zero,List.nil_append] using
    Financial.Family.Migration.Exposure.admission_indices sources (financeRun earlier)

structure Receipt (earlier : Evolution first ⟨epoch,inventory⟩) where
  private mk ::
  localAccount : Shared.ControlPayments.Receipt inventory
  localAccount_exact : localAccount = Shared.ControlPayments.generate inventory
  replacement : InheritedResponse.Result (incoming earlier) (trace inventory)
  replacement_exact : replacement = InheritedReplacement.replacement earlier
  kind : replacement.kind (incoming earlier) (trace inventory) = (trace inventory).ending.2.1.event.original.original.decision.kind
  homology : ∀ index : first.1.source.Slot,
    epoch.source.seed.slot (TaskTransport.along earlier index) = first.1.source.seed.slot index
  rows : ∀ row : Responsibility.Row first,
    let located := InheritedResponse.original (incoming earlier) (trace inventory) row
    located.row.origin = row.origin ∧ row.state.history <+: located.state.history ∧
      Nonempty (located.native.Run row.origin.initial located.state)
  boundary : ∀ row : Responsibility.Row (trace inventory).packet, Nonempty (row.native.Run row.initial row.state)
  financialCensus : (births earlier).map Financial.Family.Migration.Exposure.Birth.index =
    List.range (trace inventory).packet.2.finance.current.slots.length
  financialBirths : ∀ birth ∈ births earlier,
    (trace inventory).packet.2.finance.current.slots[birth.index]? = some birth.follow.slot ∧
      Financial.Family.slotClaim sources birth.follow.slot = birth.claim ∧ birth.remaining + birth.paid = birth.claim.2.quantity
  net : ∀ party good,
    Input.Event.FinancialBalance.quotedNet (trace inventory).packet party good + Input.Event.Costs.cost (path earlier) party (.operating good) =
      Input.Event.FinancialBalance.quotedNet first party good + Input.Event.FinancialBalance.otherCredits (path earlier) party good +
      Input.Event.FinancialBalance.issues (path earlier) .credit party good - Input.Event.FinancialBalance.issues (path earlier) .debit party good +
      Input.Event.FinancialBalance.assignments (path earlier) .credit party good
  nextEvent : (trace inventory).nextSourceEvent.before = current (trace inventory).packet.1 (trace inventory).packet.2.inputs ∧
    (World.actual (trace inventory).packet.2 (Future.ownWord (trace inventory).packet.2)).after = (trace inventory).nextSourceEvent.after

def generate (earlier : Evolution first ⟨epoch,inventory⟩) : Receipt (inventory := inventory) earlier :=
  ⟨Shared.ControlPayments.generate inventory,rfl,replacement earlier,rfl,
    InheritedResponse.classification_is_the_actual_terminal_decision (incoming earlier) (trace inventory),
    TaskTransport.content earlier,
    InheritedResponse.all_original_rows_have_their_actual_complete_runs (incoming earlier) (trace inventory),
    fun row => ⟨row.complete⟩,every_new_and_old_financial_address_is_present_once earlier,
    fun birth _ => ⟨birth.actual_slot,birth.original_claim,birth.conservation⟩,
    Input.Event.FinancialBalance.actual_net_balance (first := first) (last := (trace inventory).packet) (path earlier),
    InheritedResponse.own_next_is_generated_at_the_actual_endpoint (last := ⟨epoch,Iteration.staged inventory⟩) (trace inventory)⟩

def atCut (packet : Packet) (count : Nat) :=
  generate (epoch := (Iteration.after packet count).1) (inventory := (Iteration.after packet count).2)
    (Iteration.native packet count)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.InheritedReplacement
