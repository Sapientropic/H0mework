import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.InheritedReplacement

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Future.Expiry.Progress
noncomputable section
variable {first : Packet} {epoch : Epoch} {inventory : Inventory epoch} {intent : Input.Intent} {actor : Bool}

variable (permit : Permit inventory intent actor)
def observed : Inventory epoch := World.submit inventory (word inventory intent permit.choice)
abbrev trace : Trace (observed permit) := Future.Expiry.Progress.Runtime.trace (observed permit)

def incoming (earlier : Evolution first ⟨epoch,inventory⟩) : Evolution first ⟨epoch,observed permit⟩ :=
  Evolution.append earlier (.submit inventory (word inventory intent permit.choice))

def path (earlier : Evolution first ⟨epoch,inventory⟩) : Evolution first (trace permit).packet := InheritedResponse.combined (incoming permit earlier) (trace permit)
def response (earlier : Evolution first ⟨epoch,inventory⟩) : InheritedResponse.Result (incoming permit earlier) (trace permit) := InheritedResponse.classify (incoming permit earlier) (trace permit)
def financeRun (earlier : Evolution first ⟨epoch,inventory⟩) :=
  first.2.finance.generated.concatRuns _ (Response.financeAlong (path permit earlier))
def births (earlier : Evolution first ⟨epoch,inventory⟩) := Financial.Family.Migration.Exposure.admissions sources (financeRun permit earlier)

/-- Each option is executed by the existing source response at the same saved
cut. All consequences are retained before any declared preference reads them. -/
structure Consequences (earlier : Evolution first ⟨epoch,inventory⟩) where
  private mk ::
  actualInput : (World.actual inventory (word inventory intent permit.choice)).submitted = word inventory intent permit.choice ∧
    (World.actual inventory (word inventory intent permit.choice)).before = before inventory
  inherited : InheritedResponse.Result (incoming permit earlier) (trace permit)
  inherited_exact : inherited = response permit earlier
  kind : inherited.kind (incoming permit earlier) (trace permit) =
    (trace permit).ending.2.1.event.original.original.decision.kind
  tasks : ∀ index : first.1.source.Slot,
    (trace permit).packet.1.source.seed.slot (TaskTransport.along (path permit earlier) index) = first.1.source.seed.slot index
  rows : ∀ row : Responsibility.Row first,
    let located := InheritedResponse.original (incoming permit earlier) (trace permit) row
    located.row.origin = row.origin ∧ row.state.history <+: located.state.history ∧
      Nonempty (located.native.Run row.origin.initial located.state)
  boundary : ∀ row : Responsibility.Row (trace permit).packet, Nonempty (row.native.Run row.initial row.state)
  financialCensus : (births permit earlier).map Financial.Family.Migration.Exposure.Birth.index =
    List.range (trace permit).packet.2.finance.current.slots.length
  financialBirths : ∀ birth ∈ births permit earlier,
    (trace permit).packet.2.finance.current.slots[birth.index]? = some birth.follow.slot ∧
      Financial.Family.slotClaim sources birth.follow.slot = birth.claim ∧ birth.remaining + birth.paid = birth.claim.2.quantity
  material : ∀ party good,
    (current (trace permit).packet.1 (trace permit).packet.2.inputs).stock party good +
      Costs.cost (path permit earlier) party (.operating good) + Costs.cost (path permit earlier) party (.debtPayment good) =
    (current first.1 first.2.inputs).stock party good + Costs.credits (path permit earlier) party good
  net : ∀ party good,
    FinancialBalance.quotedNet (trace permit).packet party good + Costs.cost (path permit earlier) party (.operating good) =
      FinancialBalance.quotedNet first party good + FinancialBalance.otherCredits (path permit earlier) party good +
      FinancialBalance.issues (path permit earlier) .credit party good - FinancialBalance.issues (path permit earlier) .debit party good +
      FinancialBalance.assignments (path permit earlier) .credit party good
  time : ∀ party, Costs.cost (path permit earlier) party .elapsed =
    (current (trace permit).packet.1 (trace permit).packet.2.inputs).clock - (current first.1 first.2.inputs).clock
  nextEvent : (trace permit).nextSourceEvent.before = current (trace permit).packet.1 (trace permit).packet.2.inputs ∧
    (World.actual (trace permit).packet.2 (Future.ownWord (trace permit).packet.2)).after = (trace permit).nextSourceEvent.after
  answer : HEq ((Future.Expiry.Progress.Runtime.facade (observed permit)).readoutAt
    (Future.Expiry.Progress.Runtime.activated (observed permit) (Future.Expiry.Progress.Runtime.ordinal (observed permit))) (.inr ()))
    ((Future.Expiry.Progress.Runtime.activated (observed permit) (Future.Expiry.Progress.Runtime.ordinal (observed permit))).tick.generated.projectionOutcome (.component ()))
  ledger : HEq (Future.Expiry.Progress.Runtime.activated (observed permit) (Future.Expiry.Progress.Runtime.ordinal (observed permit))).tick.generated.wholeLedgerWriteBack
    ((Future.Expiry.Progress.Runtime.activated (observed permit) (Future.Expiry.Progress.Runtime.ordinal (observed permit))).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
      (Future.Expiry.Progress.Runtime.activated (observed permit) (Future.Expiry.Progress.Runtime.ordinal (observed permit))).current.visit.current)
  next : (Future.Expiry.Progress.Runtime.activated (observed permit) (Future.Expiry.Progress.Runtime.ordinal (observed permit))).tick.nextCurrent =
    (Future.Expiry.Progress.Runtime.facade (observed permit)).process.stateAt
      ((Future.Expiry.Progress.Runtime.facade (observed permit)).process.successor
        (Future.Expiry.Progress.Runtime.activated (observed permit) (Future.Expiry.Progress.Runtime.ordinal (observed permit))).state)

def generate (earlier : Evolution first ⟨epoch,inventory⟩) : Consequences permit earlier := by
  have factor := (Future.Expiry.Progress.Runtime.facade (observed permit)).readoutAt_factorizes
    (Future.Expiry.Progress.Runtime.activated (observed permit) (Future.Expiry.Progress.Runtime.ordinal (observed permit))) (.inr ())
  refine ⟨World.actual_word_and_cut inventory _,response permit earlier,rfl,
    InheritedResponse.classification_is_the_actual_terminal_decision (incoming permit earlier) (trace permit),
    TaskTransport.content (path permit earlier),
    InheritedResponse.all_original_rows_have_their_actual_complete_runs (first := first) (last := ⟨epoch,observed permit⟩) (incoming permit earlier) (trace permit),
    fun row => ⟨row.complete⟩,?_,fun birth _ => ⟨birth.actual_slot,birth.original_claim,birth.conservation⟩,
    Costs.material_balance (path permit earlier),FinancialBalance.actual_net_balance (first := first) (last := (trace permit).packet) (path permit earlier),
    Costs.elapsed_exact (path permit earlier),InheritedResponse.own_next_is_generated_at_the_actual_endpoint (last := ⟨epoch,observed permit⟩) (trace permit),
    factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩
  simpa only [births,ResponsibilityState.empty,List.length_nil,List.range_zero,List.nil_append] using
    Financial.Family.Migration.Exposure.admission_indices sources (financeRun permit earlier)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation
