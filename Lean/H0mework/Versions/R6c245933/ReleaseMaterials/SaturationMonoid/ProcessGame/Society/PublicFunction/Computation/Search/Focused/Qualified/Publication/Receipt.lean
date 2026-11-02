import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication.Plan
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Material

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication.Receipt
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code (horizon domain)) (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (allocation : List Allocation) (announcements : List (Rule model.source.code)) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)
  (send : Rule model.source.code) (ordinal : Nat)

variable (vocabulary : PublicFunction.Protocol.SymbolicAuthentication.OwnedAttestation.Vocabulary
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
  (encoding : PublicFunction.Protocol.SymbolicAuthentication.StageTransport.Encoding (code := model.source.code))
  (law : PublicFunction.Protocol.SymbolicAuthentication.StageReception.Law model.source.code)


abbrev Selected := Selection model domain original reference worker receiver quote allocation announcements slots point rival send ordinal
abbrev plan (selection : Selected model domain original reference worker receiver quote allocation announcements slots point rival send ordinal) :=
  materialPlan model domain original reference worker receiver quote allocation announcements slots point rival send ordinal selection

structure Delivery where
  selection : Selected model domain original reference worker receiver quote allocation announcements slots point rival send ordinal
  payload : Segmented.Publication.Material.Payload model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal
    vocabulary encoding law (plan model domain original reference worker receiver quote allocation announcements slots point rival send ordinal selection)

abbrev material (delivery : Delivery model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law) :
    Segmented.Publication.Material.Carrier model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law :=
  ⟨plan model domain original reference worker receiver quote allocation announcements slots point rival send ordinal delivery.selection,delivery.payload⟩

inductive Outcome where
  | blocked (reason : Blocked model domain original reference worker receiver quote allocation announcements slots point rival send ordinal)
  | pending (selection : Selected model domain original reference worker receiver quote allocation announcements slots point rival send ordinal)
      (residual : Segmented.Publication.Material.Pending model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law
        (plan model domain original reference worker receiver quote allocation announcements slots point rival send ordinal selection))
  | delivered (delivery : Delivery model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law)

/-- Reception reads the source-generated address, never an incoming caller receipt. -/
def generate : Outcome model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law :=
  match Publication.generate model domain original reference worker receiver quote allocation announcements slots point rival send ordinal with
  | .blocked reason => .blocked reason
  | .selected selection => match Segmented.Publication.Material.receive model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal
      vocabulary encoding law (plan model domain original reference worker receiver quote allocation announcements slots point rival send ordinal selection) with
    | .pending residual => .pending selection residual
    | .delivered payload => .delivered ⟨selection,payload⟩

variable (delivery : Delivery model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law)

theorem the_received_occurrence_keeps_both_real_queues_and_the_complete_original_choice :
    Sparse.replayPayments model domain original reference worker quote (globalQuotas allocation) rival none
      (execution model domain original reference worker quote allocation rival point).payments = some delivery.selection.finished.global ∧
    replayPayments model domain original reference worker receiver quote allocation announcements none
      (observed model domain original reference worker receiver quote allocation announcements rival point).payments = some delivery.selection.finished.qualified ∧
    Prefix.Contract model domain original (Segmented.reserved model original worker quote (globalQuotas allocation)) reference
      (.selected (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery).plan.choice) := by
  have queues := a_finished_selection_uses_only_the_original_actual_paid_queues model domain original reference worker receiver quote allocation announcements point rival send delivery.selection.finished
  exact ⟨queues.1,queues.2,Prefix.every_generated_outcome_has_the_complete_future_contract _ _ _ _ _ _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication.Receipt
