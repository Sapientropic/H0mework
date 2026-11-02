import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication.Receipt
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback.Asynchronous.Execution

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication.Execution
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

open Segmented.Publication.Reservation.Feedback
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

variable (initial : List (View (code := model.source.code))) (rounds : Nat)

abbrev received := Receipt.generate model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law
abbrev Delivery := Receipt.Delivery model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law
abbrev material (delivery : Delivery model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law) :=
  Receipt.material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery

/-- The published learning result retains the original eligible selection and each actual report. -/
structure Learning where
  delivery : Delivery model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law
  delivered : received model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law = .delivered delivery
  state : Segmented.Publication.Learning.Paid.State model domain original delivery.selection.choice.val.policy.protocol (Deployment.actualHorizon model point)
  generated : state = Asynchronous.Execution.final model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial rounds
  reports : List (Asynchronous.Report (model := model) (domain := domain) (original := original)
    (baseline := delivery.selection.choice.val.policy.protocol) (actualHorizon := Deployment.actualHorizon model point) receiver quote point rival vocabulary encoding law)
  reported : reports = Asynchronous.reports receiver quote point rival vocabulary encoding law
    (Asynchronous.Execution.seed model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial) rounds

def learning : Option (Learning model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds) :=
  match delivered : received model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law with
  | .delivered delivery => some ⟨delivery,delivered,
      Asynchronous.Execution.final model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial rounds,rfl,
      Asynchronous.reports receiver quote point rival vocabulary encoding law
        (Asynchronous.Execution.seed model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial) rounds,rfl⟩
  | _ => none

abbrev afterCommunication (delivery : Delivery model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law) :=
  Asynchronous.Execution.before model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law
    (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery)

def before : Cursor model.source.code := match received model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law with
  | .delivered delivery => afterCommunication model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery
  | _ => Deployment.paidFinal model domain original reference worker quote allocation point rival

def future : List (Rule model.source.code) := match received model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law with
  | .delivered delivery => Asynchronous.Execution.future model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law
      (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial rounds
  | .pending _ _ => announcements
  | .blocked _ => []

theorem future_fits_the_original_window :
    (future model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).length ≤ Deployment.actualHorizon model point := by
  unfold future
  split
  · change (List.drop _ (Prefix.Padding.controls original _)).length ≤ _
    rw [List.length_drop,Prefix.Padding.length]
    exact Nat.sub_le _ _
  · rename_i selection residual _
    have room := selection.within
    change announcements.length ≤ Segmented.Deployment.actualHorizon model point
    omega
  · exact Nat.zero_le _

def cutPoint (count : Nat) := Splice.install
  (before model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law) rival
  ((future model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).take count)
abbrev full := cutPoint model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds (Deployment.actualHorizon model point)

variable (delivery : Delivery model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law)
  (delivered : received model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law = .delivered delivery)

include delivered in
theorem the_actual_received_plan_enters_the_original_asynchronous_driver :
    full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds =
      Asynchronous.Execution.full model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law
        (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial rounds := by
  simp only [full,cutPoint,before,future,delivered,afterCommunication]

include delivered in
theorem actual_learning_keeps_the_original_all_opponent_contract_and_independent_review :
    (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds).source.input =
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.source point.point original
        (clip (Deployment.actualHorizon model point) (Asynchronous.Execution.programme model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law
          (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial rounds)) rival).input ∧
    (Cut.seed (full model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds)).remaining = 0 ∧
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.acceptable model domain original reference
      (Asynchronous.Execution.programme model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law
        (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial rounds) ∧
    Prefix.verify model domain original
      (Asynchronous.Execution.final model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law
        (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial rounds).past reference
      (Asynchronous.Execution.tail model domain original reference worker receiver quote (globalQuotas allocation) slots point rival ordinal vocabulary encoding law
        (material model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law delivery) initial rounds) = true := by
  rw [the_actual_received_plan_enters_the_original_asynchronous_driver model domain original reference worker receiver quote allocation announcements slots point rival send ordinal vocabulary encoding law initial rounds delivery delivered]
  exact ⟨Asynchronous.Execution.actual_new_input_is_the_same_complete_original_evaluated_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Asynchronous.Execution.all_original_remaining_slots_are_actually_executed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Asynchronous.Execution.the_original_reference_and_all_opponents_are_protected _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Asynchronous.Execution.the_actual_paid_past_and_every_finite_continuation_are_independently_reviewed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication.Execution
