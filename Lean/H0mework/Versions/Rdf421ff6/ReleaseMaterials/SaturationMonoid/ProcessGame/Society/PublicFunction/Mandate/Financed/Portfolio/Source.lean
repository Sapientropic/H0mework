import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.History.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Portfolio.Local

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Portfolio

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open Mandate.Source (Port)

/-- The entire instrument/debtor/current-creditor address space of this
source. Assignments change the balances read at these addresses. -/
def positions : List (Repayment.Position Bool Unit) :=
  [⟨(), false, true⟩, ⟨(), false, false⟩, ⟨(), true, false⟩, ⟨(), true, true⟩]

theorem all_positions_are_covered (position : Repayment.Position Bool Unit) : position ∈ positions := by
  rcases position with ⟨instrument, debtor, creditor⟩
  cases instrument
  cases debtor <;> cases creditor <;> simp [positions]

def financialWord (current : Current) := Repayment.Portfolio.word law positions current
def financialReport (current : Current) := ProgrammeSource.ProgrammeReport.original current (financialWord current)

def source (fuel : ℚ) : OutstandingSource Bool Good Port (State Bool Unit) Unit :=
  { History.source fuel with
    completionReport := fun current =>
      if current.technology.holder = none then financialReport current
      else (Response.produce base scope current).report }

def bound (fuel : ℚ) : BoundSource base scope := ⟨source fuel, rfl⟩
abbrev input (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.input (source fuel) inputs
abbrev currentAt (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.currentAt (source fuel) inputs
abbrev actualExecution (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.actualExecution (source fuel) inputs
abbrev trailAt (fuel : ℚ) (inputs : List (List Action)) := OutstandingSource.History.trailAt (source fuel) inputs

theorem zero_financial_genesis (fuel : ℚ) (inputs : List (List Action)) :
    (input fuel inputs).initial.claims = fun _ _ _ => 0 := rfl

theorem every_completed_unseated_history_emits_all_financial_positions
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none) :
    (actualExecution fuel inputs (depth + 1)).submitted = financialWord (currentAt fuel inputs (depth + 2)) := by
  rw [OutstandingSource.History.residual_is_actually_emitted _ _ depth observed]
  unfold OutstandingSource.decideAt
  have quiet := History.unseated_has_no_authorization_input fuel (currentAt fuel inputs (depth + 2)) unseated
  change (source fuel).incoming? _ = none at quiet
  rw [quiet, dif_pos complete]
  change (if (currentAt fuel inputs (depth + 2)).technology.holder = none then
    financialReport (currentAt fuel inputs (depth + 2)) else
    (Response.produce base scope (currentAt fuel inputs (depth + 2))).report).word = _
  rw [if_pos unseated]
  rfl

theorem every_completed_unseated_history_writes_all_financial_positions
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none) :
    (OutstandingSource.History.writtenReceipt (source fuel) inputs (depth + 1)).val =
      financialReport (currentAt fuel inputs (depth + 2)) := by
  rw [(OutstandingSource.History.writtenReceipt (source fuel) inputs (depth + 1)).property]
  change OutstandingSource.History.reportAt (source fuel) inputs (currentAt fuel inputs (depth + 2)) = _
  unfold OutstandingSource.History.reportAt OutstandingSource.History.report
  rw [OutstandingSource.History.ordinal_exact, if_neg (by omega), List.getElem?_eq_none (by omega)]
  unfold OutstandingSource.decideAt
  have quiet := History.unseated_has_no_authorization_input fuel (currentAt fuel inputs (depth + 2)) unseated
  change (source fuel).incoming? _ = none at quiet
  rw [quiet, dif_pos complete]
  change (if (currentAt fuel inputs (depth + 2)).technology.holder = none then
    financialReport (currentAt fuel inputs (depth + 2)) else
    (Response.produce base scope (currentAt fuel inputs (depth + 2))).report) = _
  rw [if_pos unseated]

def slice (current : Current) (index : Fin positions.length) := Repayment.Portfolio.locate law positions current index

structure ActualPortfolio (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) where
  private mk ::
  observed : inputs.length ≤ depth
  complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = []
  unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none
  outcomes : (index : Fin positions.length) →
    Repayment.Response law positions[index] (slice (currentAt fuel inputs (depth + 2)) index).before
  outcomes_exact : ∀ index, outcomes index =
    Repayment.respond law positions[index] (slice (currentAt fuel inputs (depth + 2)) index).before
  actual_word : (actualExecution fuel inputs (depth + 1)).submitted = financialWord (currentAt fuel inputs (depth + 2))
  actual_report : (OutstandingSource.History.writtenReceipt (source fuel) inputs (depth + 1)).val =
    financialReport (currentAt fuel inputs (depth + 2))

def actualAt (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) : Option (ActualPortfolio fuel inputs depth) :=
  if observed : inputs.length ≤ depth then
    if complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [] then
      if unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none then
        some ⟨observed, complete, unseated,
          fun index => Repayment.respond law positions[index] (slice (currentAt fuel inputs (depth + 2)) index).before,
          fun _ => rfl,
          every_completed_unseated_history_emits_all_financial_positions fuel inputs depth observed complete unseated,
          every_completed_unseated_history_writes_all_financial_positions fuel inputs depth observed complete unseated⟩
      else none
    else none
  else none

theorem each_actual_financial_phase_generates_all_position_outcomes
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none) :
    ∃ response, actualAt fuel inputs depth = some response := by
  unfold actualAt
  rw [dif_pos observed, dif_pos complete, dif_pos unseated]
  exact ⟨_, rfl⟩

theorem ready_payment_is_in_this_actual_history
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none)
    (index : Fin positions.length)
    (ready : Repayment.Ready law positions[index] (slice (currentAt fuel inputs (depth + 2)) index).before) :
    ∃ item ∈ (actualExecution fuel inputs (depth + 1)).interpreted.items,
      item.before = Repayment.readyCurrent law positions[index] (slice (currentAt fuel inputs (depth + 2)) index).before ∧
      item.request = Repayment.payment law positions[index] (slice (currentAt fuel inputs (depth + 2)) index).before ∧
      law.Valid item.before item.request := by
  change ∃ item ∈ law.rawItems (currentAt fuel inputs (depth + 2))
    (actualExecution fuel inputs (depth + 1)).submitted, _
  rw [every_completed_unseated_history_emits_all_financial_positions fuel inputs depth observed complete unseated]
  exact Repayment.Portfolio.Slice.ready_payment_is_in_the_whole_trace law _ ready

theorem failed_position_and_generated_repair_are_in_this_actual_history
    (fuel : ℚ) (inputs : List (List Action)) (depth : Nat) (observed : inputs.length ≤ depth)
    (complete : (source fuel).pendingSlots (trailAt fuel inputs (depth + 2)).frame.payments = [])
    (unseated : (currentAt fuel inputs (depth + 2)).technology.holder = none)
    (index : Fin positions.length)
    (positive : 0 < Repayment.balance positions[index] (slice (currentAt fuel inputs (depth + 2)) index).before)
    (failed : ¬ Repayment.Ready law positions[index] (slice (currentAt fuel inputs (depth + 2)) index).before)
    (order : Repayment.Portfolio.Repair.Order law positions[index] (slice (currentAt fuel inputs (depth + 2)) index).before)
    (present : order ∈ Repayment.Portfolio.Repair.orders law positions[index]
      (slice (currentAt fuel inputs (depth + 2)) index).before) :
    Repayment.Portfolio.shifted (slice (currentAt fuel inputs (depth + 2)) index).front.length order.failed ∈
      (actualExecution fuel inputs (depth + 1)).interpreted.items ∧
    ¬ law.Valid order.failed.before order.failed.request ∧
    order.request ∈ (actualExecution fuel inputs (depth + 1)).submitted := by
  change _ ∈ law.rawItems (currentAt fuel inputs (depth + 2))
    (actualExecution fuel inputs (depth + 1)).submitted ∧ _
  rw [every_completed_unseated_history_emits_all_financial_positions fuel inputs depth observed complete unseated]
  exact Repayment.Portfolio.Slice.failed_candidate_and_generated_repair_are_actual law _ positive failed order present

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Portfolio
