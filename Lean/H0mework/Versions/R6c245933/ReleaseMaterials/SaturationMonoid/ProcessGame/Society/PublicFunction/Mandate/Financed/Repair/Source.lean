import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.CurrentFrame
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Repair.Local

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Repair

open Institutions.Capitalism.Universal.Source.Program
open Mandate.Source (Port)
open Institutions.Capitalism.Universal.Root

def Phase (current : Current) : Prop :=
  current.technology.holder = none ∧ current.technology.last = some .exit

instance (current : Current) : Decidable (Phase current) := by unfold Phase; infer_instance

def authorizationIncoming (current : Current) : Option (IncomingWord law current) :=
  if current.technology.holder = some false then
    IncomingWord.check law current [request scope current false .exit]
  else if current.technology.holder = some true then
    IncomingWord.check law current (Response.produce base scope current).word
  else none

def sourceWithFuel (fuel : ℚ) : OutstandingSource Bool Good Port (State Bool Unit) Unit :=
  { Financed.sourceWithFuel fuel with
    incoming? := authorizationIncoming
    completionReport := fun current =>
      if Phase current then report current else (Response.produce base scope current).report }

def boundWithFuel (fuel : ℚ) : BoundSource base scope := ⟨sourceWithFuel fuel, rfl⟩
abbrev source := sourceWithFuel 3
abbrev shortSource := sourceWithFuel 2
abbrev bound := boundWithFuel 3
abbrev shortBound := boundWithFuel 2

theorem zero_financial_genesis (fuel : ℚ) :
    (sourceWithFuel fuel).input.initial.claims = fun _ _ _ => 0 := rfl

theorem financial_phase_has_no_authorization_input (fuel : ℚ) (current : Current) (phase : Phase current) :
    (sourceWithFuel fuel).incoming? current = none := by
  change authorizationIncoming current = none
  unfold authorizationIncoming
  rw [phase.1]
  rfl

structure ActualResponse (fuel : ℚ) (depth : Nat) where
  private mk ::
  phase : Phase ((sourceWithFuel fuel).currentAt (depth + 1))
  complete : (sourceWithFuel fuel).pendingSlots ((sourceWithFuel fuel).frameAt (depth + 1)).payments = []
  outcome : Repayment.Response law position ((sourceWithFuel fuel).currentAt (depth + 1))
  produced : outcome = Repayment.respond law position ((sourceWithFuel fuel).currentAt (depth + 1))
  actual_word : ((sourceWithFuel fuel).actualExecution depth).submitted =
    word ((sourceWithFuel fuel).currentAt (depth + 1))
  actual_report : ((sourceWithFuel fuel).writtenReceipt depth).val =
    report ((sourceWithFuel fuel).currentAt (depth + 1))

def actualAt (fuel : ℚ) (depth : Nat) : Option (ActualResponse fuel depth) :=
  if started : 2 ≤ depth + 1 then
    if phase : Phase ((sourceWithFuel fuel).currentAt (depth + 1)) then
      if complete : (sourceWithFuel fuel).pendingSlots ((sourceWithFuel fuel).frameAt (depth + 1)).payments = [] then
        some {
          phase := phase
          complete := complete
          outcome := Repayment.respond law position ((sourceWithFuel fuel).currentAt (depth + 1))
          produced := rfl
          actual_word := by
            have quiet := financial_phase_has_no_authorization_input fuel _ phase
            have emitted := (sourceWithFuel fuel).completed_word_is_source_continuation (depth + 1) 0
              started complete quiet
            change _ = (if Phase ((sourceWithFuel fuel).currentAt (depth + 1)) then
              report ((sourceWithFuel fuel).currentAt (depth + 1)) else _).word at emitted
            rw [if_pos phase] at emitted
            rw [(sourceWithFuel fuel).actual_execution_word,
              ← ((sourceWithFuel fuel).canonical_frame (depth + 1)).2]
            exact emitted
          actual_report := by
            rw [(sourceWithFuel fuel).written_report_exact]
            unfold OutstandingSource.reportAt
            rw [(sourceWithFuel fuel).ordinal_exact, if_neg (by omega)]
            unfold OutstandingSource.decideAt
            rw [financial_phase_has_no_authorization_input fuel _ phase, dif_pos complete]
            change (if Phase ((sourceWithFuel fuel).currentAt (depth + 1)) then _ else _) = _
            rw [if_pos phase] }
      else none
    else none
  else none

theorem phase_generates_an_actual_response (fuel : ℚ) (depth : Nat) (started : 2 ≤ depth + 1)
    (phase : Phase ((sourceWithFuel fuel).currentAt (depth + 1)))
    (complete : (sourceWithFuel fuel).pendingSlots ((sourceWithFuel fuel).frameAt (depth + 1)).payments = []) :
    ∃ response, actualAt fuel depth = some response := by
  unfold actualAt
  rw [dif_pos started, dif_pos phase, dif_pos complete]
  exact ⟨_, rfl⟩

theorem original_refusals_are_in_the_actual_trace {fuel : ℚ} {depth : Nat}
    (response : ActualResponse fuel depth)
    (positive : 0 < Repayment.balance position ((sourceWithFuel fuel).currentAt (depth + 1)))
    (failed : ¬ Repayment.Ready law position ((sourceWithFuel fuel).currentAt (depth + 1)))
    (order : Order ((sourceWithFuel fuel).currentAt (depth + 1))) :
    order.failed ∈ ((sourceWithFuel fuel).actualExecution depth).interpreted.items ∧
      ¬ law.Valid order.failed.before order.failed.request := by
  change order.failed ∈ law.rawItems ((sourceWithFuel fuel).currentAt (depth + 1))
    ((sourceWithFuel fuel).actualExecution depth).submitted ∧ _
  rw [response.actual_word]
  exact every_order_has_a_real_prefix_refusal _ order positive failed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Repair
