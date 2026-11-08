import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchWindowSource
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchWindowChecks
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open DispatchWindowSource

abbrev literalSaved := (LocalCommandRun.run ProductiveDispatchSource.model ProductiveDispatchSource.start
 ProductiveDispatchTrace.emitted).current ProductiveDispatchSource.model ProductiveDispatchSource.start

theorem saved_is_the_original_checked_execution : saved = literalSaved :=
 congrArg (fun state : ProductiveDispatchSource.State => state.current ProductiveDispatchSource.model ProductiveDispatchSource.start)
 ProductiveDispatchTrace.actual_is_the_original_execution_of_its_emitted_inputs

-- One exact check consumes the previously certified literal execution, never the chooser again.
theorem the_original_successor_pays_the_provider_and_obtains_actual_acceptance :
 admitted = true ∧
 (EventStep.seed paid).current.stock false true = 7 ∧
 (EventStep.seed paid).current.stock true true = 1 ∧
 (EventStep.seed paid).current.claims () false true = 7 ∧
 (EventStep.seed paid).current.technology.holder = none ∧ paid.cut = 64 ∧
 (EventStep.seed paid).remaining = 0 ∧
 row.submitted = [payment] ∧ ack.submitted = [acceptance] := by
 change PaidInvocationSource.admitted old contract saved true true = true ∧
  (EventStep.seed (PaidInvocationSource.paid old contract saved true true)).current.stock false true = 7 ∧
  (EventStep.seed (PaidInvocationSource.paid old contract saved true true)).current.stock true true = 1 ∧
  (EventStep.seed (PaidInvocationSource.paid old contract saved true true)).current.claims () false true = 7 ∧
  (EventStep.seed (PaidInvocationSource.paid old contract saved true true)).current.technology.holder = none ∧
  (PaidInvocationSource.paid old contract saved true true).cut = 64 ∧
  (EventStep.seed (PaidInvocationSource.paid old contract saved true true)).remaining = 0 ∧
  (PaidInvocationSource.paymentRow old contract saved true).submitted = [payment] ∧
  (PaidInvocationSource.acceptanceRow old contract saved true true).submitted = [acceptance]
 rw [saved_is_the_original_checked_execution]
 decide +kernel

abbrev actualAdmission := the_original_successor_pays_the_provider_and_obtains_actual_acceptance.1
abbrev opened := PaidInvocationSource.opened old contract saved true true actualAdmission
abbrev point := opened.point

theorem the_actual_two_occurrences_generate_the_original_new_window :
 produce = .opened opened := PaidInvocationSource.actual_admission_generates_the_paid_window old contract saved true true actualAdmission

theorem the_paid_window_has_thirty_six_new_invocations : (EventStep.seed point).remaining = 36 := by
 rw [PaidInvocationSource.paid_opening_preserves_the_entire_actual_endpoint old contract saved true true actualAdmission]
 change (EventStep.seed paid).remaining+36 = 36
 rw [the_original_successor_pays_the_provider_and_obtains_actual_acceptance.2.2.2.2.2.2.1]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchWindowChecks
