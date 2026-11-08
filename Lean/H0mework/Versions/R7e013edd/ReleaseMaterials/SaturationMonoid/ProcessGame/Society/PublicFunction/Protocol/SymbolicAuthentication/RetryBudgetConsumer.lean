import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationWorkBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryBudgetConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor (AdmissionRuntime.profile foundation).source.code)
  (past : List (EventHistory.Stage (code := (AdmissionRuntime.profile foundation).source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (AdmissionRuntime.profile foundation).source.code))
  (law : StageReception.Law (AdmissionRuntime.profile foundation).source.code) (scope : Scope) (threshold : Nat)

theorem the_original_root_consumes_retry_progress_cost_and_terminal_duties
    (allowance : Nat) (compliant : AdaptiveRejectionHistory.Compliant start allowance
      (JointResponseRuntime.full foundation start past vocabulary encoding law)) :
    let model := AdmissionRuntime.profile foundation
    let runtime := JointResponseRuntime.runtime foundation start past vocabulary encoding law scope threshold
    let census := JointResponseRuntime.rooted foundation start past vocabulary encoding law scope threshold
    RetryExecutionBudget.count model start vocabulary encoding law past +
      RetryExecutionBudget.retrySteps census.response.trace ≤ RetryProgress.capacity (code := model.source.code) ∧
    CommunicationWorkBudget.count model start vocabulary encoding law past +
      CommunicationWorkBudget.workSteps census.response.trace ≤ CommunicationWorkBudget.capacity model ∧
    CommunicationWorkBudget.retryCost model start vocabulary encoding law (JointResponse.fuel model start past) past ≤
      RetryProgress.capacity (code := model.source.code) * CommunicationWorkBudget.slotAllowance model start ∧
    (∀ content ∈ DutyConfirmation.contents start vocabulary encoding law
        (JointResponseRuntime.full foundation start past vocabulary encoding law),
      ∃ row ∈ census.duties, DutyConfirmation.key start vocabulary encoding row.1 = content ∧
        row.2.2.state.TerminalAt 0) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (JointResponseRuntime.facade foundation start past vocabulary encoding law scope threshold).process.stateAt
      ((JointResponseRuntime.facade foundation start past vocabulary encoding law scope threshold).process.successor runtime.state) := by
  dsimp only
  have installed := (JointResponseRuntime.facade foundation start past vocabulary encoding law scope threshold).readoutAt_factorizes
    (JointResponseRuntime.runtime foundation start past vocabulary encoding law scope threshold) .joint
  exact ⟨RetryExecutionBudget.every_actual_joint_run_has_a_source_generated_retry_budget
      (AdmissionRuntime.profile foundation) start vocabulary encoding law _ past,
    CommunicationWorkBudget.actual_joint_communication_work_has_a_source_generated_budget
      (AdmissionRuntime.profile foundation) start vocabulary encoding law _ past allowance compliant,
    CommunicationWorkBudget.every_actual_retry_schedule_has_a_source_generated_total_cost
      (AdmissionRuntime.profile foundation) start vocabulary encoding law _ past,
    DutyConfirmation.every_confirmed_content_has_its_original_terminal_native_duty start vocabulary encoding law _,
    installed.2.2.1, installed.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryBudgetConsumer
