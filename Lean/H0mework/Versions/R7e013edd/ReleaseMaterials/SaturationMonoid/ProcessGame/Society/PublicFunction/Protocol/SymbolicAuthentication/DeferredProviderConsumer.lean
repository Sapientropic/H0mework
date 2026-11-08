import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeferredProviderReceipt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeferredProviderConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws contract)
open RecoveredProductiveSource (recycling feeding)
open SourceCreditSource (exchange)
open DeferredProviderSource
open private SourceCreditConsumer.issued_original from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCreditConsumer
noncomputable section

local notation "oldFirst" => (FreshSigningSource.cycle contract base laws ConcreteProductiveSource.ready ConcreteProductiveSource.request)
local notation "oldDonation" => (JointReceptionSource.advance recycling oldFirst (RenewableArchiveSource.Command.renew false true))
local notation "oldSupply" => (JointReceptionSource.advance feeding oldDonation (RenewableArchiveSource.Command.renew true true))
local notation "oldReady" => (JointReceptionSource.advance contract oldSupply (RenewableArchiveSource.Command.execute [LocalCommandSource.Input.command 2,LocalCommandSource.Input.idle]))
local notation "oldPrepared" => (FreshSigningSource.prepared contract oldReady ConcreteProductiveSource.request)
local notation "oldPredecessor" => (FreshSigningSource.next contract base laws oldPrepared ConcreteProductiveSource.request)
local notation "oldRegistered" => (SourceOpportunityHandoff.register oldPredecessor)
local notation "predecessor" => (JointReceptionSource.advance contract oldRegistered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs SourceOpportunitySource.trace)))

local notation "registered" => (SourceCreditHandoff.register predecessor)
local notation "issuedState" => (JointReceptionSource.advance contract registered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs SourceCreditSource.issued)))
local notation "failed" => (JointReceptionSource.advance exchange issuedState (RenewableArchiveSource.Command.renew true false))
local notation "recovered" => (JointReceptionSource.advance contract failed (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs (DeferredProviderSource.recovery true))))
local notation "nextState" => (JointReceptionSource.advance contract recovered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs (DeferredProviderSource.trace true))))
local notation "failedWindow" => (RenewableArchiveSource.window exchange (JointReceptionSource.State.actual issuedState) true false)

section Metadata
variable {root : RenewableCodeLineage.Emitter (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit)}
 (state : JointReceptionSource.State root) (first second : List LocalCommandSource.Input)

private theorem executing_twice_keeps_the_original_windows :
 (JointReceptionSource.advance contract (JointReceptionSource.advance contract state (.execute first)) (.execute second)).actual.windows=
 state.actual.windows := rfl

private theorem executing_twice_keeps_all_history_responsibility_and_own_next :
 let next := JointReceptionSource.advance contract (JointReceptionSource.advance contract state (.execute first)) (.execute second)
 state.actual.archive <+: next.actual.archive ∧ state.rows <+: next.rows ∧
 ArchivedDeliveryConsumer.NativeContinuation next.actual.model next.actual.point := by
 have kept := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows contract state [.execute first,.execute second]
 exact ⟨kept.1,kept.2.2,JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩

private theorem the_original_window_is_kept_after_both_executions
 (terms : PaidInvocationSource.Contract (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit)) :
 RenewableArchiveSource.window terms state.actual true false ∈
 (JointReceptionSource.advance contract
  (JointReceptionSource.advance contract (JointReceptionSource.advance terms state (.renew true false)) (.execute first))
  (.execute second)).actual.windows := List.mem_append_right _ (List.mem_singleton_self _)

private theorem the_original_refused_window_keeps_its_typed_status
 (terms : PaidInvocationSource.Contract (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit))
 (refused : PaidInvocationSource.admitted state.actual.model.source.code terms state.actual.point true false=false) :
 (RenewableArchiveSource.window terms state.actual true false).status=.blocked .unpaid := by
 unfold RenewableArchiveSource.Window.status RenewableArchiveSource.Window.result RenewableArchiveSource.window
 rw [PaidInvocationSource.absent_payment_or_acceptance_cannot_open_the_window _ _ _ true false refused]
end Metadata

theorem the_failed_predecessor_keeps_the_complete_original_seed : retained=EventStep.seed saved :=
 SourceCreditConsumer.the_funded_seed_is_the_entire_actual_window_endpoint false

theorem the_failed_predecessor_is_the_complete_original_occurrence :
 FreshSigningReplay.physical (failed).actual=⟨model,saved⟩ :=
 SourceCreditConsumer.the_funded_model_is_the_entire_actual_window_occurrence false

theorem the_paired_old_payment_is_the_original_actual_source_row :
 DeferredProviderReceipt.payment=PaidInvocationSource.paymentRow SourceCreditSource.creditModel.source.code exchange
  SourceCreditSource.issued.cursor true :=
 SourceWindowCache.payment_is_the_original_actual_row SourceCreditSource.creditModel.source.code exchange
  SourceCreditSource.issued.cursor SourceCreditSource.issued.before true
  SourceCreditConsumer.the_credit_issue_replays_its_actual_source_inputs.2.1 SourceCreditConsumer.issued_original

theorem the_late_provider_replays_its_actual_source_inputs (allow : Bool) :
 SourceContinuationTrace.Sound model saved (recovery allow) (LocalCommandRun.run model saved (recovery allow).inputs) :=
 SourceOpportunityHandoff.every_controlled_prefix_replays_its_actual_source_inputs model saved retained
  the_failed_predecessor_keeps_the_complete_original_seed (provider allow) 2

theorem the_late_communication_replays_its_actual_source_inputs (allow : Bool) :
 SourceContinuationTrace.Sound model (origin allow) (trace allow)
  (LocalCommandRun.run model (origin allow) (trace allow).inputs) :=
 SourceOpportunityHandoff.every_controlled_prefix_replays_its_actual_source_inputs model (origin allow) (before allow)
  (the_late_provider_replays_its_actual_source_inputs allow).2.1 (transport allow) 18

theorem the_actual_late_provider_keeps_the_complete_original_occurrence :
 FreshSigningReplay.physical (recovered).actual=⟨model,origin true⟩ :=
 SourceCreditHandoff.controlled_execution_keeps_the_entire_actual_occurrence model saved retained contract failed
  the_failed_predecessor_is_the_complete_original_occurrence the_failed_predecessor_keeps_the_complete_original_seed
  (provider true) 2

theorem each_paired_late_acceptance_has_its_original_native_financial_inventory
 (receipt : DeferredProviderReceipt.Receipt true) :
 let final := EventHistory.execute saved (recovery true).stages
 (Financial.inventoryAt final.source.input
  (ProgrammeHistory.visitAt final.source.input (EventStep.boundary receipt.row.cursor))).filterMap
  (Financial.InstructionOrigin.instruction? final.source.input)=StageTrace.items receipt.row := by
 have sound := the_late_provider_replays_its_actual_source_inputs true
 have rows := sound.2.2.1.trans (congrArg (StageTrace.records saved) sound.2.2.2.2.symm)
 exact StageTrace.final_financial_inventory_is_the_original_record_items saved (recovery true).stages receipt.row
  (Eq.mp (congrArg (fun records : List (StageTrace.Record (code := model.source.code)) => receipt.row∈records) rows) receipt.actual)

theorem the_new_receiver_is_the_original_independent_consumer :
 observed true=HeaderReception.run (vocabulary true) (reception true) (origin true)
  (trace true).stages receiver (trace true).stages.length :=
 SourceContinuationTrace.receiver_from_the_same_complete_actual_trace model (origin true) (trace true) _
  (the_late_communication_replays_its_actual_source_inputs true) (vocabulary true) (reception true) receiver

theorem the_late_source_decision_is_the_original_authenticated_quorum :
 HeaderQuorum.produce (origin true) (vocabulary true) (reception true) (trace true).stages receiver (scope true) 1=.decided true := by
 have sound := the_late_communication_replays_its_actual_source_inputs true
 have rows := sound.2.2.1.trans (congrArg (StageTrace.records (origin true)) sound.2.2.2.2.symm)
 have same := CachedWorkDispatch.produce_eq (vocabulary true) (origin true) (reception true) (trace true).stages receiver (scope true) 1
 have checked := congrArg (fun rows : List (StageTrace.Record (code := model.source.code)) =>
  CachedWorkDispatch.produce (vocabulary true) (origin true) (reception true) rows receiver (scope true) 1) rows.symm
 exact same.symm.trans (checked.trans the_later_actual_service_generates_a_new_authenticated_decision.1)

theorem the_actual_next_keeps_the_complete_original_model_and_generated_cursor :
 FreshSigningReplay.physical (nextState).actual=⟨model,(trace true).cursor⟩ :=
 SourceCreditHandoff.controlled_execution_keeps_the_entire_actual_occurrence model (origin true) (before true)
  contract recovered the_actual_late_provider_keeps_the_complete_original_occurrence
  (the_late_provider_replays_its_actual_source_inputs true).2.1 (transport true) 18

theorem the_actual_next_has_the_generated_entire_current :
 (EventStep.seed (nextState).actual.point).current=(trace true).before.current :=
 SourceContinuationTrace.current_from_the_same_complete_occurrence model (trace true).cursor (nextState).actual (trace true).before
  the_actual_next_keeps_the_complete_original_model_and_generated_cursor
  (the_late_communication_replays_its_actual_source_inputs true).2.1

theorem the_actual_next_keeps_the_original_failed_window_history :
 (nextState).actual.windows=(failed).actual.windows :=
 executing_twice_keeps_the_original_windows failed (recovery true).inputs (trace true).inputs

theorem the_old_refusal_actual_late_receipt_and_safe_decision_coexist :
 (failedWindow)∈(nextState).actual.windows ∧ (failedWindow).status=.blocked .unpaid ∧
 (∃ receipt,DeferredProviderReceipt.produce true=.completed receipt) ∧
 HeaderQuorum.produce (origin true) (vocabulary true) (reception true) (trace true).stages receiver (scope true) 1=.decided true := by
 refine ⟨?_,the_original_refused_window_keeps_its_typed_status issuedState exchange
  SourceCreditConsumer.only_the_actual_paid_provider_branch_opens_the_original_window.2,
  DeferredProviderReceipt.actual_late_participation_generates_a_completed_receipt.1,
  the_late_source_decision_is_the_original_authenticated_quorum⟩
 exact the_original_window_is_kept_after_both_executions issuedState (recovery true).inputs (trace true).inputs exchange

theorem the_actual_recovery_keeps_all_history_responsibility_and_own_next :
 (failed).actual.archive <+: (nextState).actual.archive ∧ (failed).rows <+: (nextState).rows ∧
 ArchivedDeliveryConsumer.NativeContinuation (nextState).actual.model (nextState).actual.point :=
 executing_twice_keeps_all_history_responsibility_and_own_next failed (recovery true).inputs (trace true).inputs

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeferredProviderConsumer
