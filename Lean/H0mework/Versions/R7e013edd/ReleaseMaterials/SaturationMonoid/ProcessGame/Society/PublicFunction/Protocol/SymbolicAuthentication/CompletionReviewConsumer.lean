import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionReviewSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionReviewConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws contract)
open RecoveredProductiveSource (recycling feeding)
open SourceCreditSource (exchange)
open CompletionReviewSource
open private SourceCreditConsumer.issued_original from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCreditConsumer
noncomputable section

local notation "oldFirst" => (FreshSigningSource.cycle contract base laws ConcreteProductiveSource.ready ConcreteProductiveSource.request)
local notation "oldDonation" => (JointReceptionSource.advance recycling oldFirst (RenewableArchiveSource.Command.renew false true))
local notation "oldSupply" => (JointReceptionSource.advance feeding oldDonation (RenewableArchiveSource.Command.renew true true))
local notation "oldReady" => (JointReceptionSource.advance contract oldSupply (RenewableArchiveSource.Command.execute [LocalCommandSource.Input.command 2,LocalCommandSource.Input.idle]))
local notation "oldPrepared" => (FreshSigningSource.prepared contract oldReady ConcreteProductiveSource.request)
local notation "oldPredecessor" => (FreshSigningSource.next contract base laws oldPrepared ConcreteProductiveSource.request)
local notation "oldRegistered" => (SourceOpportunityHandoff.register oldPredecessor)
local notation "oldOpportunity" => (JointReceptionSource.advance contract oldRegistered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs SourceOpportunitySource.trace)))

local notation "registered" => (SourceCreditHandoff.register oldOpportunity)
local notation "issuedState" => (JointReceptionSource.advance contract registered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs SourceCreditSource.issued)))
local notation "failed" => (JointReceptionSource.advance exchange issuedState (RenewableArchiveSource.Command.renew true false))
local notation "recovered" => (JointReceptionSource.advance contract failed (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs (DeferredProviderSource.recovery true))))
local notation "predecessor" => (JointReceptionSource.advance contract recovered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs (DeferredProviderSource.trace true))))
local notation "registeredReview" => (CompletionReviewHandoff.register predecessor)
local notation "nextState" => (JointReceptionSource.advance contract registeredReview (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs CompletionReviewSource.trace)))

theorem the_predecessor_is_the_complete_original_seed : predecessorSeed=EventStep.seed predecessorPoint :=
 (DeferredProviderConsumer.the_late_communication_replays_its_actual_source_inputs true).2.1

theorem the_predecessor_is_the_complete_original_occurrence :
 FreshSigningReplay.physical (predecessor).actual=⟨predecessorModel,predecessorPoint⟩ :=
 DeferredProviderConsumer.the_actual_next_keeps_the_complete_original_model_and_generated_cursor

private theorem predecessor_original : predecessorPoint.side=.original := by
 have first := (SourceWindowCache.cached_point_keeps_the_source_side SourceCreditSource.creditModel.source.code exchange
  SourceCreditSource.issued.cursor SourceCreditSource.issued.before true false).trans SourceCreditConsumer.issued_original
 have later := (SourceOpportunityHandoff.controlled_keeps_the_source_side DeferredProviderSource.model DeferredProviderSource.saved
  DeferredProviderSource.retained (DeferredProviderSource.provider true) 2).trans first
 exact (SourceOpportunityHandoff.controlled_keeps_the_source_side DeferredProviderSource.model (DeferredProviderSource.origin true)
  (DeferredProviderSource.before true) (DeferredProviderSource.transport true) 18).trans later

theorem the_registered_review_keeps_the_complete_original_seed : before=EventStep.seed origin :=
 CompletionReviewHandoff.after_is_the_entire_actual_extended_seed predecessorModel predecessorPoint predecessorSeed
  the_predecessor_is_the_complete_original_seed predecessor_original

theorem the_registered_review_keeps_the_complete_original_occurrence :
 FreshSigningReplay.physical (registeredReview).actual=⟨model,origin⟩ :=
 CompletionReviewHandoff.registration_at_the_same_complete_cached_occurrence predecessorModel predecessorPoint predecessorSeed
  predecessor the_predecessor_is_the_complete_original_occurrence the_predecessor_is_the_complete_original_seed

theorem the_review_permission_comes_from_the_original_native_law :
 Mandate.CanRun predecessorModel.scope predecessorSeed.current DeferredProviderReceipt.bill.payer (.review) := by
 have valid := (CompletionReviewHandoff.offered_requires_actual_pairing_freshness_and_native_admission
  predecessorModel predecessorSeed CompletionReviewHandoff.receiptReady
  actual_completion_and_live_native_admission_generate_the_review_offer.2.2.1).2.2
 rw [CompletionReviewHandoff.request,predecessorModel.law_exact] at valid
 exact (Mandate.command_policy predecessorModel.base predecessorModel.scope predecessorSeed.current
  DeferredProviderReceipt.bill.payer (.review)).mp valid.1.2

theorem the_review_replays_its_actual_source_inputs :
 SourceContinuationTrace.Sound model origin trace (LocalCommandRun.run model origin trace.inputs) :=
 SourceOpportunityHandoff.every_controlled_prefix_replays_its_actual_source_inputs model origin before
  the_registered_review_keeps_the_complete_original_seed (control CompletionReviewHandoff.receiptReady) 2

theorem all_review_rows_are_the_complete_original_execution_records :
 trace.rows=StageTrace.records origin trace.stages :=
 the_review_replays_its_actual_source_inputs.2.2.1.trans
  (congrArg (StageTrace.records origin) the_review_replays_its_actual_source_inputs.2.2.2.2.symm)

theorem every_review_row_is_in_its_original_native_financial_inventory
 (row : StageTrace.Record (code := model.source.code)) (inside : row∈trace.rows) :
 let final := EventHistory.execute origin trace.stages
 (Financial.inventoryAt final.source.input (ProgrammeHistory.visitAt final.source.input (EventStep.boundary row.cursor))).filterMap
  (Financial.InstructionOrigin.instruction? final.source.input)=StageTrace.items row :=
 StageTrace.final_financial_inventory_is_the_original_record_items origin trace.stages row
  (Eq.mp (congrArg (fun records : List (StageTrace.Record (code := model.source.code)) => row∈records)
   all_review_rows_are_the_complete_original_execution_records) inside)

theorem the_new_review_ballots_have_the_original_paid_native_ledger :
 ledger=StageBudget.ledger vocabulary origin trace.stages :=
 (congrArg (CachedWorkDispatch.ledger vocabulary) all_review_rows_are_the_complete_original_execution_records).trans
  (CachedWorkDispatch.ledger_eq vocabulary origin trace.stages)

theorem the_review_block_is_the_original_quorum_consumer :
 HeaderQuorum.produce origin vocabulary reception trace.stages receiver scope 1=.blocked .missingQuorum := by
 have same := CachedWorkDispatch.produce_eq vocabulary origin reception trace.stages receiver scope 1
 have checked := congrArg (fun rows : List (StageTrace.Record (code := model.source.code)) =>
  CachedWorkDispatch.produce vocabulary origin reception rows receiver scope 1)
  all_review_rows_are_the_complete_original_execution_records.symm
 exact same.symm.trans (checked.trans the_native_review_has_a_paid_new_phase_ballot_but_no_free_decision.2.2)

theorem the_actual_next_keeps_the_complete_original_model_and_generated_cursor :
 FreshSigningReplay.physical (nextState).actual=⟨model,trace.cursor⟩ :=
 CompletionReviewHandoff.controlled_execution_keeps_the_entire_actual_occurrence model origin before contract registeredReview
  the_registered_review_keeps_the_complete_original_occurrence the_registered_review_keeps_the_complete_original_seed
  (control CompletionReviewHandoff.receiptReady) 2

theorem the_actual_next_has_the_generated_entire_current :
 (EventStep.seed (nextState).actual.point).current=trace.before.current :=
 SourceContinuationTrace.current_from_the_same_complete_occurrence model trace.cursor (nextState).actual trace.before
  the_actual_next_keeps_the_complete_original_model_and_generated_cursor the_review_replays_its_actual_source_inputs.2.1

theorem the_actual_next_keeps_the_paid_review_epoch_cost_and_all_debt :
 (EventStep.seed (nextState).actual.point).current.technology.version=1 ∧
 (EventStep.seed (nextState).actual.point).current.technology.last=some (.review) ∧
 (EventStep.seed (nextState).actual.point).current.stock 1 .service=0 ∧
 (∀ instrument debtor creditor,(EventStep.seed (nextState).actual.point).current.claims instrument debtor creditor=
  predecessorSeed.current.claims instrument debtor creditor) := by
 have source := the_actual_paid_review_changes_the_native_epoch_and_preserves_debt
 have known : trace.before.current.technology.version=1 ∧ trace.before.current.technology.last=some (.review) ∧
  trace.before.current.stock 1 .service=0 ∧ (∀ instrument debtor creditor,trace.before.current.claims instrument debtor creditor=
  predecessorSeed.current.claims instrument debtor creditor) := ⟨source.1,source.2.1,source.2.2.1,source.2.2.2.2.1⟩
 exact Eq.mp (congrArg (fun current : RecycledQuorumMaterial.Current => current.technology.version=1 ∧
  current.technology.last=some (.review) ∧ current.stock 1 .service=0 ∧
  (∀ instrument debtor creditor,current.claims instrument debtor creditor=predecessorSeed.current.claims instrument debtor creditor))
  the_actual_next_has_the_generated_entire_current.symm) known

theorem the_actual_review_epoch_rejects_the_old_invoice_under_any_resource_state
 (retained : Feedback.State model.source.code)
 (sameEpoch : retained.current.technology.version=(EventStep.seed (nextState).actual.point).current.technology.version) :
 CompletionReviewHandoff.offered model retained CompletionReviewHandoff.receiptReady=false := by
 apply CompletionReviewHandoff.a_changed_native_epoch_blocks_the_old_invoice_independently_of_resources
 have current := the_actual_next_keeps_the_paid_review_epoch_cost_and_all_debt.1
 have original := actual_completion_and_live_native_admission_generate_the_review_offer.2.1
 intro equal
 omega

theorem the_actual_review_keeps_history_responsibility_and_own_next :
 (predecessor).actual.archive <+: (nextState).actual.archive ∧ (predecessor).actual.windows <+: (nextState).actual.windows ∧
 (predecessor).rows <+: (nextState).rows ∧ ArchivedDeliveryConsumer.NativeContinuation (nextState).actual.model (nextState).actual.point :=
 CompletionReviewHandoff.every_registered_execution_keeps_history_responsibility_and_own_next contract predecessor trace.inputs

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionReviewConsumer
