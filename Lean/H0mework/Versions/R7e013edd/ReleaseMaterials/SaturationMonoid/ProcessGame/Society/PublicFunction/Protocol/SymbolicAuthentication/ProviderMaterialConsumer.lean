import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProviderMaterialCapacity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProviderMaterialConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws contract)
open RecoveredProductiveSource (recycling feeding)
open SourceCreditSource (exchange)
open ProviderMaterialSource
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
local notation "oldDeferred" => (JointReceptionSource.advance contract recovered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs (DeferredProviderSource.trace true))))
local notation "registeredReview" => (CompletionReviewHandoff.register oldDeferred)
local notation "predecessor" => (JointReceptionSource.advance contract registeredReview (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs CompletionReviewSource.trace)))
local notation "nextState" => (JointReceptionSource.advance contract predecessor (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs (ProviderMaterialSource.trace 3 true true))))

theorem the_material_origin_is_the_complete_original_actual_seed : before=EventStep.seed origin :=
 CompletionReviewConsumer.the_review_replays_its_actual_source_inputs.2.1

theorem the_material_origin_is_the_complete_original_actual_occurrence :
 FreshSigningReplay.physical (predecessor).actual=⟨model,origin⟩ :=
 CompletionReviewConsumer.the_actual_next_keeps_the_complete_original_model_and_generated_cursor

theorem every_material_request_replays_only_its_actual_source_inputs (units : Nat) (produce deliver : Bool) :
 SourceContinuationTrace.Sound model origin (trace units produce deliver)
  (LocalCommandRun.run model origin (trace units produce deliver).inputs) :=
 SourceOpportunityHandoff.every_controlled_prefix_replays_its_actual_source_inputs model origin before
  the_material_origin_is_the_complete_original_actual_seed (control units produce deliver) (4*units)

theorem every_material_request_keeps_the_complete_actual_joint_occurrence (units : Nat) (produce deliver : Bool) :
 FreshSigningReplay.physical (JointReceptionSource.advance contract predecessor (.execute (trace units produce deliver).inputs)).actual=
  ⟨model,(trace units produce deliver).cursor⟩ :=
 SourceCreditHandoff.controlled_execution_keeps_the_entire_actual_occurrence model origin before contract predecessor
  the_material_origin_is_the_complete_original_actual_occurrence the_material_origin_is_the_complete_original_actual_seed
  (control units produce deliver) (4*units)

theorem the_material_rows_are_the_complete_original_native_records :
 (trace 3 true true).rows=StageTrace.records origin (trace 3 true true).stages :=
 (every_material_request_replays_only_its_actual_source_inputs 3 true true).2.2.1.trans
  (congrArg (StageTrace.records origin) (every_material_request_replays_only_its_actual_source_inputs 3 true true).2.2.2.2.symm)

theorem every_real_production_and_transfer_has_its_original_native_financial_inventory
 (row : StageTrace.Record (code := model.source.code)) (inside : row∈(trace 3 true true).rows) :
 let final := EventHistory.execute origin (trace 3 true true).stages
 (Financial.inventoryAt final.source.input (ProgrammeHistory.visitAt final.source.input (EventStep.boundary row.cursor))).filterMap
  (Financial.InstructionOrigin.instruction? final.source.input)=StageTrace.items row :=
 StageTrace.final_financial_inventory_is_the_original_record_items origin (trace 3 true true).stages row
  (Eq.mp (congrArg (fun records : List (StageTrace.Record (code := model.source.code)) => row∈records)
   the_material_rows_are_the_complete_original_native_records) inside)

theorem the_material_result_is_the_original_current_of_the_actual_joint_next :
 (EventStep.seed (nextState).actual.point).current=(trace 3 true true).before.current :=
 SourceContinuationTrace.current_from_the_same_complete_occurrence model (trace 3 true true).cursor (nextState).actual
  (trace 3 true true).before (every_material_request_keeps_the_complete_actual_joint_occurrence 3 true true)
  (every_material_request_replays_only_its_actual_source_inputs 3 true true).2.1

theorem the_actual_next_has_three_new_feedstock_units_and_spends_the_real_provider_inputs :
 (EventStep.seed (nextState).actual.point).current.stock 1 .feedstock=3 ∧
 (EventStep.seed (nextState).actual.point).current.stock 2 .waste=0 ∧
 (EventStep.seed (nextState).actual.point).current.stock 2 .energy=0 ∧
 (EventStep.seed (nextState).actual.point).current.stock 2 .labor=0 := by
 have source := three_actual_productions_and_transfers_generate_three_new_feedstock_units
 have known : (trace 3 true true).before.current.stock 1 .feedstock=3 ∧
  (trace 3 true true).before.current.stock 2 .waste=0 ∧ (trace 3 true true).before.current.stock 2 .energy=0 ∧
  (trace 3 true true).before.current.stock 2 .labor=0 := ⟨source.2.1,source.2.2.2.1,source.2.2.2.2.1,source.2.2.2.2.2.1⟩
 exact Eq.mp (congrArg (fun current : RecycledQuorumMaterial.Current => current.stock 1 .feedstock=3 ∧
  current.stock 2 .waste=0 ∧ current.stock 2 .energy=0 ∧ current.stock 2 .labor=0)
  the_material_result_is_the_original_current_of_the_actual_joint_next.symm) known

theorem the_actual_material_next_keeps_debt_epoch_and_the_worker_production_obstruction :
 (∀ instrument debtor creditor,(EventStep.seed (nextState).actual.point).current.claims instrument debtor creditor=
  before.current.claims instrument debtor creditor) ∧
 (EventStep.seed (nextState).actual.point).current.technology.version=1 ∧
 (EventStep.seed (nextState).actual.point).current.stock 1 .service=0 ∧
 (EventStep.seed (nextState).actual.point).current.stock 2 .service=0 ∧
 ¬model.source.code.law.Valid (EventStep.seed (nextState).actual.point).current RecycledQuorumMaterial.production :=
 Eq.mp (congrArg (fun current : RecycledQuorumMaterial.Current =>
  (∀ instrument debtor creditor,current.claims instrument debtor creditor=before.current.claims instrument debtor creditor) ∧
  current.technology.version=1 ∧ current.stock 1 .service=0 ∧ current.stock 2 .service=0 ∧
  ¬model.source.code.law.Valid current RecycledQuorumMaterial.production)
  the_material_result_is_the_original_current_of_the_actual_joint_next.symm)
  material_progress_keeps_all_debt_native_epoch_and_zero_service

theorem the_material_quorum_block_is_the_original_independent_consumer :
 HeaderQuorum.produce origin ProviderMaterialCapacity.vocabulary ProviderMaterialCapacity.reception
  (trace 3 true true).stages ProviderMaterialCapacity.receiver ProviderMaterialCapacity.scope 1=.blocked .missingQuorum := by
 have same := CachedWorkDispatch.produce_eq ProviderMaterialCapacity.vocabulary origin ProviderMaterialCapacity.reception
  (trace 3 true true).stages ProviderMaterialCapacity.receiver ProviderMaterialCapacity.scope 1
 have checked := congrArg (fun rows : List (StageTrace.Record (code := model.source.code)) =>
  CachedWorkDispatch.produce ProviderMaterialCapacity.vocabulary origin ProviderMaterialCapacity.reception rows
   ProviderMaterialCapacity.receiver ProviderMaterialCapacity.scope 1)
  the_material_rows_are_the_complete_original_native_records.symm
 exact same.symm.trans (checked.trans ProviderMaterialCapacity.real_material_output_does_not_fabricate_signatures_packets_or_quorum.2.2)

theorem the_actual_material_next_keeps_all_history_responsibility_and_own_next :
 (predecessor).actual.archive <+: (nextState).actual.archive ∧ (predecessor).actual.windows <+: (nextState).actual.windows ∧
 (predecessor).rows <+: (nextState).rows ∧ ArchivedDeliveryConsumer.NativeContinuation (nextState).actual.model (nextState).actual.point := by
 have kept := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows contract predecessor [.execute (trace 3 true true).inputs]
 exact ⟨kept.1,kept.2.1,kept.2.2,JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProviderMaterialConsumer
