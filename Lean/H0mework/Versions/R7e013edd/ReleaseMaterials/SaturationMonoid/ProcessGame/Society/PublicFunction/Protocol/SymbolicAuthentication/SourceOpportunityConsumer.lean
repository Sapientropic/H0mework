import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceOpportunitySource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceOpportunityConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws contract)
open RecoveredProductiveSource (recycling feeding)
open SourceOpportunitySource
open private RecoveredSigningConsumer.production_original from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredSigningConsumer
noncomputable section

local notation "oldFirst" => (FreshSigningSource.cycle contract base laws ConcreteProductiveSource.ready ConcreteProductiveSource.request)
local notation "oldDonation" => (JointReceptionSource.advance recycling oldFirst (RenewableArchiveSource.Command.renew false true))
local notation "oldSupply" => (JointReceptionSource.advance feeding oldDonation (RenewableArchiveSource.Command.renew true true))
local notation "oldReady" => (JointReceptionSource.advance contract oldSupply (RenewableArchiveSource.Command.execute [LocalCommandSource.Input.command 2,LocalCommandSource.Input.idle]))
local notation "oldPrepared" => (FreshSigningSource.prepared contract oldReady ConcreteProductiveSource.request)
local notation "predecessor" => (FreshSigningSource.next contract base laws oldPrepared ConcreteProductiveSource.request)
local notation "registered" => (SourceOpportunityHandoff.register predecessor)
local notation "nextState" => (JointReceptionSource.advance contract registered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs SourceOpportunitySource.trace)))

theorem the_cached_predecessor_is_the_entire_original_seed : predecessorSeed=EventStep.seed predecessorPoint :=
 RecoveredSigningConsumer.the_new_trace_is_the_original_dynamic_execution.2.1

theorem the_cached_predecessor_is_the_entire_original_occurrence :
 FreshSigningReplay.physical (predecessor).actual=⟨predecessorModel,predecessorPoint⟩ :=
 RecoveredSigningConsumer.the_actual_new_endpoint_keeps_the_entire_original_occurrence

private theorem predecessor_original : predecessorPoint.side=.original := by
 have kept : predecessorPoint.side=RecoveredSigningSource.signingPoint.side :=
  SourceOpportunityHandoff.original_dynamic_keeps_the_source_side RecoveredSigningSource.signingModel
   RecoveredSigningSource.signingPoint RecoveredSigningSource.signingSeed
   RecoveredSigningSource.signingSeed.frame.sent.length base (laws RecoveredSigningSource.signingModel)
    ConcreteProductiveSource.request.work ConcreteProductiveSource.request.beats
 exact kept.trans ((SourceWindowCache.cached_point_keeps_the_source_side
  RecoveredSigningSource.suppliedModel.source.code contract RecoveredSigningSource.production.cursor
  RecoveredSigningSource.production.before true true).trans RecoveredSigningConsumer.production_original)

theorem the_new_interface_is_the_original_source_generated_catalogue :
 SourceOpportunityHandoff.catalogue predecessorModel predecessorSeed=
 SuccessorSigningSource.catalogue predecessorModel predecessorPoint :=
 SourceOpportunityHandoff.the_catalogue_is_generated_by_the_original_source
  predecessorModel predecessorPoint predecessorSeed the_cached_predecessor_is_the_entire_original_seed

theorem the_registration_is_the_same_entire_original_root_occurrence :
 FreshSigningReplay.physical (registered).actual=⟨model,origin⟩ :=
 SourceOpportunityHandoff.registration_at_the_same_complete_cached_occurrence predecessorModel predecessorPoint
  predecessorSeed predecessor the_cached_predecessor_is_the_entire_original_occurrence
  the_cached_predecessor_is_the_entire_original_seed

theorem the_registered_seed_is_the_entire_original_extended_seed : before=EventStep.seed origin :=
 SourceOpportunityHandoff.after_is_the_entire_actual_extended_seed predecessorModel predecessorPoint predecessorSeed
  the_cached_predecessor_is_the_entire_original_seed predecessor_original

theorem the_generated_control_is_the_original_actual_execution :
 SourceContinuationTrace.Sound model origin trace (LocalCommandRun.run model origin trace.inputs) :=
 SourceOpportunityHandoff.every_controlled_prefix_replays_its_actual_source_inputs model origin before
  the_registered_seed_is_the_entire_original_extended_seed (control model origin) 36

theorem the_generated_rows_are_the_complete_original_execution_records :
 trace.rows=StageTrace.records origin trace.stages :=
 the_generated_control_is_the_original_actual_execution.2.2.1.trans
  (congrArg (StageTrace.records origin) the_generated_control_is_the_original_actual_execution.2.2.2.2.symm)

theorem the_actual_receiver_is_the_original_independent_receiver :
 observed=HeaderReception.run vocabulary reception origin trace.stages receiver trace.stages.length :=
 SourceContinuationTrace.receiver_from_the_same_complete_actual_trace model origin trace _
  the_generated_control_is_the_original_actual_execution vocabulary reception receiver

theorem the_actual_communication_decision_comes_from_the_original_source_budget_consumer :
 HeaderQuorum.produce origin vocabulary reception trace.stages receiver scope 1=.decided true := by
 have same := CachedWorkDispatch.produce_eq vocabulary origin reception trace.stages receiver scope 1
 have checked := congrArg (fun rows : List (StageTrace.Record (code := model.source.code)) =>
  CachedWorkDispatch.produce vocabulary origin reception rows receiver scope 1)
  the_generated_rows_are_the_complete_original_execution_records.symm
 exact same.symm.trans (checked.trans registration_generates_an_actual_new_packet_delivery_and_authenticated_decision.1)

theorem the_source_generated_packet_has_its_original_paid_signature
 (receipt : HeaderReception.Receipt (code := model.source.code)) (inside : receipt∈observed.receipts) :
 receipt.wire.ballot∈StageBudget.ledger vocabulary origin trace.stages :=
 HeaderReception.receipt_has_original_paid_ballot vocabulary reception origin trace.stages receiver trace.stages.length
  receipt (Eq.mp (congrArg (fun seen : HeaderReception.Receiver (code := model.source.code) => receipt∈seen.receipts)
   the_actual_receiver_is_the_original_independent_receiver) inside)

theorem the_actual_next_keeps_the_entire_original_model_and_generated_cursor :
 FreshSigningReplay.physical (nextState).actual=⟨model,trace.cursor⟩ := by
 have fixed := SourceContinuationTrace.fixed_execution_keeps_the_entire_actual_model_and_cursor
  model origin (registered).actual before the_registration_is_the_same_entire_original_root_occurrence
  the_registered_seed_is_the_entire_original_extended_seed trace.inputs
 have fixedSound := (SourceContinuationTrace.every_fixed_prefix_is_the_same_actual_execution model origin before
  the_registered_seed_is_the_entire_original_extended_seed trace.inputs).1
 have sameCursor := fixedSound.trans the_generated_control_is_the_original_actual_execution.1.symm
 exact fixed.trans (congrArg (fun cursor => (⟨model,cursor⟩ : FreshSigningReplay.Physical
  (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good) (Port := Delegation.Funded.Port)
  (Technology := Bool) (Instrument := Unit))) sameCursor)

theorem the_actual_next_has_the_generated_entire_current :
 (EventStep.seed (nextState).actual.point).current=trace.before.current :=
 SourceContinuationTrace.current_from_the_same_complete_occurrence model trace.cursor (nextState).actual trace.before
  the_actual_next_keeps_the_entire_original_model_and_generated_cursor
  the_generated_control_is_the_original_actual_execution.2.1

theorem the_actual_successful_decision_retains_the_actual_production_failure :
 HeaderQuorum.produce origin vocabulary reception trace.stages receiver scope 1=.decided true ∧
 ¬model.source.code.law.Valid (EventStep.seed (nextState).actual.point).current RecycledQuorumMaterial.production := by
 refine ⟨the_actual_communication_decision_comes_from_the_original_source_budget_consumer,?_⟩
 exact Eq.mp (congrArg (fun current : RecycledQuorumMaterial.Current =>
  ¬model.source.code.law.Valid current RecycledQuorumMaterial.production)
  the_actual_next_has_the_generated_entire_current.symm) successful_communication_preserves_the_actual_production_obstruction.2.1

theorem the_actual_transition_keeps_all_prior_history_responsibility_and_own_next :
 (predecessor).actual.archive <+: (nextState).actual.archive ∧
 (predecessor).actual.windows <+: (nextState).actual.windows ∧ (predecessor).rows <+: (nextState).rows ∧
 ArchivedDeliveryConsumer.NativeContinuation (nextState).actual.model (nextState).actual.point :=
 SourceOpportunityHandoff.every_registered_execution_keeps_history_responsibility_and_own_next
  contract predecessor trace.inputs

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceOpportunityConsumer
