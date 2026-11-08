import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredSigningSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredSigningConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws contract)
open RecoveredProductiveSource (recycling feeding prior)
open RecoveredSigningSource
noncomputable section

local notation "nativePredecessor" => (FreshSigningSource.cycle contract base laws ConcreteProductiveSource.ready ConcreteProductiveSource.request)
local notation "nativeDonation" => (RenewableArchiveSource.renew recycling (JointReceptionSource.State.actual nativePredecessor) false true)
local notation "nativeSupply" => (RenewableArchiveSource.renew feeding nativeDonation true true)
local notation "nativeReady" => (RenewableArchiveSource.execute nativeSupply [LocalCommandSource.Input.command 2,LocalCommandSource.Input.idle])
local notation "nativePrepared" => (RenewableArchiveSource.renew contract nativeReady true true)
local notation "jointSupply" => (JointReceptionSource.advance feeding (JointReceptionSource.advance recycling nativePredecessor (RenewableArchiveSource.Command.renew false true)) (RenewableArchiveSource.Command.renew true true))
local notation "jointReady" => (JointReceptionSource.advance contract jointSupply (RenewableArchiveSource.Command.execute [LocalCommandSource.Input.command 2,LocalCommandSource.Input.idle]))
local notation "jointPrepared" => (FreshSigningSource.prepared contract jointReady ConcreteProductiveSource.request)
local notation "jointEndpoint" => (FreshSigningSource.next contract base laws jointPrepared ConcreteProductiveSource.request)

theorem the_production_trace_is_the_original_actual_execution :
 SourceContinuationTrace.Sound suppliedModel RecoveredWindowSource.suppliedPoint production
  (LocalCommandRun.run suppliedModel RecoveredWindowSource.suppliedPoint [.command 2,.idle]) :=
 SourceContinuationTrace.every_fixed_prefix_is_the_same_actual_execution suppliedModel RecoveredWindowSource.suppliedPoint
  RecoveredWindowSource.supplied RecoveredWindowConsumer.the_paid_feed_window_keeps_the_entire_actual_seed _

theorem the_production_endpoint_keeps_the_entire_original_occurrence :
 FreshSigningReplay.physical nativeReady=⟨suppliedModel,production.cursor⟩ :=
 SourceContinuationTrace.fixed_execution_keeps_the_entire_actual_model_and_cursor suppliedModel
  RecoveredWindowSource.suppliedPoint nativeSupply RecoveredWindowSource.supplied
  RecoveredWindowConsumer.the_paid_feed_window_has_the_same_entire_actual_model_and_cursor
  RecoveredWindowConsumer.the_paid_feed_window_keeps_the_entire_actual_seed _

private theorem supplied_original : RecoveredWindowSource.suppliedPoint.side=.original := by
 have stream := SourceWindowCache.cached_stream_keeps_the_source_side prior.actual.model prior.actual.point
  (EventStep.seed prior.actual.point).frame.sent.length base (laws prior.actual.model)
  ConcreteProductiveSource.request.work ConcreteProductiveSource.request.beats
 have first : RecoveredWindowSource.origin.side=.original := stream.trans
  ((SourceWindowCache.actual_window_keeps_the_source_side
   (RenewableArchiveSource.window contract ConcreteProductiveSource.ready.actual true true)).trans (by rfl))
 have donated := (SourceWindowCache.cached_point_keeps_the_source_side RecoveredWindowSource.model.source.code
  recycling RecoveredWindowSource.origin RecoveredWindowSource.before false true).trans first
 exact (SourceWindowCache.cached_point_keeps_the_source_side _ feeding
  RecoveredWindowSource.donatedPoint RecoveredWindowSource.donated true true).trans donated

private theorem production_original : production.cursor.side=.original :=
 (SourceContinuationTrace.fixed_keeps_the_source_side suppliedModel RecoveredWindowSource.suppliedPoint
  RecoveredWindowSource.supplied [.command 2,.idle]).trans supplied_original

theorem the_signing_seed_is_the_entire_original_actual_seed : signingSeed=EventStep.seed signingPoint :=
 SourceWindowCache.after_is_the_entire_actual_endpoint suppliedModel.source.code contract
  production.cursor production.before true true the_production_trace_is_the_original_actual_execution.2.1 production_original

theorem the_signing_window_keeps_the_entire_original_occurrence :
 FreshSigningReplay.physical nativePrepared=⟨signingModel,signingPoint⟩ :=
 SourceWindowCache.renewal_at_the_same_complete_cached_occurrence contract true true nativeReady
  suppliedModel production.cursor production.before the_production_endpoint_keeps_the_entire_original_occurrence
  the_production_trace_is_the_original_actual_execution.2.1 production_original

theorem the_new_trace_is_the_original_dynamic_execution :
 SourceContinuationTrace.Sound signingModel signingPoint trace
  (SourceDynamicCache.actual signingModel signingPoint signingSeed.frame.sent.length base (laws signingModel)
   ConcreteProductiveSource.request.work ConcreteProductiveSource.request.beats) :=
 SourceContinuationTrace.every_dynamic_prefix_is_the_original_normal_policy_execution signingModel signingPoint
  signingSeed.frame.sent.length base (laws signingModel) ConcreteProductiveSource.request.work signingSeed
  the_signing_seed_is_the_entire_original_actual_seed ConcreteProductiveSource.request.beats

theorem the_new_rows_are_the_complete_original_execution_records :
 trace.rows=StageTrace.records signingPoint trace.stages :=
 the_new_trace_is_the_original_dynamic_execution.2.2.1.trans
  (congrArg (StageTrace.records signingPoint) the_new_trace_is_the_original_dynamic_execution.2.2.2.2.symm)

theorem the_new_receiver_is_the_original_independent_receiver :
 observed receiver=HeaderReception.run vocabulary reception signingPoint trace.stages receiver trace.stages.length :=
 SourceContinuationTrace.receiver_from_the_same_complete_actual_trace signingModel signingPoint trace _
  the_new_trace_is_the_original_dynamic_execution vocabulary reception receiver

theorem the_new_quorum_is_generated_by_the_original_source_consumer :
 HeaderQuorum.produce signingPoint vocabulary reception trace.stages receiver scope 1=.decided true := by
 have same := CachedWorkDispatch.produce_eq vocabulary signingPoint reception trace.stages receiver scope 1
 have checked := congrArg (fun rows => CachedWorkDispatch.produce vocabulary signingPoint reception rows receiver scope 1)
  the_new_rows_are_the_complete_original_execution_records.symm
 exact same.symm.trans (checked.trans the_new_phase_has_an_actual_authenticated_receiver_quorum)

theorem the_new_decision_has_the_actual_source_identity_budget_and_distinct_support :
 (ActorEnvelope.roster signingPoint.source).card+ActorStageEnvelope.budget signingPoint vocabulary trace.stages scope<1+1 ∧
 ActorQuorum.readout (HeaderQuorum.observed signingPoint vocabulary reception trace.stages receiver) scope 1=.decided true ∧
 0<1 ∧ 1≤(ActorQuorum.support (HeaderQuorum.observed signingPoint vocabulary reception trace.stages receiver) scope true).card :=
 HeaderQuorum.a_produced_decision_keeps_the_actual_identity_budget_and_distinct_actor_quorum
  signingPoint vocabulary reception trace.stages receiver scope 1 true the_new_quorum_is_generated_by_the_original_source_consumer

theorem every_new_receipt_retains_its_actual_paid_signature_and_new_phase
 (receipt : HeaderReception.Receipt (code := signingModel.source.code))
 (inside : receipt∈(observed receiver).receipts) :
 receipt.wire.ballot∈StageBudget.ledger vocabulary signingPoint trace.stages ∧
 signingPoint.cut≤receipt.wire.ballot.cut ∧ receipt.wire.ballot.scope.phase=signingPoint.cut := by
 have original := HeaderReception.receipt_has_original_paid_ballot vocabulary reception signingPoint trace.stages
  receiver trace.stages.length receipt (Eq.mp (congrArg (fun received => receipt∈received.receipts)
   the_new_receiver_is_the_original_independent_receiver) inside)
 exact ⟨original,SourceContinuationTrace.every_generated_ballot_keeps_the_new_actual_phase signingModel signingPoint
  signingSeed.frame.sent.length base (laws signingModel) ConcreteProductiveSource.request.work signingSeed
  the_signing_seed_is_the_entire_original_actual_seed ConcreteProductiveSource.request.beats receipt.wire.ballot original⟩

theorem the_actual_new_endpoint_keeps_the_entire_original_occurrence :
 FreshSigningReplay.physical (jointEndpoint).actual=⟨signingModel,trace.cursor⟩ :=
 SourceContinuationTrace.fresh_next_keeps_the_entire_actual_model_and_cached_cursor signingModel signingPoint
  base contract laws jointPrepared signingSeed the_signing_window_keeps_the_entire_original_occurrence
  the_signing_seed_is_the_entire_original_actual_seed ConcreteProductiveSource.request rfl

theorem the_actual_new_endpoint_has_the_generated_full_current :
 (EventStep.seed (jointEndpoint).actual.point).current=trace.before.current :=
 SourceContinuationTrace.current_from_the_same_complete_occurrence signingModel trace.cursor
  (jointEndpoint).actual trace.before the_actual_new_endpoint_keeps_the_entire_original_occurrence
  the_new_trace_is_the_original_dynamic_execution.2.1

theorem the_actual_new_endpoint_grows_service_and_keeps_all_original_claims :
 (∀ instrument debtor creditor,(EventStep.seed (jointEndpoint).actual.point).current.claims instrument debtor creditor=
  RecoveredWindowSource.before.current.claims instrument debtor creditor) ∧
 (∑ party,RecoveredWindowSource.before.current.stock party .service)+3≤
  ∑ party,(EventStep.seed (jointEndpoint).actual.point).current.stock party .service := by
 refine ⟨?_,?_⟩
 · intro instrument debtor creditor
   exact (congrArg (fun current : RecycledQuorumMaterial.Current => current.claims instrument debtor creditor)
    the_actual_new_endpoint_has_the_generated_full_current).trans
     (the_new_actual_endpoint_retains_claims_and_grows_total_service.1 instrument debtor creditor)
 · exact the_new_actual_endpoint_retains_claims_and_grows_total_service.2.trans_eq
    (congrArg (fun current : RecycledQuorumMaterial.Current => ∑ party,current.stock party .service)
     the_actual_new_endpoint_has_the_generated_full_current).symm

theorem the_new_actual_endpoint_keeps_original_responsibility_and_own_next :
 ArchivedDeliveryConsumer.NativeContinuation (jointEndpoint).actual.model (jointEndpoint).actual.point :=
 JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next jointEndpoint

theorem the_new_actual_round_retains_every_prior_archive_window_and_row :
 (jointPrepared).actual.archive <+: (jointEndpoint).actual.archive ∧
 (jointPrepared).actual.windows <+: (jointEndpoint).actual.windows ∧
 (jointPrepared).rows <+: (jointEndpoint).rows :=
 FreshSigningSource.every_round_retains_all_original_archives_windows_and_rows
  contract base laws jointPrepared ConcreteProductiveSource.request

theorem every_earlier_signature_is_rejected_in_the_new_issuing_context
 (wire : HeaderTransport.Wire (code := signingModel.source.code)) (earlier : wire.ballot.cut<signingPoint.cut) :
 HeaderTransport.verify vocabulary signingPoint trace.stages wire=false :=
 SourceContinuationTrace.earlier_signatures_are_not_in_the_new_actual_issuing_context signingModel signingPoint
  signingSeed.frame.sent.length base (laws signingModel) ConcreteProductiveSource.request.work signingSeed
  the_signing_seed_is_the_entire_original_actual_seed ConcreteProductiveSource.request.beats wire earlier

theorem the_send_only_control_is_an_actual_source_prefix :
 ∃ stages, stages <+: trace.stages ∧ undeliveredRows=StageTrace.records signingPoint stages := by
 unfold undeliveredRows
 cases found : (CachedWorkDispatch.wires vocabulary trace.rows).head? with
 | none => exact ⟨[],List.nil_prefix,rfl⟩
 | some wire =>
  let count := wire.sendCut-signingPoint.cut+1
  refine ⟨trace.stages.take count,List.take_prefix _ _,?_⟩
  exact (congrArg (List.take count) the_new_rows_are_the_complete_original_execution_records).trans
   (SourceContinuationTrace.taking_records_is_the_same_actual_source_prefix signingModel signingPoint trace.stages count)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredSigningConsumer
