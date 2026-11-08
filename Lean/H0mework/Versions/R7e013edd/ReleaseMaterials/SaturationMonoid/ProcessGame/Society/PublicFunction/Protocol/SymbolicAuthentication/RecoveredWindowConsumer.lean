import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredWindowSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredWindowConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws contract)
open RecoveredProductiveSource (start prior snapshot recycling feeding)
open RecoveredWindowSource
noncomputable section

def actualDonation := JointReceptionSource.advance recycling start (.renew false true)
def actualSupply := JointReceptionSource.advance feeding actualDonation (.renew true true)

local notation "nativePredecessor" => (FreshSigningSource.cycle contract base laws ConcreteProductiveSource.ready ConcreteProductiveSource.request)
local notation "nativeDonation" => (RenewableArchiveSource.renew recycling (JointReceptionSource.State.actual nativePredecessor) false true)
local notation "nativeSupply" => (RenewableArchiveSource.renew feeding nativeDonation true true)

theorem the_cached_predecessor_is_the_complete_original_seed : before=EventStep.seed origin :=
 (SourceDynamicCache.the_executable_stream_has_the_same_complete_source_execution
  prior.actual.model prior.actual.point (EventStep.seed prior.actual.point).frame.sent.length
  base (laws prior.actual.model) ConcreteProductiveSource.request.work ConcreteProductiveSource.request.beats).2.1

theorem the_cached_predecessor_is_the_original_model_and_cursor :
 FreshSigningReplay.physical (FreshSigningSource.cycle contract base laws
  ConcreteProductiveSource.ready ConcreteProductiveSource.request).actual=
 ⟨(FreshSigningSource.prepared contract ConcreteProductiveSource.ready ConcreteProductiveSource.request).actual.model,
  (SourceDynamicCache.Fresh.generated base laws
   (FreshSigningSource.prepared contract ConcreteProductiveSource.ready ConcreteProductiveSource.request)
   ConcreteProductiveSource.request).cursor⟩ :=
 SourceWindowCache.a_zero_repair_cycle_has_the_complete_cached_occurrence
  contract base laws ConcreteProductiveSource.ready ConcreteProductiveSource.request rfl

private theorem predecessor_original : origin.side=.original := by
 have kept := SourceWindowCache.cached_stream_keeps_the_source_side prior.actual.model prior.actual.point
  (EventStep.seed prior.actual.point).frame.sent.length base (laws prior.actual.model)
  ConcreteProductiveSource.request.work ConcreteProductiveSource.request.beats
 have initialSide : prior.actual.point.side=.original :=
  (SourceWindowCache.actual_window_keeps_the_source_side
   (RenewableArchiveSource.window contract ConcreteProductiveSource.ready.actual true true)).trans (by rfl)
 exact kept.trans initialSide

theorem the_refused_attempt_has_the_same_entire_actual_model_and_cursor :
 FreshSigningReplay.physical nativeDonation=
 SourceWindowCache.output recycling false true model origin before := by
 exact SourceWindowCache.renewal_at_the_same_complete_cached_occurrence recycling false true (nativePredecessor).actual
  model origin before the_cached_predecessor_is_the_original_model_and_cursor
  the_cached_predecessor_is_the_complete_original_seed predecessor_original

theorem the_refused_attempt_keeps_the_entire_actual_seed : donated=EventStep.seed donatedPoint :=
 SourceWindowCache.after_is_the_entire_actual_endpoint model.source.code recycling origin before false true
  the_cached_predecessor_is_the_complete_original_seed predecessor_original

theorem the_paid_feed_window_has_the_same_entire_actual_model_and_cursor :
 FreshSigningReplay.physical nativeSupply=
 SourceWindowCache.output feeding true true
  (SourceWindowCache.modelAfter recycling false true model origin before) donatedPoint donated := by
 have original : donatedPoint.side=.original := by
  exact (SourceWindowCache.cached_point_keeps_the_source_side model.source.code recycling origin before false true).trans predecessor_original
 exact SourceWindowCache.renewal_at_the_same_complete_cached_occurrence feeding true true nativeDonation
  (SourceWindowCache.modelAfter recycling false true model origin before) donatedPoint donated
  the_refused_attempt_has_the_same_entire_actual_model_and_cursor
  the_refused_attempt_keeps_the_entire_actual_seed original

theorem the_paid_feed_window_keeps_the_entire_actual_seed : supplied=EventStep.seed suppliedPoint := by
 have original : donatedPoint.side=.original := by
  exact (SourceWindowCache.cached_point_keeps_the_source_side model.source.code recycling origin before false true).trans predecessor_original
 exact SourceWindowCache.after_is_the_entire_actual_endpoint _ feeding donatedPoint donated true true
  the_refused_attempt_keeps_the_entire_actual_seed original

theorem the_actual_two_window_endpoint_is_the_generated_full_current :
 (EventStep.seed (nativeSupply).point).current=supplied.current := by
 have face := congrArg (fun endpoint : FreshSigningReplay.Physical
  (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good) (Port := Delegation.Funded.Port)
  (Technology := Bool) (Instrument := Unit) => (EventStep.seed endpoint.2).current)
  the_paid_feed_window_has_the_same_entire_actual_model_and_cursor
 exact face.trans (congrArg (fun state => state.current) the_paid_feed_window_keeps_the_entire_actual_seed).symm

theorem the_actual_two_windows_generate_real_worker_fuel_and_paid_time :
 (EventStep.seed (nativeSupply).point).current.stock 1 .feedstock=2 ∧
 (EventStep.seed (nativeSupply).point).current.stock 2 .energy=3 ∧
 (EventStep.seed (nativeSupply).point).current.stock 2 .labor=3 := by
 rw [the_actual_two_window_endpoint_is_the_generated_full_current]
 exact ⟨the_two_actual_windows_replenish_from_the_original_provider.1,
  the_two_actual_windows_replenish_from_the_original_provider.2.1,
  the_two_actual_windows_replenish_from_the_original_provider.2.2.1⟩

theorem the_actual_predecessor_is_the_generated_full_current :
 (EventStep.seed (nativePredecessor).actual.point).current=before.current := by
 have face := congrArg (fun endpoint : FreshSigningReplay.Physical
  (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good) (Port := Delegation.Funded.Port)
  (Technology := Bool) (Instrument := Unit) => (EventStep.seed endpoint.2).current)
  the_cached_predecessor_is_the_original_model_and_cursor
 exact face.trans (congrArg (fun state => state.current) the_cached_predecessor_is_the_complete_original_seed).symm

theorem the_actual_two_attempts_keep_all_claims_and_charge_four_ticks :
 (∀ instrument debtor creditor,
  (EventStep.seed (nativeSupply).point).current.claims instrument debtor creditor=
  (EventStep.seed (nativePredecessor).actual.point).current.claims instrument debtor creditor) ∧
 (EventStep.seed (nativeSupply).point).current.clock=
  (EventStep.seed (nativePredecessor).actual.point).current.clock+4 := by
 rw [the_actual_two_window_endpoint_is_the_generated_full_current,
  the_actual_predecessor_is_the_generated_full_current]
 exact the_two_attempts_keep_all_claims_and_charge_the_actual_clock

theorem the_first_actual_window_is_unpaid :
 PaidInvocationSource.admitted (nativePredecessor).actual.model.source.code recycling
  (nativePredecessor).actual.point false true=false :=
 (SourceWindowCache.admission_at_the_same_complete_cached_occurrence recycling false true
  (nativePredecessor).actual model origin before the_cached_predecessor_is_the_original_model_and_cursor
  the_cached_predecessor_is_the_complete_original_seed predecessor_original).trans
  the_unpaid_supplier_attempt_cannot_mint_a_window

theorem the_second_actual_window_is_paid :
 PaidInvocationSource.admitted (nativeDonation).model.source.code feeding (nativeDonation).point true true=true :=
 (SourceWindowCache.admission_at_the_same_complete_cached_occurrence feeding true true nativeDonation
  (SourceWindowCache.modelAfter recycling false true model origin before) donatedPoint donated
  the_refused_attempt_has_the_same_entire_actual_model_and_cursor
  the_refused_attempt_keeps_the_entire_actual_seed
  ((SourceWindowCache.cached_point_keeps_the_source_side model.source.code recycling origin before false true).trans
   predecessor_original)).trans the_real_waste_payment_and_feed_delivery_generate_a_window

theorem the_two_actual_windows_have_distinct_success_and_refusal :
 (RenewableArchiveSource.window recycling (nativePredecessor).actual false true).status=.blocked .unpaid ∧
 (RenewableArchiveSource.window feeding nativeDonation true true).status=.opened :=
 ⟨(RenewableArchiveSource.refused_payment_keeps_the_actual_attempt_endpoint_without_credit
   recycling (nativePredecessor).actual false true the_first_actual_window_is_unpaid).1,
  (RenewableArchiveSource.admitted_payment_generates_the_exact_next_window
   feeding nativeDonation true true the_second_actual_window_is_paid).1⟩

theorem the_actual_two_attempts_keep_original_history_and_own_next :
 start.actual.archive <+: actualSupply.actual.archive ∧ start.actual.windows <+: actualSupply.actual.windows ∧
 start.rows <+: actualSupply.rows ∧
 ArchivedDeliveryConsumer.NativeContinuation actualSupply.actual.model actualSupply.actual.point := by
 have first := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows recycling start [.renew false true]
 have second := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows feeding actualDonation [.renew true true]
 exact ⟨first.1.trans second.1,first.2.1.trans second.2.1,first.2.2.trans second.2.2,
  JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next actualSupply⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredWindowConsumer
