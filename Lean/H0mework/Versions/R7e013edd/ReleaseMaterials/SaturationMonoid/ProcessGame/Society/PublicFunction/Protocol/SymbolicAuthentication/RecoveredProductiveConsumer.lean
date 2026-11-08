import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredProductiveSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredProductiveConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (bound base laws contract)
open RecoveredProductiveSource
open ProductiveSigningSource (current total)

private theorem donated_history (state : State) (control : Control) :
 state.actual.archive <+: (donated state control).actual.archive ∧
 state.actual.windows <+: (donated state control).actual.windows ∧ state.rows <+: (donated state control).rows := by
 unfold donated
 split
 · exact SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows recycling state [.renew false control.recycle]
 · exact ⟨List.prefix_refl _,List.prefix_refl _,List.prefix_refl _⟩

theorem every_actual_attempt_retains_all_prior_history_and_its_own_next (state : State) (control : Control) :
 state.actual.archive <+: (RecoveredProductiveSource.step state control).actual.archive ∧
 state.actual.windows <+: (RecoveredProductiveSource.step state control).actual.windows ∧ state.rows <+: (RecoveredProductiveSource.step state control).rows ∧
 ArchivedDeliveryConsumer.NativeContinuation (RecoveredProductiveSource.step state control).actual.model (RecoveredProductiveSource.step state control).actual.point := by
 have suppliedHistory : state.actual.archive <+: (supplied state control).actual.archive ∧
  state.actual.windows <+: (supplied state control).actual.windows ∧ state.rows <+: (supplied state control).rows := by
  unfold supplied
  split
  · have donor := donated_history state control
    have feed := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows feeding
     (donated state control) [.renew control.payFeed control.deliverFeed]
    exact ⟨donor.1.trans feed.1,donor.2.1.trans feed.2.1,donor.2.2.trans feed.2.2⟩
  · exact ⟨List.prefix_refl _,List.prefix_refl _,List.prefix_refl _⟩
 have prefixHistory := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows contract
  (supplied state control) [.execute [.command 2,.idle]]
 have prepared : SourceRepairSearch.execute contract (supplied state control) [.execute [.command 2,.idle]]=
  ready state control := rfl
 rw [prepared] at prefixHistory
 have signing := FreshSigningSource.every_paid_cycle_retains_all_original_archives_windows_and_rows contract base laws
  (ready state control) (RecoveredProductiveSource.request control)
 have actual : RecoveredProductiveSource.step state control=
  FreshSigningSource.cycle contract base laws (ready state control) (RecoveredProductiveSource.request control) := rfl
 rw [actual]
 exact ⟨(suppliedHistory.1.trans prefixHistory.1).trans signing.1,
  (suppliedHistory.2.1.trans prefixHistory.2.1).trans signing.2.1,
  (suppliedHistory.2.2.trans prefixHistory.2.2).trans signing.2.2,
  JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next
   (FreshSigningSource.cycle contract base laws (ready state control) (RecoveredProductiveSource.request control))⟩

theorem every_dynamic_round_keeps_original_history_and_its_own_next
 (state : State) (control : Nat → State → Control) (count : Nat) :
 state.actual.archive <+: (RecoveredProductiveSource.run state control count).actual.archive ∧
 state.actual.windows <+: (RecoveredProductiveSource.run state control count).actual.windows ∧ state.rows <+: (RecoveredProductiveSource.run state control count).rows ∧
 ArchivedDeliveryConsumer.NativeContinuation (RecoveredProductiveSource.run state control count).actual.model (RecoveredProductiveSource.run state control count).actual.point := by
 induction count with
 | zero => exact ⟨List.prefix_refl _,List.prefix_refl _,List.prefix_refl _,
    JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next state⟩
 | succ count ih =>
  have next := every_actual_attempt_retains_all_prior_history_and_its_own_next (RecoveredProductiveSource.run state control count)
   (control count (RecoveredProductiveSource.run state control count))
  have actual : RecoveredProductiveSource.run state control (count+1)=
   RecoveredProductiveSource.step (RecoveredProductiveSource.run state control count)
    (control count (RecoveredProductiveSource.run state control count)) := rfl
  rw [actual]
  exact ⟨ih.1.trans next.1,ih.2.1.trans next.2.1,ih.2.2.1.trans next.2.2.1,next.2.2.2⟩

theorem the_actual_net_ledger_accounts_for_success_and_failure
 (state : State) (control : Nat → State → Control) (count : Nat) :
 total (RecoveredProductiveSource.run state control count) .service=total state .service+accumulated state control count := by
 induction count with
 | zero => change total state .service=total state .service+0;ring
 | succ count ih =>
  change total (RecoveredProductiveSource.step (RecoveredProductiveSource.run state control count) (control count (RecoveredProductiveSource.run state control count))) .service=
   total state .service+(accumulated state control count+
    (total (RecoveredProductiveSource.step (RecoveredProductiveSource.run state control count) (control count (RecoveredProductiveSource.run state control count))) .service-
     total (RecoveredProductiveSource.run state control count) .service))
  linarith

private theorem cached_current_is_the_actual_current
 {root : RenewableCodeLineage.Emitter (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit)}
 (before : JointReceptionSource.State root) (request : FreshSigningSource.Request (Party := Delegation.Funded.Party)
 (Good := Repayment.Recovery.Good) (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit))
 (zero : request.depth=0) :
 (SourceDynamicCache.Fresh.generated base laws before request).before.current=
 current (FreshSigningSource.next contract base laws before request) := by
 have same := SourceDynamicCache.Fresh.zero_repair_keeps_the_entire_original_model_and_cached_cursor
  base laws before request contract zero
 have currentFace := congrArg (fun endpoint : Sigma fun model : Native.Authority.Bound
  (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good) (Port := Delegation.Funded.Port)
  (Technology := Bool) (Instrument := Unit) => Cursor model.source.code => (EventStep.seed endpoint.2).current) same
 have cache := (SourceDynamicCache.the_executable_stream_has_the_same_complete_source_execution
  before.actual.model before.actual.point (EventStep.seed before.actual.point).frame.sent.length
  base (laws before.actual.model) request.work request.beats).2.1
 exact (congrArg (fun state => state.current) cache).trans currentFace.symm

theorem the_generated_snapshot_is_the_actual_authenticated_predecessor : material=current start := by
 have same : FreshSigningSource.next contract base laws prior ConcreteProductiveSource.request=start := by
  unfold start ConcreteProductiveSource.endpoint FreshSigningSource.cycle
  rfl
 exact (cached_current_is_the_actual_current prior ConcreteProductiveSource.request rfl).trans
  (congrArg current same)

private theorem inherited_law (state : State) : state.actual.model.source.code.law=bound.source.code.law := by
 rw [state.lineage.same]
 rfl

theorem the_original_refueling_word_is_legal_at_the_actual_authenticated_predecessor :
 ∀ item∈start.actual.model.source.code.law.rawItems (current start) refuelingWord,
  start.actual.model.source.code.law.Valid item.before item.request := by
 have offered := the_generated_current_offers_the_original_refueling_word
 have checked : ∀ item∈bound.source.code.law.rawItems material refuelingWord,
  bound.source.code.law.Valid item.before item.request := by
  unfold refuelingOffer at offered
  split at offered
  · rename_i accepted
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).2
  · contradiction
 rw [inherited_law,← the_generated_snapshot_is_the_actual_authenticated_predecessor]
 exact checked

theorem the_original_law_generates_provider_fuel_from_the_actual_predecessor :
 (start.actual.model.source.code.law.next (current start) refuelingWord).stock 1 .feedstock=2 ∧
 (start.actual.model.source.code.law.next (current start) refuelingWord).stock 2 .energy=3 ∧
 (start.actual.model.source.code.law.next (current start) refuelingWord).stock 2 .labor=3 := by
 rw [inherited_law,← the_generated_snapshot_is_the_actual_authenticated_predecessor]
 exact the_refueling_word_replenishes_the_worker_from_real_provider_inputs

private theorem recycling_preserves_claims (before : RecycledQuorumMaterial.Current) :
 (bound.source.code.law.step before RecycledQuorumMaterial.recycle).claims=before.claims := by
 unfold RawLaw.step
 split <;> rfl

private theorem payment_preserves_claims (before : RecycledQuorumMaterial.Current) :
 (bound.source.code.law.step before RecycledQuorumMaterial.waste).claims=before.claims := by
 unfold RawLaw.step
 split <;> rfl

private theorem feeding_preserves_claims (before : RecycledQuorumMaterial.Current) :
 (bound.source.code.law.step before RecycledQuorumMaterial.feed).claims=before.claims := by
 unfold RawLaw.step
 split <;> rfl

private theorem refueling_preserves_claims (before : RecycledQuorumMaterial.Current) :
 (bound.source.code.law.next before refuelingWord).claims=before.claims := by
 change (bound.source.code.law.step
  (bound.source.code.law.step (bound.source.code.law.step before RecycledQuorumMaterial.recycle)
   RecycledQuorumMaterial.waste) RecycledQuorumMaterial.feed).claims=before.claims
 rw [feeding_preserves_claims,payment_preserves_claims,recycling_preserves_claims]

theorem the_original_refueling_word_keeps_every_original_financial_position :
 (start.actual.model.source.code.law.next (current start) refuelingWord).claims=(current start).claims := by
 rw [inherited_law]
 exact refueling_preserves_claims _

theorem productive_status_is_exactly_the_original_actual_guard
 (state : State) (control : Control) :
 RecoveredProductiveSource.status state control=.productive ↔
 ProductiveSigningSource.accepts contract base laws (RecoveredProductiveSource.request control) .service 3 1 state
  (RecoveredProductiveSource.candidate state control)=true := by
 unfold RecoveredProductiveSource.status
 split
 · rename_i accepted
   exact ⟨fun _ => accepted,fun _ => rfl⟩
 · rename_i refused
   constructor
   · intro impossible
     cases impossible
   · intro accepted
     exact False.elim (refused accepted)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredProductiveConsumer
