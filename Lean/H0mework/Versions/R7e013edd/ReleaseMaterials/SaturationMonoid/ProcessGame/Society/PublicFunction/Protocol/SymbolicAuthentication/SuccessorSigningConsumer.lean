import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningMaterial
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueConsumer
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open SuccessorSigningMaterial
abbrev point := RenewedDispatchTrace.point
abbrev model := freshModelAt point
abbrev start := freshStartAt point
abbrev vocabulary := freshVocabulary point
abbrev law := freshLaw point
abbrev scope := freshScope point
abbrev zero := zeroAt point
abbrev one := oneAt point
abbrev commands := (generatedAt point).2
abbrev material := (generatedAt point).1
abbrev rows := material.2.2
def actual := LocalCommandRun.run model start commands
abbrev final := actual.current model start
abbrev observed (receiver : Fin model.source.code.sites) := HeaderQuorum.observed start vocabulary law actual.stages receiver
abbrev produce (receiver : Fin model.source.code.sites) := HeaderQuorum.produce start vocabulary law actual.stages receiver scope 2
attribute [local irreducible] CachedWorkDispatch.wires CachedWorkDispatch.run CachedWorkDispatch.affected HeaderReception.run ActorStageEnvelope.affected SuccessorSigningSource.Material.generate PaidOriginQueueMemo.wire PaidOriginQueueMemo.wireAt PaidOriginHeader.produce PaidOriginHeader.observed StageBudget.verify HeaderTransport.verify

theorem generated_rows_are_the_actual_new_execution : rows = StageTrace.records start actual.stages := by
 simpa only [rows,material,actual,commands,generatedAt] using
  (SuccessorSigningSource.Material.generated_rows_are_the_actual_source_records model start (freshBeforeAt point)
   fresh_seed_is_the_same_actual_state (OriginQueue.baseline (RenewedDispatchSource.start point))
   vocabulary law (ProductiveMandateSource.body.take 4) 24)

theorem generated_endpoint_is_the_actual_new_execution : material.1 = final := by
 simpa only [material,final,actual,commands,generatedAt] using
  (SuccessorSigningSource.Material.generated_cursor_is_the_actual_source_endpoint model start (freshBeforeAt point)
   fresh_seed_is_the_same_actual_state (OriginQueue.baseline (RenewedDispatchSource.start point))
   vocabulary law (ProductiveMandateSource.body.take 4) 24)

theorem actual_new_reception_is_the_incremental_reception (receiver : Fin model.source.code.sites) :
 observed receiver = CachedWorkDispatch.run vocabulary law rows receiver rows.length := by
 have count : actual.stages.length = rows.length :=
  (StageTrace.record_count start actual.stages).symm.trans
   (congrArg List.length generated_rows_are_the_actual_new_execution.symm)
 exact (CachedWorkDispatch.run_eq vocabulary law start actual.stages receiver actual.stages.length).symm.trans
  (congrArg₂ (fun records count => CachedWorkDispatch.run vocabulary law records receiver count)
   generated_rows_are_the_actual_new_execution.symm count)

theorem actual_new_wires_are_the_original_generated_wires :
 HeaderTransport.wires vocabulary start actual.stages = CachedWorkDispatch.wires vocabulary rows :=
 (CachedWorkDispatch.wires_eq vocabulary start actual.stages).symm.trans
  (congrArg (CachedWorkDispatch.wires vocabulary) generated_rows_are_the_actual_new_execution.symm)

theorem both_receivers_obtain_the_new_identity_quorum :
 (observed zero).receipts.length=2 ∧ (observed one).receipts.length=2 ∧
 ActorQuorum.readout (observed zero) scope 2=.decided true ∧
 ActorQuorum.readout (observed one) scope 2=.decided true := by
 have checked := generated_new_signing_and_two_receivers_pass_the_same_source_check
 have facts : rows.length=24 ∧ (freshBeforeAt point).remaining=46 ∧ material.2.1.remaining=22 ∧
  material.2.1.frame.sent.length=12 ∧ (CachedWorkDispatch.wires vocabulary rows).length=4 ∧
  scope.phase=90 ∧
  (CachedWorkDispatch.run vocabulary law rows zero rows.length).receipts.length=2 ∧
  (CachedWorkDispatch.run vocabulary law rows one rows.length).receipts.length=2 ∧
  ActorQuorum.readout (CachedWorkDispatch.run vocabulary law rows zero rows.length) scope 2=.decided true ∧
  ActorQuorum.readout (CachedWorkDispatch.run vocabulary law rows one rows.length) scope 2=.decided true := by
  simpa only [successCheck,decide_eq_true_eq] using checked
 rw [actual_new_reception_is_the_incremental_reception,actual_new_reception_is_the_incremental_reception]
 exact facts.2.2.2.2.2.2

private theorem checked_budget (p : Cursor DispatchWindowSource.code) (checked : controlCheck p=true) :
 (CachedWorkDispatch.affected (freshVocabulary p) (freshStartAt p) (generatedAt p).1.2.2 (freshScope p)).card=0 ∧
 (ActorEnvelope.roster (freshStartAt p).source).card=2 := by
 unfold controlCheck at checked
 have facts := of_decide_eq_true checked
 exact ⟨facts.1,facts.2.1⟩

theorem actual_new_identity_budget_is_generated_by_the_original_execution :
 ActorStageEnvelope.budget start vocabulary actual.stages scope=0 ∧
 (ActorEnvelope.roster start.source).card=2 := by
 have computed := checked_budget point retained_attempts_and_all_new_wire_refusals_pass_the_same_source_check
 have affected := (CachedWorkDispatch.affected_eq vocabulary start actual.stages scope).symm.trans
  (congrArg (fun records => CachedWorkDispatch.affected vocabulary start records scope)
   generated_rows_are_the_actual_new_execution.symm)
 exact ⟨(congrArg Finset.card affected).trans computed.1,computed.2⟩

private theorem source_decides_from_its_actual_budget
 (bound : Native.Authority.Bound (Party := Bool) (Good := Bool) (Port := ProductiveMandateSource.Port)
  (Technology := Bool) (Instrument := Unit))
 (origin : Cursor bound.source.code) (vocab : OwnedAttestation.Vocabulary (Party := Bool) (Good := Bool)
  (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit))
 (deliveryLaw : StageReception.Law bound.source.code) (stages : List (EventHistory.Stage (code := bound.source.code)))
 (receiver : Fin bound.source.code.sites) (voteScope : Scope)
 (roster : (ActorEnvelope.roster origin.source).card=2)
 (affected : ActorStageEnvelope.budget origin vocab stages voteScope=0)
 (readout : ActorQuorum.readout (HeaderQuorum.observed origin vocab deliveryLaw stages receiver) voteScope 2=.decided true) :
 HeaderQuorum.produce origin vocab deliveryLaw stages receiver voteScope 2=.decided true := by
 unfold HeaderQuorum.produce
 rw [roster,affected]
 simp only [Nat.reduceAdd,Nat.reduceLT,not_true_eq_false,if_false,readout]

theorem the_actual_new_source_generates_both_safe_decisions : produce zero=.decided true ∧ produce one=.decided true :=
 ⟨source_decides_from_its_actual_budget model start vocabulary law actual.stages zero scope
   actual_new_identity_budget_is_generated_by_the_original_execution.2
   actual_new_identity_budget_is_generated_by_the_original_execution.1
   both_receivers_obtain_the_new_identity_quorum.2.2.1,
  source_decides_from_its_actual_budget model start vocabulary law actual.stages one scope
   actual_new_identity_budget_is_generated_by_the_original_execution.2
   actual_new_identity_budget_is_generated_by_the_original_execution.1
   both_receivers_obtain_the_new_identity_quorum.2.2.2⟩

private theorem checked_attempt_history (p : Cursor DispatchWindowSource.code) (checked : controlCheck p=true) :
 ((generatedAt p).1.2.2).all (fun row => (List.range 8).all (fun serial => !HeaderReception.delivered row serial))=true := by
 unfold controlCheck at checked
 exact (of_decide_eq_true checked).2.2.2.2.1

theorem the_new_execution_never_replays_an_original_packet
 (row : StageTrace.Record (code := model.source.code))
 (inside : row ∈ StageTrace.records start actual.stages) (serial : Nat) (old : serial<8) :
 HeaderReception.delivered row serial=false := by
 have checked := checked_attempt_history point retained_attempts_and_all_new_wire_refusals_pass_the_same_source_check
 rw [← generated_rows_are_the_actual_new_execution] at inside
 have here := List.all_eq_true.mp (List.all_eq_true.mp checked row inside) serial (List.mem_range.mpr old)
 cases delivered : HeaderReception.delivered row serial with
 | false => rfl
 | true => simp only [delivered,Bool.not_true,Bool.false_eq_true] at here

private def WireChecks (p : Cursor DispatchWindowSource.code)
 (wire : HeaderTransport.Wire (code := (freshModelAt p).source.code))
 (row : StageTrace.Record (code := (freshModelAt p).source.code)) : Prop :=
 let vocab := freshVocabulary p
 let law := freshLaw p
 let rows := (generatedAt p).1.2.2
 CachedWorkDispatch.check vocab law rows wire.recipient row [] wire=.accepted wire ∧
 CachedWorkDispatch.check vocab law rows wire.recipient row [(wire.ballot.cut,wire.ballot.position)] wire=.rejected .duplicate ∧
 CachedWorkDispatch.check vocab ⟨law.scope,0⟩ rows wire.recipient row [] wire=.rejected .late ∧
 CachedWorkDispatch.check vocab ⟨fun _ _ => RenewedDispatchSource.scope p,1⟩ rows wire.recipient row [] wire=.rejected .staleScope ∧
 CachedWorkDispatch.check vocab law [] wire.recipient row [] wire=.rejected .unauthenticated ∧
 CachedWorkDispatch.check vocab law rows wire.recipient row []
  {wire with ballot := {wire.ballot with actor := !wire.ballot.actor}}=.rejected .unauthenticated

private theorem checked_wire_deliveries (p : Cursor DispatchWindowSource.code) (checked : controlCheck p=true) :
 ∀ wire ∈ CachedWorkDispatch.wires (freshVocabulary p) (generatedAt p).1.2.2,
 ∃ row ∈ (generatedAt p).1.2.2, WireChecks p wire row := by
 unfold controlCheck at checked
 have every := (of_decide_eq_true checked).2.2.2.2.2
 intro wire member
 obtain ⟨row,inside,verified⟩ := List.any_eq_true.mp (List.all_eq_true.mp every wire member)
 refine ⟨row,inside,?_⟩
 unfold WireChecks
 exact of_decide_eq_true verified

private def resetData (p : Cursor DispatchWindowSource.code) :=
 SuccessorSigningSource.Material.generate (freshModelAt p) (freshBeforeAt p).past.length
  (freshVocabulary p) (freshLaw p) (ProductiveMandateSource.body.take 4) 2
  (freshStartAt p,freshBeforeAt p,[])

private theorem checked_reset (p : Cursor DispatchWindowSource.code) (checked : controlCheck p=true) :
 (resetData p).1.2.2.any (fun row => HeaderReception.delivered row 0)=true := by
 unfold controlCheck at checked
 exact (of_decide_eq_true checked).2.2.2.1

theorem erasing_the_original_queue_baseline_replays_a_real_old_packet :
 ∃ row ∈ StageTrace.records start (LocalCommandRun.run model start (resetData point).2).stages,
 HeaderReception.delivered row 0=true := by
 have checked := checked_reset point retained_attempts_and_all_new_wire_refusals_pass_the_same_source_check
 obtain ⟨row,member,delivered⟩ := List.any_eq_true.mp checked
 have same := SuccessorSigningSource.Material.generated_rows_are_the_actual_source_records model start (freshBeforeAt point)
  fresh_seed_is_the_same_actual_state (freshBeforeAt point).past.length
  vocabulary law (ProductiveMandateSource.body.take 4) 2
 have exactRows : (resetData point).1.2.2 = StageTrace.records start (LocalCommandRun.run model start (resetData point).2).stages := by
  simpa only [resetData] using same
 exact ⟨row,Eq.mp (congrArg (fun records : List (StageTrace.Record (code := model.source.code)) => row ∈ records) exactRows) member,delivered⟩

theorem actual_new_check_is_the_computed_source_check
 (deliveryLaw : StageReception.Law model.source.code) (receiver : Fin model.source.code.sites)
 (row : StageTrace.Record (code := model.source.code)) (seen : List (Nat×Nat))
 (wire : HeaderTransport.Wire (code := model.source.code)) :
 HeaderReception.check vocabulary deliveryLaw start actual.stages receiver row seen wire =
 CachedWorkDispatch.check vocabulary deliveryLaw rows receiver row seen wire :=
 (CachedWorkDispatch.check_eq vocabulary deliveryLaw start actual.stages receiver row seen wire).symm.trans
  (congrArg (fun records => CachedWorkDispatch.check vocabulary deliveryLaw records receiver row seen wire)
   generated_rows_are_the_actual_new_execution.symm)

theorem every_new_wire_has_a_real_delivery_with_separate_replay_and_forgery_refusals
 (wire : HeaderTransport.Wire (code := model.source.code))
 (inside : wire ∈ HeaderTransport.wires vocabulary start actual.stages) :
 ∃ row ∈ StageTrace.records start actual.stages,
 HeaderReception.check vocabulary law start actual.stages wire.recipient row [] wire=.accepted wire ∧
 HeaderReception.check vocabulary law start actual.stages wire.recipient row [(wire.ballot.cut,wire.ballot.position)] wire=.rejected .duplicate ∧
 HeaderReception.check vocabulary ⟨law.scope,0⟩ start actual.stages wire.recipient row [] wire=.rejected .late ∧
 HeaderReception.check vocabulary ⟨fun _ _ => RenewedDispatchSource.scope point,1⟩ start actual.stages wire.recipient row [] wire=.rejected .staleScope ∧
 HeaderReception.check vocabulary law start [] wire.recipient row [] wire=.rejected .unauthenticated ∧
 HeaderReception.check vocabulary law start actual.stages wire.recipient row []
  {wire with ballot := {wire.ballot with actor := !wire.ballot.actor}}=.rejected .unauthenticated := by
 rw [actual_new_wires_are_the_original_generated_wires] at inside
 obtain ⟨row,member,checked⟩ := checked_wire_deliveries point
  retained_attempts_and_all_new_wire_refusals_pass_the_same_source_check wire inside
 refine ⟨row,by rw [← generated_rows_are_the_actual_new_execution];exact member,?_⟩
 simp only [actual_new_check_is_the_computed_source_check]
 have deleted := (CachedWorkDispatch.check_eq vocabulary law start [] wire.recipient row [] wire).symm
 have nilRecords : StageTrace.records start []=[] := rfl
 rw [nilRecords] at deleted
 rw [deleted]
 exact checked

theorem every_new_authenticated_packet_has_actual_post_birth_signing
 (wire : HeaderTransport.Wire (code := model.source.code))
 (authenticated : HeaderTransport.verify vocabulary start actual.stages wire=true) :
 (recoveredAt point).cut ≤ wire.ballot.cut ∧ wire.ballot.scope.phase=(recoveredAt point).cut := by
 obtain ⟨_,_,_,_,_,_,_,inside,_⟩ := HeaderTransport.authenticated_wire_has_actual_send_and_paid_ballot
  vocabulary start actual.stages wire authenticated
 exact SuccessorSigningSource.every_new_ballot_is_born_after_the_actual_successor
  (parentAt point) (recoveredAt point) (RenewedDispatchSource.vocabulary point) actual.stages wire.ballot inside

theorem the_new_phase_is_born_at_the_actual_recovery_endpoint : (recoveredAt point).cut=90 :=
 (congrArg (fun cursor : Cursor PaidOriginQueueMemo.code => cursor.cut) recovered_is_the_same_actual_endpoint).symm.trans
  PaidOriginQueueChecks.the_original_queue_generates_two_actual_steps_and_delivers_only_the_pending_packet.2.2.2.2.1

theorem an_older_ballot_cannot_enter_the_actual_new_issuing_ledger
 (ballot : StageBudget.Ballot (code := model.source.code)) (old : ballot.cut<90) :
 ballot ∉ StageBudget.ledger vocabulary start actual.stages := by
 intro member
 have born := SuccessorSigningSource.every_new_ballot_is_born_after_the_actual_successor
  (parentAt point) (recoveredAt point) (RenewedDispatchSource.vocabulary point) actual.stages ballot member
 rw [the_new_phase_is_born_at_the_actual_recovery_endpoint] at born
 omega

theorem the_original_decision_and_new_phase_decisions_coexist_without_equivocation :
 PaidOriginQueueConsumer.produce=.decided true ∧ produce zero=.decided true ∧ produce one=.decided true ∧
 ActorStageEnvelope.budget start vocabulary actual.stages scope=0 ∧
 scope.phase ≠ PaidOriginQueueConsumer.scope.phase := by
 have oldPhase : PaidOriginQueueConsumer.scope.phase=64 := by
  change (PaidInvocationSource.paid DispatchWindowSource.old DispatchWindowSource.contract DispatchWindowSource.saved true true).cut=64
  exact DispatchWindowChecks.the_original_successor_pays_the_provider_and_obtains_actual_acceptance.2.2.2.2.2.1
 have freshPhase : scope.phase=90 := the_new_phase_is_born_at_the_actual_recovery_endpoint
 exact ⟨PaidOriginQueueConsumer.the_generated_recovery_restores_the_original_identity_quorum.2.2.2.2,
  the_actual_new_source_generates_both_safe_decisions.1,the_actual_new_source_generates_both_safe_decisions.2,
  actual_new_identity_budget_is_generated_by_the_original_execution.1,by omega⟩

private theorem an_empty_new_segment_cannot_decide
 (bound : Native.Authority.Bound (Party := Bool) (Good := Bool) (Port := ProductiveMandateSource.Port)
  (Technology := Bool) (Instrument := Unit))
 (origin : Cursor bound.source.code) (vocab : OwnedAttestation.Vocabulary (Party := Bool) (Good := Bool)
  (Port := ProductiveMandateSource.Port) (Technology := Bool) (Instrument := Unit))
 (deliveryLaw : StageReception.Law bound.source.code) (receiver : Fin bound.source.code.sites) (voteScope : Scope)
 (roster : (ActorEnvelope.roster origin.source).card=2) :
 HeaderQuorum.produce origin vocab deliveryLaw [] receiver voteScope 2=.blocked .missingQuorum := by
 simp [HeaderQuorum.produce,roster,ActorStageEnvelope.budget,ActorStageEnvelope.affected,
  ActorStageEnvelope.choices,StageBudget.liveRecords,StageTrace.records,HeaderQuorum.observed,
  HeaderReception.run,ActorQuorum.readout,ActorQuorum.support,StageQuorum.support]

theorem the_retained_old_decision_cannot_decide_the_unexecuted_new_segment :
 HeaderQuorum.produce start vocabulary law [] zero scope 2=.blocked .missingQuorum :=
 an_empty_new_segment_cannot_decide model start vocabulary law zero scope
  actual_new_identity_budget_is_generated_by_the_original_execution.2

private theorem checked_counts (p : Cursor DispatchWindowSource.code) (checked : successCheck p=true) :
 (freshBeforeAt p).remaining=46 ∧ (generatedAt p).1.2.1.remaining=22 ∧
 (generatedAt p).1.2.2.length=24 ∧ (CachedWorkDispatch.wires (freshVocabulary p) (generatedAt p).1.2.2).length=4 := by
 unfold successCheck at checked
 have facts := of_decide_eq_true checked
 exact ⟨facts.2.1,facts.2.2.1,facts.1,facts.2.2.2.2.1⟩

private theorem execute_cut
 {emitter : Code Bool Bool ProductiveMandateSource.Port (Mandate.State Bool Bool) Unit}
 (origin : Cursor emitter) (stages : List (EventHistory.Stage (code := emitter))) :
 (EventHistory.execute origin stages).cut=origin.cut+stages.length := by
 induction stages generalizing origin with
 | nil => rfl
 | cons stage tail ih =>
  change (EventHistory.execute (origin.after stage.1 stage.2) tail).cut=_
  rw [ih]
  change origin.cut+1+tail.length=origin.cut+(tail.length+1)
  omega

theorem actual_fuel_and_packet_growth_are_paid_by_the_same_retained_endpoint :
 (EventStep.seed start).remaining=46 ∧ (EventStep.seed final).remaining=22 ∧
 actual.stages.length=24 ∧ final.cut=114 ∧ (HeaderTransport.wires vocabulary start actual.stages).length=4 := by
 have computed := checked_counts point generated_new_signing_and_two_receivers_pass_the_same_source_check
 have intrinsic := SuccessorSigningSource.Material.generated_remaining_is_the_same_actual_budget model start (freshBeforeAt point)
  fresh_seed_is_the_same_actual_state (OriginQueue.baseline (RenewedDispatchSource.start point))
  vocabulary law (ProductiveMandateSource.body.take 4) 24
 have dataEq : generatedAt point = SuccessorSigningSource.Material.generate model
  (OriginQueue.baseline (RenewedDispatchSource.start point)) vocabulary law (ProductiveMandateSource.body.take 4) 24
  (start,freshBeforeAt point,[]) := by unfold generatedAt;rfl
 have left := congrArg (fun result : SuccessorSigningSource.Material.Data model × List LocalCommandSource.Input => result.1.2.1.remaining) dataEq
 have right := congrArg (fun result : SuccessorSigningSource.Material.Data model × List LocalCommandSource.Input => (EventStep.seed result.1.1).remaining) dataEq
 have actualRemaining : material.2.1.remaining=(EventStep.seed material.1).remaining :=
  left.trans (intrinsic.trans right.symm)
 have finalRemaining := actualRemaining.trans (congrArg (fun cursor : Cursor model.source.code => (EventStep.seed cursor).remaining) generated_endpoint_is_the_actual_new_execution)
 have count : actual.stages.length=24 :=
  (StageTrace.record_count start actual.stages).symm.trans
   ((congrArg List.length generated_rows_are_the_actual_new_execution.symm).trans computed.2.2.1)
 have firstClock : start.cut=90 := the_new_phase_is_born_at_the_actual_recovery_endpoint
 have lastClock : final.cut=114 := by
  change (EventHistory.execute start actual.stages).cut=114
  rw [execute_cut,firstClock,count]
 exact ⟨(congrArg (fun state : Feedback.State model.source.code => state.remaining) fresh_seed_is_the_same_actual_state).symm.trans computed.1,
  finalRemaining.symm.trans computed.2.1,
  count,lastClock,(congrArg List.length actual_new_wires_are_the_original_generated_wires).trans computed.2.2.2⟩

theorem the_same_original_financial_prefix_is_retained (ordinal : Nat)
 (bounded : ordinal ≤ EventStep.boundary (recoveredAt point)) :
 Native.Coupling.Match (parentAt point).source.code (recoveredAt point).source.input final.source.input
  (Financial.accountAt (recoveredAt point).source.input ordinal) (Financial.accountAt final.source.input ordinal) :=
 SuccessorSigningSource.every_future_run_preserves_the_original_financial_prefix
  (parentAt point) (recoveredAt point) recovered_is_original actual.stages ordinal bounded

private theorem native_continuation
 (bound : Native.Authority.Bound (Party := Bool) (Good := Bool) (Port := ProductiveMandateSource.Port)
  (Technology := Bool) (Instrument := Unit)) (endpoint : Cursor bound.source.code) :
 PaidOriginQueueConsumer.NativeContinuation bound endpoint := by
 unfold PaidOriginQueueConsumer.NativeContinuation
 exact (WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next bound endpoint).2.2.2

theorem the_actual_new_execution_keeps_its_whole_ledger_and_own_generated_next :
 PaidOriginQueueConsumer.NativeContinuation model final := native_continuation model final

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningConsumer
