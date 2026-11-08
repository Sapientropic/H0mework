import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningReception

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {root : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (laws : (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) → StageReception.Law model.source.code)
 (before : JointReceptionSource.State root)
 (request : FreshSigningSource.Request (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

abbrev context := FreshSigningSource.origin base laws before request
abbrev vocabulary := (context base laws before request).vocabulary before.actual.model base
abbrev reception := (context base laws before request).law before.actual.model (laws before.actual.model)
abbrev issued := (context base laws before request).stages
abbrev start := (context base laws before request).origin
abbrev report := FreshSigningSource.result contract base laws before request
abbrev currentScope := FreshSigningReplay.currentScope before request.scope

private theorem report_replay :
 SourceRepairSearch.execute contract
  (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request))
  (report contract base laws before request).commands=(report contract base laws before request).final :=
 (SourceRepairRun.every_report_replays_only_its_selected_actual_source_commands contract
  (vocabulary base laws before request) (reception base laws before request)
  (start base laws before request) (issued base laws before request) (currentScope before request) request.value request.depth
  (SourceRepairSearch.debt (vocabulary base laws before request) (reception base laws before request)
    (start base laws before request) (issued base laws before request) (currentScope before request) request.value
    (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request))+1)
  (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request))).1

theorem the_global_endpoint_contains_the_entire_old_prefix_and_exact_fresh_metadata :
 (FreshSigningSource.next contract base laws before request).actual.archive=
  before.actual.archive++(report contract base laws before request).final.actual.archive ∧
 (FreshSigningSource.next contract base laws before request).actual.windows=
  before.actual.windows++(report contract base laws before request).final.actual.windows := by
 have kept := FreshSigningReplay.replay_retains_the_complete_original_metadata_prefixes contract
  (FreshSigningReplay.globalStart contract before (FreshSigningSource.inputs base laws before request))
  (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request))
  (FreshSigningReplay.both_starts_are_the_same_actual_model_and_cursor contract before (FreshSigningSource.inputs base laws before request))
  before.actual.archive before.actual.windows rfl (by exact (List.append_nil _).symm) (report contract base laws before request).commands
 rw [report_replay] at kept
 exact kept

theorem every_new_global_receipt_restores_its_actual_new_paid_signature_and_phase
 (recipient : Fin before.actual.model.source.code.sites)
 (receipt : HeaderReception.Receipt (code := before.actual.model.source.code))
 (inside : receipt∈(FreshSigningReception.observed contract base laws before request recipient).receipts) :
 receipt.wire.ballot∈StageBudget.ledger (vocabulary base laws before request)
  (start base laws before request) (issued base laws before request) ∧
 before.actual.point.cut≤receipt.wire.ballot.cut ∧ receipt.wire.ballot.scope.phase=before.actual.point.cut := by
 have paid := RenewableHistoryReception.all_received_ballots_keep_the_original_paid_issuing_ledger
  (vocabulary base laws before request) (reception base laws before request)
  (start base laws before request) (issued base laws before request) recipient
  (FreshSigningReception.rows contract base laws before request) 0 ⟨[],[]⟩ (by simp) receipt inside
 exact ⟨paid,FreshSigningReplay.new_signatures_cannot_reuse_a_previous_phase before
  (FreshSigningSource.inputs base laws before request) base receipt.wire.ballot paid⟩

theorem every_new_global_receipt_locates_its_actual_global_execution_record
 (recipient : Fin before.actual.model.source.code.sites)
 (receipt : HeaderReception.Receipt (code := before.actual.model.source.code))
 (inside : receipt∈(FreshSigningReception.observed contract base laws before request recipient).receipts) :
 ∃ row, (FreshSigningReception.rows contract base laws before request)[receipt.index]?=some row ∧
 receipt.delivery=row.material.cursor.cut ∧ ∃ seen,
 RenewableHistoryReception.check (vocabulary base laws before request) (reception base laws before request)
  (start base laws before request) (issued base laws before request) recipient row seen receipt.wire=.accepted receipt.wire := by
 rcases RenewableHistoryReception.every_received_receipt_locates_its_actual_descendant_row
  (vocabulary base laws before request) (reception base laws before request)
  (start base laws before request) (issued base laws before request) recipient
  (FreshSigningReception.rows contract base laws before request) 0 ⟨[],[]⟩ receipt inside with absent | located
 · simp at absent
 · obtain ⟨index,row,found,whereFrom,delivered,seen,checked⟩ := located
   simp only [Nat.zero_add] at whereFrom
   exact ⟨row,by rw [whereFrom];exact found,delivered,seen,checked⟩

def decision (recipient : Fin before.actual.model.source.code.sites) (threshold : Nat) : ProspectiveQuorum.Result :=
 if ¬(ActorEnvelope.roster (start base laws before request).source).card+
  ActorStageEnvelope.budget (start base laws before request) (vocabulary base laws before request)
   (issued base laws before request) (currentScope before request)<threshold+threshold then
  .blocked .unsafeSourceBudget
 else match ActorQuorum.readout (FreshSigningReception.observed contract base laws before request recipient)
   (currentScope before request) threshold with
 | .blocked => .blocked .missingQuorum
 | .decided answer => .decided answer

theorem the_new_decision_consumes_the_independent_global_receiver
 (recipient : Fin before.actual.model.source.code.sites) (threshold : Nat) :
 decision contract base laws before request recipient threshold=
 JointReceptionConsumer.produce (vocabulary base laws before request) (reception base laws before request)
  (start base laws before request) (issued base laws before request)
  (report contract base laws before request).final recipient (currentScope before request) threshold := by
 unfold decision JointReceptionConsumer.produce
 rw [FreshSigningReception.the_independent_global_receiver_equals_the_new_context_receiver]
 rfl

theorem completed_fresh_signing_generates_one_global_decision_and_its_own_next
 (complete : (report contract base laws before request).status=.complete) (threshold : Nat) (positive : 0<threshold)
 (safe : (ActorEnvelope.roster (start base laws before request).source).card+
  ActorStageEnvelope.budget (start base laws before request) (vocabulary base laws before request)
   (issued base laws before request) (currentScope before request)<threshold+threshold)
 (reference : Fin before.actual.model.source.code.sites)
 (enough : threshold≤(JointReceptionConsumer.addressedActors (vocabulary base laws before request)
  (start base laws before request) (issued base laws before request) (currentScope before request) request.value reference).card) :
 ∃ answer,
 (∀ recipient, threshold≤(JointReceptionConsumer.addressedActors (vocabulary base laws before request)
  (start base laws before request) (issued base laws before request) (currentScope before request) request.value recipient).card →
  decision contract base laws before request recipient threshold=.decided answer) ∧
 ArchivedDeliveryConsumer.NativeContinuation
  (FreshSigningSource.next contract base laws before request).actual.model
  (FreshSigningSource.next contract base laws before request).actual.point := by
 have cleared := SourceRepairRun.every_completed_report_has_no_unreceived_original_target contract
  (vocabulary base laws before request) (reception base laws before request)
  (start base laws before request) (issued base laws before request) (currentScope before request) request.value request.depth
  (SourceRepairSearch.debt (vocabulary base laws before request) (reception base laws before request)
    (start base laws before request) (issued base laws before request) (currentScope before request) request.value
    (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request))+1)
  (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request)) complete
 have empty := Finset.card_eq_zero.mp cleared
 obtain ⟨answer,first⟩ := JointReceptionConsumer.actual_joint_completion_generates_source_budget_decisions
  (vocabulary base laws before request) (reception base laws before request) (start base laws before request)
  (issued base laws before request) (currentScope before request) request.value _ empty threshold positive safe reference enough
 refine ⟨answer,?_,JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩
 intro recipient supported
 obtain ⟨other,second⟩ := JointReceptionConsumer.actual_joint_completion_generates_source_budget_decisions
  (vocabulary base laws before request) (reception base laws before request) (start base laws before request)
  (issued base laws before request) (currentScope before request) request.value _ empty threshold positive safe recipient supported
 have same := JointReceptionConsumer.all_generated_endpoint_decisions_agree
  (vocabulary base laws before request) (reception base laws before request) (start base laws before request)
  (issued base laws before request) _ _ reference recipient (currentScope before request) threshold answer other first second
 rw [the_new_decision_consumes_the_independent_global_receiver]
 simpa only [report,FreshSigningSource.result,FreshSigningReplay.report,SourceRepairRun.produce,same] using second

theorem an_old_ballot_cannot_become_a_new_round_signature
 (wire : HeaderTransport.Wire (code := before.actual.model.source.code)) (old : wire.ballot.cut<before.actual.point.cut) :
 HeaderTransport.verify (vocabulary base laws before request) (start base laws before request) (issued base laws before request) wire=false := by
 apply Bool.eq_false_iff.mpr
 intro verified
 obtain ⟨_,_,_,_,_,_,_,paid,_⟩ := HeaderTransport.authenticated_wire_has_actual_send_and_paid_ballot
  (vocabulary base laws before request) (start base laws before request) (issued base laws before request) wire verified
 have phase := FreshSigningReplay.new_signatures_cannot_reuse_a_previous_phase before
  (FreshSigningSource.inputs base laws before request) base wire.ballot paid
 omega

theorem two_repair_horizons_agree_within_the_same_actual_new_signing_context
 (otherDepth : Nat) (left right : Fin before.actual.model.source.code.sites) (threshold : Nat) (a b : Bool)
 (first : decision contract base laws before request left threshold=.decided a)
 (second : decision contract base laws before {request with depth := otherDepth} right threshold=.decided b) : a=b := by
 rw [the_new_decision_consumes_the_independent_global_receiver] at first second
 exact JointReceptionConsumer.all_generated_endpoint_decisions_agree
  (vocabulary base laws before request) (reception base laws before request) (start base laws before request)
  (issued base laws before request) _ _ left right (currentScope before request) threshold a b first second

theorem a_received_status_requires_an_actual_new_target_and_complete_reception
 (success : FreshSigningSource.status contract base laws before request=.received) :
 (JointReceptionSource.targets (vocabulary base laws before request) (start base laws before request)
  (issued base laws before request) (currentScope before request) request.value).Nonempty ∧
 (report contract base laws before request).status=.complete := by
 unfold FreshSigningSource.status at success
 split at success <;> try contradiction
 rename_i nonempty
 have target := Finset.card_pos.mp (Nat.pos_of_ne_zero nonempty)
 cases checked : (report contract base laws before request).status with
 | complete => exact ⟨target,rfl⟩
 | blocked => simp only [checked] at success;contradiction
 | exhausted => simp only [checked] at success;contradiction

theorem a_reported_new_success_has_a_fresh_signature_in_the_actual_global_receiver
 (success : FreshSigningSource.status contract base laws before request=.received) :
 ∃ recipient receipt, receipt∈(FreshSigningReception.observed contract base laws before request recipient).receipts ∧
 receipt.wire.ballot.scope=currentScope before request ∧
 receipt.wire.ballot∈StageBudget.ledger (vocabulary base laws before request)
  (start base laws before request) (issued base laws before request) ∧
 before.actual.point.cut≤receipt.wire.ballot.cut ∧ receipt.wire.ballot.scope.phase=before.actual.point.cut := by
 obtain ⟨targets,complete⟩ := a_received_status_requires_an_actual_new_target_and_complete_reception contract base laws before request success
 obtain ⟨⟨recipient,actor⟩,member⟩ := targets
 have cleared := SourceRepairRun.every_completed_report_has_no_unreceived_original_target contract
  (vocabulary base laws before request) (reception base laws before request)
  (start base laws before request) (issued base laws before request) (currentScope before request) request.value request.depth
  (SourceRepairSearch.debt (vocabulary base laws before request) (reception base laws before request)
    (start base laws before request) (issued base laws before request) (currentScope before request) request.value
    (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request))+1)
  (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request)) complete
 have supported := JointReceptionConsumer.complete_joint_delivery_supplies_each_original_addressed_actor
  (vocabulary base laws before request) (reception base laws before request) (start base laws before request)
  (issued base laws before request) (currentScope before request) request.value _ (Finset.card_eq_zero.mp cleared) recipient
 have addressed : actor∈JointReceptionConsumer.addressedActors (vocabulary base laws before request)
  (start base laws before request) (issued base laws before request) (currentScope before request) request.value recipient :=
   Finset.mem_image.mpr ⟨(recipient,actor),Finset.mem_filter.mpr ⟨member,rfl⟩,rfl⟩
 have actual := supported addressed
 have globalSupport : actor∈ActorQuorum.support
  (FreshSigningReception.observed contract base laws before request recipient) (currentScope before request) request.value := by
   rw [FreshSigningReception.the_independent_global_receiver_equals_the_new_context_receiver]
   simpa only [report,FreshSigningSource.result,FreshSigningReplay.report,SourceRepairRun.produce] using actual
 obtain ⟨key,hasKey,_⟩ := (ActorQuorum.mem_support_iff _ _ _ actor).mp globalSupport
 obtain ⟨receipt,present,scope,_,_⟩ := (StageQuorum.mem_support_iff _ _ _ key).mp hasKey
 exact ⟨recipient,receipt,present,scope,every_new_global_receipt_restores_its_actual_new_paid_signature_and_phase
  contract base laws before request recipient receipt present⟩

theorem absence_of_new_actual_targets_cannot_be_reported_as_received
 (empty : JointReceptionSource.targets (vocabulary base laws before request) (start base laws before request)
  (issued base laws before request) (currentScope before request) request.value=∅) :
 FreshSigningSource.status contract base laws before request=.missingSource := by
 unfold FreshSigningSource.status
 rw [empty]
 rfl

variable (bound : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (genesis : Cursor bound.source.code)
 (parent : RecursiveSigningSource.State bound genesis) (oldScope : Scope) (oldValue : Bool)
 (control : FreshSigningSource.Controller (root := bound.source.code))

def continueFrom (slot depth count : Nat) : Option (JointReceptionSource.State bound.source.code) :=
 match SourceRepairArchive.produce bound contract base (laws bound) genesis parent oldScope oldValue slot depth with
 | none => none
 | some prior => some (FreshSigningSource.run contract base laws prior.final control count)

theorem a_missing_original_source_cannot_create_a_fresh_round
 (slot depth count : Nat) (missing : parent.archive[slot]?=none) :
 continueFrom contract base laws bound genesis parent oldScope oldValue control slot depth count=none := by
 simp only [continueFrom,SourceRepairArchive.produce,missing]

theorem the_public_continuation_keeps_the_entire_original_archive_windows_and_rows
 (slot depth count : Nat) (prior : SourceRepairRun.Report bound.source.code)
 (original : SourceRepairArchive.produce bound contract base (laws bound) genesis parent oldScope oldValue slot depth=some prior) :
 ∃ final, continueFrom contract base laws bound genesis parent oldScope oldValue control slot depth count=some final ∧
 prior.final.actual.archive <+: final.actual.archive ∧ prior.final.actual.windows <+: final.actual.windows ∧
 prior.final.rows <+: final.rows ∧ ArchivedDeliveryConsumer.NativeContinuation final.actual.model final.actual.point := by
 refine ⟨FreshSigningSource.run contract base laws prior.final control count,?_,?_,?_,?_,?_⟩
 · simp only [continueFrom,original]
 · exact (FreshSigningSource.all_later_dynamic_rounds_keep_the_original_archive_windows_and_actual_rows contract base laws prior.final control count).1
 · exact (FreshSigningSource.all_later_dynamic_rounds_keep_the_original_archive_windows_and_actual_rows contract base laws prior.final control count).2.1
 · exact (FreshSigningSource.all_later_dynamic_rounds_keep_the_original_archive_windows_and_actual_rows contract base laws prior.final control count).2.2
 · exact JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningConsumer
