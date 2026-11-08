import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryService

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource RenewableHistoryQuorum RenewableHistoryService

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code) (genesis : Cursor bound.source.code)
 (parent : RecursiveSigningSource.State bound genesis)
 (control : RenewableHistoryQuorum.Controller (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (count slot : Nat) (recipient : Fin bound.source.code.sites)

theorem the_new_authenticated_delivery_is_in_its_actual_native_inventory
 (service : Service bound contract base law genesis parent control count slot recipient) :
 (Financial.inventoryAt (after bound contract base law genesis parent control count slot recipient service).point.source.input
  (ProgrammeHistory.visitAt (after bound contract base law genesis parent control count slot recipient service).point.source.input
   (EventStep.boundary (row bound contract genesis parent control count service.input).actual.cursor))).filterMap
  (Financial.InstructionOrigin.instruction?
   (after bound contract base law genesis parent control count slot recipient service).point.source.input)=
  StageTrace.items (row bound contract genesis parent control count service.input).material := by
 have actual : (row bound contract genesis parent control count service.input).actual∈
  (RenewableArchiveSource.fresh (current bound contract genesis parent control count) [service.input]).rows
   (current bound contract genesis parent control count).model := by
  rw [the_selected_input_is_the_actual_new_execution_row]
  exact List.mem_cons_self
 exact (StageTrace.final_financial_inventory_is_the_original_record_items
  (current bound contract genesis parent control count).point
  (RenewableArchiveSource.fresh (current bound contract genesis parent control count) [service.input]).stages
  (row bound contract genesis parent control count service.input).actual actual).trans
  (RenewableCodeLineage.recodeRow_items _ _).symm

theorem the_serviced_endpoint_keeps_its_whole_ledger_and_own_next
 (service : Service bound contract base law genesis parent control count slot recipient) :
 ArchivedDeliveryConsumer.NativeContinuation
  (after bound contract base law genesis parent control count slot recipient service).model
  (after bound contract base law genesis parent control count slot recipient service).point := by
 unfold ArchivedDeliveryConsumer.NativeContinuation
 exact (WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
  (after bound contract base law genesis parent control count slot recipient service).model
  (after bound contract base law genesis parent control count slot recipient service).point).2.2.2

theorem all_cross_window_receipts_remain_distinct
 (origin : Segment bound) :
 ((observed bound contract base law genesis parent control count origin recipient).receipts.map
  fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)).Nodup :=
 RenewableHistoryReception.duplicate_births_cannot_be_added_across_any_descendant_codes _ _ _ _ _ _ _ _ (by simp)

theorem public_decisions_agree_across_independent_actual_window_histories
 (other : RenewableHistoryQuorum.Controller (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (more : Nat) (otherRecipient : Fin bound.source.code.sites) (scope : Scope) (threshold : Nat) (a b : Bool)
 (one : RenewableHistoryQuorum.produce bound contract base law genesis parent control count slot recipient scope threshold=.decided a)
 (two : RenewableHistoryQuorum.produce bound contract base law genesis parent other more slot otherRecipient scope threshold=.decided b) : a=b := by
 cases located : parent.archive[slot]? with
 | none => simp only [RenewableHistoryQuorum.produce,located] at one; contradiction
 | some origin =>
   simp only [RenewableHistoryQuorum.produce,located] at one two
   exact original_source_decisions_agree_across_arbitrarily_many_actual_windows
    bound contract base law genesis parent control other count more origin recipient otherRecipient scope threshold a b one two

theorem deleting_the_original_archive_blocks_the_public_producer
 (missing : parent.archive[slot]?=none) (scope : Scope) (threshold : Nat) :
 RenewableHistoryQuorum.produce bound contract base law genesis parent control count slot recipient scope threshold=.blocked .missingQuorum := by
 simp only [RenewableHistoryQuorum.produce,missing]

theorem missing_actual_actor_quorum_cannot_become_a_decision
 (origin : Segment bound) (scope : Scope) (threshold : Nat) (value : Bool)
 (short : (ActorQuorum.support
  (observed bound contract base law genesis parent control count origin recipient) scope value).card<threshold) :
 decideAt bound contract base law genesis parent control count origin recipient scope threshold≠.decided value := by
 intro done
 have enough := (a_decision_computes_its_original_budget_and_received_identities
  bound contract base law genesis parent control count origin recipient scope threshold value done).2.2
 omega

theorem zero_threshold_cannot_become_a_decision
 (origin : Segment bound) (scope : Scope) (value : Bool) :
 decideAt bound contract base law genesis parent control count origin recipient scope 0≠.decided value := by
 intro done
 have positive := (a_decision_computes_its_original_budget_and_received_identities
  bound contract base law genesis parent control count origin recipient scope 0 value done).2.1
 omega

theorem zero_delivery_time_prevents_new_service (zero : law.maxDelay=0)
 (service : Service bound contract base law genesis parent control count slot recipient) : False := by
 obtain ⟨origin,wire,_,_,checked⟩ := every_generated_service_keeps_the_actual_old_source
  bound contract base law genesis parent control count slot recipient service
 obtain ⟨_,_,earlier,_,_,_,_,deadline,_,_⟩ := RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ checked
 change _≤wire.sendCut+law.maxDelay at deadline
 rw [zero,Nat.add_zero] at deadline
 omega

variable (origin : Segment bound) (record : RenewableCodeLineage.Row bound.source.code)
 (seen : List (Nat×Nat)) (wire : HeaderTransport.Wire (code := bound.source.code))

theorem forged_wire_cannot_be_an_authenticated_descendant_receipt
 (forged : HeaderTransport.verify (origin.vocabulary bound base) origin.origin origin.stages wire=false)
 (accepted : RenewableHistoryReception.check (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages recipient record seen wire=.accepted wire) : False := by
 have verified := (RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ accepted).2.2.2.1
 rw [forged] at verified
 contradiction

theorem a_wrong_signer_cannot_become_an_authenticated_descendant_receipt
 (wrong : wire.ballot.actor≠bound.source.code.siteParty wire.ballot.key)
 (accepted : RenewableHistoryReception.check (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages recipient record seen wire=.accepted wire) : False := by
 have verified := (RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ accepted).2.2.2.1
 obtain ⟨_,_,_,_,_,_,_,original,_⟩ := HeaderTransport.authenticated_wire_has_actual_send_and_paid_ballot
  (origin.vocabulary bound base) origin.origin origin.stages wire verified
 exact wrong (ActorEnvelope.actual_ballot_retains_the_original_actor (origin.vocabulary bound base)
  origin.origin origin.stages wire.ballot original)

theorem replayed_birth_cannot_create_a_second_receipt
 (used : (wire.ballot.cut,wire.ballot.position)∈seen)
 (accepted : RenewableHistoryReception.check (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages recipient record seen wire=.accepted wire) : False :=
 (RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ accepted).2.2.2.2.2.2.2.2.2 used

theorem a_later_window_does_not_refresh_the_original_send_deadline
 (expired : wire.sendCut+law.maxDelay<record.material.cursor.cut)
 (accepted : RenewableHistoryReception.check (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages recipient record seen wire=.accepted wire) : False := by
 obtain ⟨_,_,_,_,_,_,_,deadline,_,_⟩ := RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ accepted
 change _≤wire.sendCut+law.maxDelay at deadline
 omega

theorem deleting_actual_delivery_cannot_be_replaced_by_the_old_certificate
 (absent : StageReception.delivered record.material wire.serial=false)
 (accepted : RenewableHistoryReception.check (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages recipient record seen wire=.accepted wire) : False := by
 have delivered := (RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ accepted).2.1
 rw [absent] at delivered
 contradiction

theorem another_phase_is_not_the_original_scope
 (changed : wire.ballot.scope≠(origin.law bound law).scope recipient record.material.before.current)
 (accepted : RenewableHistoryReception.check (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages recipient record seen wire=.accepted wire) : False :=
 changed (RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ accepted).2.2.2.2.2.2.1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryConsumer
