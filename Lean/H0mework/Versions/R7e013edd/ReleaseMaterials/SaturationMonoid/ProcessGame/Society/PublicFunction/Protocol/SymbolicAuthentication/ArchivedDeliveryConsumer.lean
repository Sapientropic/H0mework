import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliveryProgress
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliveryConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource ArchivedDeliverySource ArchivedDeliveryProgress

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code) (genesis : Cursor bound.source.code)
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)

theorem generated_service_is_paid_in_the_same_actual_native_inventory
 (service : Service bound base law genesis state slot receiver) :
 ∃ origin receipt,
  (next bound genesis state [service.input]).archive[slot]?=some origin ∧
  receipt ∈ (RecursiveSigningReception.observed bound base law genesis
   (next bound genesis state [service.input]) origin receiver).receipts ∧
  ∃ paid ∈ (next bound genesis state [service.input]).rows bound genesis, ∃ position,
   StageBudget.issued (origin.vocabulary bound base) paid position=some receipt.wire.ballot ∧
   (Financial.inventoryAt ((next bound genesis state [service.input]).current bound genesis).source.input
    (ProgrammeHistory.visitAt ((next bound genesis state [service.input]).current bound genesis).source.input
     (EventStep.boundary paid.cursor))).filterMap
    (Financial.InstructionOrigin.instruction? ((next bound genesis state [service.input]).current bound genesis).source.input)=
    StageTrace.items paid := by
 obtain ⟨origin,wire,_,kept,updated,_,_,_⟩ :=
  a_service_executes_and_generates_its_next_real_receipt bound base law genesis state slot receiver service
 let receipt : HeaderReception.Receipt (code := bound.source.code) :=
  ⟨wire,(state.rows bound genesis).length,(row bound genesis state service.input).cursor.cut⟩
 have inside : receipt ∈ (RecursiveSigningReception.observed bound base law genesis
   (next bound genesis state [service.input]) origin receiver).receipts := by
  rw [updated]
  exact List.mem_append_right _ (List.mem_singleton_self _)
 have paid := RecursiveSigningReception.receipt_has_its_own_original_paid_ballot
  bound base law genesis _ origin receiver receipt inside
 obtain ⟨record,member,position,issued⟩ := StageBudget.ledger_origin _ _ _ receipt.wire.ballot paid
 have actual := an_archived_row_is_in_the_actual_cumulative_history bound genesis _ origin
  (List.mem_of_getElem? kept) record member
 exact ⟨origin,receipt,kept,inside,record,actual,position,issued,
  StageTrace.final_financial_inventory_is_the_original_record_items genesis _ record actual⟩

theorem zero_timing_allowance_cannot_generate_a_service
 (zero : law.maxDelay=0) (service : Service bound base law genesis state slot receiver) : False := by
 obtain ⟨origin,wire,_,_,checked⟩ :=
  every_service_has_an_original_authenticated_candidate bound base law genesis state slot receiver service
 have sound := HeaderReception.check_sound _ _ _ _ _ _ _ _ _ checked
 have ordered := sound.2.2.1
 have deadline := sound.2.2.2.2.2.2.2.1
 change _ ≤ wire.sendCut+law.maxDelay at deadline
 rw [zero,Nat.add_zero] at deadline
 omega

theorem an_empty_original_receipt_inventory_cannot_be_spent_again
 (origin : Segment bound) (located : state.archive[slot]?=some origin)
 (empty : outstanding bound base law genesis state origin receiver=∅)
 (service : Service bound base law genesis state slot receiver) : False := by
 obtain ⟨same,found,decrease⟩ :=
  service_strictly_reduces_the_original_unreceived_births bound base law genesis state slot receiver service
 have identical : same=origin := Option.some.inj (found.symm.trans located)
 subst same
 rw [empty,Finset.card_empty] at decrease
 omega

theorem absent_archive_generates_a_blocked_result
 (missing : state.archive[slot]?=none) :
 ∃ absent, produce bound base law genesis state slot receiver=.blocked absent := by
 cases selected : produce bound base law genesis state slot receiver with
 | blocked absent => exact ⟨absent,rfl⟩
 | served service =>
  have unavailable := no_issuing_archive_has_no_executable_service bound base law genesis state slot receiver missing service.input
  rw [service.accepted] at unavailable
  contradiction

def NativeContinuation (endpoint : Cursor bound.source.code) : Prop :=
 let runtime := WithdrawalInquiryRuntime.runtime bound endpoint
 HEq runtime.tick.generated.wholeLedgerWriteBack
  (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
 runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade bound endpoint).process.stateAt
  ((WithdrawalInquiryRuntime.facade bound endpoint).process.successor runtime.state)

theorem every_generated_run_keeps_original_ledger_and_own_next (count : Nat) :
 NativeContinuation bound
  ((ArchivedDeliveryProgress.run bound base law genesis state slot receiver count).current bound genesis) := by
 unfold NativeContinuation
 exact (WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
  bound ((ArchivedDeliveryProgress.run bound base law genesis state slot receiver count).current bound genesis)).2.2.2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliveryConsumer
