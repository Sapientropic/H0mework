import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveDelivery

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource RenewableArchiveDelivery

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
 (state : State bound genesis) (enabled accept : Bool) (slot : Nat) (receiver : Fin bound.source.code.sites)

abbrev final (service : Service bound contract base law genesis state enabled accept slot receiver) :=
 RenewableArchiveSource.execute (successor bound contract genesis state enabled accept) [service.input]

theorem generated_service_keeps_every_original_financial_account
 (original : (state.current bound genesis).side=.original)
 (service : Service bound contract base law genesis state enabled accept slot receiver)
 (ordinal : Nat) (earlier : ordinal≤EventStep.boundary (state.current bound genesis)) :
 Native.Coupling.Match bound.source.code (state.current bound genesis).source.input
  (final bound contract base law genesis state enabled accept slot receiver service).point.source.input
  (Financial.accountAt (state.current bound genesis).source.input ordinal)
  (Financial.accountAt (final bound contract base law genesis state enabled accept slot receiver service).point.source.input ordinal) :=
 RenewableArchiveFinance.the_paid_window_and_all_later_execution_keep_the_original_financial_prefix
  contract (before bound genesis state) enabled accept original
  (every_generated_service_has_actual_payment_and_original_authentication
   bound contract base law genesis state enabled accept slot receiver service).1
  (RenewableArchiveSource.fresh (successor bound contract genesis state enabled accept) [service.input]).stages ordinal earlier

theorem actual_delivery_keeps_the_entire_old_archive
 (service : Service bound contract base law genesis state enabled accept slot receiver) :
 state.archive.map (RenewableArchiveSource.Context.ofSegment bound) <+:
  (final bound contract base law genesis state enabled accept slot receiver service).archive :=
 (List.prefix_append _ _).trans (List.prefix_append _ _)

theorem the_actual_endpoint_consumes_whole_ledger_and_generates_its_own_next
 (service : Service bound contract base law genesis state enabled accept slot receiver) :
 ArchivedDeliveryConsumer.NativeContinuation
  (final bound contract base law genesis state enabled accept slot receiver service).model
  (final bound contract base law genesis state enabled accept slot receiver service).point := by
 unfold ArchivedDeliveryConsumer.NativeContinuation
 exact (WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
  (final bound contract base law genesis state enabled accept slot receiver service).model
  (final bound contract base law genesis state enabled accept slot receiver service).point).2.2.2

theorem zero_delivery_time_cannot_generate_service (zero : law.maxDelay=0)
 (service : Service bound contract base law genesis state enabled accept slot receiver) : False := by
 obtain ⟨_,origin,wire,_,_,checked⟩ :=
  every_generated_service_has_actual_payment_and_original_authentication bound contract base law genesis state enabled accept slot receiver service
 obtain ⟨_,_,afterSend,_,_,_,_,deadline,_,_⟩ :=
  PaidOriginHeader.check_sound _ _ _ _ _ _ _ _ _ _ checked
 change _≤wire.sendCut+law.maxDelay at deadline
 rw [zero,Nat.add_zero] at deadline
 omega

theorem a_wrong_provider_signer_cannot_generate_service
 (wrong : contract.acceptance.signer≠contract.provider)
 (service : Service bound contract base law genesis state enabled accept slot receiver) : False :=
 payment_refusal_cannot_generate_a_delivery_service bound contract base law genesis state enabled accept slot receiver
  (PaidInvocationSource.a_wrong_signer_cannot_open_any_window bound.source.code contract
   (state.current bound genesis) enabled accept wrong) service

theorem missing_original_archive_cannot_generate_service
 (missing : state.archive[slot]?=none)
 (service : Service bound contract base law genesis state enabled accept slot receiver) : False := by
 obtain ⟨_,_,_,present,_,_⟩ :=
  every_generated_service_has_actual_payment_and_original_authentication bound contract base law genesis state enabled accept slot receiver service
 rw [missing] at present
 contradiction

variable (origin : Segment bound)
 (record : StageTrace.Record (code := PaidInvocationSource.code bound.source.code contract))
 (seen : List (Nat×Nat)) (wire : HeaderTransport.Wire (code := bound.source.code))

theorem deleting_actual_delivery_rejects_the_original_wire
 (missing : StageReception.delivered record wire.serial=false)
 (accepted : PaidOriginHeader.check contract (origin.vocabulary bound base) (deliveryLaw bound contract law origin)
  origin.origin origin.stages receiver record seen wire=.accepted wire) : False := by
 have delivered := (PaidOriginHeader.check_sound _ _ _ _ _ _ _ _ _ _ accepted).2.1
 rw [missing] at delivered
 contradiction

theorem forged_wire_cannot_become_a_successor_receipt
 (forged : HeaderTransport.verify (origin.vocabulary bound base) origin.origin origin.stages wire=false)
 (accepted : PaidOriginHeader.check contract (origin.vocabulary bound base) (deliveryLaw bound contract law origin)
  origin.origin origin.stages receiver record seen wire=.accepted wire) : False := by
 have verified := (PaidOriginHeader.check_sound _ _ _ _ _ _ _ _ _ _ accepted).2.2.2.1
 rw [forged] at verified
 contradiction

theorem a_replayed_receipt_cannot_be_counted_again
 (used : (wire.ballot.cut,wire.ballot.position)∈seen)
 (accepted : PaidOriginHeader.check contract (origin.vocabulary bound base) (deliveryLaw bound contract law origin)
  origin.origin origin.stages receiver record seen wire=.accepted wire) : False :=
 (PaidOriginHeader.check_sound _ _ _ _ _ _ _ _ _ _ accepted).2.2.2.2.2.2.2.2.2 used

theorem expired_wire_cannot_become_a_successor_receipt
 (expired : wire.sendCut+law.maxDelay<record.cursor.cut)
 (accepted : PaidOriginHeader.check contract (origin.vocabulary bound base) (deliveryLaw bound contract law origin)
  origin.origin origin.stages receiver record seen wire=.accepted wire) : False := by
 obtain ⟨_,_,_,_,_,_,_,deadline,_,_⟩ := PaidOriginHeader.check_sound _ _ _ _ _ _ _ _ _ _ accepted
 change _≤wire.sendCut+law.maxDelay at deadline
 omega


end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveConsumer
