import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveFinance

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveDelivery
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource

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

abbrev before := RenewableArchiveSource.initial bound genesis state
abbrev successor := RenewableArchiveSource.renew contract (before bound genesis state) enabled accept
abbrev row (input : LocalCommandSource.Input) :=
 (LocalCommandSource.observe (successor bound contract genesis state enabled accept).model
  (successor bound contract genesis state enabled accept).point input).row
  (successor bound contract genesis state enabled accept).model
abbrev previous (origin : Segment bound) :=
 RecursiveSigningReception.observed bound base law genesis state origin receiver
def deliveryLaw (origin : Segment bound) : StageReception.Law (PaidInvocationSource.code bound.source.code contract) :=
 ⟨(origin.law bound law).scope,law.maxDelay⟩

-- Search the actual funded source menu; the original archive supplies authentication.
def review (input : LocalCommandSource.Input) : HeaderReception.Verdict (code := bound.source.code) :=
 if PaidInvocationSource.admitted bound.source.code contract (state.current bound genesis) enabled accept≠true then
  .rejected .unpaidDelivery
 else match state.archive[slot]? with
 | none => .rejected .missingWire
 | some origin => match PaidOriginHeader.incoming contract (origin.vocabulary bound base)
    origin.origin origin.stages (row bound contract genesis state enabled accept input) with
   | none => .rejected .missingWire
   | some wire => PaidOriginHeader.check contract (origin.vocabulary bound base)
     (deliveryLaw bound contract law origin) origin.origin origin.stages receiver
     (row bound contract genesis state enabled accept input)
     ((previous bound base law genesis state receiver origin).receipts.map
      fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire

def available (input : LocalCommandSource.Input) : Bool :=
 match review bound contract base law genesis state enabled accept slot receiver input with
 | .accepted _ => true
 | .rejected _ => false

structure Service where
 private mk ::
 input : LocalCommandSource.Input
 registered : input ∈ CommandWindowSource.menu (successor bound contract genesis state enabled accept).model
 accepted : available bound contract base law genesis state enabled accept slot receiver input=true

inductive Result where
 | served (service : Service bound contract base law genesis state enabled accept slot receiver)
 | blocked (absent : ∀ input ∈ CommandWindowSource.menu (successor bound contract genesis state enabled accept).model,
    available bound contract base law genesis state enabled accept slot receiver input=false)

def produce : Result bound contract base law genesis state enabled accept slot receiver :=
 match found : (CommandWindowSource.menu (successor bound contract genesis state enabled accept).model).find?
   (available bound contract base law genesis state enabled accept slot receiver) with
 | some input => .served ⟨input,List.mem_of_find?_eq_some found,List.find?_some found⟩
 | none => .blocked (by
   intro input member
   simpa only [Bool.not_eq_true] using (List.find?_eq_none.mp found) input member)

def Result.after (result : Result bound contract base law genesis state enabled accept slot receiver) :=
 match result with
 | .served service => RenewableArchiveSource.execute (successor bound contract genesis state enabled accept) [service.input]
 | .blocked _ => successor bound contract genesis state enabled accept

theorem every_generated_service_has_actual_payment_and_original_authentication
 (service : Service bound contract base law genesis state enabled accept slot receiver) :
 PaidInvocationSource.admitted bound.source.code contract (state.current bound genesis) enabled accept=true ∧
 ∃ origin wire, state.archive[slot]?=some origin ∧
  PaidOriginHeader.incoming contract (origin.vocabulary bound base) origin.origin origin.stages
   (row bound contract genesis state enabled accept service.input)=some wire ∧
  PaidOriginHeader.check contract (origin.vocabulary bound base) (deliveryLaw bound contract law origin)
   origin.origin origin.stages receiver (row bound contract genesis state enabled accept service.input)
   ((previous bound base law genesis state receiver origin).receipts.map
    fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire=.accepted wire := by
 have accepted := service.accepted
 have funded : PaidInvocationSource.admitted bound.source.code contract (state.current bound genesis) enabled accept=true := by
  by_contra missing
  simp only [available,review,if_pos missing] at accepted
  contradiction
 refine ⟨funded,?_⟩
 simp only [available,review,if_neg (not_not.mpr funded)] at accepted
 cases located : state.archive[slot]? with
 | none => simp only [located] at accepted; contradiction
 | some origin =>
   cases found : PaidOriginHeader.incoming contract (origin.vocabulary bound base) origin.origin origin.stages
    (row bound contract genesis state enabled accept service.input) with
   | none => simp only [located,found] at accepted; contradiction
   | some wire =>
     simp only [located,found] at accepted
     split at accepted <;> try contradiction
     rename_i result checked
     have same := (PaidOriginHeader.check_sound _ _ _ _ _ _ _ _ _ _ checked).1
     subst result
     exact ⟨origin,wire,rfl,found,checked⟩

theorem a_real_available_input_generates_service
 (input : LocalCommandSource.Input)
 (registered : input ∈ CommandWindowSource.menu (successor bound contract genesis state enabled accept).model)
 (opportunity : available bound contract base law genesis state enabled accept slot receiver input=true) :
 ∃ service, produce bound contract base law genesis state enabled accept slot receiver=.served service := by
 cases outcome : produce bound contract base law genesis state enabled accept slot receiver with
 | served service => exact ⟨service,rfl⟩
 | blocked absent =>
   have impossible := absent input registered
   rw [opportunity] at impossible
   contradiction

theorem generated_service_is_consumed_as_an_original_source_receipt
 (service : Service bound contract base law genesis state enabled accept slot receiver) :
 ∃ origin wire, state.archive[slot]?=some origin ∧
  wire.ballot ∈ StageBudget.ledger (origin.vocabulary bound base) origin.origin origin.stages ∧
  (PaidOriginHeader.receive contract (origin.vocabulary bound base) (deliveryLaw bound contract law origin)
   origin.origin origin.stages receiver 0
   (row bound contract genesis state enabled accept service.input)
   (previous bound base law genesis state receiver origin)).receipts=
  (previous bound base law genesis state receiver origin).receipts++
   [⟨wire,0,(row bound contract genesis state enabled accept service.input).cursor.cut⟩] ∧
  (wire.ballot.cut,wire.ballot.position) ∉
   (previous bound base law genesis state receiver origin).receipts.map
    (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) := by
 obtain ⟨_,origin,wire,located,found,checked⟩ :=
  every_generated_service_has_actual_payment_and_original_authentication bound contract base law genesis state enabled accept slot receiver service
 have sound := PaidOriginHeader.check_sound _ _ _ _ _ _ _ _ _ _ checked
 refine ⟨origin,wire,located,
  PaidOriginHeader.an_accepted_successor_receipt_retains_the_original_issued_ballot _ _ _ _ _ _ _ _ _ checked,?_,
  sound.2.2.2.2.2.2.2.2.2⟩
 simp only [PaidOriginHeader.receive,found,checked]

theorem actual_service_is_the_next_native_execution_record
 (service : Service bound contract base law genesis state enabled accept slot receiver) :
 (RenewableArchiveSource.fresh (successor bound contract genesis state enabled accept) [service.input]).rows
  (successor bound contract genesis state enabled accept).model=
 [row bound contract genesis state enabled accept service.input] := rfl

theorem payment_refusal_cannot_generate_a_delivery_service
 (unpaid : PaidInvocationSource.admitted bound.source.code contract (state.current bound genesis) enabled accept=false)
 (service : Service bound contract base law genesis state enabled accept slot receiver) : False := by
 have paid := (every_generated_service_has_actual_payment_and_original_authentication
  bound contract base law genesis state enabled accept slot receiver service).1
 rw [unpaid] at paid
 contradiction

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveDelivery
