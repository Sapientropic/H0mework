import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningReception

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliverySource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code) (genesis : Cursor bound.source.code)
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)

abbrev row (input : LocalCommandSource.Input) :=
 (LocalCommandSource.observe bound (state.current bound genesis) input).row bound
abbrev previous (origin : Segment bound) :=
 RecursiveSigningReception.observed bound base law genesis state origin receiver

-- Test the original source menu at the actual endpoint, keeping the immutable
-- issuing context. Neither a delivery receipt nor a successful endpoint is input.
def review (input : LocalCommandSource.Input) : HeaderReception.Verdict (code := bound.source.code) :=
 match state.archive[slot]? with
 | none => .rejected .missingWire
 | some origin => match RecursiveSigningReception.incoming bound base origin (row bound genesis state input) with
   | none => .rejected .missingWire
   | some wire => HeaderReception.check (origin.vocabulary bound base) (origin.law bound law)
      origin.origin origin.stages receiver (row bound genesis state input)
      ((previous bound base law genesis state receiver origin).receipts.map
       fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire

def available (input : LocalCommandSource.Input) : Bool :=
 match review bound base law genesis state slot receiver input with
 | .accepted _ => true
 | .rejected _ => false

structure Service where
 private mk ::
 input : LocalCommandSource.Input
 registered : input ∈ CommandWindowSource.menu bound
 accepted : available bound base law genesis state slot receiver input=true

inductive Result where
 | served (service : Service bound base law genesis state slot receiver)
 | blocked (absent : ∀ input ∈ CommandWindowSource.menu bound,
    available bound base law genesis state slot receiver input=false)

def produce : Result bound base law genesis state slot receiver :=
 match found : (CommandWindowSource.menu bound).find?
   (available bound base law genesis state slot receiver) with
 | some input => .served ⟨input,List.mem_of_find?_eq_some found,List.find?_some found⟩
 | none => .blocked (by
   intro input member
   simpa only [Bool.not_eq_true] using (List.find?_eq_none.mp found) input member)

def Result.after (result : Result bound base law genesis state slot receiver) : State bound genesis :=
 match result with
 | .served service => next bound genesis state [service.input]
 | .blocked _ => state

theorem an_available_source_input_forces_the_producer_to_execute
 (input : LocalCommandSource.Input) (registered : input ∈ CommandWindowSource.menu bound)
 (opportunity : available bound base law genesis state slot receiver input=true) :
 ∃ service, produce bound base law genesis state slot receiver=.served service := by
 cases outcome : produce bound base law genesis state slot receiver with
 | served service => exact ⟨service,rfl⟩
 | blocked absent =>
   have impossible := absent input registered
   rw [opportunity] at impossible
   contradiction

theorem actual_source_delivery_conditions_generate_service
 (input : LocalCommandSource.Input) (registered : input ∈ CommandWindowSource.menu bound)
 (origin : Segment bound) (located : state.archive[slot]?=some origin)
 (wire : HeaderTransport.Wire (code := bound.source.code))
 (found : RecursiveSigningReception.incoming bound base origin (row bound genesis state input)=some wire)
 (afterSend : wire.sendCut<(row bound genesis state input).cursor.cut)
 (packet : HeaderReception.matchingPacket (row bound genesis state input) wire=true)
 (address : wire.recipient=receiver)
 (scope : wire.ballot.scope=(origin.law bound law).scope receiver (row bound genesis state input).before.current)
 (timely : (row bound genesis state input).cursor.cut ≤ wire.sendCut+law.maxDelay)
 (paid : ∀ item ∈ StageTrace.items (row bound genesis state input), bound.source.code.law.Valid item.before item.request)
 (unused : (wire.ballot.cut,wire.ballot.position) ∉
  (previous bound base law genesis state receiver origin).receipts.map
   (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))) :
 ∃ service, produce bound base law genesis state slot receiver=.served service := by
 have member := List.mem_of_find?_eq_some found
 have delivered := List.find?_some found
 have verified : HeaderTransport.verify (origin.vocabulary bound base) origin.origin origin.stages wire=true :=
  decide_eq_true member
 have checked : HeaderReception.check (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages receiver (row bound genesis state input)
  ((previous bound base law genesis state receiver origin).receipts.map
   (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))) wire=.accepted wire := by
  simp_all [HeaderReception.check,Segment.law]
 apply an_available_source_input_forces_the_producer_to_execute bound base law genesis state slot receiver input registered
 simp only [available,review,located,found,checked]

theorem every_service_has_an_original_authenticated_candidate
 (service : Service bound base law genesis state slot receiver) :
 ∃ origin wire, state.archive[slot]?=some origin ∧
  RecursiveSigningReception.incoming bound base origin (row bound genesis state service.input)=some wire ∧
  HeaderReception.check (origin.vocabulary bound base) (origin.law bound law)
   origin.origin origin.stages receiver (row bound genesis state service.input)
   ((previous bound base law genesis state receiver origin).receipts.map
    fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire=.accepted wire := by
 have accepted := service.accepted
 cases located : state.archive[slot]? with
 | none => simp only [available,review,located] at accepted; contradiction
 | some origin =>
  cases found : RecursiveSigningReception.incoming bound base origin (row bound genesis state service.input) with
  | none => simp only [available,review,located,found] at accepted; contradiction
  | some wire =>
   simp only [available,review,located,found] at accepted
   split at accepted <;> try contradiction
   rename_i result checked
   have same := (HeaderReception.check_sound _ _ _ _ _ _ _ _ _ checked).1
   subst result
   exact ⟨origin,wire,rfl,found,checked⟩

theorem one_step_has_exactly_the_original_native_row (input : LocalCommandSource.Input) :
 (next bound genesis state [input]).rows bound genesis =
 state.rows bound genesis ++ [row bound genesis state input] := by
 change StageTrace.records genesis (state.stages ++ _) = _
 rw [StageQueue.records_append]
 rfl

theorem an_archived_origin_keeps_its_index (input : LocalCommandSource.Input)
 (origin : Segment bound) (located : state.archive[slot]?=some origin) :
 (next bound genesis state [input]).archive[slot]?=some origin := by
 change (state.archive++[_])[slot]?=some origin
 rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp located).choose]
 exact located

theorem a_service_executes_and_generates_its_next_real_receipt
 (service : Service bound base law genesis state slot receiver) :
 ∃ origin wire, state.archive[slot]?=some origin ∧
  (next bound genesis state [service.input]).archive[slot]?=some origin ∧
  (RecursiveSigningReception.observed bound base law genesis
   (next bound genesis state [service.input]) origin receiver).receipts =
  (previous bound base law genesis state receiver origin).receipts ++
   [⟨wire,(state.rows bound genesis).length,(row bound genesis state service.input).cursor.cut⟩] ∧
  wire ∈ origin.wires bound base ∧ wire.recipient=receiver ∧
  (wire.ballot.cut,wire.ballot.position) ∉
   (previous bound base law genesis state receiver origin).receipts.map
    (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) := by
 obtain ⟨origin,wire,located,found,checked⟩ :=
  every_service_has_an_original_authenticated_candidate bound base law genesis state slot receiver service
 have sound := HeaderReception.check_sound _ _ _ _ _ _ _ _ _ checked
 refine ⟨origin,wire,located,
  an_archived_origin_keeps_its_index bound genesis state slot service.input origin located,?_,
  List.mem_of_find?_eq_some found,sound.2.2.2.2.2.1,sound.2.2.2.2.2.2.2.2.2⟩
 unfold RecursiveSigningReception.observed
 rw [one_step_has_exactly_the_original_native_row,RecursiveSigningReception.scan_append]
 change (RecursiveSigningReception.receive bound base law origin receiver
  (0+(state.rows bound genesis).length) (row bound genesis state service.input)
  (previous bound base law genesis state receiver origin)).receipts = _
 simp only [Nat.zero_add,RecursiveSigningReception.receive,found,checked]

theorem no_issuing_archive_has_no_executable_service
 (missing : state.archive[slot]?=none) :
 ∀ input, available bound base law genesis state slot receiver input=false := by
 intro input
 simp only [available,review,missing]

theorem refusal_preserves_the_actual_endpoint
 (absent : ∀ input ∈ CommandWindowSource.menu bound,
   available bound base law genesis state slot receiver input=false) :
 (Result.after bound base law genesis state slot receiver (.blocked absent)).current bound genesis =
 state.current bound genesis := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliverySource
