import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueue
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderReception

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginHeader
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {old : Code Party Good Port (Mandate.State Party Technology) Instrument}
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law (PaidInvocationSource.code old contract))
 (origin : Cursor old) (past : List (EventHistory.Stage (code := old)))

-- Authentication belongs to the issuing segment; delivery belongs to the actual funded successor.
@[irreducible] def checkIssued (issued : List (HeaderTransport.Wire (code := old))) (receiver : Fin old.sites)
 (row : StageTrace.Record (code := PaidInvocationSource.code old contract))
 (seen : List (Nat × Nat)) (wire : HeaderTransport.Wire (code := old)) : HeaderReception.Verdict (code := old) :=
 if StageReception.delivered row wire.serial ≠ true then .rejected .missingDelivery
 else if ¬ wire.sendCut < row.cursor.cut then .rejected .unauthenticated
 else if decide (wire ∈ issued) ≠ true then .rejected .unauthenticated
 else if StageReception.matchingPacket row wire ≠ true then .rejected .missingPacket
 else if wire.recipient ≠ receiver then .rejected .wrongRecipient
 else if wire.ballot.scope ≠ law.scope receiver row.before.current then .rejected .staleScope
 else if ¬ row.cursor.cut ≤ wire.sendCut + law.maxDelay then .rejected .late
 else if ¬ ∀ item ∈ StageTrace.items row, old.law.Valid item.before item.request then .rejected .unpaidDelivery
 else if (wire.ballot.cut,wire.ballot.position) ∈ seen then .rejected .duplicate
 else .accepted wire

-- The public source checker always derives this table from the original issuing history.
def check (receiver : Fin old.sites)
 (row : StageTrace.Record (code := PaidInvocationSource.code old contract))
 (seen : List (Nat × Nat)) (wire : HeaderTransport.Wire (code := old)) : HeaderReception.Verdict (code := old) :=
 checkIssued contract law (HeaderTransport.wires vocabulary origin past) receiver row seen wire

theorem check_sound (receiver : Fin old.sites)
 (row : StageTrace.Record (code := PaidInvocationSource.code old contract))
 (seen : List (Nat × Nat)) (wire result : HeaderTransport.Wire (code := old))
 (accepted : check contract vocabulary law origin past receiver row seen wire = .accepted result) :
 result = wire ∧ StageReception.delivered row wire.serial = true ∧ wire.sendCut < row.cursor.cut ∧
 HeaderTransport.verify vocabulary origin past wire = true ∧
 StageReception.matchingPacket row wire = true ∧ wire.recipient = receiver ∧
 wire.ballot.scope = law.scope receiver row.before.current ∧
 row.cursor.cut ≤ wire.sendCut + law.maxDelay ∧
 (∀ item ∈ StageTrace.items row,old.law.Valid item.before item.request) ∧
 (wire.ballot.cut,wire.ballot.position) ∉ seen := by
 unfold check checkIssued at accepted
 split_ifs at accepted; simp_all [HeaderTransport.verify]

theorem an_accepted_successor_receipt_retains_the_original_issued_ballot
 (receiver : Fin old.sites) (row : StageTrace.Record (code := PaidInvocationSource.code old contract))
 (seen : List (Nat × Nat)) (wire : HeaderTransport.Wire (code := old))
 (accepted : check contract vocabulary law origin past receiver row seen wire = .accepted wire) :
 wire.ballot ∈ StageBudget.ledger vocabulary origin past := by
 have verified := (check_sound contract vocabulary law origin past receiver row seen wire wire accepted).2.2.2.1
 obtain ⟨_,_,_,_,_,_,_,original,_⟩ :=
  HeaderTransport.authenticated_wire_has_actual_send_and_paid_ballot vocabulary origin past wire verified
 exact original

theorem an_accepted_row_requires_a_delivery_admission
 (receiver : Fin old.sites) (row : StageTrace.Record (code := PaidInvocationSource.code old contract))
 (seen : List (Nat × Nat)) (wire : HeaderTransport.Wire (code := old))
 (accepted : check contract vocabulary law origin past receiver row seen wire = .accepted wire) :
 ∃ event, StageTransport.admission row = some event ∧ event.val = .deliver wire.serial := by
 have delivered := (check_sound contract vocabulary law origin past receiver row seen wire wire accepted).2.1
 unfold StageReception.delivered at delivered
 split at delivered <;> try contradiction
 rename_i event chosen
 split at delivered <;> try contradiction
 rename_i address kind
 have same : address = wire.serial := of_decide_eq_true delivered
 exact ⟨event,chosen,by simpa only [same] using kind⟩

def incoming (row : StageTrace.Record (code := PaidInvocationSource.code old contract)) :
 Option (HeaderTransport.Wire (code := old)) :=
 match StageTransport.admission row with
 | some event => match event.val with
   | .deliver serial => (HeaderTransport.wires vocabulary origin past).find? (fun wire => wire.serial == serial)
   | _ => none
 | none => none

def receive (receiver : Fin old.sites) (index : Nat)
 (row : StageTrace.Record (code := PaidInvocationSource.code old contract))
 (previous : HeaderReception.Receiver (code := old)) : HeaderReception.Receiver (code := old) :=
 let candidate := incoming contract vocabulary origin past row
 let verdict := match candidate with
  | none => AttestationReception.VerdictData.rejected .missingWire
  | some wire => check contract vocabulary law origin past receiver row
    (previous.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire
 ⟨match verdict with
   | .accepted wire => previous.receipts ++ [⟨wire,index,row.cursor.cut⟩]
   | .rejected _ => previous.receipts,
  previous.audit ++ [(row.cursor.cut,candidate,verdict)]⟩

-- A cached execution of the same receiver; the equality below binds its table to actual issuance.
@[irreducible] def receiveIssued (issued : List (HeaderTransport.Wire (code := old)))
 (receiver : Fin old.sites) (index : Nat)
 (row : StageTrace.Record (code := PaidInvocationSource.code old contract))
 (previous : HeaderReception.Receiver (code := old)) : HeaderReception.Receiver (code := old) :=
 let candidate := match StageTransport.admission row with
  | some event => match event.val with
    | .deliver serial => issued.find? (fun wire => wire.serial == serial)
    | _ => none
  | none => none
 let verdict := match candidate with
  | none => AttestationReception.VerdictData.rejected .missingWire
  | some wire => checkIssued contract law issued receiver row
    (previous.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire
 ⟨match verdict with
   | .accepted wire => previous.receipts ++ [⟨wire,index,row.cursor.cut⟩]
   | .rejected _ => previous.receipts,
  previous.audit ++ [(row.cursor.cut,candidate,verdict)]⟩

theorem receiveIssued_is_the_original_source_receiver
 (receiver : Fin old.sites) (index : Nat)
 (row : StageTrace.Record (code := PaidInvocationSource.code old contract))
 (previous : HeaderReception.Receiver (code := old)) :
 receiveIssued contract law (HeaderTransport.wires vocabulary origin past) receiver index row previous =
 receive contract vocabulary law origin past receiver index row previous := by
 unfold receiveIssued receive incoming check
 rfl

def runIssued (issued : List (HeaderTransport.Wire (code := old))) (receiver : Fin old.sites)
 (initial : HeaderReception.Receiver (code := old))
 (rows : Nat → StageTrace.Record (code := PaidInvocationSource.code old contract)) : Nat → HeaderReception.Receiver (code := old) :=
 Nat.rec initial fun index previous => receiveIssued contract law issued receiver index (rows index) previous

def run {enabled accept : Bool}
 (answer : PaidOriginQueue.Ready old contract origin past enabled accept)
 (receiver : Fin old.sites) (initial : HeaderReception.Receiver (code := old)) : Nat → HeaderReception.Receiver (code := old) :=
 Nat.rec initial fun index previous => receive contract vocabulary law origin past receiver index (answer.row index) previous

theorem runIssued_is_the_original_generated_receiver {enabled accept : Bool}
 (answer : PaidOriginQueue.Ready old contract origin past enabled accept)
 (receiver : Fin old.sites) (initial : HeaderReception.Receiver (code := old)) (count : Nat) :
 run contract vocabulary law origin past answer receiver initial count =
 runIssued contract law (HeaderTransport.wires vocabulary origin past) receiver initial answer.row count := by
 induction count with
 | zero => rfl
 | succ index ih =>
  change receive contract vocabulary law origin past receiver index (answer.row index)
   (run contract vocabulary law origin past answer receiver initial index) = _
  rw [ih]
  exact (receiveIssued_is_the_original_source_receiver contract vocabulary law origin past receiver index (answer.row index) _).symm

theorem all_receipts_keep_their_original_paid_source {enabled accept : Bool}
 (answer : PaidOriginQueue.Ready old contract origin past enabled accept)
 (receiver : Fin old.sites) (initial : HeaderReception.Receiver (code := old))
 (validInitial : ∀ receipt ∈ initial.receipts,receipt.wire.ballot ∈ StageBudget.ledger vocabulary origin past)
 (count : Nat) : ∀ receipt ∈ (run contract vocabulary law origin past answer receiver initial count).receipts,
 receipt.wire.ballot ∈ StageBudget.ledger vocabulary origin past := by
 induction count with
 | zero => exact validInitial
 | succ index ih =>
   intro receipt inside
   change receipt ∈ (receive contract vocabulary law origin past receiver index (answer.row index)
    (run contract vocabulary law origin past answer receiver initial index)).receipts at inside
   unfold receive at inside
   dsimp only at inside
   split at inside
   · rename_i wire outcome
     rcases List.mem_append.mp inside with previous | fresh
     · exact ih receipt previous
     · cases List.mem_singleton.mp fresh
       cases candidate : incoming contract vocabulary origin past (answer.row index) with
       | none => simp only [candidate] at outcome; contradiction
       | some body =>
         simp only [candidate] at outcome
         obtain ⟨rfl,_⟩ := check_sound contract vocabulary law origin past receiver (answer.row index) _ body wire outcome
         exact an_accepted_successor_receipt_retains_the_original_issued_ballot
          contract vocabulary law origin past receiver (answer.row index) _ wire outcome
   · exact ih receipt inside

variable (previousLaw : StageReception.Law old)
def observed {enabled accept : Bool}
 (answer : PaidOriginQueue.Ready old contract origin past enabled accept) (receiver : Fin old.sites) :=
 run contract vocabulary law origin past answer receiver
  (HeaderReception.run vocabulary previousLaw origin past receiver past.length) answer.count

theorem every_observed_receipt_has_its_original_paid_ballot {enabled accept : Bool}
 (answer : PaidOriginQueue.Ready old contract origin past enabled accept) (receiver : Fin old.sites)
 (receipt : HeaderReception.Receipt (code := old))
 (inside : receipt ∈ (observed contract vocabulary law origin past previousLaw answer receiver).receipts) :
 receipt.wire.ballot ∈ StageBudget.ledger vocabulary origin past :=
 all_receipts_keep_their_original_paid_source contract vocabulary law origin past answer receiver _
  (HeaderReception.receipt_has_original_paid_ballot vocabulary previousLaw origin past receiver past.length)
  answer.count receipt inside

theorem actual_supporter_has_the_original_source {enabled accept : Bool}
 (answer : PaidOriginQueue.Ready old contract origin past enabled accept) (receiver : Fin old.sites)
 (scope : Scope) (value : Bool) (actor : Party)
 (inside : actor ∈ ActorQuorum.support (observed contract vocabulary law origin past previousLaw answer receiver) scope value) :
 ∃ ballot ∈ StageBudget.ledger vocabulary origin past,
 ballot.actor = actor ∧ ballot.scope = scope ∧ ballot.choice = value := by
 obtain ⟨key,member,owner⟩ := (ActorQuorum.mem_support_iff _ scope value actor).mp inside
 obtain ⟨receipt,present,sameScope,choice,sameKey⟩ := (StageQuorum.mem_support_iff _ scope value key).mp member
 have original := every_observed_receipt_has_its_original_paid_ballot
  contract vocabulary law origin past previousLaw answer receiver receipt present
 have signed := ActorEnvelope.actual_ballot_retains_the_original_actor vocabulary origin past _ original
 exact ⟨receipt.wire.ballot,original,by rw [signed,sameKey,owner],sameScope,choice⟩

def produce {enabled accept : Bool}
 (answer : PaidOriginQueue.Ready old contract origin past enabled accept)
 (receiver : Fin old.sites) (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
 if ¬ (ActorEnvelope.roster origin.source).card + ActorStageEnvelope.budget origin vocabulary past scope < threshold+threshold then
  .blocked .unsafeSourceBudget
 else match ActorQuorum.readout (observed contract vocabulary law origin past previousLaw answer receiver) scope threshold with
  | .blocked => .blocked .missingQuorum
  | .decided value => .decided value

theorem produced_decision_consumes_the_original_source_budget {enabled accept : Bool}
 (answer : PaidOriginQueue.Ready old contract origin past enabled accept)
 (receiver : Fin old.sites) (scope : Scope) (threshold : Nat) (value : Bool)
 (done : produce contract vocabulary law origin past previousLaw answer receiver scope threshold = .decided value) :
 (ActorEnvelope.roster origin.source).card + ActorStageEnvelope.budget origin vocabulary past scope < threshold+threshold ∧
 ActorQuorum.readout (observed contract vocabulary law origin past previousLaw answer receiver) scope threshold = .decided value := by
 unfold produce at done
 split at done <;> try contradiction
 rename_i safe
 split at done <;> try contradiction
 rename_i result found
 cases done
 exact ⟨of_not_not safe,found⟩

theorem produced_decisions_agree_across_paid_successors
 {leftEnabled leftAccept rightEnabled rightAccept : Bool}
 (leftAnswer : PaidOriginQueue.Ready old contract origin past leftEnabled leftAccept)
 (rightAnswer : PaidOriginQueue.Ready old contract origin past rightEnabled rightAccept)
 (left right : Fin old.sites) (scope : Scope) (threshold : Nat) (a b : Bool)
 (one : produce contract vocabulary law origin past previousLaw leftAnswer left scope threshold = .decided a)
 (two : produce contract vocabulary law origin past previousLaw rightAnswer right scope threshold = .decided b) : a = b := by
 have first := produced_decision_consumes_the_original_source_budget contract vocabulary law origin past previousLaw leftAnswer left scope threshold a one
 have second := produced_decision_consumes_the_original_source_budget contract vocabulary law origin past previousLaw rightAnswer right scope threshold b two
 by_contra different
 let leftObserved := observed contract vocabulary law origin past previousLaw leftAnswer left
 let rightObserved := observed contract vocabulary law origin past previousLaw rightAnswer right
 have roster (answer : PaidOriginQueue.Ready old contract origin past leftEnabled leftAccept)
  (receiver : Fin old.sites) (value : Bool) :
  ActorQuorum.support (observed contract vocabulary law origin past previousLaw answer receiver) scope value ⊆ ActorEnvelope.roster origin.source := by
  intro actor member
  obtain ⟨key,_,owned⟩ := (ActorQuorum.mem_support_iff _ scope value actor).mp member
  exact Finset.mem_image.mpr ⟨key,Finset.mem_univ _,owned⟩
 have rightRoster : ActorQuorum.support rightObserved scope b ⊆ ActorEnvelope.roster origin.source := by
  intro actor member
  obtain ⟨key,_,owned⟩ := (ActorQuorum.mem_support_iff _ scope b actor).mp member
  exact Finset.mem_image.mpr ⟨key,Finset.mem_univ _,owned⟩
 have exposed : ActorQuorum.support leftObserved scope a ∩ ActorQuorum.support rightObserved scope b ⊆
   ActorStageEnvelope.affected origin vocabulary past scope := by
  intro actor member
  obtain ⟨x,xOrigin,xActor,xScope,xValue⟩ := actual_supporter_has_the_original_source
   contract vocabulary law origin past previousLaw leftAnswer left scope a actor (Finset.mem_inter.mp member).1
  obtain ⟨y,yOrigin,yActor,yScope,yValue⟩ := actual_supporter_has_the_original_source
   contract vocabulary law origin past previousLaw rightAnswer right scope b actor (Finset.mem_inter.mp member).2
  have affected := ActorStageEnvelope.conflicting_actual_aliases_or_cuts_spend_one_affected_identity
   origin vocabulary past scope x y xOrigin yOrigin (xActor.trans yActor.symm) xScope yScope
   (by intro same; exact different (xValue.symm.trans (same.trans yValue)))
  simpa only [xActor] using affected
 have overlap := Finset.card_le_card exposed
 have union := Finset.card_le_card (Finset.union_subset (roster leftAnswer left a) rightRoster)
 change (ActorQuorum.support leftObserved scope a ∪ ActorQuorum.support rightObserved scope b).card ≤
  (ActorEnvelope.roster origin.source).card at union
 have count := Finset.card_union_add_card_inter (ActorQuorum.support leftObserved scope a) (ActorQuorum.support rightObserved scope b)
 have leftSupport := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ first.2).2
 have rightSupport := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ second.2).2
 have safe := first.1
 unfold ActorStageEnvelope.budget at safe
 change threshold ≤ (ActorQuorum.support leftObserved scope a).card at leftSupport
 change threshold ≤ (ActorQuorum.support rightObserved scope b).card at rightSupport
 omega

theorem an_accepted_generated_delivery_is_in_the_actual_final_native_inventory {enabled accept : Bool}
 (answer : PaidOriginQueue.Ready old contract origin past enabled accept)
 (receiver : Fin old.sites) (index : Nat) (bounded : index < answer.count)
 (seen : List (Nat × Nat)) (wire : HeaderTransport.Wire (code := old))
 (accepted : check contract vocabulary law origin past receiver (answer.row index) seen wire = .accepted wire) :
 StageReception.delivered (answer.row index) wire.serial = true ∧
 ((Financial.inventoryAt answer.final.source.input
   (ProgrammeHistory.visitAt answer.final.source.input (EventStep.boundary (answer.row index).cursor))).filterMap
   (Financial.InstructionOrigin.instruction? answer.final.source.input)) = StageTrace.items (answer.row index) := by
 refine ⟨(check_sound contract vocabulary law origin past receiver (answer.row index) seen wire wire accepted).2.1,?_⟩
 exact StageTrace.final_financial_inventory_is_the_original_record_items answer.start answer.stages
  (answer.row index) (List.mem_of_getElem? (OriginQueue.row_at_its_actual_index
   (PaidOriginQueue.lifted old contract origin) answer.start answer.protocols answer.count index bounded))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginHeader
