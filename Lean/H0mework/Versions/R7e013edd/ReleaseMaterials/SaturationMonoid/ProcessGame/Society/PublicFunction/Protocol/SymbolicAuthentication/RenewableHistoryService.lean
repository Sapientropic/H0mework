import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryQuorum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryService
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource RenewableCodeLineage RenewableHistoryQuorum

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

abbrev current := RenewableHistoryQuorum.currentAt bound contract genesis parent control count
def row (input : LocalCommandSource.Input) : RenewableCodeLineage.Row bound.source.code :=
 pack (lineageAt contract (begin bound genesis parent) control count)
  ((LocalCommandSource.observe (current bound contract genesis parent control count).model
    (current bound contract genesis parent control count).point input).row
    (current bound contract genesis parent control count).model)

def review (input : LocalCommandSource.Input) : HeaderReception.Verdict (code := bound.source.code) :=
 match parent.archive[slot]? with
 | none => .rejected .missingWire
 | some origin => match RenewableHistoryReception.incoming (origin.vocabulary bound base) origin.origin origin.stages
    (row bound contract genesis parent control count input) with
   | none => .rejected .missingWire
   | some wire => RenewableHistoryReception.check (origin.vocabulary bound base) (origin.law bound law)
     origin.origin origin.stages recipient (row bound contract genesis parent control count input)
     ((observed bound contract base law genesis parent control count origin recipient).receipts.map
      fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire

def available (input : LocalCommandSource.Input) : Bool :=
 match review bound contract base law genesis parent control count slot recipient input with
 | .accepted _ => true
 | .rejected _ => false

structure Service where
 private mk ::
 input : LocalCommandSource.Input
 registered : input∈CommandWindowSource.menu (current bound contract genesis parent control count).model
 accepted : available bound contract base law genesis parent control count slot recipient input=true

inductive Result where
 | served (service : Service bound contract base law genesis parent control count slot recipient)
 | blocked (absent : ∀ input∈CommandWindowSource.menu (current bound contract genesis parent control count).model,
    available bound contract base law genesis parent control count slot recipient input=false)

def produce : Result bound contract base law genesis parent control count slot recipient :=
 match found : (CommandWindowSource.menu (current bound contract genesis parent control count).model).find?
  (available bound contract base law genesis parent control count slot recipient) with
 | some input => .served ⟨input,List.mem_of_find?_eq_some found,List.find?_some found⟩
 | none => .blocked (by
   intro input member
   simpa only [Bool.not_eq_true] using (List.find?_eq_none.mp found) input member)

def after (service : Service bound contract base law genesis parent control count slot recipient) :=
 RenewableArchiveSource.execute (current bound contract genesis parent control count) [service.input]

theorem actual_source_opportunities_generate_service
 (input : LocalCommandSource.Input)
 (registered : input∈CommandWindowSource.menu (current bound contract genesis parent control count).model)
 (opportunity : available bound contract base law genesis parent control count slot recipient input=true) :
 ∃ service, produce bound contract base law genesis parent control count slot recipient=.served service := by
 cases result : produce bound contract base law genesis parent control count slot recipient with
 | served service => exact ⟨service,rfl⟩
 | blocked absent =>
   have impossible := absent input registered
   rw [opportunity] at impossible
   contradiction

theorem every_generated_service_keeps_the_actual_old_source
 (service : Service bound contract base law genesis parent control count slot recipient) :
 ∃ origin wire, parent.archive[slot]?=some origin ∧
 RenewableHistoryReception.incoming (origin.vocabulary bound base) origin.origin origin.stages
  (row bound contract genesis parent control count service.input)=some wire ∧
 RenewableHistoryReception.check (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages
  recipient (row bound contract genesis parent control count service.input)
  ((observed bound contract base law genesis parent control count origin recipient).receipts.map
   fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire=.accepted wire := by
 have accepted := service.accepted
 cases located : parent.archive[slot]? with
 | none => simp only [available,review,located] at accepted; contradiction
 | some origin =>
   cases found : RenewableHistoryReception.incoming (origin.vocabulary bound base) origin.origin origin.stages
    (row bound contract genesis parent control count service.input) with
   | none => simp only [available,review,located,found] at accepted; contradiction
   | some wire =>
     simp only [available,review,located,found] at accepted
     split at accepted <;> try contradiction
     rename_i result checked
     have same := (RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ checked).1
     subst result
     exact ⟨origin,wire,rfl,found,checked⟩

def receivedAfter (origin : Segment bound)
 (service : Service bound contract base law genesis parent control count slot recipient) :=
 RenewableHistoryReception.scan (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages
  recipient (RenewableHistoryQuorum.rows bound contract genesis parent control count++
   [row bound contract genesis parent control count service.input]) 0 ⟨[],[]⟩

theorem generated_service_appends_its_next_actual_receipt
 (service : Service bound contract base law genesis parent control count slot recipient) :
 ∃ origin wire, parent.archive[slot]?=some origin ∧
 (receivedAfter bound contract base law genesis parent control count slot recipient origin service).receipts=
  (observed bound contract base law genesis parent control count origin recipient).receipts++
  [⟨wire,(RenewableHistoryQuorum.rows bound contract genesis parent control count).length,
    (row bound contract genesis parent control count service.input).material.cursor.cut⟩] ∧
 (wire.ballot.cut,wire.ballot.position)∉
  (observed bound contract base law genesis parent control count origin recipient).receipts.map
   (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) := by
 obtain ⟨origin,wire,located,found,checked⟩ :=
  every_generated_service_keeps_the_actual_old_source bound contract base law genesis parent control count slot recipient service
 have sound := RenewableHistoryReception.check_sound _ _ _ _ _ _ _ _ _ checked
 refine ⟨origin,wire,located,?_,sound.2.2.2.2.2.2.2.2.2⟩
 unfold receivedAfter
 rw [RenewableHistoryReception.scan_append]
 change (RenewableHistoryReception.receive _ _ _ _ _ _
  (0+(RenewableHistoryQuorum.rows bound contract genesis parent control count).length)
  (observed bound contract base law genesis parent control count origin recipient)).receipts=_
 simp only [Nat.zero_add,RenewableHistoryReception.receive,found,checked]

theorem the_selected_input_is_the_actual_new_execution_row
 (service : Service bound contract base law genesis parent control count slot recipient) :
 (RenewableArchiveSource.fresh (current bound contract genesis parent control count) [service.input]).rows
  (current bound contract genesis parent control count).model=
 [(row bound contract genesis parent control count service.input).actual] := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryService
