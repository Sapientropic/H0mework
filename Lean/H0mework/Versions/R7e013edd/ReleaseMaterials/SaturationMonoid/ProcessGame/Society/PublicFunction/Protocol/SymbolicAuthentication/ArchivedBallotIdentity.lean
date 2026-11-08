import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliveryProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedBallotIdentity
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

theorem actual_record_cut_is_injective (cursor : Cursor code)
 (stages : List (EventHistory.Stage (code := code)))
 (first second : StageTrace.Record (code := code))
 (one : first ∈ StageTrace.records cursor stages) (two : second ∈ StageTrace.records cursor stages)
 (same : first.cursor.cut=second.cursor.cut) : first=second := by
 have unique : ((StageTrace.records cursor stages).map (fun row => row.cursor.cut)).Nodup := by
  rw [StageTrace.no_occurrence_is_lost_or_duplicated]
  exact List.nodup_range.map (by
   intro a b equal
   change cursor.cut+a=cursor.cut+b at equal
   omega)
 exact List.inj_on_of_nodup_map unique one two same

-- A birth pair is an identity only inside the same immutable issuing context.
theorem one_original_birth_has_one_ballot
 (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
 (first second : StageBudget.Ballot (code := code))
 (one : first ∈ StageBudget.ledger vocabulary cursor stages)
 (two : second ∈ StageBudget.ledger vocabulary cursor stages)
 (birth : (first.cut,first.position)=(second.cut,second.position)) : first=second := by
 obtain ⟨left,leftIn,a,firstMade⟩ := StageBudget.ledger_origin vocabulary cursor stages first one
 obtain ⟨right,rightIn,b,secondMade⟩ := StageBudget.ledger_origin vocabulary cursor stages second two
 obtain ⟨_,_,_,_,_,_,_,_,_,firstCut,firstPosition,_⟩ :=
  StageBudget.issued_has_an_owned_valid_paid_origin vocabulary left a first firstMade
 obtain ⟨_,_,_,_,_,_,_,_,_,secondCut,secondPosition,_⟩ :=
  StageBudget.issued_has_an_owned_valid_paid_origin vocabulary right b second secondMade
 have sameRow := actual_record_cut_is_injective cursor stages left right leftIn rightIn
  (firstCut.symm.trans ((congrArg Prod.fst birth).trans secondCut))
 have samePosition := firstPosition.symm.trans ((congrArg Prod.snd birth).trans secondPosition)
 subst right
 rw [← samePosition] at secondMade
 exact Option.some.inj (firstMade.symm.trans secondMade)

variable (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code) (genesis : Cursor bound.source.code)

theorem an_original_wire_has_its_own_paid_ballot
 (origin : Segment bound) (wire : HeaderTransport.Wire (code := bound.source.code))
 (sent : wire ∈ origin.wires bound base) :
 wire.ballot ∈ StageBudget.ledger (origin.vocabulary bound base) origin.origin origin.stages := by
 have verified : HeaderTransport.verify (origin.vocabulary bound base) origin.origin origin.stages wire=true :=
  decide_eq_true sent
 obtain ⟨_,_,_,_,_,_,_,paid,_⟩ :=
  HeaderTransport.authenticated_wire_has_actual_send_and_paid_ballot _ _ _ wire verified
 exact paid

theorem emptied_receiver_obligations_recover_the_exact_original_ballot
 (state : State bound genesis) (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (empty : ArchivedDeliveryProgress.outstanding bound base law genesis state origin receiver=∅)
 (wire : HeaderTransport.Wire (code := bound.source.code))
 (sent : wire ∈ origin.wires bound base) (address : wire.recipient=receiver) :
 ∃ receipt ∈ (RecursiveSigningReception.observed bound base law genesis state origin receiver).receipts,
  receipt.wire.ballot=wire.ballot := by
 have original : (wire.ballot.cut,wire.ballot.position) ∈
  (((origin.wires bound base).filter (fun body => decide (body.recipient=receiver))).map
   (fun body => (body.ballot.cut,body.ballot.position))).toFinset :=
  List.mem_toFinset.mpr (List.mem_map.mpr ⟨wire,List.mem_filter.mpr ⟨sent,decide_eq_true address⟩,rfl⟩)
 have seen : (wire.ballot.cut,wire.ballot.position) ∈
  ((ArchivedDeliverySource.previous bound base law genesis state receiver origin).receipts.map
   (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))).toFinset := by
  by_contra absent
  have missing := Finset.mem_sdiff.mpr ⟨original,absent⟩
  change (wire.ballot.cut,wire.ballot.position) ∈
   ArchivedDeliveryProgress.outstanding bound base law genesis state origin receiver at missing
  rw [empty] at missing
  exact Finset.notMem_empty _ missing
 obtain ⟨receipt,inside,same⟩ := List.mem_map.mp (List.mem_toFinset.mp seen)
 have paid := RecursiveSigningReception.receipt_has_its_own_original_paid_ballot
  bound base law genesis state origin receiver receipt inside
 exact ⟨receipt,inside,one_original_birth_has_one_ballot _ _ _ receipt.wire.ballot wire.ballot paid
  (an_original_wire_has_its_own_paid_ballot bound base origin wire sent) same⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedBallotIdentity
