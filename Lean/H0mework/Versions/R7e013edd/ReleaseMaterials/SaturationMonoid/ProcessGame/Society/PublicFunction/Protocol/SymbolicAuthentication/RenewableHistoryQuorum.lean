import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryReception

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryQuorum
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource RenewableCodeLineage

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

abbrev begin := RenewableArchiveSource.initial bound genesis parent
abbrev Controller := RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument) → RenewableArchiveSource.Command
abbrev currentAt (control : Controller (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) := RenewableCodeLineage.currentAt contract (begin bound genesis parent) control

def rows (control : Controller (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (count : Nat) : List (RenewableCodeLineage.Row bound.source.code) :=
 (parent.rows bound genesis).map (pack Lineage.original)++
  (show List (RenewableCodeLineage.Row bound.source.code) from
   RenewableCodeLineage.history contract (begin bound genesis parent) control count)

def observed (control : Controller (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (count : Nat)
 (origin : Segment bound) (recipient : Fin bound.source.code.sites) :=
 RenewableHistoryReception.scan (origin.vocabulary bound base) (origin.law bound law)
  origin.origin origin.stages recipient (rows bound contract genesis parent control count) 0 ⟨[],[]⟩

theorem every_cumulative_receipt_keeps_its_original_paid_ballot
 (control : Controller (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (count : Nat) (origin : Segment bound) (recipient : Fin bound.source.code.sites)
 (receipt : HeaderReception.Receipt (code := bound.source.code))
 (inside : receipt∈(observed bound contract base law genesis parent control count origin recipient).receipts) :
 receipt.wire.ballot∈StageBudget.ledger (origin.vocabulary bound base) origin.origin origin.stages :=
 RenewableHistoryReception.all_received_ballots_keep_the_original_paid_issuing_ledger _ _ _ _ _ _ _ _
  (by simp) receipt inside

theorem every_cumulative_supporting_actor_has_its_original_source
 (control : Controller (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (count : Nat) (origin : Segment bound) (recipient : Fin bound.source.code.sites)
 (scope : Scope) (value : Bool) (actor : Party)
 (inside : actor∈ActorQuorum.support (observed bound contract base law genesis parent control count origin recipient) scope value) :
 ∃ receipt∈(observed bound contract base law genesis parent control count origin recipient).receipts,
  receipt.wire.ballot∈StageBudget.ledger (origin.vocabulary bound base) origin.origin origin.stages ∧
  receipt.wire.ballot.actor=actor ∧ receipt.wire.ballot.scope=scope ∧ receipt.wire.ballot.choice=value := by
 obtain ⟨key,member,owner⟩ := (ActorQuorum.mem_support_iff _ scope value actor).mp inside
 obtain ⟨receipt,present,sameScope,choice,sameKey⟩ := (StageQuorum.mem_support_iff _ scope value key).mp member
 have original := every_cumulative_receipt_keeps_its_original_paid_ballot bound contract base law genesis parent control count origin recipient receipt present
 have signed := ActorEnvelope.actual_ballot_retains_the_original_actor (origin.vocabulary bound base) origin.origin origin.stages _ original
 exact ⟨receipt,present,original,by rw [signed,sameKey,owner],sameScope,choice⟩

theorem cumulative_receipts_locate_the_actual_heterogeneous_row
 (control : Controller (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (count : Nat) (origin : Segment bound) (recipient : Fin bound.source.code.sites)
 (receipt : HeaderReception.Receipt (code := bound.source.code))
 (inside : receipt∈(observed bound contract base law genesis parent control count origin recipient).receipts) :
 ∃ row, (rows bound contract genesis parent control count)[receipt.index]?=some row ∧
  receipt.delivery=row.material.cursor.cut ∧ ∃ seen,
   RenewableHistoryReception.check (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages
    recipient row seen receipt.wire=.accepted receipt.wire := by
 rcases RenewableHistoryReception.every_received_receipt_locates_its_actual_descendant_row
  (origin.vocabulary bound base) (origin.law bound law) origin.origin origin.stages recipient
  (rows bound contract genesis parent control count) 0 ⟨[],[]⟩ receipt inside with impossible | located
 · simp at impossible
 · obtain ⟨index,row,found,whereFrom,delivery,seen,checked⟩ := located
   simp only [Nat.zero_add] at whereFrom
   exact ⟨row,by rw [whereFrom];exact found,delivery,seen,checked⟩

theorem all_old_receipts_survive_the_next_actual_command
 (control : Controller (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (count : Nat) (origin : Segment bound) (recipient : Fin bound.source.code.sites) :
 (observed bound contract base law genesis parent control count origin recipient).receipts <+:
 (observed bound contract base law genesis parent control (count+1) origin recipient).receipts := by
 have actual : rows bound contract genesis parent control (count+1)=
  rows bound contract genesis parent control count++
   (show List (RenewableCodeLineage.Row bound.source.code) from
    commandRows contract (begin bound genesis parent) control count) := by
  exact (List.append_assoc ((parent.rows bound genesis).map (pack Lineage.original))
   (show List (RenewableCodeLineage.Row bound.source.code) from
    RenewableCodeLineage.history contract (begin bound genesis parent) control count)
   (show List (RenewableCodeLineage.Row bound.source.code) from
    commandRows contract (begin bound genesis parent) control count)).symm
 unfold observed
 rw [actual,RenewableHistoryReception.scan_append]
 exact RenewableHistoryReception.scan_keeps_all_prior_receipts _ _ _ _ _ _ _ _

def decideAt (control : Controller (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (count : Nat)
 (origin : Segment bound) (recipient : Fin bound.source.code.sites) (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
 if ¬(ActorEnvelope.roster origin.origin.source).card+
   ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope<threshold+threshold then
  .blocked .unsafeSourceBudget
 else match ActorQuorum.readout (observed bound contract base law genesis parent control count origin recipient) scope threshold with
 | .blocked => .blocked .missingQuorum
 | .decided value => .decided value

def produce (control : Controller (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (count slot : Nat)
 (recipient : Fin bound.source.code.sites) (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
 match parent.archive[slot]? with
 | none => .blocked .missingQuorum
 | some origin => decideAt bound contract base law genesis parent control count origin recipient scope threshold

theorem a_decision_computes_its_original_budget_and_received_identities
 (control : Controller (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (count : Nat) (origin : Segment bound) (recipient : Fin bound.source.code.sites) (scope : Scope) (threshold : Nat) (value : Bool)
 (done : decideAt bound contract base law genesis parent control count origin recipient scope threshold=.decided value) :
 (ActorEnvelope.roster origin.origin.source).card+
  ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope<threshold+threshold ∧
 0<threshold ∧ threshold≤(ActorQuorum.support
  (observed bound contract base law genesis parent control count origin recipient) scope value).card := by
 unfold decideAt at done
 split at done <;> try contradiction
 rename_i safe
 split at done <;> try contradiction
 rename_i result selected
 cases done
 exact ⟨of_not_not safe,ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ selected⟩

theorem original_source_decisions_agree_across_arbitrarily_many_actual_windows
 (leftControl rightControl : Controller (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
 (leftCount rightCount : Nat) (origin : Segment bound) (left right : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat) (a b : Bool)
 (first : decideAt bound contract base law genesis parent leftControl leftCount origin left scope threshold=.decided a)
 (second : decideAt bound contract base law genesis parent rightControl rightCount origin right scope threshold=.decided b) : a=b := by
 obtain ⟨safe,_,one⟩ := a_decision_computes_its_original_budget_and_received_identities bound contract base law genesis parent _ _ _ _ _ _ _ first
 obtain ⟨_,_,two⟩ := a_decision_computes_its_original_budget_and_received_identities bound contract base law genesis parent _ _ _ _ _ _ _ second
 by_contra different
 let A := ActorQuorum.support (observed bound contract base law genesis parent leftControl leftCount origin left) scope a
 let B := ActorQuorum.support (observed bound contract base law genesis parent rightControl rightCount origin right) scope b
 have overlap : A∩B ⊆ ActorStageEnvelope.affected origin.origin (origin.vocabulary bound base) origin.stages scope := by
  intro actor member
  obtain ⟨r,_,rPaid,rActor,rScope,rChoice⟩ := every_cumulative_supporting_actor_has_its_original_source bound contract base law genesis parent leftControl leftCount origin left scope a actor (Finset.mem_inter.mp member).1
  obtain ⟨s,_,sPaid,sActor,sScope,sChoice⟩ := every_cumulative_supporting_actor_has_its_original_source bound contract base law genesis parent rightControl rightCount origin right scope b actor (Finset.mem_inter.mp member).2
  have affected := ActorStageEnvelope.conflicting_actual_aliases_or_cuts_spend_one_affected_identity origin.origin
   (origin.vocabulary bound base) origin.stages scope r.wire.ballot s.wire.ballot rPaid sPaid
   (rActor.trans sActor.symm) rScope sScope (by intro same;exact different (rChoice.symm.trans (same.trans sChoice)))
  simpa only [rActor] using affected
 have subset (observed : HeaderReception.Receiver (code := bound.source.code)) (value : Bool) :
  ActorQuorum.support observed scope value ⊆ ActorEnvelope.roster origin.origin.source := by
   intro actor member
   obtain ⟨key,_,owner⟩ := (ActorQuorum.mem_support_iff _ scope value actor).mp member
   exact Finset.mem_image.mpr ⟨key,Finset.mem_univ _,owner⟩
 have unionBound := Finset.card_le_card (Finset.union_subset
  (subset (observed bound contract base law genesis parent leftControl leftCount origin left) a)
  (subset (observed bound contract base law genesis parent rightControl rightCount origin right) b))
 have intersectionBound := Finset.card_le_card overlap
 have count := Finset.card_union_add_card_inter A B
 change threshold≤A.card at one
 change threshold≤B.card at two
 change (A∪B).card≤_ at unionBound
 unfold ActorStageEnvelope.budget at safe
 omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableHistoryQuorum
