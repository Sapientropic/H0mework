import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedQuorumSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedQuorumRun
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

theorem each_service_run_keeps_the_original_archive_index
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (origin : Segment bound) (located : state.archive[slot]?=some origin) (count : Nat) :
 (ArchivedDeliveryProgress.run bound base law genesis state slot receiver count).archive[slot]?=some origin := by
 induction count with
 | zero => exact located
 | succ count ih =>
  change (step bound base law genesis (ArchivedDeliveryProgress.run bound base law genesis state slot receiver count) slot receiver).archive[slot]?=_
  unfold step
  cases produce bound base law genesis (ArchivedDeliveryProgress.run bound base law genesis state slot receiver count) slot receiver with
  | blocked => exact ih
  | served service => exact an_archived_origin_keeps_its_index bound genesis _ slot service.input origin ih

theorem each_service_run_keeps_all_original_receipts
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (origin : Segment bound) (count : Nat) :
 (RecursiveSigningReception.observed bound base law genesis state origin receiver).receipts <+:
 (RecursiveSigningReception.observed bound base law genesis
  (ArchivedDeliveryProgress.run bound base law genesis state slot receiver count) origin receiver).receipts := by
 induction count with
 | zero => exact List.prefix_refl _
 | succ count ih =>
  apply ih.trans
  change _ <+: (RecursiveSigningReception.observed bound base law genesis
   (step bound base law genesis (ArchivedDeliveryProgress.run bound base law genesis state slot receiver count) slot receiver) origin receiver).receipts
  unfold step
  cases produce bound base law genesis (ArchivedDeliveryProgress.run bound base law genesis state slot receiver count) slot receiver with
  | blocked => exact List.prefix_refl _
  | served service =>
   exact RecursiveSigningReception.actual_later_rounds_preserve_all_old_receipts
    bound base law genesis _ origin receiver [service.input]

theorem service_runs_compose (state : State bound genesis) (slot : Nat)
 (receiver : Fin bound.source.code.sites) (first more : Nat) :
 ArchivedDeliveryProgress.run bound base law genesis state slot receiver (first+more)=
 ArchivedDeliveryProgress.run bound base law genesis (ArchivedDeliveryProgress.run bound base law genesis state slot receiver first) slot receiver more := by
 induction more with
 | zero => rfl
 | succ more ih => exact congrArg (fun current => step bound base law genesis current slot receiver) ih

theorem completed_original_receipts_stay_complete
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (origin : Segment bound) (empty : outstanding bound base law genesis state origin receiver=∅) (count : Nat) :
 outstanding bound base law genesis (ArchivedDeliveryProgress.run bound base law genesis state slot receiver count) origin receiver=∅ := by
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro birth missing
 obtain ⟨original,absent⟩ := Finset.mem_sdiff.mp missing
 have absentBefore : birth ∉ ((previous bound base law genesis state receiver origin).receipts.map
  (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))).toFinset := by
  intro present
  obtain ⟨receipt,member,same⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
  exact absent (List.mem_toFinset.mpr (List.mem_map.mpr ⟨receipt,
   (each_service_run_keeps_all_original_receipts bound base law genesis state slot receiver origin count).subset member,same⟩))
 have old : birth ∈ outstanding bound base law genesis state origin receiver :=
  Finset.mem_sdiff.mpr ⟨original,absentBefore⟩
 rw [empty] at old
 exact Finset.notMem_empty _ old

def Opportunities (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites) : Prop :=
 ∀ origin, state.archive[slot]?=some origin →
  ∀ count ≤ (outstanding bound base law genesis state origin receiver).card,
   (outstanding bound base law genesis (ArchivedDeliveryProgress.run bound base law genesis state slot receiver count) origin receiver).Nonempty →
   ∃ input ∈ CommandWindowSource.menu bound,
    available bound base law genesis (ArchivedDeliveryProgress.run bound base law genesis state slot receiver count) slot receiver input=true

theorem actual_opportunities_complete_reception_at_the_original_birth_bound
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (origin : Segment bound) (located : state.archive[slot]?=some origin)
 (services : Opportunities bound base law genesis state slot receiver) :
 outstanding bound base law genesis
  (ArchivedDeliveryProgress.run bound base law genesis state slot receiver (outstanding bound base law genesis state origin receiver).card)
  origin receiver=∅ := by
 obtain ⟨count,bounded,empty⟩ := explicit_source_opportunities_flush_the_original_receipt_obligations
  bound base law genesis state slot receiver origin located (services origin located)
 have resumed := service_runs_compose bound base law genesis state slot receiver count
  ((outstanding bound base law genesis state origin receiver).card-count)
 rw [Nat.add_sub_of_le bounded] at resumed
 rw [resumed]
 exact completed_original_receipts_stay_complete bound base law genesis _ slot receiver origin empty _

def horizon (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites) : Nat :=
 match state.archive[slot]? with
 | none => 0
 | some origin => (outstanding bound base law genesis state origin receiver).card

def after (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat) : State bound genesis :=
 match ArchivedQuorumSource.offer bound base genesis state slot receiver scope threshold with
 | .blocked _ => state
 | .offered _ => ArchivedDeliveryProgress.run bound base law genesis state slot receiver (horizon bound base law genesis state slot receiver)

def produce (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
 match ArchivedQuorumSource.offer bound base genesis state slot receiver scope threshold with
 | .blocked reason => .blocked reason
 | .offered _ => RecursiveSigningReception.produce bound base law genesis
   (after bound base law genesis state slot receiver scope threshold) slot receiver scope threshold

theorem original_sent_actor_offer_and_actual_service_opportunities_generate_quorum
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat) (value : Bool)
 (selected : ArchivedQuorumSource.offer bound base genesis state slot receiver scope threshold=.offered value)
 (services : Opportunities bound base law genesis state slot receiver) :
 produce bound base law genesis state slot receiver scope threshold=.decided value := by
 obtain ⟨origin,located,_,_,_⟩ :=
  ArchivedQuorumSource.an_offer_computes_its_original_sent_actors_and_safety_budget
   bound base genesis state slot receiver scope threshold value selected
 let final := ArchivedDeliveryProgress.run bound base law genesis state slot receiver
  (outstanding bound base law genesis state origin receiver).card
 have kept := each_service_run_keeps_the_original_archive_index bound base law genesis state slot receiver origin located
  (outstanding bound base law genesis state origin receiver).card
 change final.archive[slot]?=some origin at kept
 have offered : ArchivedQuorumSource.offer bound base genesis final slot receiver scope threshold=.offered value := by
  have same : ArchivedQuorumSource.offer bound base genesis final slot receiver scope threshold=
   ArchivedQuorumSource.offer bound base genesis state slot receiver scope threshold := by
   simp only [ArchivedQuorumSource.offer,kept,located]
  exact same.trans selected
 have complete : ∀ candidate, final.archive[slot]?=some candidate →
  outstanding bound base law genesis final candidate receiver=∅ := by
  intro candidate same
  have identical : candidate=origin := Option.some.inj (same.symm.trans kept)
  subst candidate
  exact actual_opportunities_complete_reception_at_the_original_birth_bound
   bound base law genesis state slot receiver origin located services
 have decided := ArchivedQuorumSource.original_offer_and_completed_reception_generate_a_decision
  bound base law genesis final slot receiver scope threshold value offered complete
 simpa only [produce,selected,after,horizon,located] using decided

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedQuorumRun
