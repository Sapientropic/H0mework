import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedQuorumRun
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedDeliveryConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedQuorumConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource ArchivedQuorumSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
 (law : StageReception.Law bound.source.code) (genesis : Cursor bound.source.code)
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat)

abbrev final := ArchivedQuorumRun.after bound base law genesis state slot receiver scope threshold
abbrev endpoint := (final bound base law genesis state slot receiver scope threshold).current bound genesis

theorem every_generated_decision_has_its_original_received_actors_and_safety_budget
 (value : Bool)
 (done : ArchivedQuorumRun.produce bound base law genesis state slot receiver scope threshold=.decided value) :
 ∃ origin, (final bound base law genesis state slot receiver scope threshold).archive[slot]?=some origin ∧
  (ActorEnvelope.roster origin.origin.source).card+
   ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope < threshold+threshold ∧
  0<threshold ∧ threshold ≤ (ActorQuorum.support
   (RecursiveSigningReception.observed bound base law genesis
    (final bound base law genesis state slot receiver scope threshold) origin receiver) scope value).card := by
 unfold ArchivedQuorumRun.produce at done
 split at done <;> try contradiction
 obtain ⟨origin,located,safe,decision⟩ :=
  RecursiveSigningReception.a_produced_decision_has_its_actual_archived_source_and_quorum
   bound base law genesis _ slot receiver scope threshold value done
 exact ⟨origin,located,safe,ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ decision⟩

theorem every_actual_supporting_actor_returns_to_the_same_final_native_inventory
 (origin : Segment bound)
 (located : (final bound base law genesis state slot receiver scope threshold).archive[slot]?=some origin)
 (value : Bool) (actor : Party)
 (support : actor ∈ ActorQuorum.support
  (RecursiveSigningReception.observed bound base law genesis
   (final bound base law genesis state slot receiver scope threshold) origin receiver) scope value) :
 ∃ receipt ∈ (RecursiveSigningReception.observed bound base law genesis
   (final bound base law genesis state slot receiver scope threshold) origin receiver).receipts,
  receipt.wire.ballot.actor=actor ∧ receipt.wire.ballot.scope=scope ∧ receipt.wire.ballot.choice=value ∧
  ∃ row ∈ (final bound base law genesis state slot receiver scope threshold).rows bound genesis, ∃ position,
   StageBudget.issued (origin.vocabulary bound base) row position=some receipt.wire.ballot ∧
   (Financial.inventoryAt (endpoint bound base law genesis state slot receiver scope threshold).source.input
    (ProgrammeHistory.visitAt (endpoint bound base law genesis state slot receiver scope threshold).source.input
     (EventStep.boundary row.cursor))).filterMap
    (Financial.InstructionOrigin.instruction? (endpoint bound base law genesis state slot receiver scope threshold).source.input)=
    StageTrace.items row := by
 obtain ⟨receipt,inside,paid,owner,sameScope,choice⟩ :=
  RecursiveSigningReception.a_cumulative_supporter_has_its_original_paid_ballot
   bound base law genesis _ origin receiver scope value actor support
 obtain ⟨row,member,position,issued⟩ := StageBudget.ledger_origin _ _ _ receipt.wire.ballot paid
 have actual := an_archived_row_is_in_the_actual_cumulative_history bound genesis _ origin
  (List.mem_of_getElem? located) row member
 exact ⟨receipt,inside,owner,sameScope,choice,row,actual,position,issued,
  StageTrace.final_financial_inventory_is_the_original_record_items genesis _ row actual⟩

theorem a_zero_threshold_cannot_generate_a_source_offer :
 offer bound base genesis state slot receiver scope 0=.blocked .missingQuorum := by
 unfold offer
 split <;> simp only [ite_true]

theorem fewer_original_sent_actors_cannot_generate_an_offer
 (short : ∀ origin, state.archive[slot]?=some origin →
  ∀ value, (sentActors bound base origin receiver scope value).card<threshold)
 (value : Bool) : offer bound base genesis state slot receiver scope threshold≠.offered value := by
 intro accepted
 obtain ⟨origin,located,_,_,enough⟩ :=
  an_offer_computes_its_original_sent_actors_and_safety_budget bound base genesis state slot receiver scope threshold value accepted
 have scarce := short origin located value
 omega

theorem repeated_source_keys_of_one_owner_count_at_most_one_actor
 (origin : Segment bound) (value : Bool) (owner : Party)
 (aliases : ∀ key, bound.source.code.siteParty key=owner) :
 (sentActors bound base origin receiver scope value).card≤1 := by
 have subset : sentActors bound base origin receiver scope value ⊆ {owner} := by
  intro actor member
  obtain ⟨wire,_,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact Finset.mem_singleton.mpr (same.symm.trans (aliases wire.ballot.key))
 simpa only [Finset.card_singleton] using Finset.card_le_card subset

theorem deleting_the_original_archive_blocks_the_producer
 (missing : state.archive[slot]?=none) :
 ArchivedQuorumRun.produce bound base law genesis state slot receiver scope threshold=.blocked .missingQuorum ∧
 final bound base law genesis state slot receiver scope threshold=state := by
 simp only [ArchivedQuorumRun.produce,ArchivedQuorumRun.after,offer,missing,final,and_self]

theorem the_generated_endpoint_keeps_original_ledger_and_own_next :
 ArchivedDeliveryConsumer.NativeContinuation bound
  ((final bound base law genesis state slot receiver scope threshold).current bound genesis) := by
 unfold ArchivedDeliveryConsumer.NativeContinuation
 exact (WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
  bound ((final bound base law genesis state slot receiver scope threshold).current bound genesis)).2.2.2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedQuorumConsumer
