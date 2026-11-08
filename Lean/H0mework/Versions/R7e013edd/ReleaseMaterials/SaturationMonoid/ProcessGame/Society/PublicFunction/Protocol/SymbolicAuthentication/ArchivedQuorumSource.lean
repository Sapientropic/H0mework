import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedBallotIdentity

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedQuorumSource
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

-- This is computed from actual owned sends, before receiver completion.
def sentActors (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (value : Bool) : Finset Party :=
 ((origin.wires bound base).filter (fun wire => decide
  (wire.recipient=receiver ∧ wire.ballot.scope=scope ∧ wire.ballot.choice=value))).map
   (fun wire => bound.source.code.siteParty wire.ballot.key) |>.toFinset

theorem completed_original_wires_supply_distinct_actual_receiver_support
 (state : State bound genesis) (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (empty : outstanding bound base law genesis state origin receiver=∅) (scope : Scope) (value : Bool) :
 sentActors bound base origin receiver scope value ⊆
 ActorQuorum.support (RecursiveSigningReception.observed bound base law genesis state origin receiver) scope value := by
 intro actor member
 obtain ⟨wire,member,owner⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
 obtain ⟨sent,properties⟩ := List.mem_filter.mp member
 obtain ⟨address,sameScope,choice⟩ := of_decide_eq_true properties
 obtain ⟨receipt,received,ballot⟩ :=
  ArchivedBallotIdentity.emptied_receiver_obligations_recover_the_exact_original_ballot
   bound base law genesis state origin receiver empty wire sent address
 apply (ActorQuorum.mem_support_iff _ scope value actor).mpr
 refine ⟨wire.ballot.key,(StageQuorum.mem_support_iff _ scope value _).mpr ?_,owner⟩
 exact ⟨receipt,received,by rw [ballot];exact sameScope,by rw [ballot];exact choice,by rw [ballot]⟩

private theorem actual_support_values_agree
 (state : State bound genesis) (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat) (a b : Bool)
 (safe : (ActorEnvelope.roster origin.origin.source).card+
  ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope < threshold+threshold)
 (one : threshold ≤ (ActorQuorum.support
  (RecursiveSigningReception.observed bound base law genesis state origin receiver) scope a).card)
 (two : threshold ≤ (ActorQuorum.support
  (RecursiveSigningReception.observed bound base law genesis state origin receiver) scope b).card) : a=b := by
 by_contra different
 have overlap := Finset.card_le_card
  (RecursiveSigningReception.conflicting_cumulative_support_spends_the_original_affected_identity
   bound base law genesis state origin receiver receiver scope a b different)
 have roster (value : Bool) : ActorQuorum.support
  (RecursiveSigningReception.observed bound base law genesis state origin receiver) scope value ⊆
  ActorEnvelope.roster origin.origin.source := by
  intro actor member
  obtain ⟨key,_,owner⟩ := (ActorQuorum.mem_support_iff _ scope value actor).mp member
  exact Finset.mem_image.mpr ⟨key,Finset.mem_univ _,owner⟩
 have union := Finset.card_le_card (Finset.union_subset (roster a) (roster b))
 have count := Finset.card_union_add_card_inter
  (ActorQuorum.support (RecursiveSigningReception.observed bound base law genesis state origin receiver) scope a)
  (ActorQuorum.support (RecursiveSigningReception.observed bound base law genesis state origin receiver) scope b)
 unfold ActorStageEnvelope.budget at safe
 omega

theorem actual_safe_support_generates_the_original_decision
 (state : State bound genesis) (origin : Segment bound) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat) (value : Bool) (positive : 0<threshold)
 (safe : (ActorEnvelope.roster origin.origin.source).card+
  ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope < threshold+threshold)
 (enough : threshold ≤ (ActorQuorum.support
  (RecursiveSigningReception.observed bound base law genesis state origin receiver) scope value).card) :
 ActorQuorum.readout (RecursiveSigningReception.observed bound base law genesis state origin receiver)
  scope threshold=.decided value := by
 have nonzero : threshold≠0 := by omega
 cases value with
 | false => simp only [ActorQuorum.readout,if_neg nonzero,List.find?_cons,decide_eq_true enough]
 | true =>
  have exclude : ¬ threshold ≤ (ActorQuorum.support
   (RecursiveSigningReception.observed bound base law genesis state origin receiver) scope false).card := by
   intro opposite
   have impossible := actual_support_values_agree bound base law genesis state origin receiver scope threshold false true safe opposite enough
   contradiction
  simp only [ActorQuorum.readout,if_neg nonzero,List.find?_cons,decide_eq_false exclude,decide_eq_true enough]

inductive Offer where
 | offered (value : Bool)
 | blocked (reason : ProspectiveQuorum.Obstruction)
 deriving DecidableEq

def offer (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat) : Offer :=
 match state.archive[slot]? with
 | none => .blocked .missingQuorum
 | some origin =>
  if threshold=0 then .blocked .missingQuorum else
  if ¬ (ActorEnvelope.roster origin.origin.source).card+
   ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope < threshold+threshold then
   .blocked .unsafeSourceBudget
  else match [false,true].find? (fun value => decide
   (threshold ≤ (sentActors bound base origin receiver scope value).card)) with
   | none => .blocked .missingQuorum
   | some value => .offered value

theorem an_offer_computes_its_original_sent_actors_and_safety_budget
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat) (value : Bool)
 (selected : offer bound base genesis state slot receiver scope threshold=.offered value) :
 ∃ origin, state.archive[slot]?=some origin ∧ 0<threshold ∧
  (ActorEnvelope.roster origin.origin.source).card+
   ActorStageEnvelope.budget origin.origin (origin.vocabulary bound base) origin.stages scope < threshold+threshold ∧
  threshold ≤ (sentActors bound base origin receiver scope value).card := by
 unfold offer at selected
 split at selected <;> try contradiction
 rename_i origin located
 split at selected <;> try contradiction
 rename_i positive
 split at selected <;> try contradiction
 rename_i safe
 split at selected <;> try contradiction
 rename_i chosen found
 cases selected
 exact ⟨origin,located,by omega,of_not_not safe,of_decide_eq_true
  (List.find?_some (p := fun choice => decide (threshold ≤ (sentActors bound base origin receiver scope choice).card)) found)⟩

theorem original_offer_and_completed_reception_generate_a_decision
 (state : State bound genesis) (slot : Nat) (receiver : Fin bound.source.code.sites)
 (scope : Scope) (threshold : Nat) (value : Bool)
 (selected : offer bound base genesis state slot receiver scope threshold=.offered value)
 (complete : ∀ origin, state.archive[slot]?=some origin →
  outstanding bound base law genesis state origin receiver=∅) :
 RecursiveSigningReception.produce bound base law genesis state slot receiver scope threshold=.decided value := by
 obtain ⟨origin,located,positive,safe,enough⟩ :=
  an_offer_computes_its_original_sent_actors_and_safety_budget bound base genesis state slot receiver scope threshold value selected
 have supported := Finset.card_le_card
  (completed_original_wires_supply_distinct_actual_receiver_support bound base law genesis state origin receiver
   (complete origin located) scope value)
 have decision := actual_safe_support_generates_the_original_decision
  bound base law genesis state origin receiver scope threshold value positive safe (Nat.le_trans enough supported)
 simp only [RecursiveSigningReception.produce,located,if_neg (not_not.mpr safe),decision]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ArchivedQuorumSource
