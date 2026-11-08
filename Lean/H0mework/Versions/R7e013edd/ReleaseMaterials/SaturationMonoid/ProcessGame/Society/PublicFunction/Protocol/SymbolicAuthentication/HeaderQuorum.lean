import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderReception

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderQuorum
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev observed (law : StageReception.Law code) (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) :=
  HeaderReception.run vocabulary law start stages receiver stages.length

theorem actual_supporter_has_its_verified_native_origin
    (law : StageReception.Law code) (stages : List (EventHistory.Stage (code := code)))
    (receiver : Fin code.sites) (scope : Scope) (value : Bool) (actor : Party)
    (inside : actor ∈ ActorQuorum.support (observed start vocabulary law stages receiver) scope value) :
    ∃ receipt ∈ (observed start vocabulary law stages receiver).receipts,
      receipt.wire.ballot ∈ StageBudget.ledger vocabulary start stages ∧
      receipt.wire.ballot.actor = actor ∧ receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = value := by
  obtain ⟨key,member,owner⟩ := (ActorQuorum.mem_support_iff _ scope value actor).mp inside
  obtain ⟨receipt,present,sameScope,choice,sameKey⟩ := (StageQuorum.mem_support_iff _ scope value key).mp member
  have origin := HeaderReception.receipt_has_original_paid_ballot vocabulary law start stages receiver stages.length receipt present
  have exactActor := ActorEnvelope.actual_ballot_retains_the_original_actor vocabulary start stages _ origin
  exact ⟨receipt,present,origin,by rw [exactActor,sameKey,owner],sameScope,choice⟩

theorem every_received_identity_is_in_the_original_roster
    (law : StageReception.Law code) (stages : List (EventHistory.Stage (code := code)))
    (receiver : Fin code.sites) (scope : Scope) (value : Bool) :
    ActorQuorum.support (observed start vocabulary law stages receiver) scope value ⊆ ActorEnvelope.roster start.source := by
  intro actor member
  obtain ⟨key,_,owner⟩ := (ActorQuorum.mem_support_iff _ scope value actor).mp member
  exact Finset.mem_image.mpr ⟨key,Finset.mem_univ _,owner⟩

theorem conflicting_received_actors_are_in_the_same_actual_source_envelope
    (leftLaw rightLaw : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (a b : Bool) (different : a ≠ b) :
    ActorQuorum.support (observed start vocabulary leftLaw stages left) scope a ∩
      ActorQuorum.support (observed start vocabulary rightLaw stages right) scope b ⊆
        ActorStageEnvelope.affected start vocabulary stages scope := by
  intro actor member
  obtain ⟨one,_,first,actorOne,scopeOne,valueOne⟩ := actual_supporter_has_its_verified_native_origin start vocabulary
    leftLaw stages left scope a actor (Finset.mem_inter.mp member).1
  obtain ⟨two,_,second,actorTwo,scopeTwo,valueTwo⟩ := actual_supporter_has_its_verified_native_origin start vocabulary
    rightLaw stages right scope b actor (Finset.mem_inter.mp member).2
  have exposed := ActorStageEnvelope.conflicting_actual_aliases_or_cuts_spend_one_affected_identity start vocabulary
    stages scope one.wire.ballot two.wire.ballot first second (actorOne.trans actorTwo.symm)
    scopeOne scopeTwo (by intro same;exact different (valueOne.symm.trans (same.trans valueTwo)))
  simpa only [actorOne] using exposed

theorem decisions_from_one_actual_execution_agree_across_receivers_and_laws
    (leftLaw rightLaw : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : ActorQuorum.readout (observed start vocabulary leftLaw stages left) scope threshold = .decided a)
    (two : ActorQuorum.readout (observed start vocabulary rightLaw stages right) scope threshold = .decided b)
    (safe : (ActorEnvelope.roster start.source).card + ActorStageEnvelope.budget start vocabulary stages scope < threshold + threshold) : a = b := by
  by_contra different
  have first := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ one).2
  have second := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ two).2
  have overlap := Finset.card_le_card (conflicting_received_actors_are_in_the_same_actual_source_envelope start vocabulary
    leftLaw rightLaw stages left right scope a b different)
  have union := Finset.card_le_card (Finset.union_subset
    (every_received_identity_is_in_the_original_roster start vocabulary leftLaw stages left scope a)
    (every_received_identity_is_in_the_original_roster start vocabulary rightLaw stages right scope b))
  have count := Finset.card_union_add_card_inter
    (ActorQuorum.support (observed start vocabulary leftLaw stages left) scope a)
    (ActorQuorum.support (observed start vocabulary rightLaw stages right) scope b)
  unfold ActorStageEnvelope.budget at safe
  dsimp only [observed] at *
  omega

-- The executable gate derives its budget from actual source work, not receiver evidence.
def produce (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
  if ¬ (ActorEnvelope.roster start.source).card + ActorStageEnvelope.budget start vocabulary stages scope < threshold + threshold then
    .blocked .unsafeSourceBudget
  else match ActorQuorum.readout (observed start vocabulary law stages receiver) scope threshold with
    | .blocked => .blocked .missingQuorum
    | .decided value => .decided value

theorem a_produced_decision_keeps_the_actual_identity_budget_and_distinct_actor_quorum
    (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (done : produce start vocabulary law stages receiver scope threshold = .decided value) :
    (ActorEnvelope.roster start.source).card + ActorStageEnvelope.budget start vocabulary stages scope < threshold + threshold ∧
      ActorQuorum.readout (observed start vocabulary law stages receiver) scope threshold = .decided value ∧
      0 < threshold ∧ threshold ≤ (ActorQuorum.support (observed start vocabulary law stages receiver) scope value).card := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i safe
  split at done <;> try contradiction
  rename_i answer found
  cases done
  exact ⟨of_not_not safe,found,ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ found⟩

theorem produced_decisions_agree
    (leftLaw rightLaw : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites) (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : produce start vocabulary leftLaw stages left scope threshold = .decided a)
    (two : produce start vocabulary rightLaw stages right scope threshold = .decided b) : a = b := by
  have first := a_produced_decision_keeps_the_actual_identity_budget_and_distinct_actor_quorum start vocabulary _ _ _ _ _ _ one
  have second := a_produced_decision_keeps_the_actual_identity_budget_and_distinct_actor_quorum start vocabulary _ _ _ _ _ _ two
  exact decisions_from_one_actual_execution_agree_across_receivers_and_laws start vocabulary
    leftLaw rightLaw stages left right scope threshold a b first.2.1 second.2.1 first.1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.HeaderQuorum
