import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorStageEnvelope

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorStageQuorum
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev observed := ActorQuorum.observed start vocabulary

theorem conflicting_received_actors_are_in_the_same_actual_source_envelope
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code))
    (leftLaw rightLaw : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (a b : Bool) (different : a ≠ b) :
    ActorQuorum.support (observed start vocabulary leftEncoding leftLaw stages left) scope a ∩
      ActorQuorum.support (observed start vocabulary rightEncoding rightLaw stages right) scope b ⊆
        ActorStageEnvelope.affected start vocabulary stages scope := by
  intro actor member
  obtain ⟨one,_,first,actorOne,scopeOne,valueOne⟩ := ActorQuorum.actual_supporter_has_its_verified_native_origin start vocabulary
    leftEncoding leftLaw stages left scope a actor (Finset.mem_inter.mp member).1
  obtain ⟨two,_,second,actorTwo,scopeTwo,valueTwo⟩ := ActorQuorum.actual_supporter_has_its_verified_native_origin start vocabulary
    rightEncoding rightLaw stages right scope b actor (Finset.mem_inter.mp member).2
  have exposed := ActorStageEnvelope.conflicting_actual_aliases_or_cuts_spend_one_affected_identity start vocabulary
    stages scope one.wire.ballot two.wire.ballot first second (actorOne.trans actorTwo.symm)
    scopeOne scopeTwo (by intro same;exact different (valueOne.symm.trans (same.trans valueTwo)))
  simpa only [actorOne] using exposed

theorem decisions_from_one_actual_execution_agree_across_receivers_encodings_and_laws
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code))
    (leftLaw rightLaw : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : ActorQuorum.readout (observed start vocabulary leftEncoding leftLaw stages left) scope threshold = .decided a)
    (two : ActorQuorum.readout (observed start vocabulary rightEncoding rightLaw stages right) scope threshold = .decided b)
    (safe : (ActorEnvelope.roster start.source).card + ActorStageEnvelope.budget start vocabulary stages scope < threshold + threshold) : a = b := by
  by_contra different
  have first := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ one).2
  have second := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ two).2
  have overlap := Finset.card_le_card (conflicting_received_actors_are_in_the_same_actual_source_envelope start vocabulary
    leftEncoding rightEncoding leftLaw rightLaw stages left right scope a b different)
  have union := Finset.card_le_card (Finset.union_subset
    (ActorQuorum.every_received_identity_is_in_the_original_roster start vocabulary leftEncoding leftLaw stages left scope a)
    (ActorQuorum.every_received_identity_is_in_the_original_roster start vocabulary rightEncoding rightLaw stages right scope b))
  have count := Finset.card_union_add_card_inter
    (ActorQuorum.support (observed start vocabulary leftEncoding leftLaw stages left) scope a)
    (ActorQuorum.support (observed start vocabulary rightEncoding rightLaw stages right) scope b)
  unfold ActorStageEnvelope.budget at safe
  dsimp only [observed] at *
  omega

-- The executable gate derives its budget from actual source work, not receiver evidence.
def produce (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
  if ¬ (ActorEnvelope.roster start.source).card + ActorStageEnvelope.budget start vocabulary stages scope < threshold + threshold then
    .blocked .unsafeSourceBudget
  else match ActorQuorum.readout (observed start vocabulary encoding law stages receiver) scope threshold with
    | .blocked => .blocked .missingQuorum
    | .decided value => .decided value

theorem a_produced_decision_keeps_the_actual_identity_budget_and_distinct_actor_quorum
    (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (done : produce start vocabulary encoding law stages receiver scope threshold = .decided value) :
    (ActorEnvelope.roster start.source).card + ActorStageEnvelope.budget start vocabulary stages scope < threshold + threshold ∧
      ActorQuorum.readout (observed start vocabulary encoding law stages receiver) scope threshold = .decided value ∧
      0 < threshold ∧ threshold ≤ (ActorQuorum.support (observed start vocabulary encoding law stages receiver) scope value).card := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i safe
  split at done <;> try contradiction
  rename_i answer found
  cases done
  exact ⟨of_not_not safe,found,ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ found⟩

theorem produced_decisions_agree
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code)) (leftLaw rightLaw : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites) (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : produce start vocabulary leftEncoding leftLaw stages left scope threshold = .decided a)
    (two : produce start vocabulary rightEncoding rightLaw stages right scope threshold = .decided b) : a = b := by
  have first := a_produced_decision_keeps_the_actual_identity_budget_and_distinct_actor_quorum start vocabulary _ _ _ _ _ _ _ one
  have second := a_produced_decision_keeps_the_actual_identity_budget_and_distinct_actor_quorum start vocabulary _ _ _ _ _ _ _ two
  exact decisions_from_one_actual_execution_agree_across_receivers_encodings_and_laws start vocabulary
    leftEncoding rightEncoding leftLaw rightLaw stages left right scope threshold a b first.2.1 second.2.1 first.1

theorem actual_prefix_support_agrees_when_the_common_history_pays_the_budget
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code)) (leftLaw rightLaw : StageReception.Law code)
    (leftStages rightStages common : List (EventHistory.Stage (code := code)))
    (leftPrefix : leftStages <+: common) (rightPrefix : rightStages <+: common)
    (left right : Fin code.sites) (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : ActorQuorum.readout (observed start vocabulary leftEncoding leftLaw leftStages left) scope threshold = .decided a)
    (two : ActorQuorum.readout (observed start vocabulary rightEncoding rightLaw rightStages right) scope threshold = .decided b)
    (safe : (ActorEnvelope.roster start.source).card + ActorStageEnvelope.budget start vocabulary common scope < threshold + threshold) : a = b := by
  by_contra different
  have cover : ∀ (past : List (EventHistory.Stage (code := code))), past <+: common → ∀ actor,
      ActorStageEnvelope.choices start vocabulary past scope actor ⊆ ActorStageEnvelope.choices start vocabulary common scope actor := by
    intro past ordered actor
    obtain ⟨more,same⟩ := ordered
    rw [← same]
    exact ActorStageEnvelope.actual_extension_preserves_every_installed_actor_choice start vocabulary past more scope actor
  have overlap : ActorQuorum.support (observed start vocabulary leftEncoding leftLaw leftStages left) scope a ∩
      ActorQuorum.support (observed start vocabulary rightEncoding rightLaw rightStages right) scope b ⊆
        ActorStageEnvelope.affected start vocabulary common scope := by
    intro actor member
    obtain ⟨first,_,firstOrigin,firstActor,firstScope,firstValue⟩ := ActorQuorum.actual_supporter_has_its_verified_native_origin start vocabulary
      leftEncoding leftLaw leftStages left scope a actor (Finset.mem_inter.mp member).1
    obtain ⟨second,_,secondOrigin,secondActor,secondScope,secondValue⟩ := ActorQuorum.actual_supporter_has_its_verified_native_origin start vocabulary
      rightEncoding rightLaw rightStages right scope b actor (Finset.mem_inter.mp member).2
    obtain ⟨roster,firstChoice⟩ := ActorStageEnvelope.every_actual_ballot_has_its_own_live_installed_source_word start vocabulary leftStages _ firstOrigin
    have secondChoice := (ActorStageEnvelope.every_actual_ballot_has_its_own_live_installed_source_word start vocabulary rightStages _ secondOrigin).2
    rw [firstActor,firstScope,firstValue] at firstChoice
    rw [secondActor,secondScope,secondValue] at secondChoice
    rw [firstActor] at roster
    have firstCommon := cover leftStages leftPrefix actor firstChoice
    have secondCommon := cover rightStages rightPrefix actor secondChoice
    apply Finset.mem_filter.mpr
    refine ⟨roster,?_⟩
    cases a <;> cases b <;> simp_all
  have first := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ one).2
  have second := (ActorQuorum.decision_has_positive_distinct_actor_support _ _ _ _ two).2
  have exposed := Finset.card_le_card overlap
  have union := Finset.card_le_card (Finset.union_subset
    (ActorQuorum.every_received_identity_is_in_the_original_roster start vocabulary leftEncoding leftLaw leftStages left scope a)
    (ActorQuorum.every_received_identity_is_in_the_original_roster start vocabulary rightEncoding rightLaw rightStages right scope b))
  have count := Finset.card_union_add_card_inter
    (ActorQuorum.support (observed start vocabulary leftEncoding leftLaw leftStages left) scope a)
    (ActorQuorum.support (observed start vocabulary rightEncoding rightLaw rightStages right) scope b)
  unfold ActorStageEnvelope.budget at safe
  dsimp only [observed] at *
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorStageQuorum
