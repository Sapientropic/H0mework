import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EncodingAgreement

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorEnvelope
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def roster : Finset Party := Finset.univ.image source.code.siteParty

-- Capability is pooled over every key owned by this source identity, including different keys.
def choices (scope : Scope) (actor : Party) : Finset Bool :=
  Finset.univ.filter fun value => ∃ key : Fin source.code.sites,
    source.code.siteParty key = actor ∧ value ∈ InterfaceDeviationEnvelope.choices source vocabulary scope key

def affected (scope : Scope) : Finset Party :=
  (roster source).filter fun actor => false ∈ choices source vocabulary scope actor ∧
    true ∈ choices source vocabulary scope actor

abbrev budget (scope : Scope) := (affected source vocabulary scope).card

theorem mem_choices_iff (scope : Scope) (actor : Party) (value : Bool) :
    value ∈ choices source vocabulary scope actor ↔ ∃ key : Fin source.code.sites,
      source.code.siteParty key = actor ∧ value ∈ InterfaceDeviationEnvelope.choices source vocabulary scope key := by
  simp only [choices,Finset.mem_filter,Finset.mem_univ,true_and]

theorem every_pooled_choice_has_an_actual_source_request
    (scope : Scope) (actor : Party) (value : Bool) (inside : value ∈ choices source vocabulary scope actor) :
    ∃ key : Fin source.code.sites, source.code.siteParty key = actor ∧
      ∃ request ∈ source.code.actions, DeviationBudget.labelFor source vocabulary key request = some (scope,value) := by
  obtain ⟨key,owner,possible⟩ := (mem_choices_iff source vocabulary scope actor value).mp inside
  exact ⟨key,owner,InterfaceDeviationEnvelope.every_interface_choice_has_a_registered_request source vocabulary scope key value possible⟩

variable {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

theorem classified_actor_is_the_original_key_owner
    (cut position : Nat) (key : Fin source.code.sites)
    (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument)
    (body : OwnedAttestation.Ballot source)
    (made : OwnedAttestation.classify source vocabulary cut position key item = .attested body) :
    body.actor = source.code.siteParty body.key := by
  unfold OwnedAttestation.classify at made
  split at made <;> try contradiction
  dsimp only at made
  split_ifs at made
  cases OwnedAttestation.OutcomeData.attested.inj made
  rfl

theorem actual_ballot_retains_the_original_actor
    (start : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (body : StageBudget.Ballot (code := code)) (inside : body ∈ StageBudget.ledger vocabulary start stages) :
    body.actor = code.siteParty body.key := by
  obtain ⟨row,_,position,made⟩ := StageBudget.ledger_origin vocabulary start stages body inside
  unfold StageBudget.issued at made
  split at made <;> try contradiction
  rename_i ballot classified
  cases Option.some.inj made
  unfold StageBudget.outcome at classified
  split at classified <;> try contradiction
  split at classified <;> try contradiction
  exact classified_actor_is_the_original_key_owner row.cursor.source vocabulary _ _ _ _ _ classified

theorem every_actual_ballot_consumes_its_actors_source_capability
    (start : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (body : StageBudget.Ballot (code := code)) (inside : body ∈ StageBudget.ledger vocabulary start stages) :
    body.actor ∈ roster start.source ∧ body.choice ∈ choices start.source vocabulary body.scope body.actor := by
  have owner := actual_ballot_retains_the_original_actor vocabulary start stages body inside
  refine ⟨Finset.mem_image.mpr ⟨body.key,Finset.mem_univ _,owner.symm⟩,?_⟩
  exact (mem_choices_iff start.source vocabulary body.scope body.actor body.choice).mpr
    ⟨body.key,owner.symm,InterfaceDeviationEnvelope.every_actual_ballot_is_in_the_source_generated_interface vocabulary start stages body inside⟩

theorem conflicting_actual_ballots_expose_an_affected_actor_even_across_distinct_keys
    (start : Cursor code) (left right : List (EventHistory.Stage (code := code))) (scope : Scope)
    (one two : StageBudget.Ballot (code := code))
    (first : one ∈ StageBudget.ledger vocabulary start left) (second : two ∈ StageBudget.ledger vocabulary start right)
    (sameActor : one.actor = two.actor) (scopeOne : one.scope = scope) (scopeTwo : two.scope = scope)
    (different : one.choice ≠ two.choice) : one.actor ∈ affected start.source vocabulary scope := by
  obtain ⟨member,a⟩ := every_actual_ballot_consumes_its_actors_source_capability vocabulary start left one first
  have b := (every_actual_ballot_consumes_its_actors_source_capability vocabulary start right two second).2
  rw [scopeOne] at a
  rw [scopeTwo,← sameActor] at b
  apply Finset.mem_filter.mpr
  refine ⟨member,?_⟩
  cases firstChoice : one.choice <;> cases secondChoice : two.choice <;> simp_all

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorEnvelope
