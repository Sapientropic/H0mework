import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.DomainReuse

/-!
# Cross-domain ProcessGame reuse regression

Concrete economic admissions and biological divisions generate their actor
lineages only through exact occurrence-trace witnesses.  The multi-agent case
reuses the canonical three-agent source and exposure without constructing a
second process occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace DomainReuseRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DomainReuse

/-! ## Economic coalition admission -/

def firstAdmission : Economic.AdmissionEvent := ⟨10⟩
def secondAdmission : Economic.AdmissionEvent := ⟨20⟩

def coalitionSource : Economic.Source :=
  ⟨[firstAdmission, secondAdmission]⟩

def coalitionGame :
    _root_.SaturationMonoid.ProcessGame Economic.occurrenceOf :=
  Economic.processGame coalitionSource

def firstAdmissionSeed :
    SourceSeed Economic.occurrenceOf Economic.AdmissionEvent Economic.seedAt
      coalitionSource :=
  Economic.sourceSeed coalitionSource firstAdmission (by simp [coalitionSource])

def secondAdmissionSeed :
    SourceSeed Economic.occurrenceOf Economic.AdmissionEvent Economic.seedAt
      coalitionSource :=
  Economic.sourceSeed coalitionSource secondAdmission (by simp [coalitionSource])

def firstCoalitionMember : Economic.GeneratedCoalitionMember coalitionSource :=
  generatedActorOf coalitionGame Economic.AdmissionEvent Economic.seedAt
    Economic.CoalitionLineage Economic.lineageOf firstAdmissionSeed

def secondCoalitionMember : Economic.GeneratedCoalitionMember coalitionSource :=
  generatedActorOf coalitionGame Economic.AdmissionEvent Economic.seedAt
    Economic.CoalitionLineage Economic.lineageOf secondAdmissionSeed

theorem economic_source_compiles_exact_admission_trace :
    coalitionGame.occurrence.trace =
      [.opened, .admitted firstAdmission, .admitted secondAdmission] := by
  rfl

theorem economic_seeds_have_exact_trace_witnesses :
    (∃ state ∈ coalitionGame.occurrence.trace,
        Economic.seedAt coalitionSource state firstAdmission) ∧
      (∃ state ∈ coalitionGame.occurrence.trace,
        Economic.seedAt coalitionSource state secondAdmission) :=
  ⟨firstAdmissionSeed.2, secondAdmissionSeed.2⟩

theorem economic_generated_actor_image_is_admission_lineage :
    firstCoalitionMember.admission = firstAdmission ∧
      secondCoalitionMember.admission = secondAdmission :=
  ⟨rfl, rfl⟩

theorem distinct_admissions_generate_distinct_coalition_members :
    firstCoalitionMember ≠ secondCoalitionMember := by
  intro equalMembers
  have equalAdmissions := congrArg
    Economic.GeneratedCoalitionMember.admission equalMembers
  rw [economic_generated_actor_image_is_admission_lineage.1,
    economic_generated_actor_image_is_admission_lineage.2] at equalAdmissions
  exact (by decide : firstAdmission ≠ secondAdmission) equalAdmissions

theorem every_economic_actor_is_an_exact_seed_image
    (member : Economic.GeneratedCoalitionMember coalitionSource) :
    ∃ seed : SourceSeed Economic.occurrenceOf Economic.AdmissionEvent
        Economic.seedAt coalitionSource,
      member = generatedActorOf coalitionGame Economic.AdmissionEvent
        Economic.seedAt Economic.CoalitionLineage Economic.lineageOf seed :=
  generatedActor_exhaustive coalitionGame Economic.AdmissionEvent
    Economic.seedAt Economic.CoalitionLineage Economic.lineageOf member

theorem economic_closed_fold_value_is_source_admissions :
    (Economic.admissionFoldReadout coalitionSource).value =
      [firstAdmission, secondAdmission] := by
  rfl

theorem economic_core_fold_unique
    (candidate : RootedAccountedUnfolding Economic.State →
      List Economic.AdmissionEvent)
    (commutes : ∀ origin branches,
      candidate (.occur origin branches) =
        Economic.admissionFoldAlgebra origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate coalitionGame.occurrence = [firstAdmission, secondAdmission] := by
  calc
    candidate coalitionGame.occurrence =
        (Economic.admissionFoldReadout coalitionSource).value := by
      simpa [coalitionGame] using
        Economic.candidate_eq_admissionFold coalitionSource candidate commutes
    _ = [firstAdmission, secondAdmission] :=
      economic_closed_fold_value_is_source_admissions

/-! ## Biological division ancestry -/

def firstDivision : Biological.DivisionEvent := ⟨0, 1⟩
def secondDivision : Biological.DivisionEvent := ⟨1, 2⟩

def divisionSource : Biological.Source :=
  ⟨[firstDivision, secondDivision]⟩

def divisionGame :
    _root_.SaturationMonoid.ProcessGame Biological.occurrenceOf :=
  Biological.processGame divisionSource

def firstDivisionSeed :
    SourceSeed Biological.occurrenceOf Biological.DivisionEvent Biological.seedAt
      divisionSource :=
  Biological.sourceSeed divisionSource firstDivision (by simp [divisionSource])

def secondDivisionSeed :
    SourceSeed Biological.occurrenceOf Biological.DivisionEvent Biological.seedAt
      divisionSource :=
  Biological.sourceSeed divisionSource secondDivision (by simp [divisionSource])

def firstAncestryIndividual :
    Biological.GeneratedAncestryIndividual divisionSource :=
  generatedActorOf divisionGame Biological.DivisionEvent Biological.seedAt
    Biological.AncestryLineage Biological.lineageOf firstDivisionSeed

def secondAncestryIndividual :
    Biological.GeneratedAncestryIndividual divisionSource :=
  generatedActorOf divisionGame Biological.DivisionEvent Biological.seedAt
    Biological.AncestryLineage Biological.lineageOf secondDivisionSeed

theorem biological_source_compiles_exact_division_trace :
    divisionGame.occurrence.trace =
      [.organism, .divided firstDivision, .divided secondDivision] := by
  rfl

theorem biological_seeds_have_exact_trace_witnesses :
    (∃ state ∈ divisionGame.occurrence.trace,
        Biological.seedAt divisionSource state firstDivision) ∧
      (∃ state ∈ divisionGame.occurrence.trace,
        Biological.seedAt divisionSource state secondDivision) :=
  ⟨firstDivisionSeed.2, secondDivisionSeed.2⟩

theorem biological_generated_actor_image_is_ancestry_lineage :
    firstAncestryIndividual.division = firstDivision ∧
      secondAncestryIndividual.division = secondDivision ∧
      firstAncestryIndividual.division.child = 1 ∧
      secondAncestryIndividual.division.parent = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem distinct_divisions_generate_distinct_linked_ancestry_individuals :
    firstAncestryIndividual ≠ secondAncestryIndividual ∧
      firstAncestryIndividual.division.child =
        secondAncestryIndividual.division.parent := by
  constructor
  · intro equalIndividuals
    have equalDivisions := congrArg
      Biological.GeneratedAncestryIndividual.division equalIndividuals
    rw [biological_generated_actor_image_is_ancestry_lineage.1,
      biological_generated_actor_image_is_ancestry_lineage.2.1] at equalDivisions
    exact (by decide : firstDivision ≠ secondDivision) equalDivisions
  · rfl

theorem biological_child_lineage_retains_exact_trace_witness :
    firstAncestryIndividual.division.child = 1 ∧
      ∃ state ∈ divisionGame.occurrence.trace,
        Biological.seedAt divisionSource state
          firstAncestryIndividual.division := by
  refine ⟨rfl, ?_⟩
  change ∃ state ∈ divisionGame.occurrence.trace,
    Biological.seedAt divisionSource state firstDivision
  exact firstDivisionSeed.2

theorem every_biological_actor_is_an_exact_seed_image
    (individual : Biological.GeneratedAncestryIndividual divisionSource) :
    ∃ seed : SourceSeed Biological.occurrenceOf Biological.DivisionEvent
        Biological.seedAt divisionSource,
      individual = generatedActorOf divisionGame Biological.DivisionEvent
        Biological.seedAt Biological.AncestryLineage Biological.lineageOf seed :=
  generatedActor_exhaustive divisionGame Biological.DivisionEvent
    Biological.seedAt Biological.AncestryLineage Biological.lineageOf individual

theorem biological_closed_fold_value_is_source_divisions :
    (Biological.divisionFoldReadout divisionSource).value =
      [firstDivision, secondDivision] := by
  rfl

theorem biological_core_fold_unique
    (candidate : RootedAccountedUnfolding Biological.State →
      List Biological.DivisionEvent)
    (commutes : ∀ origin branches,
      candidate (.occur origin branches) =
        Biological.divisionFoldAlgebra origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate divisionGame.occurrence = [firstDivision, secondDivision] := by
  calc
    candidate divisionGame.occurrence =
        (Biological.divisionFoldReadout divisionSource).value := by
      simpa [divisionGame] using
        Biological.candidate_eq_divisionFold divisionSource candidate commutes
    _ = [firstDivision, secondDivision] :=
      biological_closed_fold_value_is_source_divisions

/-! ## Multi-agent interaction reuses the canonical three-agent source -/

def interactionSeed0 := MultiAgent.sourceSeed ThreeCycleTime.t0
def interactionSeed1 := MultiAgent.sourceSeed ThreeCycleTime.t1
def interactionSeed2 := MultiAgent.sourceSeed ThreeCycleTime.t2

def interactionActor0 : MultiAgent.GeneratedInteractionActor :=
  generatedActorOf threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
    MultiAgent.InteractionLineage MultiAgent.lineageOf interactionSeed0

def interactionActor1 : MultiAgent.GeneratedInteractionActor :=
  generatedActorOf threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
    MultiAgent.InteractionLineage MultiAgent.lineageOf interactionSeed1

def interactionActor2 : MultiAgent.GeneratedInteractionActor :=
  generatedActorOf threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
    MultiAgent.InteractionLineage MultiAgent.lineageOf interactionSeed2

theorem multi_agent_reuses_canonical_three_agent_occurrence :
    threeAgentProcessGame.source = () ∧
      threeAgentProcessGame.occurrence = threeAgentExposure :=
  ⟨rfl, threeAgentProcessGame_occurrence_eq_exposure⟩

theorem multi_agent_seeds_have_exact_trace_witnesses :
    (∃ state ∈ threeAgentExposure.trace,
        MultiAgent.seedAt () state .t0) ∧
      (∃ state ∈ threeAgentExposure.trace,
        MultiAgent.seedAt () state .t1) ∧
      (∃ state ∈ threeAgentExposure.trace,
        MultiAgent.seedAt () state .t2) :=
  ⟨interactionSeed0.2, interactionSeed1.2, interactionSeed2.2⟩

theorem multi_agent_generated_actor_image_is_three_exposed_lineages :
    interactionActor0.agent = .t0 ∧
      interactionActor1.agent = .t1 ∧
      interactionActor2.agent = .t2 :=
  ⟨rfl, rfl, rfl⟩

theorem multi_agent_three_actors_are_pairwise_distinct :
    interactionActor0 ≠ interactionActor1 ∧
      interactionActor0 ≠ interactionActor2 ∧
      interactionActor1 ≠ interactionActor2 := by
  have images := multi_agent_generated_actor_image_is_three_exposed_lineages
  constructor
  · intro equalActors
    have equalAgents := congrArg MultiAgent.GeneratedInteractionActor.agent
      equalActors
    rw [images.1, images.2.1] at equalAgents
    cases equalAgents
  · constructor
    · intro equalActors
      have equalAgents := congrArg MultiAgent.GeneratedInteractionActor.agent
        equalActors
      rw [images.1, images.2.2] at equalAgents
      cases equalAgents
    · intro equalActors
      have equalAgents := congrArg MultiAgent.GeneratedInteractionActor.agent
        equalActors
      rw [images.2.1, images.2.2] at equalAgents
      cases equalAgents

theorem every_multi_agent_actor_is_an_exact_seed_image
    (actor : MultiAgent.GeneratedInteractionActor) :
    ∃ seed : SourceSeed threeAgentOccurrenceOf ThreeCycleTime
        MultiAgent.seedAt (),
      actor = generatedActorOf threeAgentProcessGame ThreeCycleTime
        MultiAgent.seedAt MultiAgent.InteractionLineage MultiAgent.lineageOf seed :=
  generatedActor_exhaustive threeAgentProcessGame ThreeCycleTime
    MultiAgent.seedAt MultiAgent.InteractionLineage MultiAgent.lineageOf actor

theorem canonical_three_actors_exhaust_all_generated_interaction_actors
    (actor : MultiAgent.GeneratedInteractionActor) :
    actor = interactionActor0 ∨
      actor = interactionActor1 ∨ actor = interactionActor2 := by
  rcases every_multi_agent_actor_is_an_exact_seed_image actor with
    ⟨seed, rfl⟩
  cases seedValue : seed.1 with
  | t0 =>
      left
      have seedEq : seed = interactionSeed0 := by
        apply Subtype.ext
        exact seedValue
      subst seed
      rfl
  | t1 =>
      right
      left
      have seedEq : seed = interactionSeed1 := by
        apply Subtype.ext
        exact seedValue
      subst seed
      rfl
  | t2 =>
      right
      right
      have seedEq : seed = interactionSeed2 := by
        apply Subtype.ext
        exact seedValue
      subst seed
      rfl

theorem multi_agent_reuses_canonical_three_agent_fold :
    (threeAgentFoldReadout threeCyclePhaseCochain).value = (2 : Int) := by
  rw [threeAgentFoldReadout_value_eq_ringResidual]
  decide

theorem multi_agent_canonical_fold_generates_P116_P117_H1 :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        threeCyclePhaseCochain ∧
      ¬ PathAdditive threeCyclePhaseCochain := by
  have nonzero :
      (threeAgentFoldReadout threeCyclePhaseCochain).value ≠ (0 : Int) := by
    rw [multi_agent_reuses_canonical_three_agent_fold]
    decide
  exact ⟨threeAgentFoldReadout_nonzero_h1 threeCyclePhaseCochain nonzero,
    threeAgentFoldReadout_nonzero_not_pathAdditive
      threeCyclePhaseCochain nonzero⟩

theorem multi_agent_core_fold_unique
    (candidate : RootedAccountedUnfolding ThreeAgentFoldPoint → Int)
    (commutes : ∀ origin branches,
      candidate (.occur origin branches) =
        threeAgentAlgebra threeCyclePhaseCochain origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate threeAgentExposure =
      (threeAgentFoldReadout threeCyclePhaseCochain).value :=
  threeAgentFoldReadout_candidate_unique
    threeCyclePhaseCochain candidate commutes

end DomainReuseRegression
end Regression
end ProcessGame
end SaturationMonoid
