import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.GeneratedActorInstances
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.DomainReuseRegression

/-!
# Cross-domain constructive generated-actor regression

Closed economic, biological and three-agent fixtures exercise the explicit
seed/actor equivalences.  The inverse seeds retain their original occurrence
trace proofs; no representative registry or classical inverse is used.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace Society
namespace CrossDomainGeneratedActorRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DomainReuse
open DomainReuseRegression
open _root_.SaturationMonoid.ProcessGame.Society

theorem economic_closed_seed_actor_equivalence :
    economicSeedActorEquiv coalitionSource firstAdmissionSeed =
        firstCoalitionMember ∧
      economicSeedActorEquiv coalitionSource secondAdmissionSeed =
        secondCoalitionMember ∧
      (economicSeedActorEquiv coalitionSource).symm firstCoalitionMember =
        firstAdmissionSeed ∧
      (economicSeedActorEquiv coalitionSource).symm secondCoalitionMember =
        secondAdmissionSeed :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem economic_closed_inverse_retains_trace_witness :
    ∃ state ∈ coalitionGame.occurrence.trace,
      Economic.seedAt coalitionSource state
        ((economicSeedActorEquiv coalitionSource).symm
          firstCoalitionMember).1 :=
  economic_inverse_seed_has_trace_witness coalitionSource firstCoalitionMember

theorem economic_closed_generic_bijective_consumer :
    Function.Bijective
      (generatedActorOf coalitionGame Economic.AdmissionEvent Economic.seedAt
        Economic.CoalitionLineage Economic.lineageOf) := by
  simpa [coalitionGame] using economic_generatedActorOf_bijective coalitionSource

theorem biological_closed_seed_actor_equivalence :
    biologicalSeedActorEquiv divisionSource firstDivisionSeed =
        firstAncestryIndividual ∧
      biologicalSeedActorEquiv divisionSource secondDivisionSeed =
        secondAncestryIndividual ∧
      (biologicalSeedActorEquiv divisionSource).symm firstAncestryIndividual =
        firstDivisionSeed ∧
      (biologicalSeedActorEquiv divisionSource).symm secondAncestryIndividual =
        secondDivisionSeed :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem biological_closed_inverse_retains_trace_witness :
    ∃ state ∈ divisionGame.occurrence.trace,
      Biological.seedAt divisionSource state
        ((biologicalSeedActorEquiv divisionSource).symm
          firstAncestryIndividual).1 :=
  biological_inverse_seed_has_trace_witness divisionSource
    firstAncestryIndividual

theorem biological_closed_generic_bijective_consumer :
    Function.Bijective
      (generatedActorOf divisionGame Biological.DivisionEvent Biological.seedAt
        Biological.AncestryLineage Biological.lineageOf) := by
  simpa [divisionGame] using biological_generatedActorOf_bijective divisionSource

theorem multiAgent_closed_seed_actor_equivalence :
    multiAgentSeedActorEquiv interactionSeed0 = interactionActor0 ∧
      multiAgentSeedActorEquiv interactionSeed1 = interactionActor1 ∧
      multiAgentSeedActorEquiv interactionSeed2 = interactionActor2 ∧
      multiAgentSeedActorEquiv.symm interactionActor0 = interactionSeed0 ∧
      multiAgentSeedActorEquiv.symm interactionActor1 = interactionSeed1 ∧
      multiAgentSeedActorEquiv.symm interactionActor2 = interactionSeed2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem multiAgent_closed_inverse_retains_trace_witness :
    ∃ state ∈ threeAgentProcessGame.occurrence.trace,
      MultiAgent.seedAt () state
        (multiAgentSeedActorEquiv.symm interactionActor0).1 :=
  multiAgent_inverse_seed_has_trace_witness interactionActor0

theorem multiAgent_closed_generic_bijective_consumer :
    Function.Bijective
      (generatedActorOf threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
        MultiAgent.InteractionLineage MultiAgent.lineageOf) :=
  multiAgent_generatedActorOf_bijective

theorem all_three_domain_equivalences_are_exact_and_choice_free :
    Function.Bijective (economicSeedActorEquiv coalitionSource) ∧
      Function.Bijective (biologicalSeedActorEquiv divisionSource) ∧
      Function.Bijective multiAgentSeedActorEquiv :=
  ⟨(economicSeedActorEquiv coalitionSource).bijective,
    (biologicalSeedActorEquiv divisionSource).bijective,
    multiAgentSeedActorEquiv.bijective⟩

end CrossDomainGeneratedActorRegression
end Society
end Regression
end ProcessGame
end SaturationMonoid
