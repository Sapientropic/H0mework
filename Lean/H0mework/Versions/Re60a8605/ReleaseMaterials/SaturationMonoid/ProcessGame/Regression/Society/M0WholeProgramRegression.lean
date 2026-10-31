import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.GeneratedActorMaximalityRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.CrossDomainGeneratedActorRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.GoGeneratedActorMaximalityRegression

/-!
# M0 whole-program regression

This dependency sink consumes the premise-free actor classification, the
canonical trace-seed gauge quotient, its faithful and collapsed controls, the
three constructive domain equivalences, and the existing Go generated-player
carrier in one theorem.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace Society
namespace M0WholeProgramRegression

open GeneratedActorMaximalityRegression
open CrossDomainGeneratedActorRegression
open GoGeneratedActorMaximalityRegression
open _root_.SaturationMonoid.ProcessGame.Society
open DomainReuse DomainReuseRegression
open Go GoProcessGameRegression

theorem M0_dance_generates_all_dancers_up_to_exact_lineage_gauge :
    DancingGeneratesDancers societyGame Bool societySeedAt SocietyLineage
        faithfulLineageOf ∧
      Function.Bijective
        (gaugeToActor societyGame Bool societySeedAt SocietyLineage
          faithfulLineageOf) ∧
      societySourceSeed false ≠ societySourceSeed true ∧
      collapsedFalseGauge = collapsedTrueGauge ∧
      collapsedFalseActor = collapsedTrueActor ∧
      Function.Bijective (economicSeedActorEquiv coalitionSource) ∧
      Function.Bijective (biologicalSeedActorEquiv divisionSource) ∧
      Function.Bijective multiAgentSeedActorEquiv ∧
      Function.Bijective goGaugeToGeneratedPlayer ∧
      positiveGauge ≠ negativeGauge :=
  ⟨society_premise_free_dancing_generates_dancers,
    faithful_gauge_to_actor_is_bijective,
    constant_lineage_identifies_distinct_seeds_in_one_gauge_class.1,
    constant_lineage_identifies_distinct_seeds_in_one_gauge_class.2.1,
    distinct_seeds_generate_same_actor_exactly_when_lineages_agree.2,
    all_three_domain_equivalences_are_exact_and_choice_free.1,
    all_three_domain_equivalences_are_exact_and_choice_free.2.1,
    all_three_domain_equivalences_are_exact_and_choice_free.2.2,
    go_gauge_to_existing_generatedPlayer_is_bijective,
    positive_negative_gauge_classes_are_distinct⟩

theorem M0_all_installed_inverse_seeds_retain_occurrence_provenance :
    (∃ state ∈ coalitionGame.occurrence.trace,
      Economic.seedAt coalitionSource state
        ((economicSeedActorEquiv coalitionSource).symm
          firstCoalitionMember).1) ∧
      (∃ state ∈ divisionGame.occurrence.trace,
        Biological.seedAt divisionSource state
          ((biologicalSeedActorEquiv divisionSource).symm
            firstAncestryIndividual).1) ∧
      (∃ state ∈ threeAgentProcessGame.occurrence.trace,
        MultiAgent.seedAt () state
          (multiAgentSeedActorEquiv.symm interactionActor0).1) ∧
      (∃ state ∈ game.occurrence.trace,
        goSeedAt replay state positiveSeed.1) :=
  ⟨economic_closed_inverse_retains_trace_witness,
    biological_closed_inverse_retains_trace_witness,
    multiAgent_closed_inverse_retains_trace_witness,
    both_gauge_classes_retain_same_root_trace_provenance.1⟩

end M0WholeProgramRegression
end Society
end Regression
end ProcessGame
end SaturationMonoid
