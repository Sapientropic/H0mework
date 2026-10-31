import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.DomainReuse
import H0mework.Foundation.Agency.MaximalActor

/-!
# Constructive generated-actor instances

The three domain lineages in `DomainReuse` retain their exact `SourceSeed` in
their sole constructor.  Their generated actors are therefore constructively
equivalent to occurrence-witnessed seeds: every inverse below pattern-matches
the lineage value and never selects a witness from the actor's `Prop` proof.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DomainReuse

/-! ## Economic admission -/

theorem economicLineageOf_injective (source : Economic.Source) :
    Function.Injective (Economic.lineageOf source) := by
  intro left right equalLineages
  injection equalLineages

def economicSeedActorEquiv (source : Economic.Source) :
    SourceSeed Economic.occurrenceOf Economic.AdmissionEvent Economic.seedAt
        source ≃
      Economic.GeneratedCoalitionMember source where
  toFun := generatedActorOf (Economic.processGame source)
    Economic.AdmissionEvent Economic.seedAt Economic.CoalitionLineage
      Economic.lineageOf
  invFun := fun actor =>
    match actor.1 with
    | .admitted seed => seed
  left_inv := by intro seed; rfl
  right_inv := by
    rintro ⟨lineage, generated⟩
    cases lineage
    apply Subtype.ext
    rfl

@[simp] theorem economicSeedActorEquiv_apply (source : Economic.Source)
    (seed : SourceSeed Economic.occurrenceOf Economic.AdmissionEvent
      Economic.seedAt source) :
    economicSeedActorEquiv source seed =
      generatedActorOf (Economic.processGame source) Economic.AdmissionEvent
        Economic.seedAt Economic.CoalitionLineage Economic.lineageOf seed :=
  rfl

theorem economic_generatedActorOf_bijective (source : Economic.Source) :
    Function.Bijective
      (generatedActorOf (Economic.processGame source) Economic.AdmissionEvent
        Economic.seedAt Economic.CoalitionLineage Economic.lineageOf) :=
  generatedActorOf_bijective_of_lineageOf_injective
    (Economic.processGame source) Economic.AdmissionEvent Economic.seedAt
      Economic.CoalitionLineage Economic.lineageOf
        (economicLineageOf_injective source)

theorem economic_inverse_seed_has_trace_witness (source : Economic.Source)
    (actor : Economic.GeneratedCoalitionMember source) :
    ∃ state ∈ (Economic.processGame source).occurrence.trace,
      Economic.seedAt source state (economicSeedActorEquiv source |>.symm actor).1 :=
  (economicSeedActorEquiv source |>.symm actor).2

/-! ## Biological division -/

theorem biologicalLineageOf_injective (source : Biological.Source) :
    Function.Injective (Biological.lineageOf source) := by
  intro left right equalLineages
  injection equalLineages

def biologicalSeedActorEquiv (source : Biological.Source) :
    SourceSeed Biological.occurrenceOf Biological.DivisionEvent
        Biological.seedAt source ≃
      Biological.GeneratedAncestryIndividual source where
  toFun := generatedActorOf (Biological.processGame source)
    Biological.DivisionEvent Biological.seedAt Biological.AncestryLineage
      Biological.lineageOf
  invFun := fun actor =>
    match actor.1 with
    | .divided seed => seed
  left_inv := by intro seed; rfl
  right_inv := by
    rintro ⟨lineage, generated⟩
    cases lineage
    apply Subtype.ext
    rfl

@[simp] theorem biologicalSeedActorEquiv_apply (source : Biological.Source)
    (seed : SourceSeed Biological.occurrenceOf Biological.DivisionEvent
      Biological.seedAt source) :
    biologicalSeedActorEquiv source seed =
      generatedActorOf (Biological.processGame source) Biological.DivisionEvent
        Biological.seedAt Biological.AncestryLineage Biological.lineageOf seed :=
  rfl

theorem biological_generatedActorOf_bijective (source : Biological.Source) :
    Function.Bijective
      (generatedActorOf (Biological.processGame source) Biological.DivisionEvent
        Biological.seedAt Biological.AncestryLineage Biological.lineageOf) :=
  generatedActorOf_bijective_of_lineageOf_injective
    (Biological.processGame source) Biological.DivisionEvent Biological.seedAt
      Biological.AncestryLineage Biological.lineageOf
        (biologicalLineageOf_injective source)

theorem biological_inverse_seed_has_trace_witness (source : Biological.Source)
    (actor : Biological.GeneratedAncestryIndividual source) :
    ∃ state ∈ (Biological.processGame source).occurrence.trace,
      Biological.seedAt source state
        (biologicalSeedActorEquiv source |>.symm actor).1 :=
  (biologicalSeedActorEquiv source |>.symm actor).2

/-! ## Canonical three-agent exposure -/

theorem multiAgentLineageOf_injective :
    Function.Injective (MultiAgent.lineageOf ()) := by
  intro left right equalLineages
  injection equalLineages

def multiAgentSeedActorEquiv :
    SourceSeed threeAgentOccurrenceOf ThreeCycleTime MultiAgent.seedAt () ≃
      MultiAgent.GeneratedInteractionActor where
  toFun := generatedActorOf threeAgentProcessGame ThreeCycleTime
    MultiAgent.seedAt MultiAgent.InteractionLineage MultiAgent.lineageOf
  invFun := fun actor =>
    match actor.1 with
    | .exposed seed => seed
  left_inv := by intro seed; rfl
  right_inv := by
    rintro ⟨lineage, generated⟩
    cases lineage
    apply Subtype.ext
    rfl

@[simp] theorem multiAgentSeedActorEquiv_apply
    (seed : SourceSeed threeAgentOccurrenceOf ThreeCycleTime
      MultiAgent.seedAt ()) :
    multiAgentSeedActorEquiv seed =
      generatedActorOf threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
        MultiAgent.InteractionLineage MultiAgent.lineageOf seed :=
  rfl

theorem multiAgent_generatedActorOf_bijective :
    Function.Bijective
      (generatedActorOf threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
        MultiAgent.InteractionLineage MultiAgent.lineageOf) :=
  generatedActorOf_bijective_of_lineageOf_injective
    threeAgentProcessGame ThreeCycleTime MultiAgent.seedAt
      MultiAgent.InteractionLineage MultiAgent.lineageOf
        multiAgentLineageOf_injective

theorem multiAgent_inverse_seed_has_trace_witness
    (actor : MultiAgent.GeneratedInteractionActor) :
    ∃ state ∈ threeAgentProcessGame.occurrence.trace,
      MultiAgent.seedAt () state (multiAgentSeedActorEquiv.symm actor).1 :=
  (multiAgentSeedActorEquiv.symm actor).2

end Society
end ProcessGame
end SaturationMonoid
