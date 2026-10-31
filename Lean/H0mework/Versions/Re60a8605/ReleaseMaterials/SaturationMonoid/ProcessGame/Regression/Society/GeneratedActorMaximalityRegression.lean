import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Lineage.GeneratedActorGaugeQuotient

/-!
# Generic society regression for generated-actor maximality

One exact occurrence exposes two dance seeds.  A faithful lineage compiler
separates them bijectively; a constant lineage compiler identifies them,
showing that actor equality is exactly lineage equality rather than primitive
seed identity.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace Society
namespace GeneratedActorMaximalityRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

inductive SocietyState
  | origin
  | danced (seed : Bool)

def societyOccurrenceOf : Unit → RootedAccountedUnfolding SocietyState :=
  fun _ => .occur .origin <|
    .cons (.zero (.danced false)) <|
      .singleton (.zero (.danced true))

def societyGame : SaturationMonoid.ProcessGame societyOccurrenceOf :=
  ⟨()⟩

def societySeedAt (_source : Unit) (state : SocietyState)
    (seed : Bool) : Prop :=
  state = .danced seed

def societySourceSeed (seed : Bool) :
    SourceSeed societyOccurrenceOf Bool societySeedAt () := by
  refine ⟨seed, .danced seed, ?_, rfl⟩
  cases seed <;>
    simp [societyOccurrenceOf, RootedAccountedUnfolding.trace,
      RootedAccountedUnfolding.zero, AccountedBranches.singleton]

def SocietyLineage (_source : Unit) := Bool

def faithfulLineageOf (_source : Unit)
    (seed : SourceSeed societyOccurrenceOf Bool societySeedAt ()) :
    SocietyLineage () :=
  seed.1

def falseActor :
    GeneratedActor societyGame Bool societySeedAt SocietyLineage
      faithfulLineageOf :=
  generatedActorOf societyGame Bool societySeedAt SocietyLineage
    faithfulLineageOf (societySourceSeed false)

def trueActor :
    GeneratedActor societyGame Bool societySeedAt SocietyLineage
      faithfulLineageOf :=
  generatedActorOf societyGame Bool societySeedAt SocietyLineage
    faithfulLineageOf (societySourceSeed true)

theorem society_premise_free_dancing_generates_dancers :
    DancingGeneratesDancers societyGame Bool societySeedAt SocietyLineage
      faithfulLineageOf :=
  dancingGeneratesDancers societyGame Bool societySeedAt SocietyLineage
    faithfulLineageOf

theorem every_society_actor_has_exact_trace_seed
    (actor : GeneratedActor societyGame Bool societySeedAt SocietyLineage
      faithfulLineageOf) :
    ∃ seed : SourceSeed societyOccurrenceOf Bool societySeedAt (),
      (∃ state ∈ societyGame.occurrence.trace,
        societySeedAt () state seed.1) ∧
      generatedActorOf societyGame Bool societySeedAt SocietyLineage
        faithfulLineageOf seed = actor :=
  generatedActor_has_exact_sourceSeed societyGame Bool societySeedAt
    SocietyLineage faithfulLineageOf actor

theorem society_seed_to_actor_is_surjective :
    Function.Surjective
      (generatedActorOf societyGame Bool societySeedAt SocietyLineage
        faithfulLineageOf) :=
  generatedActorOf_surjective societyGame Bool societySeedAt SocietyLineage
    faithfulLineageOf

theorem faithful_society_seed_to_actor_is_bijective :
    Function.Injective
        (generatedActorOf societyGame Bool societySeedAt SocietyLineage
          faithfulLineageOf) ∧
      Function.Surjective
        (generatedActorOf societyGame Bool societySeedAt SocietyLineage
          faithfulLineageOf) := by
  apply generatedActorOf_bijective_of_lineageOf_injective
  intro left right lineagesEqual
  exact Subtype.ext lineagesEqual

theorem faithful_society_actors_are_distinct : falseActor ≠ trueActor := by
  intro actorsEqual
  have lineagesEqual :=
    (generatedActorOf_eq_iff_lineageOf_eq societyGame Bool societySeedAt
      SocietyLineage faithfulLineageOf
      (societySourceSeed false) (societySourceSeed true)).mp actorsEqual
  cases lineagesEqual

def faithfulFalseGauge :
    TraceSeedGauge societyGame Bool societySeedAt SocietyLineage
      faithfulLineageOf :=
  traceSeedGaugeMk societyGame Bool societySeedAt SocietyLineage
    faithfulLineageOf (societySourceSeed false)

def faithfulTrueGauge :
    TraceSeedGauge societyGame Bool societySeedAt SocietyLineage
      faithfulLineageOf :=
  traceSeedGaugeMk societyGame Bool societySeedAt SocietyLineage
    faithfulLineageOf (societySourceSeed true)

theorem faithful_lineages_remain_distinct_gauge_classes :
    faithfulFalseGauge ≠ faithfulTrueGauge := by
  intro gaugesEqual
  apply faithful_society_actors_are_distinct
  exact congrArg
    (gaugeToActor societyGame Bool societySeedAt SocietyLineage
      faithfulLineageOf) gaugesEqual

theorem faithful_gauge_to_actor_is_bijective :
    Function.Injective
        (gaugeToActor societyGame Bool societySeedAt SocietyLineage
          faithfulLineageOf) ∧
      Function.Surjective
        (gaugeToActor societyGame Bool societySeedAt SocietyLineage
          faithfulLineageOf) :=
  gaugeToActor_bijective societyGame Bool societySeedAt SocietyLineage
    faithfulLineageOf

/-! A nonfaithful lineage compiler classifies different seeds together. -/

def CollapsedLineage (_source : Unit) := Unit

def collapsedLineageOf (_source : Unit)
    (_seed : SourceSeed societyOccurrenceOf Bool societySeedAt ()) :
    CollapsedLineage () :=
  ()

def collapsedFalseActor :
    GeneratedActor societyGame Bool societySeedAt CollapsedLineage
      collapsedLineageOf :=
  generatedActorOf societyGame Bool societySeedAt CollapsedLineage
    collapsedLineageOf (societySourceSeed false)

def collapsedTrueActor :
    GeneratedActor societyGame Bool societySeedAt CollapsedLineage
      collapsedLineageOf :=
  generatedActorOf societyGame Bool societySeedAt CollapsedLineage
    collapsedLineageOf (societySourceSeed true)

def collapsedFalseGauge :
    TraceSeedGauge societyGame Bool societySeedAt CollapsedLineage
      collapsedLineageOf :=
  traceSeedGaugeMk societyGame Bool societySeedAt CollapsedLineage
    collapsedLineageOf (societySourceSeed false)

def collapsedTrueGauge :
    TraceSeedGauge societyGame Bool societySeedAt CollapsedLineage
      collapsedLineageOf :=
  traceSeedGaugeMk societyGame Bool societySeedAt CollapsedLineage
    collapsedLineageOf (societySourceSeed true)

theorem distinct_seeds_generate_same_actor_exactly_when_lineages_agree :
    societySourceSeed false ≠ societySourceSeed true ∧
      collapsedFalseActor = collapsedTrueActor := by
  constructor
  · intro seedsEqual
    have valuesEqual := congrArg Subtype.val seedsEqual
    cases valuesEqual
  · apply (generatedActorOf_eq_iff_lineageOf_eq societyGame Bool societySeedAt
      CollapsedLineage collapsedLineageOf
      (societySourceSeed false) (societySourceSeed true)).mpr
    rfl

theorem constant_lineage_identifies_distinct_seeds_in_one_gauge_class :
    societySourceSeed false ≠ societySourceSeed true ∧
      collapsedFalseGauge = collapsedTrueGauge ∧
      gaugeToActor societyGame Bool societySeedAt CollapsedLineage
          collapsedLineageOf collapsedFalseGauge = collapsedFalseActor ∧
      gaugeToActor societyGame Bool societySeedAt CollapsedLineage
          collapsedLineageOf collapsedTrueGauge = collapsedTrueActor := by
  refine ⟨distinct_seeds_generate_same_actor_exactly_when_lineages_agree.1,
    ?_, rfl, rfl⟩
  apply Quotient.sound
  rfl

end GeneratedActorMaximalityRegression
end Society
end Regression
end ProcessGame
end SaturationMonoid
