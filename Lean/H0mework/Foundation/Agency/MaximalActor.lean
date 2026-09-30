import H0mework.Foundation.Agency.Lineage

/-!
# Maximal classification of generated actors

For every source-backed `ProcessGame`, the actor carrier is exactly the image
of occurrence-witnessed source seeds under the dependent lineage compiler.
Actor equality is therefore neither primitive nor seed equality: it is
exactly equality of the generated lineage values.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u v w x

/-- Every generated actor has an exact source seed, the seed's occurrence
trace witness, and an equality exhibiting the actor as that seed's image. -/
theorem generatedActor_has_exact_sourceSeed
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (actor : GeneratedActor game Seed SeedAt Lineage lineageOf) :
    ∃ seed : SourceSeed occurrenceOf Seed SeedAt game.source,
      (∃ state ∈ game.occurrence.trace,
        SeedAt game.source state seed.1) ∧
      generatedActorOf game Seed SeedAt Lineage lineageOf seed = actor := by
  rcases generatedActor_exhaustive game Seed SeedAt Lineage lineageOf actor with
    ⟨seed, actorEq⟩
  exact ⟨seed, seed.2, actorEq.symm⟩

/-- The seed-to-actor map is onto by construction of `GeneratedActor` as an
image. -/
theorem generatedActorOf_surjective
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) :
    Function.Surjective
      (generatedActorOf game Seed SeedAt Lineage lineageOf) := by
  intro actor
  rcases generatedActor_has_exact_sourceSeed
      game Seed SeedAt Lineage lineageOf actor with
    ⟨seed, _witness, generated⟩
  exact ⟨seed, generated⟩

/-- Maximal classification law: two witnessed seeds generate the same actor
exactly when their dependent lineage values agree. -/
theorem generatedActorOf_eq_iff_lineageOf_eq
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (left right : SourceSeed occurrenceOf Seed SeedAt game.source) :
    generatedActorOf game Seed SeedAt Lineage lineageOf left =
        generatedActorOf game Seed SeedAt Lineage lineageOf right ↔
      lineageOf game.source left = lineageOf game.source right := by
  constructor
  · intro actorsEqual
    exact congrArg Subtype.val actorsEqual
  · intro lineagesEqual
    exact Subtype.ext lineagesEqual

/-- Stable maximality contract for the slogan “the dance generates the
dancers”. -/
def DancingGeneratesDancers
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) : Prop :=
  (∀ actor : GeneratedActor game Seed SeedAt Lineage lineageOf,
    ∃ seed : SourceSeed occurrenceOf Seed SeedAt game.source,
      (∃ state ∈ game.occurrence.trace,
        SeedAt game.source state seed.1) ∧
      generatedActorOf game Seed SeedAt Lineage lineageOf seed = actor) ∧
  (∀ left right : SourceSeed occurrenceOf Seed SeedAt game.source,
    generatedActorOf game Seed SeedAt Lineage lineageOf left =
        generatedActorOf game Seed SeedAt Lineage lineageOf right ↔
      lineageOf game.source left = lineageOf game.source right)

/-- Premise-free constructive maximality theorem. -/
theorem dancingGeneratesDancers
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) :
    DancingGeneratesDancers game Seed SeedAt Lineage lineageOf :=
  ⟨generatedActor_has_exact_sourceSeed game Seed SeedAt Lineage lineageOf,
    generatedActorOf_eq_iff_lineageOf_eq
      game Seed SeedAt Lineage lineageOf⟩

/-- If the dependent lineage compiler is faithful on occurrence-witnessed
seeds, the seed-to-actor map is a bijection. -/
theorem generatedActorOf_bijective_of_lineageOf_injective
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (faithful : Function.Injective (lineageOf game.source)) :
    Function.Injective
        (generatedActorOf game Seed SeedAt Lineage lineageOf) ∧
      Function.Surjective
        (generatedActorOf game Seed SeedAt Lineage lineageOf) :=
  ⟨generatedActorOf_injective_of_lineageOf_injective
      game Seed SeedAt Lineage lineageOf faithful,
    generatedActorOf_surjective game Seed SeedAt Lineage lineageOf⟩

end ProcessGame
end SaturationMonoid
