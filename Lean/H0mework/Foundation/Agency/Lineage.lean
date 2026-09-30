import H0mework.Foundation.Agency.Game

/-!
# Occurrence-generated lineage face

Actors are generated downstream from seeds witnessed at an exact state of the
source occurrence trace.  A caller cannot hide a primitive player type in a
source-indexed carrier: the seed type is fixed, and every admitted seed must
carry its source/occurrence provenance.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u v w x

/-- Seeds admitted by one source occurrence.  The witness is an exact trace
state satisfying the fixed source/state-local seed law. -/
def SourceSeed {Source : Type u} {State : Type v}
    (occurrenceOf : Source → RootedAccountedUnfolding State)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (source : Source) :=
  { seed : Seed //
    ∃ state ∈ (occurrenceOf source).trace, SeedAt source state seed }

/-- Image of occurrence-generated source seeds under the dependent lineage
compiler. -/
def GeneratedActor {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source) :=
  { candidate : Lineage game.source //
    ∃ seed : SourceSeed occurrenceOf Seed SeedAt game.source,
      candidate = lineageOf game.source seed }

/-- Canonical generated actor for one occurrence-witnessed source seed. -/
def generatedActorOf {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) :
    GeneratedActor game Seed SeedAt Lineage lineageOf :=
  ⟨lineageOf game.source seed, ⟨seed, rfl⟩⟩

@[simp] theorem generatedActorOf_value
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (seed : SourceSeed occurrenceOf Seed SeedAt game.source) :
    (generatedActorOf game Seed SeedAt Lineage lineageOf seed).1 =
      lineageOf game.source seed :=
  rfl

/-- Every generic actor is exactly one admitted seed image. -/
theorem generatedActor_exhaustive
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (actor : GeneratedActor game Seed SeedAt Lineage lineageOf) :
    ∃ seed : SourceSeed occurrenceOf Seed SeedAt game.source,
      actor = generatedActorOf game Seed SeedAt Lineage lineageOf seed := by
  rcases actor.2 with ⟨seed, generated⟩
  refine ⟨seed, Subtype.ext ?_⟩
  exact generated

theorem generatedActorOf_injective_of_lineageOf_injective
    {Source : Type u} {State : Type v}
    {occurrenceOf : Source → RootedAccountedUnfolding State}
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type w) (SeedAt : Source → State → Seed → Prop)
    (Lineage : Source → Type x)
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (injective : Function.Injective (lineageOf game.source)) :
    Function.Injective (generatedActorOf game Seed SeedAt Lineage lineageOf) := by
  intro left right actorsEqual
  apply injective
  exact congrArg Subtype.val actorsEqual

end ProcessGame
end SaturationMonoid
