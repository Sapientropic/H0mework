import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.SourceGeneratedOccurrenceRate

/-!
# Source-generated crossings

One source-owned compiler turns every exact unit of the canonical M10
occurrence queue into one crossing.  Endpoints and optional boundaries are
the images of seeds witnessed at that unit's exact trace state; the crossing
itself retains the queue position, so recurrent states or endpoints cannot
collapse distinct occurrences.

There is no caller crossing list, endpoint list, graph, adjacency relation,
boundary filter, or externally selected bound in this module.  The only
crossing trace is the canonical queue mapped through the compiler, and the
only boundary list is
the compiler's own dependent classifier filtered over that trace.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Space

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity

universe uSource uState uSeed uLineage uUnit
universe uSiteSeed uSiteLineage uFlow
universe uBoundarySeed uBoundaryLineage uBoundaryClass

variable {Source : Type uSource}
variable {State : Type uState}
variable {occurrenceOf : Source → RootedAccountedUnfolding State}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {Seed : Type uSeed}
variable {SeedAt : Source → State → Seed → Prop}
variable {Lineage : Source → Type uLineage}
variable {lineageOf : ∀ source,
  SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
variable {focal : SourceSeed occurrenceOf Seed SeedAt game.source}
variable {rateCompiler : SourceOwnedOccurrenceRateCompiler
  game Seed SeedAt Lineage lineageOf focal}

noncomputable section

-- The structure sort necessarily joins these independent payload universes.
set_option linter.checkUnivs false in
/-- A source-owned crossing law over the exact M10 queue.  Every endpoint,
flow payload, and active boundary is generated at the exact state already
carried by its queue occurrence. -/
structure SourceOwnedCrossingCompiler
    (rateCompiler : SourceOwnedOccurrenceRateCompiler
      game Seed SeedAt Lineage lineageOf focal) where
  SiteSeed : Type uSiteSeed
  SiteSeedAt : Source → State → SiteSeed → Prop
  SiteLineage : Source → Type uSiteLineage
  siteLineageOf : ∀ source,
    SourceSeed occurrenceOf SiteSeed SiteSeedAt source → SiteLineage source
  originSeedAt : rateCompiler.ExactQueueUnit → SiteSeed
  targetSeedAt : rateCompiler.ExactQueueUnit → SiteSeed
  originSeedIncidence : (crossing : rateCompiler.ExactQueueUnit) →
    SiteSeedAt game.source crossing.state (originSeedAt crossing)
  targetSeedIncidence : (crossing : rateCompiler.ExactQueueUnit) →
    SiteSeedAt game.source crossing.state (targetSeedAt crossing)
  FlowPayloadAt : rateCompiler.ExactQueueUnit → Type uFlow
  flowPayloadAt : (crossing : rateCompiler.ExactQueueUnit) →
    FlowPayloadAt crossing
  BoundarySeed : Type uBoundarySeed
  BoundarySeedAt : Source → State → BoundarySeed → Prop
  BoundaryLineage : Source → Type uBoundaryLineage
  boundaryLineageOf : ∀ source,
    SourceSeed occurrenceOf BoundarySeed BoundarySeedAt source →
      BoundaryLineage source
  BoundaryActiveAt : rateCompiler.ExactQueueUnit → Type uBoundaryClass
  BoundaryInactiveAt : rateCompiler.ExactQueueUnit → Type uBoundaryClass
  classifyBoundary : (crossing : rateCompiler.ExactQueueUnit) →
    BoundaryActiveAt crossing ⊕ BoundaryInactiveAt crossing
  boundarySeedAt : (crossing : rateCompiler.ExactQueueUnit) →
    BoundaryActiveAt crossing → BoundarySeed
  boundarySeedIncidence : (crossing : rateCompiler.ExactQueueUnit) →
    (active : BoundaryActiveAt crossing) →
      BoundarySeedAt game.source crossing.state
        (boundarySeedAt crossing active)

namespace SourceOwnedCrossingCompiler

variable
  (compiler : SourceOwnedCrossingCompiler rateCompiler)

/-- A crossing is the exact, position-indexed M10 queue occurrence itself;
this module does not mint a second occurrence identity. -/
abbrev ExactCrossing
    (_compiler : SourceOwnedCrossingCompiler rateCompiler) :=
  rateCompiler.ExactQueueUnit

/-- A site is an image of an exact source-witnessed site seed. -/
abbrev Site := GeneratedActor game compiler.SiteSeed compiler.SiteSeedAt
  compiler.SiteLineage compiler.siteLineageOf

/-- A boundary is an image of an exact source-witnessed boundary seed. -/
abbrev Boundary := GeneratedActor game compiler.BoundarySeed
  compiler.BoundarySeedAt compiler.BoundaryLineage compiler.boundaryLineageOf

/-- Canonically regard a compiler-owned queue unit as the corresponding exact
crossing.  Queue membership is recovered from its position inventory. -/
def exactCrossingOf (unit : rateCompiler.QueueUnit) : compiler.ExactCrossing :=
  rateCompiler.exactQueueUnitOf unit.position unit.raw

@[simp] theorem exactCrossingOf_value
    (unit : rateCompiler.QueueUnit) :
    (compiler.exactCrossingOf unit).1 = unit := by
  cases unit
  rfl

theorem exactCrossingOf_injective :
    Function.Injective compiler.exactCrossingOf := by
  intro left right equality
  have valueEquality := congrArg Subtype.val equality
  simpa using valueEquality

/-- The sole crossing trace: the canonical M10 queue mapped without dropping,
reordering, or deduplicating any occurrence. -/
def crossingTrace : List compiler.ExactCrossing :=
  rateCompiler.queue.map compiler.exactCrossingOf

theorem crossingTrace_nodup : compiler.crossingTrace.Nodup :=
  List.Nodup.map compiler.exactCrossingOf_injective rateCompiler.queue_nodup

/-- Every exact queue occurrence is present in the generated crossing trace. -/
theorem exactCrossing_mem (crossing : compiler.ExactCrossing) :
    crossing ∈ compiler.crossingTrace := by
  apply List.mem_map.mpr
  refine ⟨crossing.1, crossing.2, ?_⟩
  apply Subtype.ext
  exact compiler.exactCrossingOf_value crossing.1

namespace ExactCrossing

variable (crossing : compiler.ExactCrossing)

/-- Origin seed with exact incidence at this crossing state. -/
def originSourceSeed :
    SourceSeed occurrenceOf compiler.SiteSeed compiler.SiteSeedAt game.source :=
  ⟨compiler.originSeedAt crossing,
    ⟨crossing.state, stateAt_mem game crossing.position,
      compiler.originSeedIncidence crossing⟩⟩

@[simp] theorem originSourceSeed_value :
    crossing.originSourceSeed.1 = compiler.originSeedAt crossing :=
  rfl

/-- The recovered origin seed is incident at this exact crossing state. -/
theorem originSourceIncidence :
    compiler.SiteSeedAt game.source crossing.state
      crossing.originSourceSeed.1 :=
  compiler.originSeedIncidence crossing

/-- Target seed with exact incidence at this crossing state. -/
def targetSourceSeed :
    SourceSeed occurrenceOf compiler.SiteSeed compiler.SiteSeedAt game.source :=
  ⟨compiler.targetSeedAt crossing,
    ⟨crossing.state, stateAt_mem game crossing.position,
      compiler.targetSeedIncidence crossing⟩⟩

@[simp] theorem targetSourceSeed_value :
    crossing.targetSourceSeed.1 = compiler.targetSeedAt crossing :=
  rfl

/-- The recovered target seed is incident at this exact crossing state. -/
theorem targetSourceIncidence :
    compiler.SiteSeedAt game.source crossing.state
      crossing.targetSourceSeed.1 :=
  compiler.targetSeedIncidence crossing

/-- Generated origin site of this exact crossing. -/
def originSite : compiler.Site :=
  generatedActorOf game compiler.SiteSeed compiler.SiteSeedAt
    compiler.SiteLineage compiler.siteLineageOf crossing.originSourceSeed

/-- Generated target site of this exact crossing. -/
def targetSite : compiler.Site :=
  generatedActorOf game compiler.SiteSeed compiler.SiteSeedAt
    compiler.SiteLineage compiler.siteLineageOf crossing.targetSourceSeed

/-- Flow payload in the exact crossing fibre. -/
def flowPayload : compiler.FlowPayloadAt crossing :=
  compiler.flowPayloadAt crossing

/-- Recurrent visits remain distinct crossings whenever their actual trace
positions differ, even if states, seeds, and endpoints all coincide. -/
theorem ne_of_position_ne
    {left right : rateCompiler.ExactQueueUnit}
    (position_ne :
      Capacity.SourceOwnedOccurrenceRateCompiler.ExactQueueUnit.position
          rateCompiler left ≠
        Capacity.SourceOwnedOccurrenceRateCompiler.ExactQueueUnit.position
          rateCompiler right) :
    left ≠ right := by
  intro crossing_eq
  exact position_ne (congrArg
    (Capacity.SourceOwnedOccurrenceRateCompiler.ExactQueueUnit.position
      rateCompiler) crossing_eq)

end ExactCrossing

/-- Exact proof that the source classifier activated a boundary at this
crossing.  The constructor is private: public certificates can only be emitted
by `boundaryCertificate?`. -/
structure BoundaryCertificateAt (crossing : compiler.ExactCrossing) where
  private mk ::
  active : compiler.BoundaryActiveAt crossing
  classified : compiler.classifyBoundary crossing = Sum.inl active

namespace BoundaryCertificateAt

variable {crossingOccurrence : compiler.ExactCrossing}

/-- Boundary seed with exact incidence at the certified crossing state. -/
def sourceSeed
    (certificate : compiler.BoundaryCertificateAt crossingOccurrence) :
    SourceSeed occurrenceOf compiler.BoundarySeed compiler.BoundarySeedAt
      game.source :=
  ⟨compiler.boundarySeedAt crossingOccurrence certificate.active,
    ⟨crossingOccurrence.state, stateAt_mem game crossingOccurrence.position,
      compiler.boundarySeedIncidence crossingOccurrence certificate.active⟩⟩

@[simp] theorem sourceSeed_value
    (certificate : compiler.BoundaryCertificateAt crossingOccurrence) :
    certificate.sourceSeed.1 =
      compiler.boundarySeedAt crossingOccurrence certificate.active :=
  rfl

/-- Exact incidence of the recovered boundary seed at the certified crossing
state. -/
theorem sourceIncidence
    (certificate : compiler.BoundaryCertificateAt crossingOccurrence) :
    compiler.BoundarySeedAt game.source crossingOccurrence.state
      certificate.sourceSeed.1 :=
  compiler.boundarySeedIncidence crossingOccurrence certificate.active

/-- Boundary generated from the certificate's exact source incidence. -/
def boundary
    (certificate : compiler.BoundaryCertificateAt crossingOccurrence) :
    compiler.Boundary :=
  generatedActorOf game compiler.BoundarySeed compiler.BoundarySeedAt
    compiler.BoundaryLineage compiler.boundaryLineageOf certificate.sourceSeed

/-- Exact crossing retained by a dependent boundary certificate fibre. -/
def crossing
    (_certificate : compiler.BoundaryCertificateAt crossingOccurrence) :
    compiler.ExactCrossing := crossingOccurrence

end BoundaryCertificateAt

/-- Source-owned optional boundary classifier.  No caller supplies a filter
predicate or chooses the active branch. -/
def boundaryCertificate? (crossing : compiler.ExactCrossing) :
    Option (compiler.BoundaryCertificateAt crossing) :=
  match classified : compiler.classifyBoundary crossing with
  | .inl active => some ⟨active, classified⟩
  | .inr _ => none

/-- Uniform carrier for boundary certificates at heterogeneous crossings. -/
abbrev AnyBoundaryCertificate :=
  Sigma compiler.BoundaryCertificateAt

/-- Pack the dependent result of the source classifier for use in the
canonical heterogeneous boundary trace. -/
def boundaryCertificateEntry?
    (crossing : compiler.ExactCrossing) :
    Option compiler.AnyBoundaryCertificate :=
  (compiler.boundaryCertificate? crossing).map fun certificate =>
    ⟨crossing, certificate⟩

/-- Sole generated boundary-certificate list: source classification filtered
over the exact generated crossing trace. -/
def boundaryCertificates : List compiler.AnyBoundaryCertificate :=
  compiler.crossingTrace.filterMap compiler.boundaryCertificateEntry?

namespace AnyBoundaryCertificate

variable (certificate : compiler.AnyBoundaryCertificate)

/-- Exact crossing occurrence classified by this boundary certificate. -/
def crossing : compiler.ExactCrossing := certificate.1

/-- Dependent certificate at the retained exact crossing. -/
def proof : compiler.BoundaryCertificateAt certificate.crossing :=
  certificate.2

/-- Exact boundary source seed recovered from this generated certificate. -/
def sourceSeed :
    SourceSeed occurrenceOf compiler.BoundarySeed compiler.BoundarySeedAt
      game.source :=
  certificate.proof.sourceSeed

/-- Boundary image generated at the retained exact crossing. -/
def boundary : compiler.Boundary := certificate.proof.boundary

/-- Exact boundary incidence retained by the heterogeneous certificate. -/
theorem sourceIncidence :
    compiler.BoundarySeedAt game.source certificate.crossing.state
      certificate.sourceSeed.1 :=
  certificate.proof.sourceIncidence

/-- Every emitted certificate retains its source-classified crossing and exact
membership in the canonical crossing trace. -/
theorem provenance
    (membership : certificate ∈ compiler.boundaryCertificates) :
    certificate.crossing ∈ compiler.crossingTrace ∧
      compiler.boundaryCertificate? certificate.crossing =
        some certificate.proof := by
  rcases List.mem_filterMap.mp membership with
    ⟨crossing, crossingMem, packedEq⟩
  unfold boundaryCertificateEntry? at packedEq
  cases classified : compiler.boundaryCertificate? crossing with
  | none => simp [classified] at packedEq
  | some proof =>
      simp only [classified, Option.map_some] at packedEq
      cases packedEq
      exact ⟨crossingMem, classified⟩

end AnyBoundaryCertificate

end SourceOwnedCrossingCompiler

end
end Space
end Society
end ProcessGame
end SaturationMonoid
