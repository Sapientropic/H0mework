import H0mework.Society.Renewal.RenewalFaceSource
import H0mework.Versions.AB.Society.Renewal.RootInstalledRenewal

/-!
# Root-installed ProcessGame renewal projection

This is the only bridge from operational renewal to a local social-domain
face.  A projection compiler consumes the private temporal generated-entry
token and produces one exact `ProcessGame.SourceSeed` plus its existing
seed-indexed consumer and disposition.  The local standing value remains a
readout of that seed.

The compiler cannot produce root authority in the reverse direction.  A
root-grounded projected face stores the `RootInstalledRenewalAt`; without that
temporal root transition no projected operational face exists.  The compiler
may transport any exact local seed, so this module claims root grounding, not
independent semantic faithfulness of the local readout.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Renewal

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u uSource uState uSeed uLineage uStanding uConsumer uDisposition

variable {N : WorldRelationNetwork.{u}}
variable {V : ConstructiveRoot.Vocabulary.{u}}
variable {root : SourceNativeLedgerRootClosure N V}
variable {visit : SourceNativeTemporalVisitAt root}
variable {generated : SourceNativeTemporalVisitGeneratedEvolutionAt root visit}
variable {sourceEntry : OpenResponsibilityAt N
  (root.source.source.toRootSource.account.supportOf
    (root.emitted visit.current))}

variable {LocalSource : Type uSource}
variable {LocalState : Type uState}
variable {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {Seed : Type uSeed}
variable {SeedAt : LocalSource → LocalState → Seed → Prop}
variable {Lineage : LocalSource → Type uLineage}
variable {lineageOf : ∀ source,
  SourceSeed occurrenceOf Seed SeedAt source → Lineage source}
variable {Standing : Type uStanding}
variable {standingOf : SourceSeed occurrenceOf Seed SeedAt game.source →
  Standing}
variable {ConsumerAt : SourceSeed occurrenceOf Seed SeedAt game.source →
  Type uConsumer}
variable {DispositionAt : SourceSeed occurrenceOf Seed SeedAt game.source →
  Type uDisposition}

/-- Fixed dependent-face compiler from one exact temporal root row to a
local occurrence seed and its existing responsibility data. -/
structure TemporalRenewalFaceProjection
    (generated : SourceNativeTemporalVisitGeneratedEvolutionAt root visit)
    (sourceEntry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) where
  projectSeed : generated.GeneratedEntryRowAt sourceEntry →
    SourceSeed occurrenceOf Seed SeedAt game.source
  projectConsumer : (membership : generated.GeneratedEntryRowAt sourceEntry) →
    ConsumerAt (projectSeed membership)
  projectDisposition :
    (membership : generated.GeneratedEntryRowAt sourceEntry) →
      DispositionAt (projectSeed membership)

namespace RootInstalledRenewalAt

/-- The local face is generated definitionally from the exact temporal row
membership consumed by the operational renewal. -/
def projectedLocalFace
    (installed : RootInstalledRenewalAt generated sourceEntry)
    (projection : TemporalRenewalFaceProjection
      (game := game) (Seed := Seed) (SeedAt := SeedAt)
      (ConsumerAt := ConsumerAt) (DispositionAt := DispositionAt)
      generated sourceEntry) :
    SourceGeneratedRenewalFace game Seed SeedAt Lineage lineageOf
      Standing standingOf ConsumerAt DispositionAt :=
  SourceGeneratedRenewalFace.generate
    (projection.projectSeed installed.exactEventMembership)
    (projection.projectConsumer installed.exactEventMembership)
    (projection.projectDisposition installed.exactEventMembership)

end RootInstalledRenewalAt

/-- Sealed root-grounded local face.  Its only stored datum is the existing
temporal-root renewal; the local face is computed by the projection above. -/
structure RootProjectedRenewalFaceAt
    (projection : TemporalRenewalFaceProjection
      (game := game) (Seed := Seed) (SeedAt := SeedAt)
      (ConsumerAt := ConsumerAt) (DispositionAt := DispositionAt)
      generated sourceEntry) : Type (max (u + 1) uSeed uConsumer uDisposition) where
  private mk ::
  installed : RootInstalledRenewalAt generated sourceEntry

namespace RootProjectedRenewalFaceAt

/-- Generate the root-grounded projection from an existing operational renewal. -/
def generate
    (projection : TemporalRenewalFaceProjection
      (game := game) (Seed := Seed) (SeedAt := SeedAt)
      (ConsumerAt := ConsumerAt) (DispositionAt := DispositionAt)
      generated sourceEntry)
    (installed : RootInstalledRenewalAt generated sourceEntry) :
    RootProjectedRenewalFaceAt projection :=
  ⟨installed⟩

variable {projection : TemporalRenewalFaceProjection
  (game := game) (Seed := Seed) (SeedAt := SeedAt)
  (ConsumerAt := ConsumerAt) (DispositionAt := DispositionAt)
  generated sourceEntry}

/-- Local ProcessGame face generated by the stored exact root transition. -/
def localFace (projected : RootProjectedRenewalFaceAt projection) :
    SourceGeneratedRenewalFace game Seed SeedAt Lineage lineageOf
      Standing standingOf ConsumerAt DispositionAt :=
  projected.installed.projectedLocalFace projection

/-- Operational standing authority remains exactly the root-installed
renewal; the local face cannot replace it. -/
def operationalAuthority
    (projected : RootProjectedRenewalFaceAt projection) :
    RootInstalledRenewalAt generated sourceEntry :=
  projected.installed

end RootProjectedRenewalFaceAt

/-- Without the exact temporal root renewal there is no root-grounded operational
projection, regardless of which local source seeds happen to exist. -/
theorem noRootRenewal_noProjectedOperationalFace
    (projection : TemporalRenewalFaceProjection
      (game := game) (Seed := Seed) (SeedAt := SeedAt)
      (ConsumerAt := ConsumerAt) (DispositionAt := DispositionAt)
      generated sourceEntry)
    (noRootRenewal : RootInstalledRenewalAt generated sourceEntry → False) :
    RootProjectedRenewalFaceAt projection → False :=
  fun projected => noRootRenewal projected.installed

end Renewal
end Society
end ProcessGame
end SaturationMonoid
