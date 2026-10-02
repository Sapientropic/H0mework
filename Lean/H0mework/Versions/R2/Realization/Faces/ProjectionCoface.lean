import H0mework.Versions.R2.Foundation.Authority.SourceProjectionInventory

/-!
# Generic source-projection coface

One complete source projection inventory may expose a further source-owned
coordinate without changing the underlying occurrence, ledger compiler, or
law surface.  This kernel provides that visibility uplift for an arbitrary
dependent projection law.  The inherited and added coordinates are both
installed by occurrence-wise `HEq` contracts; neither side is a second
source, a post-emission annotation, or a free authority premise.

The construction is deliberately neutral about the payload.  A domain
producer supplies the component law; the coface only preserves it and the
already admitted inventory.  Thus a later history/cochain/duality producer
can be installed at the same source occurrence without re-charting the root.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Coordinates of a source projection inventory after adjoining one
source-owned component. -/
inductive SourceNativeProjectionCoface (Base Component : Type u) : Type u
  | component (projection : Component)
  | inherited (projection : Base)

namespace SourceNativeAuthoritySource

/-- Adjoin one complete dependent projection law to an existing authority
source.  All non-projection source identity fields are retained verbatim. -/
def withProjectionCoface
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (component : SourceNativeProjectionLaw
      base.restructuringSource.toLedgerSource) :
    SourceNativeAuthoritySource N V where
  restructuringSource := base.restructuringSource
  eventInventoryAdmission := base.eventInventoryAdmission
  lawSurface := base.lawSurface
  observationAt := base.observationAt
  projectionLaw :=
    { Projection := SourceNativeProjectionCoface
        base.projectionLaw.Projection component.Projection
      ActiveAt := fun projection {_current} occurrence =>
        match projection with
        | .component projection => component.ActiveAt projection occurrence
        | .inherited inherited =>
            base.projectionLaw.ActiveAt inherited occurrence
      InactiveAt := fun projection {_current} occurrence =>
        match projection with
        | .component projection => component.InactiveAt projection occurrence
        | .inherited inherited =>
            base.projectionLaw.InactiveAt inherited occurrence
      classify := by
        intro projection current occurrence
        cases projection with
        | component projection =>
            exact component.classify projection occurrence
        | inherited inherited =>
            exact base.projectionLaw.classify inherited occurrence
      PayloadAt := fun projection {_current} occurrence active =>
        match projection with
        | .component projection =>
            component.PayloadAt projection occurrence active
        | .inherited inherited =>
            base.projectionLaw.PayloadAt inherited occurrence active
      project := by
        intro projection current occurrence active
        cases projection with
        | component projection =>
            exact component.project projection occurrence active
        | inherited inherited =>
            exact base.projectionLaw.project inherited occurrence active }

@[simp] theorem withProjectionCoface_restructuringSource
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (component : SourceNativeProjectionLaw
      base.restructuringSource.toLedgerSource) :
    (base.withProjectionCoface component).restructuringSource =
      base.restructuringSource :=
  rfl

@[simp] theorem withProjectionCoface_lawSurface
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (component : SourceNativeProjectionLaw
      base.restructuringSource.toLedgerSource) :
    (base.withProjectionCoface component).lawSurface = base.lawSurface :=
  rfl

@[simp] theorem withProjectionCoface_observationAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (component : SourceNativeProjectionLaw base.restructuringSource.toLedgerSource)
    {current : V.Current}
    (occurrence : base.restructuringSource.source.toRootSource.actual.OccurrenceAt current) :
    (base.withProjectionCoface component).observationAt occurrence = base.observationAt occurrence := rfl

end SourceNativeAuthoritySource

namespace SourceNativeProjectionLaw.InstallationAt

/-- The newly adjoined component is a direct coface of the widened
inventory. -/
def componentCoface
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (component : SourceNativeProjectionLaw
      base.restructuringSource.toLedgerSource) :
    SourceNativeProjectionLaw.InstallationAt component
      (base.withProjectionCoface component).projectionLaw where
  embed := SourceNativeProjectionCoface.component
  embed_injective := by
    intro left right equality
    injection equality
  outcome_heq := by
    intro current occurrence projection
    dsimp only [SourceNativeProjectionLaw.outcomeAt,
      SourceNativeAuthoritySource.withProjectionCoface]
    cases component.classify projection occurrence <;> rfl

/-- Every pre-existing source projection remains a direct coface after the
new component is adjoined. -/
def inheritedCoface
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (component : SourceNativeProjectionLaw
      base.restructuringSource.toLedgerSource) :
    SourceNativeProjectionLaw.InstallationAt base.projectionLaw
      (base.withProjectionCoface component).projectionLaw where
  embed := SourceNativeProjectionCoface.inherited
  embed_injective := by
    intro left right equality
    injection equality
  outcome_heq := by
    intro current occurrence projection
    dsimp only [SourceNativeProjectionLaw.outcomeAt,
      SourceNativeAuthoritySource.withProjectionCoface]
    cases base.projectionLaw.classify projection occurrence <;> rfl

end SourceNativeProjectionLaw.InstallationAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
