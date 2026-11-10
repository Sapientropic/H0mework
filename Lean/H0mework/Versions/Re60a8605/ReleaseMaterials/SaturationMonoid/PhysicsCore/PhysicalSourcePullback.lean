import Mathlib

/-!
# Two-axis physical-source pullback

This module states the minimum architecture needed before a shared physical
law can be assembled honestly.  Representation/incidence data and smooth
source geometry remain independent axes.  Their typed equal-anchor fiber
product retains both axis coordinates; the physical adequacy of the anchor
must be proved by future concrete source modules.

All structures here are interfaces and candidate packaging, not concrete
SU(7) producer theorems.  In particular there is no map from the existing thin
datum into a physically adequate shared source, and no terminal metric, Hodge
operator, coupling, or stationary-family field is added to that thin datum.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uInternalSource uGeometrySource uAnchor
universe uInternal uCouplings
universe uSmooth uOrientation uSignature uTetrad uMetric uHodge uStationary

/-- Candidate data read from the representation/incidence axis. -/
structure InternalConstitutiveCandidate
    (InternalConstitutive : Type uInternal)
    (CouplingNormalization : Type uCouplings) where
  internalConstitutive : InternalConstitutive
  couplingNormalization : CouplingNormalization

/-- An obligation for the representation/incidence axis.  A concrete module
must define this map from genuine internal-source coordinates; merely storing
the result in a thin datum would not discharge that obligation. -/
structure InternalConstitutiveCandidateAxis
    (InternalSource : Type uInternalSource)
    (InternalConstitutive : Type uInternal)
    (CouplingNormalization : Type uCouplings) where
  candidateOf : InternalSource →
    InternalConstitutiveCandidate InternalConstitutive CouplingNormalization

/-- Candidate data read from an independent smooth source-geometry axis.
Separate carriers keep differential structure, orientation, signature,
tetrad, metric, Hodge data, and stationary family from being conflated. -/
structure SmoothGeometryCandidate
    (SmoothStructure : Type uSmooth) (Orientation : Type uOrientation)
    (Signature : Type uSignature) (Tetrad : Type uTetrad)
    (Metric : Type uMetric) (HodgeData : Type uHodge)
    (StationaryFamily : Type uStationary) where
  smoothStructure : SmoothStructure
  orientation : Orientation
  signature : Signature
  tetrad : Tetrad
  metric : Metric
  hodgeData : HodgeData
  stationaryFamily : StationaryFamily

/-- An obligation for the smooth source-geometry axis.  Concrete work must
derive this candidate from smooth source coordinates and prove the intended
relations among its fields; this interface does not manufacture those laws. -/
structure SmoothGeometryCandidateAxis
    (GeometrySource : Type uGeometrySource)
    (SmoothStructure : Type uSmooth) (Orientation : Type uOrientation)
    (Signature : Type uSignature) (Tetrad : Type uTetrad)
    (Metric : Type uMetric) (HodgeData : Type uHodge)
    (StationaryFamily : Type uStationary) where
  candidateOf : GeometrySource →
    SmoothGeometryCandidate SmoothStructure Orientation Signature Tetrad
      Metric HodgeData StationaryFamily

/-- The canonical typed pullback of two source axes over a shared anchor.
The anchor equality is part of the type, rather than an arbitrary downstream
`Compatible : ... → Prop`.  Concrete anchor maps must still be fixed by the
upstream source modules. -/
abbrev SharedPhysicalSource
    (InternalSource : Type uInternalSource)
    (GeometrySource : Type uGeometrySource) (Anchor : Type uAnchor)
    (internalAnchor : InternalSource → Anchor)
    (geometryAnchor : GeometrySource → Anchor) :=
  { sources : InternalSource × GeometrySource //
    internalAnchor sources.1 = geometryAnchor sources.2 }

namespace SharedPhysicalSource

variable {InternalSource : Type uInternalSource}
variable {GeometrySource : Type uGeometrySource}
variable {Anchor : Type uAnchor}
variable (internalAnchor : InternalSource → Anchor)
variable (geometryAnchor : GeometrySource → Anchor)

/-- Read the internal axis from a typed shared source. -/
def internalProjection
    (source : SharedPhysicalSource InternalSource GeometrySource Anchor
      internalAnchor geometryAnchor) : InternalSource :=
  source.1.1

/-- Read the smooth-geometry axis from a typed shared source. -/
def geometryProjection
    (source : SharedPhysicalSource InternalSource GeometrySource Anchor
      internalAnchor geometryAnchor) : GeometrySource :=
  source.1.2

/-- The joint observation whose injectivity is the pullback faithfulness
condition. -/
def jointProjection
    (source : SharedPhysicalSource InternalSource GeometrySource Anchor
      internalAnchor geometryAnchor) :
    InternalSource × GeometrySource :=
  (source.internalProjection, source.geometryProjection)

/-- The canonical pullback observation is jointly faithful because the shared
source retains the entire axis pair.  This structural fact does not certify
that the supplied anchor maps are physically adequate; concrete producer
modules must define and justify those maps independently. -/
theorem jointProjection_injective
    : Function.Injective
      (jointProjection internalAnchor geometryAnchor) := by
  intro source₁ source₂ hequal
  apply Subtype.ext
  exact hequal

/-- Diagnostic boundary: with a constant `Unit` anchor, the typed pullback is
equivalent to the unrestricted product of both axes.  Thus structural joint
faithfulness alone cannot certify a physically meaningful common origin. -/
def unitAnchorPullbackEquiv :
    SharedPhysicalSource InternalSource GeometrySource Unit
        (fun _ => ()) (fun _ => ()) ≃
      InternalSource × GeometrySource where
  toFun := fun source => source.1
  invFun := fun sources => ⟨sources, rfl⟩
  left_inv := by
    intro source
    apply Subtype.ext
    rfl
  right_inv := by
    intro sources
    rfl

/-- Equality of both axis observations identifies the equal-anchor source
record. -/
theorem eq_of_internalProjection_eq_of_geometryProjection_eq
    {source₁ source₂ : SharedPhysicalSource InternalSource GeometrySource
      Anchor internalAnchor geometryAnchor}
    (hinternal : source₁.internalProjection = source₂.internalProjection)
    (hgeometry : source₁.geometryProjection = source₂.geometryProjection) :
    source₁ = source₂ :=
  jointProjection_injective internalAnchor geometryAnchor
    (Prod.ext hinternal hgeometry)

/-- Assemble the two candidate readouts at one equal-anchor source record.
This is only a shared packaging operation; physical generation remains the
obligation of the two concrete axes and a separately proved cross-axis typed
law. -/
def jointCandidate
    {InternalConstitutive : Type uInternal}
    {CouplingNormalization : Type uCouplings}
    {SmoothStructure : Type uSmooth} {Orientation : Type uOrientation}
    {Signature : Type uSignature} {Tetrad : Type uTetrad}
    {Metric : Type uMetric} {HodgeData : Type uHodge}
    {StationaryFamily : Type uStationary}
    (I : InternalConstitutiveCandidateAxis InternalSource
      InternalConstitutive CouplingNormalization)
    (G : SmoothGeometryCandidateAxis GeometrySource SmoothStructure
      Orientation Signature Tetrad Metric HodgeData StationaryFamily)
    (source : SharedPhysicalSource InternalSource GeometrySource Anchor
      internalAnchor geometryAnchor) :
    InternalConstitutiveCandidate InternalConstitutive
        CouplingNormalization ×
      SmoothGeometryCandidate SmoothStructure Orientation Signature Tetrad
        Metric HodgeData StationaryFamily :=
  (I.candidateOf source.internalProjection,
    G.candidateOf source.geometryProjection)

end SharedPhysicalSource

end PhysicsCore
end SaturationMonoid
