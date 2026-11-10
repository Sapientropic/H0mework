import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.QuadraticGeometryPlebanskiStationaryFamily
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.SU7RicherLineageResponsibility
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.SU7RepresentationIncidenceInternalCandidate

/-!
# Conditional reference-incidence / quadratic-geometry dual-axis candidates

This module advances the two independent physical producer axes without
collapsing one into the other.

* The reference/incidence axis reads the chosen P523 block-incidence carrier
  and computes the three conditional one-loop normalization coefficients from
  its trace input.
* The quadratic-coordinate axis produces a coframe jet, metric, Hodge data,
  pointwise affine/spin connection, omega gluing, and an exact
  finite-coordinate common-action stationary family on its nondegenerate
  slice.
* A typed pullback fixes the complete richer source/phase/field lineage and
  its origin endpoint on both axes.  The combined Hodge/coupling candidate is
  assembled from those two generated outputs; no caller-supplied
  `CrossAxisCompatible` proposition is accepted.

The stationary family has the precise finite, source-aligned strength stated
by `QuadraticGeometryPlebanskiStationaryFamily`: it is not yet a continuum
Plebanski/Einstein producer.  The incidence coefficients now generate
canonical nonzero rational normalization units, but not measured
reference-scale `g_i^2` units.  Consequently this module still does not close
the full stage-two SM/GR constitutive hard gate.

Stage-7 containment note: the reference axis is not an actual P286
representation-restriction producer.  This legacy dual-axis construction
remains a compatibility readout only.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7DualAxisPhysicalCandidate

open StandardModelConstraint
open StandardModelConstraint.RunningSigmaBeta
open GeneratedEndpointQuadraticCoframeSource
open QuadraticGeometryPlebanskiStationaryFamily
open SU7RicherLineageResponsibility
open SU7RepresentationIncidenceInternalCandidate

noncomputable section

/-! ## Quadratic smooth-geometry stationary axis -/

/-- The quadratic source computes geometry and a nonzero finite
common-action stationary-family member. -/
theorem quadraticGeometry_generates_tetradMetricHodgeStationaryFamily
    (source : NondegenerateQuadraticGeometrySource) :
    let candidate := stationaryCandidateOf source
    candidate.jet = source.1.source.jetAt source.1.point ∧
      candidate.geometry.metric = candidate.jet.metric ∧
      candidate.geometry.hodge = lorentzianCoframeHodge ∧
      candidate.stationaryTetrad ≠ 0 ∧
      PlebanskiActionProvenanceAdmissible system rawSubstitution ∧
      residuals.HasNontrivialVariationChannels ∧
      residuals.MasterOnShell candidate.law candidate.stationaryPoint ∧
      residuals.DeltaEOnShell candidate.law candidate.stationaryPoint
        candidate.stationaryTetrad :=
  QuadraticGeometryPlebanskiStationaryFamily.quadraticGeometry_generates_tetradMetricHodgeStationaryFamily
    source

def nonconstantThreeThreeNondegenerateGeometrySource :
    NondegenerateQuadraticGeometrySource :=
  ⟨nonconstantThreeThreeObservation,
    nonconstantCoordinateSource_nondegenerate (3, 3)⟩

theorem nonconstantThreeThree_generates_stationaryGeometry :
    Nonempty QuadraticGeometryStationaryCandidate :=
  ⟨stationaryCandidateOf
    nonconstantThreeThreeNondegenerateGeometrySource⟩

/-! ## Fixed richer-anchor cross-axis pullback -/

/-- Conditional reference-representation source tagged by the complete richer
lineage.  Lineage equality does not turn it into a generated matter carrier. -/
structure RichAnchoredRepresentationSource where
  lineage : RichSourcePhaseFieldLineage
  representation : RepresentationIncidenceSource

/-- Geometry source tagged by the same richer lineage.  Geometry is tied to
the immutable origin endpoint, never to a mutable repaired terminal. -/
structure RichAnchoredQuadraticGeometrySource where
  lineage : RichSourcePhaseFieldLineage
  geometry : NondegenerateQuadraticGeometrySource
  originEndpoint_eq :
    lineage.originEndpoint = geometry.1.endpointAnchor

def representationAnchor
    (source : RichAnchoredRepresentationSource) :
    RichSourcePhaseFieldLineage :=
  source.lineage

def geometryAnchor
    (source : RichAnchoredQuadraticGeometrySource) :
    RichSourcePhaseFieldLineage :=
  source.lineage

/-- The two axes are paired over exact equality of the full richer lineage,
not over endpoint equality alone. -/
abbrev FixedRicherAnchorPhysicalSource :=
  SharedPhysicalSource RichAnchoredRepresentationSource
    RichAnchoredQuadraticGeometrySource RichSourcePhaseFieldLineage
    representationAnchor geometryAnchor

namespace FixedRicherAnchorPhysicalSource

def representationSource
    (source : FixedRicherAnchorPhysicalSource) :
    RichAnchoredRepresentationSource :=
  source.1.1

def geometrySource
    (source : FixedRicherAnchorPhysicalSource) :
    RichAnchoredQuadraticGeometrySource :=
  source.1.2

theorem lineage_eq (source : FixedRicherAnchorPhysicalSource) :
    source.representationSource.lineage =
      source.geometrySource.lineage :=
  source.2

end FixedRicherAnchorPhysicalSource

/-- Typed Standard-Model-facing candidate assembled from the two independent
axis outputs.  It deliberately stops before multiplying a Hodge operator by
unproduced nonzero `g_i^2` units. -/
structure StandardModelHodgeCouplingCandidate where
  spacetimeHodge : LorentzianTwoFormHodgeOperator
  couplingNormalization : IncidenceCouplingNormalizationCandidate

/-- Combined cross-axis output at finite stationary / internal-candidate
strength. -/
structure FixedRicherAnchorCrossAxisCandidate where
  lineage : RichSourcePhaseFieldLineage
  internal :
    InternalConstitutiveCandidate
      SU7BlockIncidenceMatterCarrierCertificate
      IncidenceCouplingNormalizationCandidate
  geometry : QuadraticGeometryStationaryCandidate
  standardModel : StandardModelHodgeCouplingCandidate
  originEndpoint_geometry_eq :
    lineage.originEndpoint = geometry.coordinateSource.endpointAnchor
  hodge_from_geometry :
    standardModel.spacetimeHodge = geometry.geometry.hodge
  coupling_from_internal :
    standardModel.couplingNormalization = internal.couplingNormalization

/-- Construct cross-axis coherence from the two concrete producer definitions
and exact richer-anchor equality.  No arbitrary compatibility predicate is an
argument. -/
def fixedRicherAnchorCrossAxisCandidateOf
    (source : FixedRicherAnchorPhysicalSource) :
    FixedRicherAnchorCrossAxisCandidate :=
  let internal :=
    representationIncidenceCandidateAxis.candidateOf
      source.representationSource.representation
  let geometry :=
    stationaryCandidateOf source.geometrySource.geometry
  { lineage := source.representationSource.lineage
    internal := internal
    geometry := geometry
    standardModel :=
      { spacetimeHodge := geometry.geometry.hodge
        couplingNormalization := internal.couplingNormalization }
    originEndpoint_geometry_eq := by
      calc
        source.representationSource.lineage.originEndpoint =
            source.geometrySource.lineage.originEndpoint :=
          congrArg RichSourcePhaseFieldLineage.originEndpoint
            source.lineage_eq
        _ = source.geometrySource.geometry.1.endpointAnchor :=
          source.geometrySource.originEndpoint_eq
        _ = geometry.coordinateSource.endpointAnchor := rfl
    hodge_from_geometry := rfl
    coupling_from_internal := rfl }

/-- Final coherence statement at the currently proved strength: both axes
share the complete richer lineage, geometry remains tied to its origin, the
Hodge/coupling candidate fields are forced by their respective producers, and
the same geometry output carries its nonzero stationary member and on-shell
proofs. -/
theorem fixedRicherAnchor_crossAxisCoherence
    (source : FixedRicherAnchorPhysicalSource) :
    let candidate := fixedRicherAnchorCrossAxisCandidateOf source
    candidate.lineage.originEndpoint =
        candidate.geometry.coordinateSource.endpointAnchor ∧
      candidate.standardModel.spacetimeHodge =
        candidate.geometry.geometry.hodge ∧
      candidate.standardModel.couplingNormalization =
        candidate.internal.couplingNormalization ∧
      (∀ factor,
        (candidate.standardModel.couplingNormalization.asymptoticB0Unit
          factor : ℚ) ≠ 0) ∧
      candidate.geometry.stationaryTetrad ≠ 0 ∧
      residuals.MasterOnShell candidate.geometry.law
        candidate.geometry.stationaryPoint ∧
      residuals.DeltaEOnShell candidate.geometry.law
        candidate.geometry.stationaryPoint
        candidate.geometry.stationaryTetrad := by
  dsimp only
  exact
    ⟨(fixedRicherAnchorCrossAxisCandidateOf source
        ).originEndpoint_geometry_eq,
      (fixedRicherAnchorCrossAxisCandidateOf source).hodge_from_geometry,
      (fixedRicherAnchorCrossAxisCandidateOf source).coupling_from_internal,
      (fun factor =>
        (fixedRicherAnchorCrossAxisCandidateOf source
          ).standardModel.couplingNormalization.asymptoticB0_ne_zero factor),
      (fixedRicherAnchorCrossAxisCandidateOf source
        ).geometry.stationaryTetrad_ne_zero,
      (fixedRicherAnchorCrossAxisCandidateOf source).geometry.master_onShell,
      (fixedRicherAnchorCrossAxisCandidateOf source).geometry.tetrad_onShell⟩

end
end SU7DualAxisPhysicalCandidate
end PhysicsCore
end SaturationMonoid
