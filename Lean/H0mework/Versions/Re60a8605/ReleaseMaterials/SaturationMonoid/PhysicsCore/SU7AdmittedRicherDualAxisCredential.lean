import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.SU7A6PhysicalStandingContract
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.SU7DualAxisPhysicalCandidate

/-!
# Physical admission consumed by the richer dual-axis candidate

This module closes the calibrated delivery chain without importing endpoint
atomhood.  Its input contains:

* a native `PhysicalAdmissionCredential` for one endpoint-stable SU7/A6 state;
* an explicit closed phase/H1 cochain (still an attachment, not a generated
  phase theorem);
* the conditional reference-incidence receipt;
* an independent nondegenerate quadratic-geometry source at the immutable
  origin endpoint.

From those data it computes one richer source/phase/field lineage, constructs
both axis sources over exactly that lineage, and returns a proof-relevant
credential containing the seven-facet audit readout, anchor preservation,
nonzero one-loop normalization units, and the finite source-aligned stationary
family.  No endpoint realization, atomhood, `Nat.Prime`, or FactorHolonomy
certificate occurs in the input or output.

Boundary: the phase cochain and the independent geometry coefficients remain
explicit source coordinates.  The stationary member has the finite candidate
strength documented in `QuadraticGeometryPlebanskiStationaryFamily`; the
normalization units are not measured reference-scale `g_i^2`.

Stage-7 containment note: consuming physical standing admission does not make
the independent P523 reference receipt source-generated.  This module remains
a compatibility credential and is not used by the Stage-4/5/6 physical
dynamics chain or the canonical pre-P950 adapter.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7AdmittedRicherDualAxisCredential

open StandardModelConstraint
open SU7A6PhysicalStandingContract
open SU7RicherLineageResponsibility
open SU7RepresentationIncidenceInternalCandidate
open QuadraticGeometryPlebanskiStationaryFamily
open SU7DualAxisPhysicalCandidate

noncomputable section

/-- All source coordinates needed to assemble the admitted richer dual-axis
candidate.  The final credential is not accepted as a field. -/
structure AdmittedRicherDualAxisSource
    (scale : RawAffineScaleValidity) where
  state : State scale
  admission : PhysicalAdmissionCredential scale state
  phaseCochain : ComponentPhaseCochain
  h1Closed : ComponentH1Closed phaseCochain
  originEndpoint : Nat × Nat
  currentEndpoint : Nat × Nat
  representation : RepresentationIncidenceSource
  geometry : NondegenerateQuadraticGeometrySource
  originEndpoint_geometry_eq :
    originEndpoint = geometry.1.endpointAnchor

namespace AdmittedRicherDualAxisSource

def anchor
    {scale : RawAffineScaleValidity}
    (source : AdmittedRicherDualAxisSource scale) :
    SourcePhaseFieldAnchor :=
  SourcePhaseFieldAnchor.ofStandingState scale source.state
    source.phaseCochain source.h1Closed

def lineage
    {scale : RawAffineScaleValidity}
    (source : AdmittedRicherDualAxisSource scale) :
    RichSourcePhaseFieldLineage where
  anchor := source.anchor
  originEndpoint := source.originEndpoint
  endpoint := source.currentEndpoint

/-- Both axes are constructed over definitionally the same richer lineage. -/
def fixedRicherAnchorSource
    {scale : RawAffineScaleValidity}
    (source : AdmittedRicherDualAxisSource scale) :
    FixedRicherAnchorPhysicalSource :=
  ⟨(
      { lineage := source.lineage
        representation := source.representation },
      { lineage := source.lineage
        geometry := source.geometry
        originEndpoint_eq := source.originEndpoint_geometry_eq }),
    rfl⟩

def candidate
    {scale : RawAffineScaleValidity}
    (source : AdmittedRicherDualAxisSource scale) :
    FixedRicherAnchorCrossAxisCandidate :=
  fixedRicherAnchorCrossAxisCandidateOf source.fixedRicherAnchorSource

end AdmittedRicherDualAxisSource

/-- Proof-relevant final credential at the currently proved dual-axis
strength.  Its first field is obtained by consuming the native physical
admission credential; all remaining fields retain the richer anchor and the
two independently generated candidate axes. -/
structure PhysicalAdmissionDualAxisCredential
    (scale : RawAffineScaleValidity)
    (source : AdmittedRicherDualAxisSource scale) : Prop where
  auditSafe :
    CSafe (SU7A6SevenDirectionStandingAudit.predicates scale) source.state
  sourceRoot_preserved :
    source.candidate.lineage.anchor.sourceRoot =
      source.state.six.base.rootLabel
  sourcePathData_preserved :
    source.candidate.lineage.anchor.sourcePathData =
      source.state.six.base.moves
  phaseCochain_preserved :
    source.candidate.lineage.anchor.phaseCochain = source.phaseCochain
  h1Ledger_closed :
    source.candidate.lineage.anchor.h1Ledger = 0
  sigma_preserved :
    source.candidate.lineage.anchor.sigma = scale.sigma
  field_preserved :
    source.candidate.lineage.anchor.field = source.state.six.base.field
  originEndpoint_preserved :
    source.candidate.lineage.originEndpoint = source.originEndpoint
  geometry_at_origin :
    source.candidate.lineage.originEndpoint =
      source.candidate.geometry.coordinateSource.endpointAnchor
  hodge_from_geometry :
    source.candidate.standardModel.spacetimeHodge =
      source.candidate.geometry.geometry.hodge
  coupling_from_representation :
    source.candidate.standardModel.couplingNormalization =
      source.candidate.internal.couplingNormalization
  normalizationUnits_nonzero :
    ∀ factor,
      (source.candidate.standardModel.couplingNormalization.asymptoticB0Unit
        factor : ℚ) ≠ 0
  stationaryTetrad_nonzero :
    source.candidate.geometry.stationaryTetrad ≠ 0
  master_onShell :
    residuals.MasterOnShell source.candidate.geometry.law
      source.candidate.geometry.stationaryPoint
  tetrad_onShell :
    residuals.DeltaEOnShell source.candidate.geometry.law
      source.candidate.geometry.stationaryPoint
      source.candidate.geometry.stationaryTetrad

/-- The native physical admission is consumed to construct the complete
credential; no audit atom, endpoint realization, or atomhood witness is an
input to the dual-axis construction. -/
def physicalAdmissionDualAxisCredentialOf
    {scale : RawAffineScaleValidity}
    (source : AdmittedRicherDualAxisSource scale) :
    PhysicalAdmissionDualAxisCredential scale source where
  auditSafe :=
    auditSafe_of_physicalAdmissionCredential scale source.admission
  sourceRoot_preserved := rfl
  sourcePathData_preserved := rfl
  phaseCochain_preserved := rfl
  h1Ledger_closed := source.h1Closed
  sigma_preserved := rfl
  field_preserved := rfl
  originEndpoint_preserved := rfl
  geometry_at_origin := source.candidate.originEndpoint_geometry_eq
  hodge_from_geometry := source.candidate.hodge_from_geometry
  coupling_from_representation := source.candidate.coupling_from_internal
  normalizationUnits_nonzero := fun factor =>
    source.candidate.standardModel.couplingNormalization.asymptoticB0_ne_zero
      factor
  stationaryTetrad_nonzero :=
    source.candidate.geometry.stationaryTetrad_ne_zero
  master_onShell := source.candidate.geometry.master_onShell
  tetrad_onShell := source.candidate.geometry.tetrad_onShell

theorem physicalAdmission_generates_richerDualAxisCredential
    {scale : RawAffineScaleValidity}
    (source : AdmittedRicherDualAxisSource scale) :
    PhysicalAdmissionDualAxisCredential scale source :=
  physicalAdmissionDualAxisCredentialOf source

end
end SU7AdmittedRicherDualAxisCredential
end PhysicsCore
end SaturationMonoid
