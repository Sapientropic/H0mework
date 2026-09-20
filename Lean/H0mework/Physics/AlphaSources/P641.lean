import H0mework.Physics.JointSources.P640
import H0mework.Physics.AlphaSources.P618

/-!
# Proposition 641: finite geometry is the positive alpha_s source-label producer

P640 proves the negative side: the active source label cannot be recovered from
the scalar alpha residual.  P613/P618 already supply the positive finite layer:
a finite-geometry witness exists exactly for `su7Breaking`, and the current
representation / QCD / Poincare package produces such a witness.

This file connects those two facts.  The source-sensitive selector can be
implemented by finite-geometry surface membership, and that selector:

* accepts the canonical SU7 receipt;
* rejects the threshold-only same-gap receipt;
* recovers the correct source labels on both witnesses;
* is provably not total-gap-only.

Boundary: this is still the finite-geometry producer, not the smooth
threshold-spectrum or three-loop-RG calculation.  It closes the next input
shape: the future producer must supply finite-geometry / representation data
that selects `su7Breaking`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Finite-geometry surface membership for the two branch witnesses -/

/-- THEOREM 1: the canonical SU7-only receipt lies on the finite-geometry
surface. -/
theorem alphaStrongCanonicalFourSourceReceipt_finiteGeometrySurface :
    AlphaStrongResidualProducerFiniteGeometrySurface
      alphaStrongCanonicalFourSourceReceipt.toGapProducer := by
  exact
    (alphaStrongResidualProducerFiniteSourceSurface_iff_finiteGeometrySurface
      alphaStrongCanonicalFourSourceReceipt.toGapProducer).mp
        alphaStrongCanonicalFourSourceReceipt_sourceSurface

/-- THEOREM 2: the threshold-only same-gap receipt is outside the
finite-geometry surface. -/
theorem alphaStrongThresholdOnlyFourSourceReceipt_not_finiteGeometrySurface :
    ¬ AlphaStrongResidualProducerFiniteGeometrySurface
        alphaStrongThresholdOnlyFourSourceReceipt.toGapProducer := by
  intro hgeo
  exact
    alphaStrongThresholdOnlyFourSourceReceipt_not_sourceSurface
      ((alphaStrongResidualProducerFiniteSourceSurface_iff_finiteGeometrySurface
        alphaStrongThresholdOnlyFourSourceReceipt.toGapProducer).mpr hgeo)

/-! ## Finite-geometry active-source selector -/

/-- Active-source label selected by finite-geometry surface membership.

The fallback branch is intentionally `threshold`: it is the explicit same-gap
counter-receipt from P638/P640.  The point is not to model all non-SU7 physics;
the point is to witness that the finite-geometry label selector separates the
canonical branch from the scalar-equivalent threshold branch. -/
def alphaStrongFiniteGeometryActiveSourceSelector
    (R : AlphaStrongFourSourceClosureReceipt) :
    AlphaStrongResidualSource :=
  by
    classical
    exact
      if AlphaStrongResidualProducerFiniteGeometrySurface R.toGapProducer then
        AlphaStrongResidualSource.su7Breaking
      else
        AlphaStrongResidualSource.threshold

/-- THEOREM 3: finite geometry selects `su7Breaking` on the canonical receipt.
-/
theorem alphaStrongFiniteGeometryActiveSourceSelector_canonical :
    alphaStrongFiniteGeometryActiveSourceSelector
        alphaStrongCanonicalFourSourceReceipt =
      AlphaStrongResidualSource.su7Breaking := by
  classical
  unfold alphaStrongFiniteGeometryActiveSourceSelector
  rw [if_pos alphaStrongCanonicalFourSourceReceipt_finiteGeometrySurface]

/-- THEOREM 4: finite geometry selects `threshold` on the threshold-only
same-gap receipt. -/
theorem alphaStrongFiniteGeometryActiveSourceSelector_threshold :
    alphaStrongFiniteGeometryActiveSourceSelector
        alphaStrongThresholdOnlyFourSourceReceipt =
      AlphaStrongResidualSource.threshold := by
  classical
  unfold alphaStrongFiniteGeometryActiveSourceSelector
  rw [if_neg alphaStrongThresholdOnlyFourSourceReceipt_not_finiteGeometrySurface]

/-- THEOREM 5: the finite-geometry selector recovers the correct active-source
labels on the two branch witnesses. -/
theorem alphaStrongFiniteGeometryActiveSourceSelector_correctOnBranchWitnesses :
    AlphaStrongActiveSourceLabelCorrectOnBranchWitnesses
      alphaStrongFiniteGeometryActiveSourceSelector := by
  constructor
  · exact alphaStrongFiniteGeometryActiveSourceSelector_canonical
  · exact alphaStrongFiniteGeometryActiveSourceSelector_threshold

/-- THEOREM 6: the finite-geometry active-source selector is not total-gap-only.
-/
theorem alphaStrongFiniteGeometryActiveSourceSelector_not_totalGapOnly :
    ¬ AlphaStrongFourSourceTotalGapOnly
        alphaStrongFiniteGeometryActiveSourceSelector := by
  intro hgap
  exact
    alphaStrong_no_totalGapOnly_activeSourceLabelSelector
      alphaStrongFiniteGeometryActiveSourceSelector
      hgap
      alphaStrongFiniteGeometryActiveSourceSelector_correctOnBranchWitnesses

/-! ## Representation / QCD / Poincare package emits the SU7 label -/

/-- THEOREM 7: any P618 finite physical producer is selected as `su7Breaking`
by the finite-geometry active-source selector after conversion to the
four-source receipt normal form. -/
theorem alphaStrongPhysicalFiniteGeometryProducer_receiptSelector_su7
    (C : FourDPoincareCertificate.{0})
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    alphaStrongFiniteGeometryActiveSourceSelector
        (alphaStrongPhysicalFiniteGeometryProducer C e).toFourSourceClosureReceipt =
      AlphaStrongResidualSource.su7Breaking := by
  classical
  unfold alphaStrongFiniteGeometryActiveSourceSelector
  rw [if_pos]
  simpa [AlphaStrongResidualGapProducer.toFourSourceClosureReceipt_toGapProducer]
    using alphaStrongPhysicalFiniteGeometryProducer_finiteGeometrySurface C e

/-! ## Receipt -/

/-- Compact receipt connecting the finite-geometry producer to the P640
source-label no-scalar-recovery theorem. -/
structure AlphaStrongFiniteGeometrySourceLabelProducerCertificate where
  witness_iff_su7 :
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongFiniteGeometryWitness s ↔ s = .su7Breaking
  canonical_on_geometry_surface :
    AlphaStrongResidualProducerFiniteGeometrySurface
      alphaStrongCanonicalFourSourceReceipt.toGapProducer
  threshold_not_geometry_surface :
    ¬ AlphaStrongResidualProducerFiniteGeometrySurface
        alphaStrongThresholdOnlyFourSourceReceipt.toGapProducer
  selector_correct_on_branch_witnesses :
    AlphaStrongActiveSourceLabelCorrectOnBranchWitnesses
      alphaStrongFiniteGeometryActiveSourceSelector
  selector_not_total_gap_only :
    ¬ AlphaStrongFourSourceTotalGapOnly
        alphaStrongFiniteGeometryActiveSourceSelector
  physical_producer_selects_su7 :
    ∀ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier),
        alphaStrongFiniteGeometryActiveSourceSelector
            ((alphaStrongPhysicalFiniteGeometryProducer C e)
              |>.toFourSourceClosureReceipt) =
          AlphaStrongResidualSource.su7Breaking
  physical_producer_active_support :
    ∀ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier)
      (s : AlphaStrongResidualSource),
        AlphaStrongResidualActiveSourceSupport
            (alphaStrongPhysicalFiniteGeometryProducer C e).contribution s ↔
          s = .su7Breaking
  representation_receipt :
    SU7RepresentationPhysicalizationReceipt

/-- THEOREM 8: finite-geometry source-label producer certificate. -/
def alphaStrongFiniteGeometrySourceLabelProducerCertificate :
    AlphaStrongFiniteGeometrySourceLabelProducerCertificate where
  witness_iff_su7 := alphaStrongFiniteGeometryWitness_iff_su7
  canonical_on_geometry_surface :=
    alphaStrongCanonicalFourSourceReceipt_finiteGeometrySurface
  threshold_not_geometry_surface :=
    alphaStrongThresholdOnlyFourSourceReceipt_not_finiteGeometrySurface
  selector_correct_on_branch_witnesses :=
    alphaStrongFiniteGeometryActiveSourceSelector_correctOnBranchWitnesses
  selector_not_total_gap_only :=
    alphaStrongFiniteGeometryActiveSourceSelector_not_totalGapOnly
  physical_producer_selects_su7 := by
    intro C e
    exact alphaStrongPhysicalFiniteGeometryProducer_receiptSelector_su7 C e
  physical_producer_active_support := by
    intro C e s
    exact alphaStrongPhysicalFiniteGeometryProducer_activeSupport_iff C e s
  representation_receipt :=
    su7RepresentationPhysicalizationReceipt

end StandardModelConstraint
end SaturationMonoid
