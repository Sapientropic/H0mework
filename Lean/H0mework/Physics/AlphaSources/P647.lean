import H0mework.Physics.AlphaSources.P643
import H0mework.Physics.JointSources.P646

/-!
# Proposition 647: finite alpha_s producer-debt closure

P646 made one primitive axis carry the three current producer nails.  This file
tightens the `alpha_s` nail itself.

The current finite `alpha_s` producer is no longer just a numeric target:

* the QCD/Poincare unified-axis producer is the canonical SU(7)-breaking
  `AlphaStrongResidualGapProducer`;
* its four-source normal form is exactly the canonical four-source receipt;
* the physical finite-geometry producer is object-equal to that same
  unified-axis producer;
* threshold, three-loop-RG, and Higgs/extra-representation are zero on this
  finite layer, while the SU(7)-breaking source carries `89/10000`;
* the same one-axis primitive source still forces the Yukawa depth list and
  typed Jarlskog sum.

Boundary: this closes the present finite producer debt, not the smooth
SU(7)-breaking / threshold-spectrum / three-loop-RG / Higgs-spectrum dynamics
that should eventually produce the same primitive finite fields.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Unified-axis alpha_s producer is the canonical four-source object -/

/-- THEOREM 1: the QCD/Poincare unified-axis residual producer is the
canonical finite SU(7)-breaking residual producer. -/
theorem alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_eq_canonical :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer =
      alphaStrongSU7BreakingResidualGapProducer := by
  exact
    eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_sourceSurface

/-- THEOREM 2: the QCD/Poincare unified-axis producer has exactly the
canonical four-source closure receipt. -/
theorem alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_toFourSource_eq_canonical :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.toFourSourceClosureReceipt =
      alphaStrongCanonicalFourSourceReceipt := by
  rw [alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_eq_canonical,
    alphaStrongSU7BreakingResidualGapProducer_toFourSource_eq_canonical]

/-- THEOREM 3: the unified-axis producer's SU(7)-breaking source carries the
finite alpha-level gap `89/10000`. -/
theorem alphaStrongQCDPoincareUnifiedAxis_su7Source_gap :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
        .su7Breaking =
      (89 : ℚ) / 10000 := by
  change
    alphaStrongQCDPoincareUnifiedAxisContribution .su7Breaking =
      (89 : ℚ) / 10000
  exact qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate_gap

/-- THEOREM 4: threshold, three-loop RG, and Higgs/extra-representation carry
zero contribution on the current finite alpha_s layer. -/
theorem alphaStrongQCDPoincareUnifiedAxis_nonSU7_sources_zero :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threshold = 0 ∧
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threeLoopRG = 0 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .higgsExtraRepresentation = 0 := by
  change
    alphaStrongQCDPoincareUnifiedAxisContribution .threshold = 0 ∧
      alphaStrongQCDPoincareUnifiedAxisContribution .threeLoopRG = 0 ∧
        alphaStrongQCDPoincareUnifiedAxisContribution
            .higgsExtraRepresentation = 0
  simp [alphaStrongQCDPoincareUnifiedAxisContribution]

/-! ## Physical finite producer collapses to the same object -/

/-- THEOREM 5: every current physical finite-geometry producer is object-equal
to the QCD/Poincare unified-axis producer. -/
theorem alphaStrongPhysicalFiniteGeometryProducer_eq_unifiedAxis
    (C : FourDPoincareCertificate.{0})
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    alphaStrongPhysicalFiniteGeometryProducer C e =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer := by
  change
    alphaStrongPoincareResolutionResidualGapProducer C e =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
  exact alphaStrongPoincareResolutionResidualGapProducer_eq_unifiedAxis C e

/-- THEOREM 6: every current physical finite-geometry producer has the
canonical four-source closure receipt. -/
theorem alphaStrongPhysicalFiniteGeometryProducer_toFourSource_eq_canonical_via_unifiedAxis
    (C : FourDPoincareCertificate.{0})
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    (alphaStrongPhysicalFiniteGeometryProducer C e).toFourSourceClosureReceipt =
      alphaStrongCanonicalFourSourceReceipt := by
  rw [alphaStrongPhysicalFiniteGeometryProducer_eq_unifiedAxis C e,
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_toFourSource_eq_canonical]

/-! ## Bundled finite closure certificate -/

/-- Compact certificate: the present finite producer debt for the three main
nails is single-sourced, with the alpha_s producer identified all the way down
to its canonical four-source receipt. -/
structure AlphaStrongFiniteProducerDebtClosureCertificate where
  representation :
    SU7RepresentationPhysicalizationReceipt
  finite_carrier :
    AlphaStrongFiniteCarrierGapProducerReceipt
  unified_axis :
    AlphaStrongQCDPoincareUnifiedAxisProducerReceipt
  producer_faces :
    AlphaStrongCurrentProducerFacesIdentityCertificate
  finite_geometry_canonical :
    AlphaStrongFiniteGeometryCanonicalReceiptCertificate
  one_axis_three_nail :
    OneAxisPrimitiveSourceThreeNailProducerCertificate
      canonicalOneAxisPrimitiveSourceProducer
  unified_axis_eq_canonical :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer =
      alphaStrongSU7BreakingResidualGapProducer
  unified_axis_four_source_canonical :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.toFourSourceClosureReceipt =
      alphaStrongCanonicalFourSourceReceipt
  su7_source_gap :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
        .su7Breaking =
      (89 : ℚ) / 10000
  non_su7_sources_zero :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threshold = 0 ∧
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threeLoopRG = 0 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .higgsExtraRepresentation = 0
  physical_eq_unified_axis :
    ∀ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier),
        alphaStrongPhysicalFiniteGeometryProducer C e =
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
  physical_four_source_canonical :
    ∀ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier),
        (alphaStrongPhysicalFiniteGeometryProducer C e).toFourSourceClosureReceipt =
          alphaStrongCanonicalFourSourceReceipt
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  typed_jarlskog_sum :
    ckmJarlskogFourProductDepthSum
        primitiveCardYukawaProducerInputCandidate.depthTable =
      (ckmCPDepthSum : Int)

/-- THEOREM 7: finite producer-debt closure certificate for the current
three-nail chain. -/
def alphaStrongFiniteProducerDebtClosureCertificate :
    AlphaStrongFiniteProducerDebtClosureCertificate where
  representation := su7RepresentationPhysicalizationReceipt
  finite_carrier := alphaStrongFiniteCarrierGapProducerReceipt
  unified_axis := alphaStrongQCDPoincareUnifiedAxisProducerReceipt
  producer_faces := alphaStrongCurrentProducerFacesIdentityCertificate
  finite_geometry_canonical :=
    alphaStrongFiniteGeometryCanonicalReceiptCertificate
  one_axis_three_nail :=
    canonicalOneAxisPrimitiveSourceThreeNailProducerCertificate
  unified_axis_eq_canonical :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_eq_canonical
  unified_axis_four_source_canonical :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_toFourSource_eq_canonical
  su7_source_gap := alphaStrongQCDPoincareUnifiedAxis_su7Source_gap
  non_su7_sources_zero :=
    alphaStrongQCDPoincareUnifiedAxis_nonSU7_sources_zero
  physical_eq_unified_axis :=
    alphaStrongPhysicalFiniteGeometryProducer_eq_unifiedAxis
  physical_four_source_canonical :=
    alphaStrongPhysicalFiniteGeometryProducer_toFourSource_eq_canonical_via_unifiedAxis
  alpha_inverse_residual :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection
  yukawa_depths :=
    oneAxisPrimitiveSource_forces_yukawaDepths
      canonicalOneAxisPrimitiveSourceProducer
  typed_jarlskog_sum :=
    oneAxisPrimitiveSource_forces_typedJarlskogDepthSum
      canonicalOneAxisPrimitiveSourceProducer

end StandardModelConstraint
end SaturationMonoid
