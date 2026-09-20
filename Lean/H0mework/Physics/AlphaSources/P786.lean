import H0mework.Physics.AlphaSources.P785

/-!
# Proposition 786: alpha_s four-source producer identity

P785 computes the four requested alpha_s source coordinates directly from the
SU(7) breaking / threshold / RG / Higgs-extra spectrum surfaces.  This file
welds that explicit receipt back to the already canonical finite alpha source
surface.

The result is an identity theorem, not another numerical closure: the
independent four-source receipt, the canonical four-source receipt, and the
unified-axis alpha residual producer are the same producer face.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Receipt and producer identity -/

/-- THEOREM 1: the P785 independently computed four-source receipt is exactly
the canonical finite-law receipt. -/
theorem alphaStrongIndependentFourSourceReceipt_eq_canonical :
    alphaStrongIndependentFourSourceReceipt =
      alphaStrongCanonicalFourSourceReceipt := by
  calc
    alphaStrongIndependentFourSourceReceipt =
        alphaStrongIndependentFourSourceReceipt.toGapProducer.toFourSourceClosureReceipt := by
          exact
            (AlphaStrongFourSourceClosureReceipt.toGapProducer_toFourSourceClosureReceipt
              alphaStrongIndependentFourSourceReceipt).symm
    _ =
        alphaStrongCanonicalFourSourceReceipt.toGapProducer.toFourSourceClosureReceipt := by
          have hprod :
              alphaStrongIndependentFourSourceReceipt.toGapProducer =
                alphaStrongCanonicalFourSourceReceipt.toGapProducer := by
            apply AlphaStrongResidualGapProducer.ext
            intro s
            cases s <;>
              simp [AlphaStrongFourSourceClosureReceipt.toGapProducer,
                AlphaStrongFourSourceClosureReceipt.contribution,
                alphaStrongIndependentFourSourceReceipt,
                alphaStrongCanonicalFourSourceReceipt,
                alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000,
                alphaStrongThresholdMismatchSourceGap_eq_zero,
                alphaStrongThreeLoopRGMismatchSourceGap_eq_zero,
                alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero,
                alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
          exact congrArg AlphaStrongResidualGapProducer.toFourSourceClosureReceipt hprod
    _ = alphaStrongCanonicalFourSourceReceipt := by
          exact
            AlphaStrongFourSourceClosureReceipt.toGapProducer_toFourSourceClosureReceipt
              alphaStrongCanonicalFourSourceReceipt

/-- THEOREM 2: the P785 four-source contribution function is the canonical
unified-axis alpha contribution function. -/
theorem alphaStrongIndependentFourSourceContribution_eq_unifiedAxis :
    alphaStrongFourSourceIndependentContribution =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution := by
  funext s
  have hreceipt :
      alphaStrongIndependentFourSourceReceipt.toGapProducer =
        alphaStrongCanonicalFourSourceReceipt.toGapProducer := by
    rw [alphaStrongIndependentFourSourceReceipt_eq_canonical]
  have hcanon :
      alphaStrongCanonicalFourSourceReceipt.toGapProducer =
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer := by
    calc
      alphaStrongCanonicalFourSourceReceipt.toGapProducer =
          (AlphaStrongFourSourceClosureReceipt.toGapProducer
            (AlphaStrongResidualGapProducer.toFourSourceClosureReceipt
              alphaStrongQCDPoincareUnifiedAxisResidualGapProducer)) := by
            rw [alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_toFourSource_eq_canonical]
      _ = alphaStrongQCDPoincareUnifiedAxisResidualGapProducer := by
            exact
              AlphaStrongResidualGapProducer.toFourSourceClosureReceipt_toGapProducer
                alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
  have hfun :=
    congrArg AlphaStrongResidualGapProducer.contribution
      (hreceipt.trans hcanon)
  have hleft :
      alphaStrongIndependentFourSourceReceipt.toGapProducer.contribution =
        alphaStrongFourSourceIndependentContribution := by
    exact alphaStrongIndependentFourSourceReceipt_contribution
  calc
    alphaStrongFourSourceIndependentContribution s =
        alphaStrongIndependentFourSourceReceipt.toGapProducer.contribution s := by
          rw [hleft]
    _ = alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution s := by
          rw [hfun]

/-- THEOREM 3: the P785 receipt's producer is the canonical unified-axis alpha
residual producer. -/
theorem alphaStrongIndependentFourSourceReceipt_toGapProducer_eq_unifiedAxis :
    alphaStrongIndependentFourSourceReceipt.toGapProducer =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer := by
  calc
    alphaStrongIndependentFourSourceReceipt.toGapProducer =
        alphaStrongCanonicalFourSourceReceipt.toGapProducer := by
          rw [alphaStrongIndependentFourSourceReceipt_eq_canonical]
    _ =
        (AlphaStrongFourSourceClosureReceipt.toGapProducer
          (AlphaStrongResidualGapProducer.toFourSourceClosureReceipt
            alphaStrongQCDPoincareUnifiedAxisResidualGapProducer)) := by
          rw [alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_toFourSource_eq_canonical]
    _ = alphaStrongQCDPoincareUnifiedAxisResidualGapProducer := by
          exact
            AlphaStrongResidualGapProducer.toFourSourceClosureReceipt_toGapProducer
              alphaStrongQCDPoincareUnifiedAxisResidualGapProducer

/-- THEOREM 4: P785's source-surface proof is exactly the canonical SU7 finite
source surface after the receipt/producer identity. -/
theorem alphaStrongIndependentFourSourceReceipt_sourceSurface_eq_unifiedAxis :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer := by
  rw [← alphaStrongIndependentFourSourceReceipt_toGapProducer_eq_unifiedAxis]
  exact alphaStrongIndependentFourSourceReceipt_sourceSurface

/-! ## Bundled certificate -/

/-- The explicit four-source computation, canonical four-source receipt,
unified-axis alpha producer, full-beta source normal form, and
representation/matter/Higgs producer are one alpha_s producer face. -/
structure AlphaStrongFourSourceIdentityProducerCertificate : Prop where
  independent_four_source :
    AlphaStrongIndependentFourSourceResidualProducerCertificate
  source_normal_form :
    AlphaStrongResidualProducerSourceNormalFormCertificate
  representation_residual_source :
    AlphaStrongSU7RepresentationResidualSourceCertificate
  receipt_eq_canonical :
    alphaStrongIndependentFourSourceReceipt =
      alphaStrongCanonicalFourSourceReceipt
  contribution_eq_unified_axis :
    alphaStrongFourSourceIndependentContribution =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
  receipt_to_producer_eq_unified_axis :
    alphaStrongIndependentFourSourceReceipt.toGapProducer =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
  source_surface :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFourSourceIndependentContribution s) =
      -((89000 : ℚ) / 128511)

/-- THEOREM 5: alpha_s four-source identity producer certificate. -/
theorem alphaStrongFourSourceIdentityProducerCertificate :
    AlphaStrongFourSourceIdentityProducerCertificate where
  independent_four_source :=
    alphaStrongIndependentFourSourceResidualProducerCertificate
  source_normal_form :=
    alphaStrongResidualProducerSourceNormalFormCertificate
  representation_residual_source :=
    alphaStrongSU7RepresentationResidualSourceCertificate
  receipt_eq_canonical :=
    alphaStrongIndependentFourSourceReceipt_eq_canonical
  contribution_eq_unified_axis :=
    alphaStrongIndependentFourSourceContribution_eq_unifiedAxis
  receipt_to_producer_eq_unified_axis :=
    alphaStrongIndependentFourSourceReceipt_toGapProducer_eq_unifiedAxis
  source_surface :=
    alphaStrongIndependentFourSourceReceipt_sourceSurface_eq_unifiedAxis
  inverse_residual :=
    alphaStrongIndependentFourSource_inverseResidual

end StandardModelConstraint
end SaturationMonoid
