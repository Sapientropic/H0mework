import H0mework.Computation.Phase.P759
import H0mework.Physics.JointSources.P770

/-!
# Proposition 771: input-surface alpha residual source decomposition

P770 welds the accepted input surface to the physicalized SU(7) finite readout.
This file pushes the alpha leg one step further into its source decomposition:

* the input alpha gap is exactly the `.su7Breaking` contribution;
* the threshold, three-loop RG, and Higgs-extra channels are zero on this
  finite source surface;
* the `.su7Breaking` contribution is the whole produced gap;
* the active-source predicate is the singleton `s = .su7Breaking`.

So the input-surface alpha residual is not a four-source tuning residue.  It is
the finite SU(7)-breaking source normal form read back through the input
surface.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-- THEOREM 1: the input alpha gap is exactly the SU(7)-breaking contribution
of the canonical unified-axis alpha producer. -/
theorem inputSurface_alphaGap_eq_su7BreakingContribution
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.1.producedGap =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
        .su7Breaking := by
  calc
    C.1.producedGap = (89 : ℚ) / 10000 := by
      exact inputSurfaceFiniteNumerical_alphaGap_eq C hC
    _ =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
        .su7Breaking := by
      exact
        alphaStrongIndependentResidualProducerCertificate.su7_breaking_gap.symm

/-- THEOREM 2: the input alpha gap is the whole produced gap of the canonical
unified-axis alpha producer. -/
theorem inputSurface_alphaGap_eq_unifiedAxisProducedGap
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.1.producedGap =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap := by
  calc
    C.1.producedGap =
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking := by
      exact inputSurface_alphaGap_eq_su7BreakingContribution C hC
    _ = alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap := by
      exact
        alphaStrong_sourceSurface_su7_contribution_eq_producedGap
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
          alphaStrongIndependentResidualProducerCertificate.finite_source_surface

/-- THEOREM 3: the three non-SU7 alpha residual sources are zero on the
canonical unified-axis producer. -/
theorem inputSurface_alpha_nonSu7Sources_zero :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threshold = 0 ∧
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threeLoopRG = 0 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .higgsExtraRepresentation = 0 :=
  alphaStrongIndependentResidualProducerCertificate.threshold_rg_higgs_zero

/-- THEOREM 4: the canonical unified-axis producer has singleton active source
`.su7Breaking`. -/
theorem inputSurface_alpha_activeSource_iff_su7Breaking
    (s : AlphaStrongResidualSource) :
    AlphaStrongActiveResidualSource
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
      s = .su7Breaking :=
  alphaStrongIndependentResidualProducerCertificate.active_source_iff_su7 s

/-- THEOREM 5: inverse transport of the SU7 contribution itself gives the
canonical alpha inverse residual. -/
theorem inputSurface_su7Contribution_inverseResidual
    :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking) =
      -((89000 : ℚ) / 128511) := by
  rw [
    alphaStrong_sourceSurface_su7_contribution_eq_producedGap
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
      alphaStrongIndependentResidualProducerCertificate.finite_source_surface]
  exact alphaStrongIndependentResidualProducerCertificate.inverse_residual

/-- THEOREM 6: the input alpha residual can be computed directly from the
single SU7 source contribution. -/
theorem inputSurface_alphaResidual_eq_su7ContributionResidual
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        C.1.producedGap =
      inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking) := by
  rw [inputSurface_alphaGap_eq_su7BreakingContribution C hC]

/-- The accepted input-surface alpha leg is exactly the SU7 active-source
normal form. -/
structure InputSurfaceAlphaSourceDecompositionCertificate : Prop where
  input_surface_physicalized_bridge :
    InputSurfacePhysicalizedProducerBridgeCertificate
  alpha_active_source_normal_form :
    AlphaStrongActiveSourceNormalFormCertificate
  alpha_independent_residual :
    Nonempty AlphaStrongIndependentResidualProducerCertificate
  finite_source_surface :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
  input_gap_eq_su7_contribution :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.1.producedGap =
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .su7Breaking
  input_gap_eq_unified_axis_produced_gap :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.1.producedGap =
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap
  non_su7_sources_zero :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threshold = 0 ∧
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threeLoopRG = 0 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .higgsExtraRepresentation = 0
  active_source_iff_su7 :
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongActiveResidualSource
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
        s = .su7Breaking
  su7_contribution_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking) =
      -((89000 : ℚ) / 128511)
  input_residual_eq_su7_contribution_residual :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.1.producedGap =
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
              .su7Breaking)

/-- THEOREM 7: input-surface alpha residual source decomposition certificate. -/
theorem inputSurfaceAlphaSourceDecompositionCertificate :
    InputSurfaceAlphaSourceDecompositionCertificate where
  input_surface_physicalized_bridge :=
    inputSurfacePhysicalizedProducerBridgeCertificate
  alpha_active_source_normal_form :=
    alphaStrongActiveSourceNormalFormCertificate
  alpha_independent_residual :=
    ⟨alphaStrongIndependentResidualProducerCertificate⟩
  finite_source_surface :=
    alphaStrongIndependentResidualProducerCertificate.finite_source_surface
  input_gap_eq_su7_contribution :=
    inputSurface_alphaGap_eq_su7BreakingContribution
  input_gap_eq_unified_axis_produced_gap :=
    inputSurface_alphaGap_eq_unifiedAxisProducedGap
  non_su7_sources_zero :=
    inputSurface_alpha_nonSu7Sources_zero
  active_source_iff_su7 :=
    inputSurface_alpha_activeSource_iff_su7Breaking
  su7_contribution_inverse_residual :=
    inputSurface_su7Contribution_inverseResidual
  input_residual_eq_su7_contribution_residual :=
    inputSurface_alphaResidual_eq_su7ContributionResidual

end StandardModelConstraint
end SaturationMonoid
