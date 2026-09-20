import H0mework.Physics.SourceForms.P781

/-!
# Proposition 782: structural alpha_s producer normal form

P781 roofs the concrete producer numerical chain.  The remaining pressure on
the alpha leg is sharper: the `-89000/128511` inverse residual should not only
be attached to the accepted source surface; it should be read from the single
QCD/Poincare structural axis that already carries the finite producer.

P627 supplies that axis:

* `axis = b0_QCD + PoincareSlots_4D = 7 + 3 = 10`;
* `visible = axis - 1 = 9`;
* `alpha_em denominator = 2^7 + visible = 137`;
* `SU(7)-breaking numerator = 137 - 48 = 89`;
* `denominator = axis^4 = 10000`.

This file welds that structural axis directly to the current unified-axis
active-source producer.  The result is the alpha-side producer normal form:
structural carrier, source surface, active singleton, alpha-level gap, and
inverse residual are one object.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-! ## Direct structural formula -/

/-- THEOREM 1: the QCD/Poincare structural formula itself closes to
`89/10000`.

This is the naked axis formula:

`((2^7 + (axis - 1)) - dim SU(7)) / axis^4`,

with `axis = b0_QCD + PoincareSlots_4D = 10`.
-/
theorem alphaStrongStructuralAxisGapFormula_eq_89_div_10000 :
    (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
        su7GaugeFreedomDimension ℚ) /
      (alphaStrongQCDPoincareResolutionAxis ^
        alphaStrongResidualResolutionExponent) =
      (89 : ℚ) / 10000 := by
  rw [alphaStrongQCDPoincareStructuralAlphaEMDenominator_eq_137,
    alphaStrongQCDPoincareResolutionAxis_eq_ten]
  norm_num [su7GaugeFreedomDimension, alphaStrongResidualResolutionExponent]

/-- THEOREM 2: the unified-axis alpha-gap candidate is exactly the structural
axis formula. -/
theorem qcdPoincareUnifiedAxisAlphaGap_eq_structuralFormula :
    qcdPoincareUnifiedAxisAlphaStrongSU7BreakingGapCandidate.gap =
      (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
          su7GaugeFreedomDimension ℚ) /
        (alphaStrongQCDPoincareResolutionAxis ^
          alphaStrongResidualResolutionExponent) := by
  rfl

/-- THEOREM 3: the structural axis formula transports to the exact inverse
residual `-89000/128511`. -/
theorem alphaStrongStructuralAxisFormula_inverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        ((alphaStrongQCDPoincareStructuralAlphaEMDenominator -
            su7GaugeFreedomDimension ℚ) /
          (alphaStrongQCDPoincareResolutionAxis ^
            alphaStrongResidualResolutionExponent)) =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongStructuralAxisGapFormula_eq_89_div_10000]
  norm_num [inverseCorrectionFromAlphaGap, alphaStrongTwoLoopSMOutput]

/-! ## Structural producer equals the current active-source producer -/

/-- THEOREM 4: the P626 structural QCD/Poincare producer lies on the same
finite source surface. -/
theorem alphaStrongQCDPoincareStructuralProducer_sourceSurface :
    AlphaStrongResidualProducerFiniteSourceSurface
      (alphaStrongQCDPoincareResidualGapProducer
        unifiedGaugeIntoAlphaEMStructural) :=
  alphaStrongQCDPoincareContribution_law unifiedGaugeIntoAlphaEMStructural

/-- THEOREM 5: the P626 structural producer is object-equal to the current
P627/P647 unified-axis producer. -/
theorem alphaStrongQCDPoincareStructuralProducer_eq_unifiedAxis :
    alphaStrongQCDPoincareResidualGapProducer
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer := by
  rw [eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface
      (alphaStrongQCDPoincareResidualGapProducer
        unifiedGaugeIntoAlphaEMStructural)
      alphaStrongQCDPoincareStructuralProducer_sourceSurface]
  rw [alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_eq_canonical]

/-- THEOREM 6: the current unified-axis producer's active source carries
exactly the structural axis formula. -/
theorem alphaStrongUnifiedAxis_su7Source_eq_structuralFormula :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
        .su7Breaking =
      (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
          su7GaugeFreedomDimension ℚ) /
        (alphaStrongQCDPoincareResolutionAxis ^
          alphaStrongResidualResolutionExponent) := by
  rw [alphaStrongQCDPoincareUnifiedAxis_su7Source_gap,
    alphaStrongStructuralAxisGapFormula_eq_89_div_10000]

/-- THEOREM 7: the current unified-axis producer's produced gap is exactly the
structural axis formula. -/
theorem alphaStrongUnifiedAxis_producedGap_eq_structuralFormula :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
          su7GaugeFreedomDimension ℚ) /
        (alphaStrongQCDPoincareResolutionAxis ^
          alphaStrongResidualResolutionExponent) := by
  rw [← alphaStrongUnifiedAxis_su7Source_eq_structuralFormula]
  exact
    (alphaStrong_sourceSurface_su7_contribution_eq_producedGap
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_sourceSurface).symm

/-! ## Bundled alpha producer normal form -/

/-- One certificate saying the alpha residual is produced by the structural
QCD/Poincare axis and then read as the current singleton active source. -/
structure AlphaStrongStructuralProducerNormalFormCertificate : Prop where
  qcd_poincare_receipt :
    Nonempty
      (AlphaStrongQCDPoincareProducerReceipt unifiedGaugeIntoAlphaEMStructural)
  unified_axis_receipt :
    Nonempty AlphaStrongQCDPoincareUnifiedAxisProducerReceipt
  finite_debt_closure :
    Nonempty AlphaStrongFiniteProducerDebtClosureCertificate
  structural_gap_formula :
    (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
        su7GaugeFreedomDimension ℚ) /
      (alphaStrongQCDPoincareResolutionAxis ^
        alphaStrongResidualResolutionExponent) =
      (89 : ℚ) / 10000
  structural_formula_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        ((alphaStrongQCDPoincareStructuralAlphaEMDenominator -
            su7GaugeFreedomDimension ℚ) /
          (alphaStrongQCDPoincareResolutionAxis ^
            alphaStrongResidualResolutionExponent)) =
      -((89000 : ℚ) / 128511)
  structural_producer_source_surface :
    AlphaStrongResidualProducerFiniteSourceSurface
      (alphaStrongQCDPoincareResidualGapProducer
        unifiedGaugeIntoAlphaEMStructural)
  structural_producer_eq_unified_axis :
    alphaStrongQCDPoincareResidualGapProducer
        unifiedGaugeIntoAlphaEMStructural =
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer
  active_source_eq_structural_formula :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
        .su7Breaking =
      (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
          su7GaugeFreedomDimension ℚ) /
        (alphaStrongQCDPoincareResolutionAxis ^
          alphaStrongResidualResolutionExponent)
  produced_gap_eq_structural_formula :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
          su7GaugeFreedomDimension ℚ) /
        (alphaStrongQCDPoincareResolutionAxis ^
          alphaStrongResidualResolutionExponent)
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  active_source_normal_form :
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .su7Breaking =
        (89 : ℚ) / 10000 ∧
      alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
          .threshold = 0 ∧
        alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
            .threeLoopRG = 0 ∧
          alphaStrongQCDPoincareUnifiedAxisResidualGapProducer.contribution
              .higgsExtraRepresentation = 0 ∧
            (∀ s : AlphaStrongResidualSource,
              AlphaStrongActiveResidualSource
                  alphaStrongQCDPoincareUnifiedAxisResidualGapProducer s ↔
                s = .su7Breaking)

/-- THEOREM 8: alpha strong structural producer normal-form certificate. -/
theorem alphaStrongStructuralProducerNormalFormCertificate :
    AlphaStrongStructuralProducerNormalFormCertificate where
  qcd_poincare_receipt :=
    ⟨alphaStrongQCDPoincareProducerReceipt unifiedGaugeIntoAlphaEMStructural⟩
  unified_axis_receipt :=
    ⟨alphaStrongQCDPoincareUnifiedAxisProducerReceipt⟩
  finite_debt_closure :=
    ⟨alphaStrongFiniteProducerDebtClosureCertificate⟩
  structural_gap_formula :=
    alphaStrongStructuralAxisGapFormula_eq_89_div_10000
  structural_formula_inverse_residual :=
    alphaStrongStructuralAxisFormula_inverseResidual
  structural_producer_source_surface :=
    alphaStrongQCDPoincareStructuralProducer_sourceSurface
  structural_producer_eq_unified_axis :=
    alphaStrongQCDPoincareStructuralProducer_eq_unifiedAxis
  active_source_eq_structural_formula :=
    alphaStrongUnifiedAxis_su7Source_eq_structuralFormula
  produced_gap_eq_structural_formula :=
    alphaStrongUnifiedAxis_producedGap_eq_structuralFormula
  inverse_residual :=
    alphaStrongQCDPoincareUnifiedAxisResidualGapProducer_inverseCorrection
  active_source_normal_form := by
    exact alphaStrongSU7RepresentationResidual_singleActiveSource

end StandardModelConstraint
end SaturationMonoid
