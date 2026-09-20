import H0mework.Physics.MixingSources.P784

/-!
# Proposition 785: four-source alpha_s residual producer

This file turns the alpha_s residual nail into the requested four-source
producer calculation.

The four coordinates are the existing finite alpha source carrier:

* `SU(7)` breaking: the structural QCD/Poincare gap
  `(137 - 48) / 10^4`;
* threshold: the mismatch between the Standard-Model color slope and the
  SU(7) incidence color slope;
* three-loop/RG: the mismatch between the QCD block slope and the incidence
  color slope;
* Higgs-extra spectrum: the mismatch between the incidence slots and the
  generated matter/Higgs carrier slots.

The SU(7) representation/matter/Higgs certificate forces the three mismatch
terms to zero.  Therefore the four-source sum is the structural alpha-level
gap, and inverse-coordinate transport produces the exact residual
`-89000/128511`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-! ## Four independent source terms -/

/-- The SU(7)-breaking contribution read from the structural QCD/Poincare
axis. -/
def alphaStrongSU7BreakingStructuralSourceGap : ℚ :=
  (alphaStrongQCDPoincareStructuralAlphaEMDenominator -
      su7GaugeFreedomDimension ℚ) /
    (alphaStrongQCDPoincareResolutionAxis ^
      alphaStrongResidualResolutionExponent)

/-- The finite-threshold source is the mismatch between the Standard-Model
color slope and the SU(7) incidence color slope. -/
def alphaStrongThresholdMismatchSourceGap : ℚ :=
  (standardModelAsymptoticB0 .colorSU3 -
      betaCoeff (incidenceCarrierTraceInput .colorSU3)) /
    (alphaStrongQCDPoincareResolutionAxis ^
      alphaStrongResidualResolutionExponent)

/-- The RG source is the mismatch between the QCD block slope and the
incidence color slope. -/
def alphaStrongThreeLoopRGMismatchSourceGap : ℚ :=
  (betaCoeff qcdBlockIncidenceOneLoopInput -
      betaCoeff (incidenceCarrierTraceInput .colorSU3)) /
    (alphaStrongQCDPoincareResolutionAxis ^
      alphaStrongResidualResolutionExponent)

/-- The Higgs-extra spectrum source is the mismatch between the incidence
slots and the generated matter/Higgs carrier slots. -/
def alphaStrongHiggsExtraSpectrumMismatchSourceGap : ℚ :=
  ((Fintype.card SU7BlockIncidence : ℚ) -
      (Fintype.card SU7GeneratedCarrierSlot : ℚ)) /
    (alphaStrongQCDPoincareResolutionAxis ^
      alphaStrongResidualResolutionExponent)

/-- The requested four-source contribution function. -/
def alphaStrongFourSourceIndependentContribution :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking => alphaStrongSU7BreakingStructuralSourceGap
  | .threshold => alphaStrongThresholdMismatchSourceGap
  | .threeLoopRG => alphaStrongThreeLoopRGMismatchSourceGap
  | .higgsExtraRepresentation => alphaStrongHiggsExtraSpectrumMismatchSourceGap

/-! ## The three mismatch sources are independently forced to zero -/

/-- THEOREM 1: the SU(7)-breaking source is exactly `89/10000`. -/
theorem alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000 :
    alphaStrongSU7BreakingStructuralSourceGap = (89 : ℚ) / 10000 := by
  exact alphaStrongStructuralAxisGapFormula_eq_89_div_10000

/-- THEOREM 2: the threshold mismatch source vanishes because the
representation carrier's color slope equals the Standard-Model color slope. -/
theorem alphaStrongThresholdMismatchSourceGap_eq_zero :
    alphaStrongThresholdMismatchSourceGap = 0 := by
  unfold alphaStrongThresholdMismatchSourceGap
  have hcolor :
      betaCoeff (incidenceCarrierTraceInput .colorSU3) =
        standardModelAsymptoticB0 .colorSU3 :=
    su7RepresentationMatterHiggsNormalForm_b0Values.2.2.2 .colorSU3
  rw [← hcolor]
  ring

/-- THEOREM 3: the RG mismatch source vanishes because the QCD block and the
incidence color carrier compute the same `b0 = 7`. -/
theorem alphaStrongThreeLoopRGMismatchSourceGap_eq_zero :
    alphaStrongThreeLoopRGMismatchSourceGap = 0 := by
  unfold alphaStrongThreeLoopRGMismatchSourceGap
  rw [su7RepresentationMatterHiggsNormalForm_numericalSpine.1,
    su7RepresentationMatterHiggsNormalForm_b0Values.1]
  norm_num

/-- THEOREM 4: the Higgs-extra spectrum mismatch vanishes because the
incidence and generated matter/Higgs carriers have the same six slots. -/
theorem alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero :
    alphaStrongHiggsExtraSpectrumMismatchSourceGap = 0 := by
  unfold alphaStrongHiggsExtraSpectrumMismatchSourceGap
  have hshape := su7RepresentationMatterHiggsNormalForm_incidenceShape
  rw [hshape.1, hshape.2.1]
  norm_num

/-- THEOREM 5: pointwise normal form for the independent four-source
contribution. -/
theorem alphaStrongFourSourceIndependentContribution_normalForm :
    alphaStrongFourSourceIndependentContribution .su7Breaking =
        (89 : ℚ) / 10000 ∧
      alphaStrongFourSourceIndependentContribution .threshold = 0 ∧
        alphaStrongFourSourceIndependentContribution .threeLoopRG = 0 ∧
          alphaStrongFourSourceIndependentContribution
              .higgsExtraRepresentation = 0 := by
  exact
    ⟨alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000,
      alphaStrongThresholdMismatchSourceGap_eq_zero,
      alphaStrongThreeLoopRGMismatchSourceGap_eq_zero,
      alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero⟩

/-! ## Four-source sum and inverse residual -/

/-- THEOREM 6: the independent four-source sum is the alpha-level displayed
gap. -/
theorem alphaStrongFourSourceIndependentContribution_sum_eq_gap :
    (∑ s : AlphaStrongResidualSource,
        alphaStrongFourSourceIndependentContribution s) =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  rw [alphaStrongResidualSource_univ_sum]
  simp [alphaStrongFourSourceIndependentContribution]
  rw [alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000,
    alphaStrongThresholdMismatchSourceGap_eq_zero,
    alphaStrongThreeLoopRGMismatchSourceGap_eq_zero,
    alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero,
    alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
  norm_num

/-- The four-source receipt whose fields are computed by the four independent
structural source terms above. -/
def alphaStrongIndependentFourSourceReceipt :
    AlphaStrongFourSourceClosureReceipt where
  su7_breaking := alphaStrongSU7BreakingStructuralSourceGap
  threshold := alphaStrongThresholdMismatchSourceGap
  three_loop_rg := alphaStrongThreeLoopRGMismatchSourceGap
  higgs_extra_representation := alphaStrongHiggsExtraSpectrumMismatchSourceGap
  total_gap := by
    rw [alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000,
      alphaStrongThresholdMismatchSourceGap_eq_zero,
      alphaStrongThreeLoopRGMismatchSourceGap_eq_zero,
      alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero,
      alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
    norm_num

/-- THEOREM 7: the receipt's contribution function is exactly the independent
four-source contribution. -/
theorem alphaStrongIndependentFourSourceReceipt_contribution :
    alphaStrongIndependentFourSourceReceipt.contribution =
      alphaStrongFourSourceIndependentContribution := by
  funext s
  cases s <;> rfl

/-- THEOREM 8: the independent four-source producer induces the exact
inverse residual `-89000/128511`. -/
theorem alphaStrongIndependentFourSource_inverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFourSourceIndependentContribution s) =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongFourSourceIndependentContribution_sum_eq_gap]
  exact inverseGapImage_eq_neg_89000_div_128511

/-- THEOREM 9: the independent four-source receipt transports to the exact
inverse residual `-89000/128511`. -/
theorem alphaStrongIndependentFourSourceReceipt_inverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongIndependentFourSourceReceipt.contribution s) =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongIndependentFourSourceReceipt_contribution]
  exact alphaStrongIndependentFourSource_inverseResidual

/-- THEOREM 10: the independent four-source receipt is the canonical finite
source-surface alpha producer. -/
theorem alphaStrongIndependentFourSourceReceipt_sourceSurface :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongIndependentFourSourceReceipt.toGapProducer := by
  unfold AlphaStrongResidualProducerFiniteSourceSurface
  unfold AlphaStrongSU7FiniteContributionLaw
  refine ⟨?_, ?_, ?_, ?_⟩
  · change alphaStrongSU7BreakingStructuralSourceGap =
      alphaStrongSU7BreakingAlphaGap ℚ
    rw [alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000,
      alphaStrongSU7BreakingAlphaGap_eq_89_div_10000]
  · change alphaStrongThresholdMismatchSourceGap = 0
    exact alphaStrongThresholdMismatchSourceGap_eq_zero
  · change alphaStrongThreeLoopRGMismatchSourceGap = 0
    exact alphaStrongThreeLoopRGMismatchSourceGap_eq_zero
  · change alphaStrongHiggsExtraSpectrumMismatchSourceGap = 0
    exact alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero

/-! ## Bundled certificate -/

/-- One certificate for the requested producer chain:

`SU(7) breaking / threshold / RG / Higgs-extra spectrum`

independently determine the four finite source terms, whose sum transports to
the exact inverse residual `-89000/128511`. -/
structure AlphaStrongIndependentFourSourceResidualProducerCertificate : Prop where
  representation_matter_higgs :
    SU7RepresentationMatterHiggsSourceNormalFormCertificate
  su7_breaking :
    alphaStrongSU7BreakingStructuralSourceGap = (89 : ℚ) / 10000
  threshold_zero :
    alphaStrongThresholdMismatchSourceGap = 0
  three_loop_rg_zero :
    alphaStrongThreeLoopRGMismatchSourceGap = 0
  higgs_extra_spectrum_zero :
    alphaStrongHiggsExtraSpectrumMismatchSourceGap = 0
  contribution_normal_form :
    alphaStrongFourSourceIndependentContribution .su7Breaking =
        (89 : ℚ) / 10000 ∧
      alphaStrongFourSourceIndependentContribution .threshold = 0 ∧
        alphaStrongFourSourceIndependentContribution .threeLoopRG = 0 ∧
          alphaStrongFourSourceIndependentContribution
              .higgsExtraRepresentation = 0
  four_source_sum :
    (∑ s : AlphaStrongResidualSource,
        alphaStrongFourSourceIndependentContribution s) =
      alphaStrongTwoLoopSMDisplayedGap ℚ
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFourSourceIndependentContribution s) =
      -((89000 : ℚ) / 128511)
  receipt_source_surface :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongIndependentFourSourceReceipt.toGapProducer
  receipt_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongIndependentFourSourceReceipt.contribution s) =
      -((89000 : ℚ) / 128511)

/-- THEOREM 11: independent four-source residual producer certificate. -/
theorem alphaStrongIndependentFourSourceResidualProducerCertificate :
    AlphaStrongIndependentFourSourceResidualProducerCertificate where
  representation_matter_higgs :=
    su7RepresentationMatterHiggsSourceNormalFormCertificate
  su7_breaking :=
    alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000
  threshold_zero :=
    alphaStrongThresholdMismatchSourceGap_eq_zero
  three_loop_rg_zero :=
    alphaStrongThreeLoopRGMismatchSourceGap_eq_zero
  higgs_extra_spectrum_zero :=
    alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero
  contribution_normal_form :=
    alphaStrongFourSourceIndependentContribution_normalForm
  four_source_sum :=
    alphaStrongFourSourceIndependentContribution_sum_eq_gap
  inverse_residual :=
    alphaStrongIndependentFourSource_inverseResidual
  receipt_source_surface :=
    alphaStrongIndependentFourSourceReceipt_sourceSurface
  receipt_inverse_residual :=
    alphaStrongIndependentFourSourceReceipt_inverseResidual

end StandardModelConstraint
end SaturationMonoid
