import H0mework.Arithmetic.PrimeShadow.P625
import H0mework.Realization.RelaxationAlgebra.P281

/-!
# Proposition 626: QCD/Poincare denominator producer for alpha_s

P618 closes the current finite `alpha_s` residual through the P602
Poincare-resolution denominator `(9 + 1)^4 = 10000`.  This file lowers that
denominator one step toward the physics producer debt:

* `7` is the QCD one-loop coefficient `b0`, produced from the SU(7)
  block-incidence matter/RG carrier in P461/P523;
* `3` is the 4D Poincare degree-pairing slot count from P281;
* therefore the finite resolution axis can be read as `b0_QCD + slots_4D`;
* the same embedded SU(7)-complement numerator then gives
  `(137 - 48) / (7 + 3)^4 = 89 / 10000`, hence the exact inverse residual
  `-89000/128511`.

Boundary: this still is not a smooth threshold spectrum or three-loop
calculation.  It proves that the current finite denominator is not an
independent decimal choice: it is reproducible from the already checked
matter/RG `b0` carrier plus the 4D Poincare slot carrier.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## QCD plus Poincare finite resolution axis -/

/-- The resolution-axis size read from two independently checked finite
structures: the QCD one-loop `b0` carrier and the 4D Poincare pairing slot
count. -/
def alphaStrongQCDPoincareResolutionAxis : ℚ :=
  RunningSigmaBeta.betaCoeff
      RunningSigmaBeta.qcdBlockIncidenceOneLoopInput +
    (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 : ℚ)

/-- THEOREM 1: the QCD/Poincare axis has size `7 + 3 = 10`. -/
theorem alphaStrongQCDPoincareResolutionAxis_eq_ten :
    alphaStrongQCDPoincareResolutionAxis = (10 : ℚ) := by
  rw [alphaStrongQCDPoincareResolutionAxis,
    RunningSigmaBeta.qcd_b0_from_final_carrier_formula,
    AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three]
  norm_num

/-- The QCD/Poincare denominator: four Poincare-resolution directions, each
valued in the `b0_QCD + slots_4D` axis. -/
def alphaStrongQCDPoincareResolutionDenominator : ℚ :=
  alphaStrongQCDPoincareResolutionAxis ^
    alphaStrongResidualResolutionExponent

/-- THEOREM 2: the QCD/Poincare denominator is exactly `10000`. -/
theorem alphaStrongQCDPoincareResolutionDenominator_eq_10000 :
    alphaStrongQCDPoincareResolutionDenominator = (10000 : ℚ) := by
  rw [alphaStrongQCDPoincareResolutionDenominator,
    alphaStrongQCDPoincareResolutionAxis_eq_ten]
  norm_num [alphaStrongResidualResolutionExponent]

/-- THEOREM 3: the QCD/Poincare denominator is the same denominator used by
the P600 finite-carrier equation surface. -/
theorem alphaStrongQCDPoincareResolutionDenominator_eq_finiteCarrierDenominator :
    alphaStrongQCDPoincareResolutionDenominator =
      alphaStrongFiniteCarrierDenominator := by
  rw [alphaStrongQCDPoincareResolutionDenominator_eq_10000,
    alphaStrongFiniteCarrierDenominator,
    alphaStrongFourDimensionalResolutionCarrier_card_eq_10000]
  norm_num

/-- THEOREM 4: the QCD/Poincare denominator also agrees with any supplied P602
4D Poincare-resolution denominator. -/
theorem alphaStrongQCDPoincareResolutionDenominator_eq_poincareResolution
    (C : FourDPoincareCertificate) :
    alphaStrongQCDPoincareResolutionDenominator =
      alphaStrongPoincareResolutionDenominator C := by
  rw [alphaStrongQCDPoincareResolutionDenominator_eq_10000,
    alphaStrongPoincareResolutionDenominator_eq_10000 C]

/-! ## Gap candidate fed by the QCD/Poincare denominator -/

/-- Candidate alpha-gap coordinates whose numerator is the embedded SU(7)
complement and whose denominator is the QCD/Poincare axis to the fourth power.
-/
def qcdPoincareAlphaStrongSU7BreakingGapCandidate
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongSU7BreakingGapCandidate where
  numerator :=
    (Fintype.card (AlphaEMUnifiedComplementCarrier e) : ℚ)
  denominator := alphaStrongQCDPoincareResolutionDenominator
  gap :=
    (Fintype.card (AlphaEMUnifiedComplementCarrier e) : ℚ) /
      alphaStrongQCDPoincareResolutionDenominator

/-- THEOREM 5: the QCD/Poincare candidate satisfies the P598 carrier
equations. -/
theorem qcdPoincareAlphaStrongSU7BreakingGapCandidate_equations
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongSU7BreakingGapCarrierEquations
      (qcdPoincareAlphaStrongSU7BreakingGapCandidate e) := by
  constructor
  · rw [qcdPoincareAlphaStrongSU7BreakingGapCandidate,
      alphaEMUnifiedComplementCarrier_card_eq_finiteCarrierNumerator e]
    exact alphaStrongFiniteCarrierNumerator_eq_p598_numerator
  constructor
  · rw [qcdPoincareAlphaStrongSU7BreakingGapCandidate,
      alphaStrongQCDPoincareResolutionDenominator_eq_finiteCarrierDenominator]
    exact alphaStrongFiniteCarrierDenominator_eq_p598_denominator
  · rfl

/-- THEOREM 6: the QCD/Poincare candidate is the unique carrier-sourced
finite alpha-gap candidate. -/
theorem qcdPoincareAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    qcdPoincareAlphaStrongSU7BreakingGapCandidate e =
      carrierSourcedAlphaStrongSU7BreakingGapCandidate :=
  eq_carrierSourcedAlphaStrongGapCandidate_of_equations
    (qcdPoincareAlphaStrongSU7BreakingGapCandidate e)
    (qcdPoincareAlphaStrongSU7BreakingGapCandidate_equations e)

/-- THEOREM 7: the QCD/Poincare candidate produces the exact alpha-level gap
`89/10000`. -/
theorem qcdPoincareAlphaStrongSU7BreakingGapCandidate_gap
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    (qcdPoincareAlphaStrongSU7BreakingGapCandidate e).gap =
      (89 : ℚ) / 10000 :=
  alphaStrongGapCandidate_gap_eq_89_div_10000
    (qcdPoincareAlphaStrongSU7BreakingGapCandidate e)
    (qcdPoincareAlphaStrongSU7BreakingGapCandidate_equations e)

/-- THEOREM 8: the QCD/Poincare candidate transports to the exact inverse
residual `-89000/128511`. -/
theorem qcdPoincareAlphaStrongSU7BreakingGapCandidate_inverseCorrection
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (qcdPoincareAlphaStrongSU7BreakingGapCandidate e).gap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongGapCandidate_inverseCorrection_eq_neg
    (qcdPoincareAlphaStrongSU7BreakingGapCandidate e)
    (qcdPoincareAlphaStrongSU7BreakingGapCandidate_equations e)

/-! ## Four-source producer from the QCD/Poincare candidate -/

/-- The four-source contribution function whose active SU(7)-breaking source
is fed by the QCD/Poincare denominator. -/
def alphaStrongQCDPoincareContribution
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking =>
      (qcdPoincareAlphaStrongSU7BreakingGapCandidate e).gap
  | .threshold => 0
  | .threeLoopRG => 0
  | .higgsExtraRepresentation => 0

/-- THEOREM 9: the QCD/Poincare contribution satisfies the finite
SU(7)-breaking contribution law. -/
theorem alphaStrongQCDPoincareContribution_law
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongSU7FiniteContributionLaw
      (alphaStrongQCDPoincareContribution e) := by
  constructor
  · rw [alphaStrongQCDPoincareContribution,
      qcdPoincareAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced e]
    rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The focused residual-gap producer fed by the QCD/Poincare denominator. -/
def alphaStrongQCDPoincareResidualGapProducer
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongResidualGapProducer :=
  alphaStrongGapProducerOfSU7FiniteContributionLaw
    (alphaStrongQCDPoincareContribution e)
    (alphaStrongQCDPoincareContribution_law e)

/-- THEOREM 10: the QCD/Poincare four-source producer transports to the exact
inverse residual `-89000/128511`. -/
theorem alphaStrongQCDPoincareResidualGapProducer_inverseCorrection
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongQCDPoincareResidualGapProducer e).producedGap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongGapProducerOfSU7FiniteContributionLaw_inverseCorrection_eq_neg
    (alphaStrongQCDPoincareContribution e)
    (alphaStrongQCDPoincareContribution_law e)

/-- THEOREM 11: the QCD/Poincare four-source producer closes the displayed
strong-coupling alpha value. -/
theorem alphaStrongQCDPoincareResidualGapProducer_closes_displayedAlpha
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongQCDPoincareResidualGapProducer e).producedGap) =
      alphaStrongDisplayed ℚ :=
  alphaStrongGapProducerOfSU7FiniteContributionLaw_closes_displayedAlpha
    (alphaStrongQCDPoincareContribution e)
    (alphaStrongQCDPoincareContribution_law e)

/-! ## Bundled receipt -/

/-- Compact receipt that the finite `alpha_s` residual denominator can be read
from the QCD one-loop matter/RG carrier plus the 4D Poincare slot count. -/
structure AlphaStrongQCDPoincareProducerReceipt
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) where
  qcd_b0 :
    RunningSigmaBeta.betaCoeff
        RunningSigmaBeta.qcdBlockIncidenceOneLoopInput = 7
  poincare_slots :
    AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 = 3
  axis :
    alphaStrongQCDPoincareResolutionAxis = (10 : ℚ)
  denominator :
    alphaStrongQCDPoincareResolutionDenominator = (10000 : ℚ)
  denominator_eq_finite :
    alphaStrongQCDPoincareResolutionDenominator =
      alphaStrongFiniteCarrierDenominator
  equations :
    AlphaStrongSU7BreakingGapCarrierEquations
      (qcdPoincareAlphaStrongSU7BreakingGapCandidate e)
  alpha_gap :
    (qcdPoincareAlphaStrongSU7BreakingGapCandidate e).gap =
      (89 : ℚ) / 10000
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongQCDPoincareResidualGapProducer e).producedGap =
      -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongQCDPoincareResidualGapProducer e).producedGap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 12: bundled QCD/Poincare alpha_s residual producer receipt. -/
theorem alphaStrongQCDPoincareProducerReceipt
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongQCDPoincareProducerReceipt e where
  qcd_b0 := RunningSigmaBeta.qcd_b0_from_final_carrier_formula
  poincare_slots :=
    AffineRelaxation.GeometryConnection.four_poincarePairingSlotCount_eq_three
  axis := alphaStrongQCDPoincareResolutionAxis_eq_ten
  denominator := alphaStrongQCDPoincareResolutionDenominator_eq_10000
  denominator_eq_finite :=
    alphaStrongQCDPoincareResolutionDenominator_eq_finiteCarrierDenominator
  equations := qcdPoincareAlphaStrongSU7BreakingGapCandidate_equations e
  alpha_gap := qcdPoincareAlphaStrongSU7BreakingGapCandidate_gap e
  inverse_residual :=
    alphaStrongQCDPoincareResidualGapProducer_inverseCorrection e
  closes_displayed_alpha :=
    alphaStrongQCDPoincareResidualGapProducer_closes_displayedAlpha e

end StandardModelConstraint

/-! ## Connection back to the current unified-equation root -/

/-- The current unified-equation root with the `alpha_s` finite denominator
lowered to QCD `b0` plus 4D Poincare slots. -/
structure CurrentUnifiedEquationAlphaStrongQCDPoincareCoreCertificate where
  coded_descent_liftability_core :
    CurrentUnifiedEquationCodedDescentLiftabilityCoreCertificate
  qcd_poincare_alpha_s :
    StandardModelConstraint.AlphaStrongQCDPoincareProducerReceipt
      StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongQCDPoincareResidualGapProducer
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 13: current unified root with the QCD/Poincare denominator producer
attached to the alpha_s nail. -/
noncomputable def currentUnifiedEquationAlphaStrongQCDPoincareCoreCertificate :
    CurrentUnifiedEquationAlphaStrongQCDPoincareCoreCertificate where
  coded_descent_liftability_core :=
    currentUnifiedEquationCodedDescentLiftabilityCoreCertificate
  qcd_poincare_alpha_s :=
    StandardModelConstraint.alphaStrongQCDPoincareProducerReceipt
      StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural
  alpha_s_residual :=
    StandardModelConstraint.alphaStrongQCDPoincareResidualGapProducer_inverseCorrection
      StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural

end SaturationMonoid
