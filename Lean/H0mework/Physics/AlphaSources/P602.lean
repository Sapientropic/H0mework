import Mathlib.Tactic
import H0mework.Physics.Generation.P280
import H0mework.Physics.AlphaSources.P601

/-!
# Proposition 602: Poincare-resolution denominator for the alpha_s producer

P601 lowered the alpha-gap numerator to an embedded-complement carrier.
This file lowers the denominator side:

`(low-energy visible gauge directions ⊕ unit)^4`

is read as a four-dimensional resolution carrier.  The `4` is supplied by the
same certificate-relative 4D Poincare geometry interface used elsewhere in the
Standard Model track.  Thus the current finite `alpha_s` producer has both
halves as carriers:

* numerator: complement of an embedded unified-gauge subcarrier;
* denominator: four Poincare resolution directions, each valued in the
  `10`-point visible-gauge-plus-basepoint axis.

Boundary: this still does not construct a real smooth spacetime/de Rham
producer, threshold spectrum, three-loop RG, or Higgs-extra-representation
dynamics.  It proves that once a 4D Poincare geometry certificate is supplied,
the finite denominator used by the current `alpha_s` producer is the associated
resolution-carrier cardinality rather than an untyped exponent.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-- Local abbreviation for the certificate-relative 4D Poincare geometry
interface from P280. -/
abbrev FourDPoincareCertificate :=
  AffineRelaxation.GeometryConnection.PoincareDualityCohomologyCertificate 4

/-! ## Four-dimensional Poincare resolution carrier -/

/-- A four-dimensional Poincare geometry certificate supplies four resolution
directions.  The certificate is carried as a parameter to keep the boundary
honest: P602 uses the 4D interface, but does not construct physical de Rham
cohomology. -/
abbrev AlphaStrongPoincareResolutionDirection
    (_C : FourDPoincareCertificate) :=
  Fin 4

/-- THEOREM 1: a 4D Poincare resolution direction carrier has cardinality `4`,
the exponent used by P581/P600. -/
theorem alphaStrongPoincareResolutionDirection_card_eq_exponent
    (C : FourDPoincareCertificate) :
    Fintype.card (AlphaStrongPoincareResolutionDirection C) =
      alphaStrongResidualResolutionExponent := by
  simp [AlphaStrongPoincareResolutionDirection,
    alphaStrongResidualResolutionExponent]

/-- The Poincare-resolution denominator carrier: for each of the four 4D
resolution directions, choose one visible-gauge/basepoint axis value. -/
abbrev AlphaStrongPoincareResolutionCarrier
    (C : FourDPoincareCertificate) :=
  AlphaStrongPoincareResolutionDirection C -> AlphaStrongResolutionAxis

/-- THEOREM 2: the Poincare-resolution carrier has cardinality `10^4=10000`. -/
theorem alphaStrongPoincareResolutionCarrier_card_eq_10000
    (C : FourDPoincareCertificate) :
    Fintype.card (AlphaStrongPoincareResolutionCarrier C) = 10000 := by
  rw [show Fintype.card (AlphaStrongPoincareResolutionCarrier C) =
      Fintype.card AlphaStrongResolutionAxis ^
        Fintype.card (AlphaStrongPoincareResolutionDirection C) by
        exact Fintype.card_fun]
  rw [alphaStrongResolutionAxis_card_eq_ten,
    alphaStrongPoincareResolutionDirection_card_eq_exponent C]
  norm_num [alphaStrongResidualResolutionExponent]

/-- Denominator read from a supplied 4D Poincare-resolution carrier. -/
def alphaStrongPoincareResolutionDenominator
    (C : FourDPoincareCertificate) : ℚ :=
  (Fintype.card (AlphaStrongPoincareResolutionCarrier C) : ℚ)

/-- THEOREM 3: the Poincare-resolution denominator agrees with the P600 finite
carrier denominator. -/
theorem alphaStrongPoincareResolutionDenominator_eq_finiteCarrierDenominator
    (C : FourDPoincareCertificate) :
    alphaStrongPoincareResolutionDenominator C =
      alphaStrongFiniteCarrierDenominator := by
  rw [alphaStrongPoincareResolutionDenominator,
    alphaStrongFiniteCarrierDenominator,
    alphaStrongPoincareResolutionCarrier_card_eq_10000 C,
    alphaStrongFourDimensionalResolutionCarrier_card_eq_10000]

/-- THEOREM 4: the Poincare-resolution denominator is exactly `10000`. -/
theorem alphaStrongPoincareResolutionDenominator_eq_10000
    (C : FourDPoincareCertificate) :
    alphaStrongPoincareResolutionDenominator C = (10000 : ℚ) := by
  rw [alphaStrongPoincareResolutionDenominator,
    alphaStrongPoincareResolutionCarrier_card_eq_10000 C]
  norm_num

/-! ## Embedded-complement numerator plus Poincare-resolution denominator -/

/-- Candidate alpha-gap coordinates whose numerator is an embedded complement
and whose denominator is supplied by a 4D Poincare-resolution carrier. -/
def poincareResolutionAlphaStrongSU7BreakingGapCandidate
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongSU7BreakingGapCandidate where
  numerator :=
    (Fintype.card (AlphaEMUnifiedComplementCarrier e) : ℚ)
  denominator := alphaStrongPoincareResolutionDenominator C
  gap :=
    (Fintype.card (AlphaEMUnifiedComplementCarrier e) : ℚ) /
      alphaStrongPoincareResolutionDenominator C

/-- THEOREM 5: the embedded-complement / Poincare-resolution candidate
satisfies the P598 singleton carrier equations. -/
theorem poincareResolutionAlphaStrongSU7BreakingGapCandidate_equations
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongSU7BreakingGapCarrierEquations
      (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e) := by
  constructor
  · rw [poincareResolutionAlphaStrongSU7BreakingGapCandidate,
      alphaEMUnifiedComplementCarrier_card_eq_finiteCarrierNumerator e]
    exact alphaStrongFiniteCarrierNumerator_eq_p598_numerator
  constructor
  · rw [poincareResolutionAlphaStrongSU7BreakingGapCandidate,
      alphaStrongPoincareResolutionDenominator_eq_finiteCarrierDenominator C]
    exact alphaStrongFiniteCarrierDenominator_eq_p598_denominator
  · rfl

/-- THEOREM 6: any such candidate is the unique carrier-sourced P598
candidate. -/
theorem poincareResolutionAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    poincareResolutionAlphaStrongSU7BreakingGapCandidate C e =
      carrierSourcedAlphaStrongSU7BreakingGapCandidate :=
  eq_carrierSourcedAlphaStrongGapCandidate_of_equations
    (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e)
    (poincareResolutionAlphaStrongSU7BreakingGapCandidate_equations C e)

/-- THEOREM 7: the embedded-complement / Poincare-resolution candidate
produces the exact `89/10000` alpha gap. -/
theorem poincareResolutionAlphaStrongSU7BreakingGapCandidate_gap
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e).gap =
      (89 : ℚ) / 10000 :=
  alphaStrongGapCandidate_gap_eq_89_div_10000
    (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e)
    (poincareResolutionAlphaStrongSU7BreakingGapCandidate_equations C e)

/-- THEOREM 8: the embedded-complement / Poincare-resolution candidate
transports to the exact inverse residual `-89000/128511`. -/
theorem poincareResolutionAlphaStrongSU7BreakingGapCandidate_inverseCorrection
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e).gap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongGapCandidate_inverseCorrection_eq_neg
    (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e)
    (poincareResolutionAlphaStrongSU7BreakingGapCandidate_equations C e)

/-! ## Four-source producer receipt -/

/-- The four-source contribution function whose SU(7)-breaking source is read
from an embedded-complement / Poincare-resolution candidate. -/
def alphaStrongPoincareResolutionContribution
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking =>
      (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e).gap
  | .threshold => 0
  | .threeLoopRG => 0
  | .higgsExtraRepresentation => 0

/-- THEOREM 9: the embedded-complement / Poincare-resolution contribution
satisfies the P597 finite SU(7)-breaking law. -/
theorem alphaStrongPoincareResolutionContribution_law
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongSU7FiniteContributionLaw
      (alphaStrongPoincareResolutionContribution C e) := by
  constructor
  · rw [alphaStrongPoincareResolutionContribution]
    rw [poincareResolutionAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced C e]
    rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- A focused residual-gap producer fed by an embedded-complement numerator and
a 4D Poincare-resolution denominator. -/
def alphaStrongPoincareResolutionResidualGapProducer
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongResidualGapProducer :=
  alphaStrongGapProducerOfSU7FiniteContributionLaw
    (alphaStrongPoincareResolutionContribution C e)
    (alphaStrongPoincareResolutionContribution_law C e)

/-- THEOREM 10: the Poincare-resolution four-source producer closes to the
exact inverse residual `-89000/128511`. -/
theorem alphaStrongPoincareResolutionResidualGapProducer_inverseCorrection
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPoincareResolutionResidualGapProducer C e).producedGap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongGapProducerOfSU7FiniteContributionLaw_inverseCorrection_eq_neg
    (alphaStrongPoincareResolutionContribution C e)
    (alphaStrongPoincareResolutionContribution_law C e)

/-- Receipt that a supplied 4D Poincare geometry certificate turns the current
finite `alpha_s` denominator into a genuine resolution carrier. -/
structure AlphaStrongPoincareResolutionProducerReceipt
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) where
  direction_card :
    Fintype.card (AlphaStrongPoincareResolutionDirection C) =
      alphaStrongResidualResolutionExponent
  denominator_card :
    Fintype.card (AlphaStrongPoincareResolutionCarrier C) = 10000
  denominator_eq_finite :
    alphaStrongPoincareResolutionDenominator C =
      alphaStrongFiniteCarrierDenominator
  equations :
    AlphaStrongSU7BreakingGapCarrierEquations
      (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e)
  alpha_gap :
    (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e).gap =
      (89 : ℚ) / 10000
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (poincareResolutionAlphaStrongSU7BreakingGapCandidate C e).gap =
      -((89000 : ℚ) / 128511)
  four_source_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPoincareResolutionResidualGapProducer C e).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 11: bundled Poincare-resolution producer receipt. -/
theorem alphaStrongPoincareResolutionProducerReceipt
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongPoincareResolutionProducerReceipt C e where
  direction_card :=
    alphaStrongPoincareResolutionDirection_card_eq_exponent C
  denominator_card :=
    alphaStrongPoincareResolutionCarrier_card_eq_10000 C
  denominator_eq_finite :=
    alphaStrongPoincareResolutionDenominator_eq_finiteCarrierDenominator C
  equations :=
    poincareResolutionAlphaStrongSU7BreakingGapCandidate_equations C e
  alpha_gap :=
    poincareResolutionAlphaStrongSU7BreakingGapCandidate_gap C e
  inverse_residual :=
    poincareResolutionAlphaStrongSU7BreakingGapCandidate_inverseCorrection C e
  four_source_inverse_residual :=
    alphaStrongPoincareResolutionResidualGapProducer_inverseCorrection C e

end StandardModelConstraint
end SaturationMonoid
