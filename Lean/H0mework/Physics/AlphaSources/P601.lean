import Mathlib.Tactic
import H0mework.Physics.AlphaSources.P600

/-!
# Proposition 601: embedded-complement finite-carrier producer for alpha_s

P600 lowered the finite `alpha_s` gap to typed finite-cardinality carriers.
P597 had already fused the earlier P581 formula into the four-source residual
producer surface.

This file welds those two layers and lowers the P600 numerator once more.
The `89` numerator is no longer only a cardinal difference

`card AlphaEMStructuralCarrier - card UnifiedGaugeFreedomCarrier`;

it is the cardinality of the complement of an embedded unified-gauge subcarrier
inside the `137`-point structural electromagnetic carrier.

Thus the current `alpha_s` closed loop is:

`embedded complement carrier -> P600 finite carriers -> P598 singleton surface
 -> P597 four-source law`.

Boundary: this still does not supply threshold / three-loop / Higgs-spectrum
dynamics.  It proves that the current finite-cardinality producer is a genuine
four-source residual producer and inherits the exact inverse correction
`-89000/128511`.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Embedded-complement carrier for the numerator -/

/-- The complement of an embedded unified-gauge carrier inside the structural
electromagnetic carrier.  This is the structural version of the P600 numerator
carrier: remove a `48`-point unified gauge subcarrier from the `137`-point
electromagnetic structural carrier. -/
abbrev AlphaEMUnifiedComplementCarrier
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :=
  { x : AlphaEMStructuralCarrier // x ∉ Set.range e }

/-- THEOREM 1: any embedded unified-gauge subcarrier has range cardinal `48`. -/
theorem alphaEMUnifiedEmbeddedRange_card_eq_48
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    Fintype.card (Set.range e) = 48 := by
  rw [← Fintype.card_congr e.toEquivRange]
  exact unifiedGaugeFreedomCarrier_card_eq_48

/-- THEOREM 2: the complement of any embedded unified-gauge subcarrier inside
the structural electromagnetic carrier has cardinality `89`. -/
theorem alphaEMUnifiedComplementCarrier_card_eq_89
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    Fintype.card (AlphaEMUnifiedComplementCarrier e) = 89 := by
  change
    Fintype.card
      { x : AlphaEMStructuralCarrier // ¬x ∈ Set.range e } = 89
  rw [Fintype.card_subtype_compl]
  rw [alphaEMStructuralCarrier_card_eq_137,
    alphaEMUnifiedEmbeddedRange_card_eq_48 e]

/-- THEOREM 3: the embedded complement cardinal agrees with the P600 finite
carrier numerator. -/
theorem alphaEMUnifiedComplementCarrier_card_eq_finiteCarrierNumerator
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    (Fintype.card (AlphaEMUnifiedComplementCarrier e) : ℚ) =
      alphaStrongFiniteCarrierNumerator := by
  rw [alphaEMUnifiedComplementCarrier_card_eq_89 e,
    alphaStrongFiniteCarrierNumerator]
  rw [alphaEMGaugeContrastCarrier_card_eq_89]

/-- Candidate alpha-gap coordinates whose numerator is read from an embedded
complement carrier instead of from a bare finite cardinal difference. -/
def embeddedComplementAlphaStrongSU7BreakingGapCandidate
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongSU7BreakingGapCandidate where
  numerator :=
    (Fintype.card (AlphaEMUnifiedComplementCarrier e) : ℚ)
  denominator := alphaStrongFiniteCarrierDenominator
  gap :=
    (Fintype.card (AlphaEMUnifiedComplementCarrier e) : ℚ) /
      alphaStrongFiniteCarrierDenominator

/-- THEOREM 4: the embedded-complement candidate satisfies the P598 carrier
equations. -/
theorem embeddedComplementAlphaStrongSU7BreakingGapCandidate_equations
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    AlphaStrongSU7BreakingGapCarrierEquations
      (embeddedComplementAlphaStrongSU7BreakingGapCandidate e) := by
  constructor
  · rw [embeddedComplementAlphaStrongSU7BreakingGapCandidate,
      alphaEMUnifiedComplementCarrier_card_eq_finiteCarrierNumerator e]
    exact alphaStrongFiniteCarrierNumerator_eq_p598_numerator
  constructor
  · rw [embeddedComplementAlphaStrongSU7BreakingGapCandidate]
    exact alphaStrongFiniteCarrierDenominator_eq_p598_denominator
  · rfl

/-- THEOREM 5: any embedded-complement candidate is the same unique P598
carrier-sourced candidate. -/
theorem embeddedComplementAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    embeddedComplementAlphaStrongSU7BreakingGapCandidate e =
      carrierSourcedAlphaStrongSU7BreakingGapCandidate :=
  eq_carrierSourcedAlphaStrongGapCandidate_of_equations
    (embeddedComplementAlphaStrongSU7BreakingGapCandidate e)
    (embeddedComplementAlphaStrongSU7BreakingGapCandidate_equations e)

/-! ## A canonical embedding instance -/

/-- A concrete embedding of the unified `48`-point gauge-freedom carrier into
the structural electromagnetic carrier.  It lands in the seven-facet Boolean
side by composing the standard `Fin 48 -> Fin 128` inclusion with the binary
equivalence `Fin 128 ≃ (Fin 7 -> Bool)`.  The complement-cardinality theorem
above is independent of this particular embedding; this witness just makes the
carrier inhabited on the nose. -/
noncomputable def unifiedGaugeIntoAlphaEMStructural :
    UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier where
  toFun i :=
    Sum.inl
      ((Fintype.equivFin SevenFacetBooleanCarrier).symm
        ⟨(i : ℕ), by
          have hi : (i : ℕ) < 48 := i.isLt
          have hcard : Fintype.card SevenFacetBooleanCarrier = 128 :=
            sevenFacetBooleanCarrier_card_eq_128
          omega⟩)
  inj' := by
    intro i j h
    simp only [Sum.inl.injEq] at h
    have hfin := congrArg
      (Fintype.equivFin SevenFacetBooleanCarrier) h
    simp at hfin
    exact Fin.ext hfin

/-! ## The P600 finite carrier as the SU(7)-breaking source -/

/-- THEOREM 1: the P600 finite-carrier gap is exactly the P581
SU(7)-breaking alpha gap. -/
theorem finiteCarrierAlphaStrongGap_eq_su7BreakingAlphaGap :
    finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap =
      alphaStrongSU7BreakingAlphaGap ℚ := by
  rw [finiteCarrierAlphaStrongSU7BreakingGapCandidate_eq_carrierSourced]
  rfl

/-- The four-source contribution function whose SU(7)-breaking source is read
from the P600 finite-carrier candidate. -/
def alphaStrongFiniteCarrierContribution :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking =>
      finiteCarrierAlphaStrongSU7BreakingGapCandidate.gap
  | .threshold => 0
  | .threeLoopRG => 0
  | .higgsExtraRepresentation => 0

/-- THEOREM 2: the P600 finite-carrier contribution function satisfies the
P597 finite SU(7)-breaking contribution law. -/
theorem alphaStrongFiniteCarrierContribution_law :
    AlphaStrongSU7FiniteContributionLaw
      alphaStrongFiniteCarrierContribution := by
  constructor
  · exact finiteCarrierAlphaStrongGap_eq_su7BreakingAlphaGap
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- THEOREM 3: the P600 finite-carrier contribution is the same contribution
function selected by P581/P597. -/
theorem alphaStrongFiniteCarrierContribution_eq_p597_contribution :
    alphaStrongFiniteCarrierContribution =
      alphaStrongSU7BreakingResidualGapProducer.contribution := by
  exact alphaStrongSU7FiniteContributionLaw_unique
    alphaStrongFiniteCarrierContribution
    alphaStrongSU7BreakingResidualGapProducer.contribution
    alphaStrongFiniteCarrierContribution_law
    alphaStrongSU7BreakingResidualGapProducer_contributionLaw

/-! ## The P600-fed four-source producer -/

/-- The focused residual-gap producer whose SU(7)-breaking source is the P600
finite-carrier gap and whose other three sources are zero. -/
def alphaStrongFiniteCarrierResidualGapProducer :
    AlphaStrongResidualGapProducer :=
  alphaStrongGapProducerOfSU7FiniteContributionLaw
    alphaStrongFiniteCarrierContribution
    alphaStrongFiniteCarrierContribution_law

/-- THEOREM 4: the P600-fed four-source producer has produced gap
`89/10000`. -/
theorem alphaStrongFiniteCarrierResidualGapProducer_gap :
    alphaStrongFiniteCarrierResidualGapProducer.producedGap =
      (89 : ℚ) / 10000 := by
  exact alphaStrongGapProducerOfSU7FiniteContributionLaw_gap
    alphaStrongFiniteCarrierContribution
    alphaStrongFiniteCarrierContribution_law

/-- THEOREM 5: the P600-fed four-source producer transports to the exact
inverse residual `-89000/128511`. -/
theorem alphaStrongFiniteCarrierResidualGapProducer_inverseCorrection :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongFiniteCarrierResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) := by
  exact alphaStrongGapProducerOfSU7FiniteContributionLaw_inverseCorrection_eq_neg
    alphaStrongFiniteCarrierContribution
    alphaStrongFiniteCarrierContribution_law

/-- THEOREM 6: the P600-fed four-source producer closes the displayed
strong-coupling alpha value. -/
theorem alphaStrongFiniteCarrierResidualGapProducer_closes_displayedAlpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongFiniteCarrierResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ := by
  exact alphaStrongGapProducerOfSU7FiniteContributionLaw_closes_displayedAlpha
    alphaStrongFiniteCarrierContribution
    alphaStrongFiniteCarrierContribution_law

/-! ## Bundled receipt -/

/-- Receipt that the P600 finite-cardinality producer feeds the four-source
`alpha_s` residual law directly. -/
structure AlphaStrongFiniteCarrierFourSourceProducerReceipt where
  finite_carrier :
    AlphaStrongFiniteCarrierGapProducerReceipt
  contribution_law :
    AlphaStrongSU7FiniteContributionLaw
      alphaStrongFiniteCarrierContribution
  contribution_eq_p597 :
    alphaStrongFiniteCarrierContribution =
      alphaStrongSU7BreakingResidualGapProducer.contribution
  alpha_gap :
    alphaStrongFiniteCarrierResidualGapProducer.producedGap =
      (89 : ℚ) / 10000
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongFiniteCarrierResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            alphaStrongFiniteCarrierResidualGapProducer.producedGap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 7: bundled finite-carrier four-source producer receipt. -/
theorem alphaStrongFiniteCarrierFourSourceProducerReceipt :
    AlphaStrongFiniteCarrierFourSourceProducerReceipt where
  finite_carrier := alphaStrongFiniteCarrierGapProducerReceipt
  contribution_law := alphaStrongFiniteCarrierContribution_law
  contribution_eq_p597 :=
    alphaStrongFiniteCarrierContribution_eq_p597_contribution
  alpha_gap := alphaStrongFiniteCarrierResidualGapProducer_gap
  inverse_residual :=
    alphaStrongFiniteCarrierResidualGapProducer_inverseCorrection
  closes_displayed_alpha :=
    alphaStrongFiniteCarrierResidualGapProducer_closes_displayedAlpha

end StandardModelConstraint
end SaturationMonoid
