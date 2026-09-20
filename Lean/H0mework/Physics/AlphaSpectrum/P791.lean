import H0mework.Physics.RepresentationSources.P790

/-!
# Proposition 791: SU(7)-breaking card source producer

P789 bottomed the four alpha_s source coordinates and P790 removed the
remaining six-slot incidence schedule freedom.  The last visible scalar in the
active SU(7)-breaking source was the `89 / 10000` gap.

This file pushes that gap one layer lower.  The numerator is not a free scalar:

`89 = (2^7 + 9) - 48`,

where `2^7` is the seven-facet information-state count, `9` is the
low-energy visible gauge count recovered from the same QCD/Poincare axis, and
`48` is the SU(7) gauge-freedom count.  The denominator is also produced by
the same axis:

`10000 = (b0_QCD + PoincareSlots_4D)^4 = 10^4`.

Thus the SU(7)-breaking source is now a card-source producer rather than an
unexplained displayed rational.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Card-source numerator and denominator -/

/-- The alpha-em denominator used by the SU(7)-breaking source is exactly
information states plus the low-energy visible gauge carrier. -/
theorem alphaStrongStructuralAlphaEMDenominator_eq_info_plus_visible :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator =
      sevenFacetInformationStateCount ℚ +
        lowEnergyVisibleGaugeDimensionFromCard ℚ := by
  rw [alphaStrongQCDPoincareStructuralAlphaEMDenominator,
    alphaStrongQCDPoincareVisibleGaugeFromAxis_eq_lowEnergyVisible]

/-- THEOREM 1: the structural alpha-em denominator is `137` from
`2^7 + 9`. -/
theorem alphaStrongStructuralAlphaEMDenominator_eq_137_from_cards :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator = (137 : ℚ) := by
  rw [alphaStrongStructuralAlphaEMDenominator_eq_info_plus_visible,
    sevenFacetInformationStateCount_eq_128,
    lowEnergyVisibleGaugeDimensionFromCard_eq_nine]
  norm_num

/-- The SU(7)-breaking numerator read from the visible alpha-em carrier minus
the unified SU(7) gauge-freedom carrier. -/
def alphaStrongSU7BreakingCardNumerator : ℚ :=
  (sevenFacetInformationStateCount ℚ +
      lowEnergyVisibleGaugeDimensionFromCard ℚ) -
    unifiedGaugeFreedomDimensionFromCard ℚ

/-- THEOREM 2: the card-source numerator is `137 - 48 = 89`. -/
theorem alphaStrongSU7BreakingCardNumerator_eq_89 :
    alphaStrongSU7BreakingCardNumerator = (89 : ℚ) := by
  rw [alphaStrongSU7BreakingCardNumerator,
    sevenFacetInformationStateCount_eq_128,
    lowEnergyVisibleGaugeDimensionFromCard_eq_nine,
    unifiedGaugeFreedomDimensionFromCard_eq_su7GaugeFreedomDimension]
  norm_num [su7GaugeFreedomDimension]

/-- The SU(7)-breaking denominator read from the same QCD/Poincare axis. -/
def alphaStrongSU7BreakingCardDenominator : ℚ :=
  alphaStrongQCDPoincareResolutionAxis ^
    alphaStrongResidualResolutionExponent

/-- THEOREM 3: the card-source denominator is `(7 + 3)^4 = 10000`. -/
theorem alphaStrongSU7BreakingCardDenominator_eq_10000 :
    alphaStrongSU7BreakingCardDenominator = (10000 : ℚ) := by
  rw [alphaStrongSU7BreakingCardDenominator,
    alphaStrongQCDPoincareResolutionAxis_eq_ten]
  norm_num [alphaStrongResidualResolutionExponent]

/-- The card-source SU(7)-breaking gap. -/
def alphaStrongSU7BreakingCardSourceGap : ℚ :=
  alphaStrongSU7BreakingCardNumerator /
    alphaStrongSU7BreakingCardDenominator

/-- THEOREM 4: the card-source gap is the structural source gap used by the
four-source alpha producer. -/
theorem alphaStrongSU7BreakingCardSourceGap_eq_structuralSourceGap :
    alphaStrongSU7BreakingCardSourceGap =
      alphaStrongSU7BreakingStructuralSourceGap := by
  unfold alphaStrongSU7BreakingCardSourceGap
    alphaStrongSU7BreakingCardNumerator
    alphaStrongSU7BreakingCardDenominator
    alphaStrongSU7BreakingStructuralSourceGap
  rw [alphaStrongStructuralAlphaEMDenominator_eq_info_plus_visible,
    unifiedGaugeFreedomDimensionFromCard_eq_su7GaugeFreedomDimension]

/-- THEOREM 5: the SU(7)-breaking card-source gap is exactly `89/10000`. -/
theorem alphaStrongSU7BreakingCardSourceGap_eq_89_div_10000 :
    alphaStrongSU7BreakingCardSourceGap = (89 : ℚ) / 10000 := by
  rw [alphaStrongSU7BreakingCardSourceGap,
    alphaStrongSU7BreakingCardNumerator_eq_89,
    alphaStrongSU7BreakingCardDenominator_eq_10000]

/-- THEOREM 6: the structural source gap is exactly the card-source gap. -/
theorem alphaStrongSU7BreakingStructuralSourceGap_eq_cardSourceGap :
    alphaStrongSU7BreakingStructuralSourceGap =
      alphaStrongSU7BreakingCardSourceGap :=
  alphaStrongSU7BreakingCardSourceGap_eq_structuralSourceGap.symm

/-- THEOREM 7: the card-source SU(7)-breaking gap transports to the exact
inverse residual. -/
theorem alphaStrongSU7BreakingCardSourceGap_inverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongSU7BreakingCardSourceGap =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongSU7BreakingCardSourceGap_eq_89_div_10000]
  norm_num [inverseCorrectionFromAlphaGap, alphaStrongTwoLoopSMOutput]

/-- THEOREM 8: the active SU(7)-breaking coordinate of the independent
four-source producer is the card-source gap. -/
theorem alphaStrongFourSource_su7Breaking_eq_cardSourceGap :
    alphaStrongFourSourceIndependentContribution .su7Breaking =
      alphaStrongSU7BreakingCardSourceGap := by
  rw [alphaStrongFourSourceIndependentContribution,
    alphaStrongSU7BreakingStructuralSourceGap_eq_cardSourceGap]

/-! ## Bundled source producer -/

/-- Card-source certificate for the nonzero SU(7)-breaking alpha source. -/
structure AlphaStrongSU7BreakingCardSourceProducerCertificate : Prop where
  schedule_no_free :
    RunningSigmaBeta.SU7IncidenceScheduleNoFreeCertificate
  information_states :
    sevenFacetInformationStateCount ℚ = (128 : ℚ)
  visible_gauge :
    lowEnergyVisibleGaugeDimensionFromCard ℚ = (9 : ℚ)
  alpha_em_denominator_from_cards :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator =
      sevenFacetInformationStateCount ℚ +
        lowEnergyVisibleGaugeDimensionFromCard ℚ
  alpha_em_denominator :
    alphaStrongQCDPoincareStructuralAlphaEMDenominator = (137 : ℚ)
  unified_gauge_freedom :
    unifiedGaugeFreedomDimensionFromCard ℚ =
      su7GaugeFreedomDimension ℚ
  su7_gauge_freedom :
    su7GaugeFreedomDimension ℚ = (48 : ℚ)
  numerator :
    alphaStrongSU7BreakingCardNumerator = (89 : ℚ)
  axis :
    alphaStrongQCDPoincareResolutionAxis = (10 : ℚ)
  denominator :
    alphaStrongSU7BreakingCardDenominator = (10000 : ℚ)
  gap_is_structural_source :
    alphaStrongSU7BreakingCardSourceGap =
      alphaStrongSU7BreakingStructuralSourceGap
  gap :
    alphaStrongSU7BreakingCardSourceGap = (89 : ℚ) / 10000
  source_coordinate :
    alphaStrongFourSourceIndependentContribution .su7Breaking =
      alphaStrongSU7BreakingCardSourceGap
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongSU7BreakingCardSourceGap =
      -((89000 : ℚ) / 128511)
  bottomed_alpha_four_source :
    AlphaStrongBottomedFourSourceResidualProducerCertificate

/-- THEOREM 9: SU(7)-breaking card-source producer certificate. -/
theorem alphaStrongSU7BreakingCardSourceProducerCertificate :
    AlphaStrongSU7BreakingCardSourceProducerCertificate where
  schedule_no_free :=
    RunningSigmaBeta.su7IncidenceScheduleNoFreeCertificate
  information_states :=
    sevenFacetInformationStateCount_eq_128 ℚ
  visible_gauge :=
    lowEnergyVisibleGaugeDimensionFromCard_eq_nine ℚ
  alpha_em_denominator_from_cards :=
    alphaStrongStructuralAlphaEMDenominator_eq_info_plus_visible
  alpha_em_denominator :=
    alphaStrongStructuralAlphaEMDenominator_eq_137_from_cards
  unified_gauge_freedom :=
    unifiedGaugeFreedomDimensionFromCard_eq_su7GaugeFreedomDimension ℚ
  su7_gauge_freedom :=
    su7GaugeFreedomDimension_eq_48 ℚ
  numerator :=
    alphaStrongSU7BreakingCardNumerator_eq_89
  axis :=
    alphaStrongQCDPoincareResolutionAxis_eq_ten
  denominator :=
    alphaStrongSU7BreakingCardDenominator_eq_10000
  gap_is_structural_source :=
    alphaStrongSU7BreakingCardSourceGap_eq_structuralSourceGap
  gap :=
    alphaStrongSU7BreakingCardSourceGap_eq_89_div_10000
  source_coordinate :=
    alphaStrongFourSource_su7Breaking_eq_cardSourceGap
  inverse_residual :=
    alphaStrongSU7BreakingCardSourceGap_inverseResidual
  bottomed_alpha_four_source :=
    alphaStrongBottomedFourSourceResidualProducerCertificate

end StandardModelConstraint
end SaturationMonoid
