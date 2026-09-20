import H0mework.Physics.MixingSources.P788

/-!
# Proposition 789: bottomed alpha_s four-source producer

P785 proves that the four requested alpha_s sources

`SU(7) breaking / threshold / RG / Higgs-extra spectrum`

sum to the exact gap whose inverse-coordinate transport is
`-89000/128511`.

This file pushes the three zero-source proofs one layer lower.  Instead of
using only the packaged P778 representation/matter/Higgs normal form, it
exhibits the carrier identities that make the three mismatch terms vanish:

* threshold: incidence `b0` is the carrier `b0`, and carrier `b0` is the
  Standard-Model asymptotic table;
* RG: the QCD block input is definitionally the color incidence input;
* Higgs-extra spectrum: the six incidence slots are equivalent to the six
  generated matter/Higgs slots.

The resulting certificate says that the alpha_s residual is bottomed in the
`3+2+1+1` block-incidence carrier rather than merely restated by a higher
normal-form package.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta

/-! ## Bottomed proofs of the four source coordinates -/

/-- THEOREM 1: the SU(7)-breaking source is the structural
`(137 - 48) / 10^4` gap. -/
theorem alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000_from_cards :
    alphaStrongSU7BreakingStructuralSourceGap = (89 : ℚ) / 10000 := by
  exact alphaStrongStructuralAxisGapFormula_eq_89_div_10000

/-- THEOREM 2: the threshold source vanishes from the carrier identity
`incidence b0 = carrier b0 = SM asymptotic b0`. -/
theorem alphaStrongThresholdMismatchSourceGap_eq_zero_from_carrierB0 :
    alphaStrongThresholdMismatchSourceGap = 0 := by
  unfold alphaStrongThresholdMismatchSourceGap
  have hinc :
      betaCoeff (incidenceCarrierTraceInput .colorSU3) =
        carrierB0 .colorSU3 :=
    betaCoeff_incidenceCarrierTraceInput_eq_carrierB0 .colorSU3
  have hsm :
      carrierB0 .colorSU3 =
        standardModelAsymptoticB0 .colorSU3 :=
    carrierB0_eq_standardModelAsymptoticB0 .colorSU3
  rw [← hsm, hinc]
  ring

/-- THEOREM 3: the RG source vanishes because the direct QCD block input is
the color incidence input. -/
theorem alphaStrongThreeLoopRGMismatchSourceGap_eq_zero_from_qcdBlockInput :
    alphaStrongThreeLoopRGMismatchSourceGap = 0 := by
  unfold alphaStrongThreeLoopRGMismatchSourceGap
  rw [qcdBlockIncidenceOneLoopInput_eq_incidenceCarrierTraceInput]
  ring

/-- THEOREM 4: the Higgs-extra spectrum source vanishes because the
block-incidence carrier and generated matter/Higgs carrier both have six
slots. -/
theorem alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero_from_slotEquiv :
    alphaStrongHiggsExtraSpectrumMismatchSourceGap = 0 := by
  unfold alphaStrongHiggsExtraSpectrumMismatchSourceGap
  rw [SU7BlockIncidence.card, SU7GeneratedCarrierSlot.card]
  norm_num

/-- THEOREM 5: bottomed pointwise normal form for the four independent alpha
source contributions. -/
theorem alphaStrongFourSourceIndependentContribution_bottomedNormalForm :
    alphaStrongFourSourceIndependentContribution .su7Breaking =
        (89 : ℚ) / 10000 ∧
      alphaStrongFourSourceIndependentContribution .threshold = 0 ∧
        alphaStrongFourSourceIndependentContribution .threeLoopRG = 0 ∧
          alphaStrongFourSourceIndependentContribution
              .higgsExtraRepresentation = 0 := by
  exact
    ⟨alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000_from_cards,
      alphaStrongThresholdMismatchSourceGap_eq_zero_from_carrierB0,
      alphaStrongThreeLoopRGMismatchSourceGap_eq_zero_from_qcdBlockInput,
      alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero_from_slotEquiv⟩

/-- THEOREM 6: the bottomed four-source sum is still the alpha displayed gap. -/
theorem alphaStrongFourSourceIndependentContribution_bottomedSum_eq_gap :
    (∑ s : AlphaStrongResidualSource,
        alphaStrongFourSourceIndependentContribution s) =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  rw [alphaStrongResidualSource_univ_sum]
  simp [alphaStrongFourSourceIndependentContribution]
  rw [alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000_from_cards,
    alphaStrongThresholdMismatchSourceGap_eq_zero_from_carrierB0,
    alphaStrongThreeLoopRGMismatchSourceGap_eq_zero_from_qcdBlockInput,
    alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero_from_slotEquiv,
    alphaStrongTwoLoopAlphaGap_eq_89_div_10000]
  norm_num

/-- THEOREM 7: the bottomed four-source producer induces the exact inverse
residual `-89000/128511`. -/
theorem alphaStrongBottomedFourSource_inverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFourSourceIndependentContribution s) =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongFourSourceIndependentContribution_bottomedSum_eq_gap]
  exact inverseGapImage_eq_neg_89000_div_128511

/-! ## Bundled bottomed certificate -/

/-- The independent four-source alpha residual producer, bottomed in the
explicit SU(7) block-incidence carrier identities. -/
structure AlphaStrongBottomedFourSourceResidualProducerCertificate : Prop where
  four_source_identity :
    AlphaStrongFourSourceIdentityProducerCertificate
  qcd_carrier :
    Nonempty QCDCarrierB0FinalReceipt
  incidence_orientation :
    Nonempty SU7IncidenceOrientationUniquenessCertificate
  coefficient_provenance :
    OneLoopCoefficientProvenanceReceipt
  su7_breaking_from_cards :
    alphaStrongSU7BreakingStructuralSourceGap = (89 : ℚ) / 10000
  threshold_from_carrier_b0 :
    alphaStrongThresholdMismatchSourceGap = 0
  rg_from_qcd_block_input :
    alphaStrongThreeLoopRGMismatchSourceGap = 0
  higgs_extra_from_slot_equiv :
    alphaStrongHiggsExtraSpectrumMismatchSourceGap = 0
  bottomed_normal_form :
    alphaStrongFourSourceIndependentContribution .su7Breaking =
        (89 : ℚ) / 10000 ∧
      alphaStrongFourSourceIndependentContribution .threshold = 0 ∧
        alphaStrongFourSourceIndependentContribution .threeLoopRG = 0 ∧
          alphaStrongFourSourceIndependentContribution
              .higgsExtraRepresentation = 0
  bottomed_sum :
    (∑ s : AlphaStrongResidualSource,
        alphaStrongFourSourceIndependentContribution s) =
      alphaStrongTwoLoopSMDisplayedGap ℚ
  bottomed_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongFourSourceIndependentContribution s) =
      -((89000 : ℚ) / 128511)

/-- THEOREM 8: bottomed alpha_s four-source residual producer certificate. -/
theorem alphaStrongBottomedFourSourceResidualProducerCertificate :
    AlphaStrongBottomedFourSourceResidualProducerCertificate where
  four_source_identity :=
    alphaStrongFourSourceIdentityProducerCertificate
  qcd_carrier :=
    ⟨qcdCarrierB0FinalReceipt⟩
  incidence_orientation :=
    ⟨su7IncidenceOrientationUniquenessCertificate⟩
  coefficient_provenance :=
    oneLoopCoefficientProvenanceReceipt
  su7_breaking_from_cards :=
    alphaStrongSU7BreakingStructuralSourceGap_eq_89_div_10000_from_cards
  threshold_from_carrier_b0 :=
    alphaStrongThresholdMismatchSourceGap_eq_zero_from_carrierB0
  rg_from_qcd_block_input :=
    alphaStrongThreeLoopRGMismatchSourceGap_eq_zero_from_qcdBlockInput
  higgs_extra_from_slot_equiv :=
    alphaStrongHiggsExtraSpectrumMismatchSourceGap_eq_zero_from_slotEquiv
  bottomed_normal_form :=
    alphaStrongFourSourceIndependentContribution_bottomedNormalForm
  bottomed_sum :=
    alphaStrongFourSourceIndependentContribution_bottomedSum_eq_gap
  bottomed_inverse_residual :=
    alphaStrongBottomedFourSource_inverseResidual

end StandardModelConstraint
end SaturationMonoid
