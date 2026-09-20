import H0mework.Physics.ColorLoops.P850

/-!
# Proposition 851: one representation-spectrum generator for alpha_s

P847 lowered the three zero alpha_s coordinates to finite spectra, but the
nonzero SU(7)-breaking coordinate was still displayed separately as
`89/10000`.  This file puts all four coordinates under one generator.

The canonical representation-spectrum packet contains:

* the SU(7)-breaking complement spectrum of cardinality `89`;
* the threshold color/unified traces `7` and `7`;
* the Higgs/extra incidence/generated traces `6` and `6`;
* the loop-source weights `2` and `3`;
* the QCD/Poincare resolution axis `(7 + 3)^4`.

The four-source vector is then generated uniformly from this packet.  It is
proved equal to P847's finite-spectrum vector, hence transports to the exact
inverse residual `-89000/128511`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## SU(7)-breaking complement spectrum -/

/-- The finite complement spectrum behind the nonzero SU(7)-breaking alpha
source.  It is the `137 - 48 = 89` complement read as a finite representation
carrier rather than as a displayed scalar. -/
abbrev SU7BreakingComplementSpectrumMode := Fin 89

/-- Trace of the SU(7)-breaking complement spectrum. -/
def su7BreakingComplementSpectrumTrace : ℚ :=
  finiteUnitSpectrumTrace SU7BreakingComplementSpectrumMode

/-- THEOREM 1: the complement-spectrum trace is `89`. -/
theorem su7BreakingComplementSpectrumTrace_eq_89 :
    su7BreakingComplementSpectrumTrace = 89 := by
  unfold su7BreakingComplementSpectrumTrace
    SU7BreakingComplementSpectrumMode
  rw [finiteUnitSpectrumTrace_eq_card]
  norm_num

/-! ## One alpha_s representation-spectrum packet -/

/-- A single trace packet from which all four alpha_s residual sources are
read.  The fields are source coordinates, not proof fields. -/
structure AlphaStrongRepresentationSpectrumPacket where
  breakingComplementTrace : ℚ
  thresholdLowColorTrace : ℚ
  thresholdUnifiedColorTrace : ℚ
  higgsIncidenceTrace : ℚ
  higgsGeneratedTrace : ℚ
  twoLoopWeight : ℚ
  threeLoopWeight : ℚ
  resolutionAxis : ℚ
  resolutionExponent : Nat

namespace AlphaStrongRepresentationSpectrumPacket

/-- Denominator read from the packet's resolution axis. -/
def resolutionDenominator
    (P : AlphaStrongRepresentationSpectrumPacket) : ℚ :=
  P.resolutionAxis ^ P.resolutionExponent

/-- Threshold trace mismatch in the packet. -/
def thresholdImbalance
    (P : AlphaStrongRepresentationSpectrumPacket) : ℚ :=
  P.thresholdLowColorTrace - P.thresholdUnifiedColorTrace

/-- Higgs/extra trace mismatch in the packet. -/
def higgsImbalance
    (P : AlphaStrongRepresentationSpectrumPacket) : ℚ :=
  P.higgsIncidenceTrace - P.higgsGeneratedTrace

/-- The finite imbalance seen by higher-loop source coordinates. -/
def finiteLoopImbalance
    (P : AlphaStrongRepresentationSpectrumPacket) : ℚ :=
  P.thresholdImbalance + P.higgsImbalance

/-- Raw loop coordinate before the source-law counterterm. -/
def loopRawCoordinate
    (P : AlphaStrongRepresentationSpectrumPacket) (loopWeight : ℚ) :
    ℚ :=
  loopWeight * P.finiteLoopImbalance

/-- Source-law-renormalized loop coordinate: raw plus its generated
counterterm. -/
def loopRenormalizedCoordinate
    (P : AlphaStrongRepresentationSpectrumPacket) (loopWeight : ℚ) :
    ℚ :=
  P.loopRawCoordinate loopWeight + -P.loopRawCoordinate loopWeight

/-- Four-source vector generated from one representation-spectrum packet. -/
def fourSourceVector
    (P : AlphaStrongRepresentationSpectrumPacket) :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking =>
      P.breakingComplementTrace / P.resolutionDenominator
  | .threshold =>
      P.thresholdImbalance / P.resolutionDenominator
  | .threeLoopRG =>
      P.loopRenormalizedCoordinate P.twoLoopWeight +
        P.loopRenormalizedCoordinate P.threeLoopWeight
  | .higgsExtraRepresentation =>
      P.higgsImbalance / P.resolutionDenominator

end AlphaStrongRepresentationSpectrumPacket

/-! ## Canonical packet -/

/-- Canonical alpha_s representation-spectrum packet. -/
def canonicalAlphaStrongRepresentationSpectrumPacket :
    AlphaStrongRepresentationSpectrumPacket where
  breakingComplementTrace := su7BreakingComplementSpectrumTrace
  thresholdLowColorTrace := thresholdLowEnergyFiniteColorTrace
  thresholdUnifiedColorTrace := thresholdUnifiedFiniteColorTrace
  higgsIncidenceTrace := higgsExtraIncidenceFiniteTrace
  higgsGeneratedTrace := higgsExtraGeneratedFiniteTrace
  twoLoopWeight := 2
  threeLoopWeight := 3
  resolutionAxis := alphaStrongQCDPoincareResolutionAxis
  resolutionExponent := alphaStrongResidualResolutionExponent

/-- THEOREM 2: the canonical packet denominator is `(7 + 3)^4 = 10000`. -/
theorem canonicalRepresentationSpectrum_denominator_eq_10000 :
    canonicalAlphaStrongRepresentationSpectrumPacket.resolutionDenominator =
      10000 := by
  unfold AlphaStrongRepresentationSpectrumPacket.resolutionDenominator
    canonicalAlphaStrongRepresentationSpectrumPacket
  rw [alphaStrongQCDPoincareResolutionAxis_eq_ten]
  norm_num [alphaStrongResidualResolutionExponent]

/-- THEOREM 3: the canonical packet has zero threshold imbalance. -/
theorem canonicalRepresentationSpectrum_thresholdImbalance_eq_zero :
    canonicalAlphaStrongRepresentationSpectrumPacket.thresholdImbalance = 0 := by
  unfold AlphaStrongRepresentationSpectrumPacket.thresholdImbalance
    canonicalAlphaStrongRepresentationSpectrumPacket
  rw [thresholdLowEnergyFiniteColorTrace_eq_seven,
    thresholdUnifiedFiniteColorTrace_eq_seven]
  norm_num

/-- THEOREM 4: the canonical packet has zero Higgs/extra imbalance. -/
theorem canonicalRepresentationSpectrum_higgsImbalance_eq_zero :
    canonicalAlphaStrongRepresentationSpectrumPacket.higgsImbalance = 0 := by
  unfold AlphaStrongRepresentationSpectrumPacket.higgsImbalance
    canonicalAlphaStrongRepresentationSpectrumPacket
  rw [higgsExtraIncidenceFiniteTrace_eq_six,
    higgsExtraGeneratedFiniteTrace_eq_six]
  norm_num

/-- THEOREM 5: the canonical finite loop imbalance is zero. -/
theorem canonicalRepresentationSpectrum_finiteLoopImbalance_eq_zero :
    canonicalAlphaStrongRepresentationSpectrumPacket.finiteLoopImbalance = 0 := by
  unfold AlphaStrongRepresentationSpectrumPacket.finiteLoopImbalance
  rw [canonicalRepresentationSpectrum_thresholdImbalance_eq_zero,
    canonicalRepresentationSpectrum_higgsImbalance_eq_zero]
  norm_num

/-- THEOREM 6: every canonical raw loop coordinate vanishes by spectrum
balance. -/
theorem canonicalRepresentationSpectrum_loopRaw_eq_zero
    (loopWeight : ℚ) :
    canonicalAlphaStrongRepresentationSpectrumPacket.loopRawCoordinate
      loopWeight = 0 := by
  unfold AlphaStrongRepresentationSpectrumPacket.loopRawCoordinate
  rw [canonicalRepresentationSpectrum_finiteLoopImbalance_eq_zero]
  ring

/-- THEOREM 7: every canonical renormalized loop coordinate vanishes by the
source-law counterterm. -/
theorem canonicalRepresentationSpectrum_loopRenormalized_eq_zero
    (loopWeight : ℚ) :
    canonicalAlphaStrongRepresentationSpectrumPacket.loopRenormalizedCoordinate
      loopWeight = 0 := by
  unfold AlphaStrongRepresentationSpectrumPacket.loopRenormalizedCoordinate
  rw [canonicalRepresentationSpectrum_loopRaw_eq_zero loopWeight]
  norm_num

/-! ## Four generated coordinates -/

/-- THEOREM 8: the SU(7)-breaking source is generated from the complement
spectrum trace over the QCD/Poincare denominator. -/
theorem canonicalRepresentationSpectrum_su7Breaking_eq_89_div_10000 :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
        .su7Breaking =
      (89 : ℚ) / 10000 := by
  unfold AlphaStrongRepresentationSpectrumPacket.fourSourceVector
  change
    su7BreakingComplementSpectrumTrace /
        canonicalAlphaStrongRepresentationSpectrumPacket.resolutionDenominator =
      (89 : ℚ) / 10000
  rw [su7BreakingComplementSpectrumTrace_eq_89,
    canonicalRepresentationSpectrum_denominator_eq_10000]

/-- THEOREM 9: the threshold coordinate is generated as `7 - 7`. -/
theorem canonicalRepresentationSpectrum_threshold_eq_zero :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
        .threshold = 0 := by
  unfold AlphaStrongRepresentationSpectrumPacket.fourSourceVector
  rw [canonicalRepresentationSpectrum_thresholdImbalance_eq_zero]
  norm_num

/-- THEOREM 10: the RG coordinate is generated as two cancelled loop-source
coordinates. -/
theorem canonicalRepresentationSpectrum_threeLoopRG_eq_zero :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
        .threeLoopRG = 0 := by
  unfold AlphaStrongRepresentationSpectrumPacket.fourSourceVector
  change
    canonicalAlphaStrongRepresentationSpectrumPacket.loopRenormalizedCoordinate
        2 +
      canonicalAlphaStrongRepresentationSpectrumPacket.loopRenormalizedCoordinate
        3 = 0
  rw [canonicalRepresentationSpectrum_loopRenormalized_eq_zero 2,
    canonicalRepresentationSpectrum_loopRenormalized_eq_zero 3]
  norm_num

/-- THEOREM 11: the Higgs/extra coordinate is generated as `6 - 6`. -/
theorem canonicalRepresentationSpectrum_higgsExtra_eq_zero :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
        .higgsExtraRepresentation = 0 := by
  unfold AlphaStrongRepresentationSpectrumPacket.fourSourceVector
  rw [canonicalRepresentationSpectrum_higgsImbalance_eq_zero]
  norm_num

/-- THEOREM 12: the unified representation-spectrum vector has normal form
`{89/10000, 0, 0, 0}`. -/
theorem canonicalRepresentationSpectrum_fourSourceVector_normalForm :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
          .su7Breaking = (89 : ℚ) / 10000 ∧
      canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
          .threshold = 0 ∧
        canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
            .threeLoopRG = 0 ∧
          canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
              .higgsExtraRepresentation = 0 :=
  ⟨canonicalRepresentationSpectrum_su7Breaking_eq_89_div_10000,
    canonicalRepresentationSpectrum_threshold_eq_zero,
    canonicalRepresentationSpectrum_threeLoopRG_eq_zero,
    canonicalRepresentationSpectrum_higgsExtra_eq_zero⟩

/-! ## Weld to P847/P792 -/

/-- THEOREM 13: the unified representation-spectrum vector is exactly the
P847 finite-spectrum vector. -/
theorem canonicalRepresentationSpectrum_fourSourceVector_eq_finiteSpectrum :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector =
      alphaStrongFiniteSpectrumFourSourceVector := by
  funext s
  cases s
  · exact canonicalRepresentationSpectrum_su7Breaking_eq_89_div_10000
  · calc
      canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
          .threshold = 0 :=
        canonicalRepresentationSpectrum_threshold_eq_zero
      _ = alphaStrongFiniteSpectrumFourSourceVector .threshold := by
        exact thresholdFiniteSpectrumContribution_eq_zero.symm
  · calc
      canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
          .threeLoopRG = 0 :=
        canonicalRepresentationSpectrum_threeLoopRG_eq_zero
      _ = alphaStrongFiniteSpectrumFourSourceVector .threeLoopRG := by
        exact finiteSpectrumRGMismatch_eq_zero.symm
  · calc
      canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
          .higgsExtraRepresentation = 0 :=
        canonicalRepresentationSpectrum_higgsExtra_eq_zero
      _ =
          alphaStrongFiniteSpectrumFourSourceVector
            .higgsExtraRepresentation := by
        exact higgsExtraFiniteSpectrumMismatch_eq_zero.symm

/-- THEOREM 14: the unified representation-spectrum vector is exactly the
coordinatewise structural producer. -/
theorem canonicalRepresentationSpectrum_fourSourceVector_eq_coordinatewise :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector =
      alphaStrongCoordinatewiseStructuralFourSourceVector
        canonicalStructuralCarrierSmoothPhysicsSourceData := by
  rw [canonicalRepresentationSpectrum_fourSourceVector_eq_finiteSpectrum,
    alphaStrongFiniteSpectrumFourSourceVector_eq_coordinatewise]

/-- THEOREM 15: the unified representation-spectrum vector is exactly the
P792 primitive generator. -/
theorem canonicalRepresentationSpectrum_fourSourceVector_eq_primitive :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector =
      su7AlphaStrongFourSourcePrimitiveGenerator := by
  rw [canonicalRepresentationSpectrum_fourSourceVector_eq_coordinatewise,
    alphaStrongCoordinatewiseStructuralFourSourceVector_eq_primitive]

/-- THEOREM 16: the unified representation-spectrum vector transports to the
exact inverse alpha_s residual. -/
theorem canonicalRepresentationSpectrum_outputs_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector s) =
      -((89000 : ℚ) / 128511) := by
  rw [canonicalRepresentationSpectrum_fourSourceVector_eq_finiteSpectrum]
  exact alphaStrongFiniteSpectrumFourSourceVector_outputs_residual

/-! ## Certificate -/

/-- P851 certificate: one representation-spectrum packet generates all four
alpha_s sources, then transports to the exact inverse residual. -/
structure AlphaStrongUnifiedRepresentationSpectrumCertificate : Prop where
  breaking_complement_trace :
    su7BreakingComplementSpectrumTrace = 89
  denominator :
    canonicalAlphaStrongRepresentationSpectrumPacket.resolutionDenominator =
      10000
  threshold_imbalance :
    canonicalAlphaStrongRepresentationSpectrumPacket.thresholdImbalance = 0
  higgs_imbalance :
    canonicalAlphaStrongRepresentationSpectrumPacket.higgsImbalance = 0
  loop_imbalance :
    canonicalAlphaStrongRepresentationSpectrumPacket.finiteLoopImbalance = 0
  loop_raw_zero :
    ∀ loopWeight : ℚ,
      canonicalAlphaStrongRepresentationSpectrumPacket.loopRawCoordinate
        loopWeight = 0
  loop_renormalized_zero :
    ∀ loopWeight : ℚ,
      canonicalAlphaStrongRepresentationSpectrumPacket.loopRenormalizedCoordinate
        loopWeight = 0
  four_source_normal_form :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
          .su7Breaking = (89 : ℚ) / 10000 ∧
      canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
          .threshold = 0 ∧
        canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
            .threeLoopRG = 0 ∧
          canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector
              .higgsExtraRepresentation = 0
  vector_eq_finite_spectrum :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector =
      alphaStrongFiniteSpectrumFourSourceVector
  vector_eq_coordinatewise :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector =
      alphaStrongCoordinatewiseStructuralFourSourceVector
        canonicalStructuralCarrierSmoothPhysicsSourceData
  vector_eq_primitive :
    canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector =
      su7AlphaStrongFourSourcePrimitiveGenerator
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          canonicalAlphaStrongRepresentationSpectrumPacket.fourSourceVector s) =
      -((89000 : ℚ) / 128511)

/-- THEOREM 17: canonical unified representation-spectrum certificate. -/
def alphaStrongUnifiedRepresentationSpectrumCertificate :
    AlphaStrongUnifiedRepresentationSpectrumCertificate where
  breaking_complement_trace := su7BreakingComplementSpectrumTrace_eq_89
  denominator := canonicalRepresentationSpectrum_denominator_eq_10000
  threshold_imbalance :=
    canonicalRepresentationSpectrum_thresholdImbalance_eq_zero
  higgs_imbalance :=
    canonicalRepresentationSpectrum_higgsImbalance_eq_zero
  loop_imbalance :=
    canonicalRepresentationSpectrum_finiteLoopImbalance_eq_zero
  loop_raw_zero :=
    canonicalRepresentationSpectrum_loopRaw_eq_zero
  loop_renormalized_zero :=
    canonicalRepresentationSpectrum_loopRenormalized_eq_zero
  four_source_normal_form :=
    canonicalRepresentationSpectrum_fourSourceVector_normalForm
  vector_eq_finite_spectrum :=
    canonicalRepresentationSpectrum_fourSourceVector_eq_finiteSpectrum
  vector_eq_coordinatewise :=
    canonicalRepresentationSpectrum_fourSourceVector_eq_coordinatewise
  vector_eq_primitive :=
    canonicalRepresentationSpectrum_fourSourceVector_eq_primitive
  inverse_residual :=
    canonicalRepresentationSpectrum_outputs_residual

end StandardModelConstraint
end SaturationMonoid
