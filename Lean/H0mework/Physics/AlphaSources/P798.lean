import H0mework.Physics.AlphaSources.P797

/-!
# Proposition 798: low-level smooth-source generators for alpha_s

P797 proves that a canonical smooth-physics state outputs the P792 alpha_s
four-source primitive generator.  This file lowers the three smooth zero
coordinates one layer again: the canonical smooth state is generated from
low-level source data.

* threshold is generated from a Standard-Model color trace and the unified
  SU(7) incidence color trace;
* RG is generated from beta coefficients by the exact source-law integral
  `effectiveSlope ↦ effectiveSlope`;
* Higgs-extra is generated from an incidence-to-generated-slot equivalence.

The output theorem is therefore phrased as a producer chain:

`low-level smooth source data -> smooth state -> four-source vector ->
inverse alpha_s residual`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open scoped BigOperators

/-! ## Threshold source producer -/

/-- Low-level threshold trace data: the low-energy color trace and the unified
SU(7)-incidence color trace. -/
structure ThresholdTraceSourceData where
  lowEnergyColorTrace : ℚ
  unifiedIncidenceColorTrace : ℚ

/-- Generate the P797 threshold spectrum from trace-source data. -/
def thresholdSpectrumFromTraceSource
    (D : ThresholdTraceSourceData) :
    CompleteDegenerateSU7MultipletSpectrum where
  colorTrace := D.lowEnergyColorTrace
  unifiedColorTrace := D.unifiedIncidenceColorTrace

/-- The trace-source data is balanced exactly when it generates a complete
degenerate threshold spectrum. -/
def ThresholdTraceSourceBalanced
    (D : ThresholdTraceSourceData) : Prop :=
  D.lowEnergyColorTrace = D.unifiedIncidenceColorTrace

/-- Balanced trace-source data generates a complete degenerate spectrum. -/
theorem thresholdSpectrumFromTraceSource_complete
    (D : ThresholdTraceSourceData)
    (hD : ThresholdTraceSourceBalanced D) :
    CompleteDegenerateSU7Multiplet
      (thresholdSpectrumFromTraceSource D) := by
  exact hD

/-- Balanced trace-source data generates zero threshold contribution. -/
theorem thresholdContribution_fromTraceSource_eq_zero
    (D : ThresholdTraceSourceData)
    (hD : ThresholdTraceSourceBalanced D) :
    thresholdContribution (thresholdSpectrumFromTraceSource D) = 0 :=
  thresholdContribution_eq_zero_of_completeDegenerate
    (thresholdSpectrumFromTraceSource D)
    (thresholdSpectrumFromTraceSource_complete D hD)

/-- Canonical threshold source data generated from the Standard-Model color
slope and the SU(7) incidence color slope. -/
def canonicalThresholdTraceSourceData : ThresholdTraceSourceData where
  lowEnergyColorTrace := standardModelAsymptoticB0 .colorSU3
  unifiedIncidenceColorTrace := betaCoeff (incidenceCarrierTraceInput .colorSU3)

/-- The canonical threshold source data is balanced by the SU(7) incidence
carrier `b0` identity. -/
theorem canonicalThresholdTraceSourceData_balanced :
    ThresholdTraceSourceBalanced canonicalThresholdTraceSourceData := by
  unfold ThresholdTraceSourceBalanced canonicalThresholdTraceSourceData
  have hinc :
      betaCoeff (incidenceCarrierTraceInput .colorSU3) =
        carrierB0 .colorSU3 :=
    betaCoeff_incidenceCarrierTraceInput_eq_carrierB0 .colorSU3
  have hsm :
      carrierB0 .colorSU3 =
        standardModelAsymptoticB0 .colorSU3 :=
    carrierB0_eq_standardModelAsymptoticB0 .colorSU3
  exact (hinc.trans hsm).symm

/-- The canonical threshold trace-source data generates the canonical P797
threshold spectrum. -/
theorem thresholdSpectrumFromTraceSource_canonical :
    thresholdSpectrumFromTraceSource canonicalThresholdTraceSourceData =
      canonicalCompleteDegenerateSU7MultipletSpectrum := by
  rfl

/-! ## RG source-law producer -/

/-- Generate an exact RG integral certificate from beta coefficients by
reading both the integrated slope and source-law running-sigma slope through
the same effective beta slope. -/
def exactRGIntegralFromBeta
    (B : ThreeLoopBetaCoefficients) : ExactRGIntegralCertificate where
  integratedSlope := B.effectiveSlope
  sourceLawRunningSigmaSlope := B.effectiveSlope

/-- Generate an RG source state from beta coefficients and an incidence color
slope. -/
def threeLoopRGStateFromBetaAndIncidence
    (B : ThreeLoopBetaCoefficients)
    (incidenceColorSlope : ℚ) :
    ThreeLoopRGSourceState where
  beta := B
  integral := exactRGIntegralFromBeta B
  incidenceColorSlope := incidenceColorSlope

/-- The beta producer matches the incidence slope when its effective slope is
the incidence color slope. -/
def ThreeLoopBetaIncidenceMatch
    (B : ThreeLoopBetaCoefficients)
    (incidenceColorSlope : ℚ) : Prop :=
  B.effectiveSlope = incidenceColorSlope

/-- A beta/incidence match generates an exact source-law RG match. -/
theorem threeLoopRGStateFromBetaAndIncidence_sourceLawMatch
    (B : ThreeLoopBetaCoefficients)
    (incidenceColorSlope : ℚ)
    (hB : ThreeLoopBetaIncidenceMatch B incidenceColorSlope) :
    ThreeLoopRGExactSourceLawMatch
      (threeLoopRGStateFromBetaAndIncidence B incidenceColorSlope) := by
  unfold ThreeLoopRGExactSourceLawMatch
    threeLoopRGStateFromBetaAndIncidence exactRGIntegralFromBeta
  constructor
  · rfl
  constructor
  · rfl
  · exact hB

/-- A beta/incidence match generates zero RG mismatch. -/
theorem rgMismatch_fromBetaAndIncidence_eq_zero
    (B : ThreeLoopBetaCoefficients)
    (incidenceColorSlope : ℚ)
    (hB : ThreeLoopBetaIncidenceMatch B incidenceColorSlope) :
    rgMismatch
        (threeLoopRGStateFromBetaAndIncidence B incidenceColorSlope) = 0 :=
  rgMismatch_eq_zero_of_sourceLawMatch
    (threeLoopRGStateFromBetaAndIncidence B incidenceColorSlope)
    (threeLoopRGStateFromBetaAndIncidence_sourceLawMatch
      B incidenceColorSlope hB)

/-- The canonical beta coefficients match the SU(7) incidence color slope. -/
theorem canonicalThreeLoopBetaCoefficients_incidenceMatch :
    ThreeLoopBetaIncidenceMatch
      canonicalThreeLoopBetaCoefficients
      (betaCoeff (incidenceCarrierTraceInput .colorSU3)) := by
  unfold ThreeLoopBetaIncidenceMatch canonicalThreeLoopBetaCoefficients
    ThreeLoopBetaCoefficients.effectiveSlope
  rw [qcdBlockIncidenceOneLoopInput_eq_incidenceCarrierTraceInput]
  ring

/-- The canonical RG source state is generated from beta coefficients and the
incidence color slope. -/
theorem threeLoopRGStateFromBetaAndIncidence_canonical :
    threeLoopRGStateFromBetaAndIncidence
        canonicalThreeLoopBetaCoefficients
        (betaCoeff (incidenceCarrierTraceInput .colorSU3)) =
      canonicalThreeLoopRGSourceState := by
  unfold threeLoopRGStateFromBetaAndIncidence canonicalThreeLoopRGSourceState
    exactRGIntegralFromBeta canonicalExactRGIntegralCertificate
    canonicalThreeLoopBetaCoefficients ThreeLoopBetaCoefficients.effectiveSlope
  rw [qcdBlockIncidenceOneLoopInput_eq_incidenceCarrierTraceInput]
  simp

/-! ## Higgs-extra incidence-slot producer -/

/-- Generate the P797 Higgs/extra spectrum from an equivalence between
incidences and generated matter/Higgs slots.  The equivalence is the producer;
the two counts are its domain and codomain cardinalities. -/
def generatedHiggsExtraSpectrumFromIncidenceEquiv
    (_e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot) :
    GeneratedHiggsExtraSpectrum where
  incidenceSlotCount := (Fintype.card SU7BlockIncidence : ℚ)
  generatedSpectrumSlotCount := (Fintype.card SU7GeneratedCarrierSlot : ℚ)

/-- Any incidence/generated-slot equivalence generates a balanced
Higgs/extra spectrum. -/
theorem generatedHiggsExtraSpectrumFromIncidenceEquiv_balanced
    (e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot) :
    SU7IncidenceSlotBalance
      (generatedHiggsExtraSpectrumFromIncidenceEquiv e) := by
  unfold SU7IncidenceSlotBalance generatedHiggsExtraSpectrumFromIncidenceEquiv
  change (Fintype.card SU7BlockIncidence : ℚ) =
    (Fintype.card SU7GeneratedCarrierSlot : ℚ)
  exact_mod_cast Fintype.card_congr e

/-- Any incidence/generated-slot equivalence generates zero Higgs-extra
mismatch. -/
theorem higgsExtraMismatch_fromIncidenceEquiv_eq_zero
    (e : SU7BlockIncidence ≃ SU7GeneratedCarrierSlot) :
    higgsExtraMismatch
        (generatedHiggsExtraSpectrumFromIncidenceEquiv e) = 0 :=
  higgsExtraMismatch_eq_zero_of_slotBalance
    (generatedHiggsExtraSpectrumFromIncidenceEquiv e)
    (generatedHiggsExtraSpectrumFromIncidenceEquiv_balanced e)

/-- The canonical incidence equivalence generates the canonical P797
Higgs/extra spectrum. -/
theorem generatedHiggsExtraSpectrumFromIncidenceEquiv_canonical :
    generatedHiggsExtraSpectrumFromIncidenceEquiv
        blockIncidenceGeneratedSlotEquiv =
      canonicalGeneratedHiggsExtraSpectrum := by
  rfl

/-! ## Low-level smooth-state producer -/

/-- Low-level source data for the full smooth alpha_s producer. -/
structure LowLevelSmoothPhysicsSourceData where
  su7BreakingSource : ℚ
  thresholdTrace : ThresholdTraceSourceData
  beta : ThreeLoopBetaCoefficients
  incidenceColorSlope : ℚ
  incidenceGeneratedSlotEquiv :
    SU7BlockIncidence ≃ SU7GeneratedCarrierSlot

/-- Generate the P797 smooth-physics state from low-level source data. -/
def smoothPhysicsStateFromLowLevelSource
    (D : LowLevelSmoothPhysicsSourceData) :
    SmoothPhysicsAlphaStrongState where
  su7BreakingSource := D.su7BreakingSource
  thresholdSpectrum :=
    thresholdSpectrumFromTraceSource D.thresholdTrace
  rgState :=
    threeLoopRGStateFromBetaAndIncidence
      D.beta D.incidenceColorSlope
  higgsExtraSpectrum :=
    generatedHiggsExtraSpectrumFromIncidenceEquiv
      D.incidenceGeneratedSlotEquiv

/-- Canonical low-level source data for the smooth alpha_s producer. -/
def canonicalLowLevelSmoothPhysicsSourceData :
    LowLevelSmoothPhysicsSourceData where
  su7BreakingSource := alphaStrongSU7BreakingCardSourceGap
  thresholdTrace := canonicalThresholdTraceSourceData
  beta := canonicalThreeLoopBetaCoefficients
  incidenceColorSlope := betaCoeff (incidenceCarrierTraceInput .colorSU3)
  incidenceGeneratedSlotEquiv := blockIncidenceGeneratedSlotEquiv

/-- The canonical low-level source data generates the P797 canonical smooth
physics state. -/
theorem smoothPhysicsStateFromLowLevelSource_canonical :
    smoothPhysicsStateFromLowLevelSource
        canonicalLowLevelSmoothPhysicsSourceData =
      canonicalSmoothPhysicsState := by
  unfold smoothPhysicsStateFromLowLevelSource
    canonicalLowLevelSmoothPhysicsSourceData canonicalSmoothPhysicsState
  rw [threeLoopRGStateFromBetaAndIncidence_canonical]
  rfl

/-- THEOREM 1: the low-level source producer outputs exactly the P792
four-source primitive generator. -/
theorem lowLevelSmoothPhysicsFourSourceOutput_eq_target :
    smoothPhysicsFourSourceOutput
        (smoothPhysicsStateFromLowLevelSource
          canonicalLowLevelSmoothPhysicsSourceData) =
      su7AlphaStrongFourSourcePrimitiveGenerator := by
  rw [smoothPhysicsStateFromLowLevelSource_canonical]
  exact smoothPhysicsFourSourceOutput_eq_target

/-- THEOREM 2: the low-level smooth-source producer transports to the exact
inverse alpha_s residual. -/
theorem alphaStrongLowLevelSmoothPhysicsProducer_outputs_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          smoothPhysicsFourSourceOutput
            (smoothPhysicsStateFromLowLevelSource
              canonicalLowLevelSmoothPhysicsSourceData) s) =
      -((89000 : ℚ) / 128511) := by
  rw [lowLevelSmoothPhysicsFourSourceOutput_eq_target]
  exact su7AlphaStrongFourSourcePrimitiveGenerator_inverseResidual

/-! ## Bundled certificate -/

/-- Low-level smooth-source producer certificate. -/
structure AlphaStrongLowLevelSmoothSourceProducerCertificate : Prop where
  threshold_balanced :
    ThresholdTraceSourceBalanced canonicalThresholdTraceSourceData
  threshold_zero :
    thresholdContribution
        (thresholdSpectrumFromTraceSource canonicalThresholdTraceSourceData) =
      0
  rg_beta_incidence_match :
    ThreeLoopBetaIncidenceMatch
      canonicalThreeLoopBetaCoefficients
      (betaCoeff (incidenceCarrierTraceInput .colorSU3))
  rg_zero :
    rgMismatch
        (threeLoopRGStateFromBetaAndIncidence
          canonicalThreeLoopBetaCoefficients
          (betaCoeff (incidenceCarrierTraceInput .colorSU3))) = 0
  higgs_extra_balance :
    SU7IncidenceSlotBalance
      (generatedHiggsExtraSpectrumFromIncidenceEquiv
        blockIncidenceGeneratedSlotEquiv)
  higgs_extra_zero :
    higgsExtraMismatch
        (generatedHiggsExtraSpectrumFromIncidenceEquiv
          blockIncidenceGeneratedSlotEquiv) = 0
  state_eq_canonical :
    smoothPhysicsStateFromLowLevelSource
        canonicalLowLevelSmoothPhysicsSourceData =
      canonicalSmoothPhysicsState
  output_eq_primitive :
    smoothPhysicsFourSourceOutput
        (smoothPhysicsStateFromLowLevelSource
          canonicalLowLevelSmoothPhysicsSourceData) =
      su7AlphaStrongFourSourcePrimitiveGenerator
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          smoothPhysicsFourSourceOutput
            (smoothPhysicsStateFromLowLevelSource
              canonicalLowLevelSmoothPhysicsSourceData) s) =
      -((89000 : ℚ) / 128511)

/-- THEOREM 3: bundled low-level smooth-source alpha_s producer certificate. -/
theorem alphaStrongLowLevelSmoothSourceProducerCertificate :
    AlphaStrongLowLevelSmoothSourceProducerCertificate where
  threshold_balanced :=
    canonicalThresholdTraceSourceData_balanced
  threshold_zero :=
    thresholdContribution_fromTraceSource_eq_zero
      canonicalThresholdTraceSourceData
      canonicalThresholdTraceSourceData_balanced
  rg_beta_incidence_match :=
    canonicalThreeLoopBetaCoefficients_incidenceMatch
  rg_zero :=
    rgMismatch_fromBetaAndIncidence_eq_zero
      canonicalThreeLoopBetaCoefficients
      (betaCoeff (incidenceCarrierTraceInput .colorSU3))
      canonicalThreeLoopBetaCoefficients_incidenceMatch
  higgs_extra_balance :=
    generatedHiggsExtraSpectrumFromIncidenceEquiv_balanced
      blockIncidenceGeneratedSlotEquiv
  higgs_extra_zero :=
    higgsExtraMismatch_fromIncidenceEquiv_eq_zero
      blockIncidenceGeneratedSlotEquiv
  state_eq_canonical :=
    smoothPhysicsStateFromLowLevelSource_canonical
  output_eq_primitive :=
    lowLevelSmoothPhysicsFourSourceOutput_eq_target
  inverse_residual :=
    alphaStrongLowLevelSmoothPhysicsProducer_outputs_residual

end StandardModelConstraint
end SaturationMonoid
