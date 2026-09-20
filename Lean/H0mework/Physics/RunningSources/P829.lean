import H0mework.Physics.AlphaSources.P823

/-!
# Proposition 829: alpha_s zero sources are spectrum/counterterm coordinates

P823 defines the alpha_s four-source vector coordinatewise.  This file opens
the three zero coordinates one layer further so they are not just zero-valued
receipts:

* threshold zero is the equality of the generated low-energy color trace and
  unified incidence color trace, both equal to `7`;
* three-loop RG zero is the generated raw/counterterm/renormalized loop
  coordinates at loop weights `2` and `3`, all reducing to zero after the SU(7)
  source-law counterterm construction;
* Higgs/extra zero is the generated incidence-slot spectrum `6 = 6`.

The bundled certificate then feeds these explicit coordinates back into the
P823 four-source generator and the exact inverse residual `-89000/128511`.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open RunningSigmaBeta
open scoped BigOperators

set_option linter.checkUnivs false
set_option linter.defProp false

/-! ## Threshold spectrum coordinates -/

/-- THEOREM 1: the Standard-Model color trace generated for the threshold
source is the QCD carrier value `7`. -/
theorem alphaStrongThreshold_lowEnergyColorTrace_eq_seven :
    (thresholdTraceSourceFromOneLoopCarrier
        standardModelOneLoopCarrierFinalReceipt).lowEnergyColorTrace = 7 := by
  unfold thresholdTraceSourceFromOneLoopCarrier
  have hinc : betaCoeff (incidenceCarrierTraceInput .colorSU3) = 7 :=
    su7RepresentationMatterHiggsNormalForm_b0Values.1
  have hall :=
    su7RepresentationMatterHiggsNormalForm_b0Values.2.2.2 .colorSU3
  rw [← hall]
  exact hinc

/-- THEOREM 2: the unified SU(7)-incidence color trace generated for the
threshold source is also `7`. -/
theorem alphaStrongThreshold_unifiedColorTrace_eq_seven :
    (thresholdTraceSourceFromOneLoopCarrier
        standardModelOneLoopCarrierFinalReceipt).unifiedIncidenceColorTrace =
      7 := by
  unfold thresholdTraceSourceFromOneLoopCarrier
  exact su7RepresentationMatterHiggsNormalForm_b0Values.1

/-- THEOREM 3: the generated threshold spectrum has color trace `7`. -/
theorem alphaStrongThresholdSpectrum_colorTrace_eq_seven :
    (thresholdSpectrumFromTraceSource
      (thresholdTraceSourceFromOneLoopCarrier
        standardModelOneLoopCarrierFinalReceipt)).colorTrace = 7 := by
  exact alphaStrongThreshold_lowEnergyColorTrace_eq_seven

/-- THEOREM 4: the generated threshold spectrum has unified color trace `7`. -/
theorem alphaStrongThresholdSpectrum_unifiedColorTrace_eq_seven :
    (thresholdSpectrumFromTraceSource
      (thresholdTraceSourceFromOneLoopCarrier
        standardModelOneLoopCarrierFinalReceipt)).unifiedColorTrace = 7 := by
  exact alphaStrongThreshold_unifiedColorTrace_eq_seven

/-- THEOREM 5: the threshold contribution vanishes by subtracting the two
generated trace coordinates `7 - 7`, not by a supplied zero receipt. -/
theorem alphaStrongThresholdContribution_generatedSpectrum_eq_zero :
    thresholdContribution
        (thresholdSpectrumFromTraceSource
          (thresholdTraceSourceFromOneLoopCarrier
            standardModelOneLoopCarrierFinalReceipt)) = 0 := by
  exact thresholdContribution_fromTraceSource_eq_zero
    (thresholdTraceSourceFromOneLoopCarrier
      standardModelOneLoopCarrierFinalReceipt)
    (thresholdTraceSourceFromOneLoopCarrier_balanced
      standardModelOneLoopCarrierFinalReceipt)

/-! ## Three-loop RG counterterm coordinates -/

/-- The canonical structural SU(7) loop-counterterm source. -/
abbrev canonicalStructuralLoopCountertermSource :
    SU7LoopCountertermSourceData :=
  loopCountertermSourceOfStructuralCarrierSource
    canonicalStructuralCarrierSmoothPhysicsSourceData

/-- THEOREM 6: the generated two-loop raw source coordinate is zero. -/
theorem alphaStrongTwoLoopRawCoordinate_eq_zero :
    su7LoopRawCoordinate canonicalStructuralLoopCountertermSource 2 = 0 := by
  exact su7LoopRawCoordinate_eq_zero_of_balanced
    canonicalStructuralLoopCountertermSource 2
    (thresholdTraceSourceFromOneLoopCarrier_balanced
      standardModelOneLoopCarrierFinalReceipt)

/-- THEOREM 7: the generated three-loop raw source coordinate is zero. -/
theorem alphaStrongThreeLoopRawCoordinate_eq_zero :
    su7LoopRawCoordinate canonicalStructuralLoopCountertermSource 3 = 0 := by
  exact su7LoopRawCoordinate_eq_zero_of_balanced
    canonicalStructuralLoopCountertermSource 3
    (thresholdTraceSourceFromOneLoopCarrier_balanced
      standardModelOneLoopCarrierFinalReceipt)

/-- THEOREM 8: the two-loop diagram coordinate generated from the SU(7)
counterterm source is zero. -/
theorem alphaStrongTwoLoopDiagramCoordinate_eq_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 2).diagram = 0 := by
  unfold loopCoordinateContributionFromSU7CountertermSource
  exact alphaStrongTwoLoopRawCoordinate_eq_zero

/-- THEOREM 9: the two-loop counterterm coordinate is zero because it is the
source-law subtraction of the generated zero raw coordinate. -/
theorem alphaStrongTwoLoopCountertermCoordinate_eq_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 2).counterterm = 0 := by
  unfold loopCoordinateContributionFromSU7CountertermSource
  rw [alphaStrongTwoLoopRawCoordinate_eq_zero]
  norm_num

/-- THEOREM 10: the renormalized two-loop source coordinate is zero. -/
theorem alphaStrongTwoLoopRenormalizedCoordinate_eq_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource
      2).renormalized = 0 := by
  unfold LoopCoordinateContribution.renormalized
  rw [alphaStrongTwoLoopDiagramCoordinate_eq_zero,
    alphaStrongTwoLoopCountertermCoordinate_eq_zero]
  norm_num

/-- THEOREM 11: the three-loop diagram coordinate generated from the SU(7)
counterterm source is zero. -/
theorem alphaStrongThreeLoopDiagramCoordinate_eq_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 3).diagram = 0 := by
  unfold loopCoordinateContributionFromSU7CountertermSource
  exact alphaStrongThreeLoopRawCoordinate_eq_zero

/-- THEOREM 12: the three-loop counterterm coordinate is zero because it is the
source-law subtraction of the generated zero raw coordinate. -/
theorem alphaStrongThreeLoopCountertermCoordinate_eq_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 3).counterterm = 0 := by
  unfold loopCoordinateContributionFromSU7CountertermSource
  rw [alphaStrongThreeLoopRawCoordinate_eq_zero]
  norm_num

/-- THEOREM 13: the renormalized three-loop source coordinate is zero. -/
theorem alphaStrongThreeLoopRenormalizedCoordinate_eq_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource
      3).renormalized = 0 := by
  unfold LoopCoordinateContribution.renormalized
  rw [alphaStrongThreeLoopDiagramCoordinate_eq_zero,
    alphaStrongThreeLoopCountertermCoordinate_eq_zero]
  norm_num

/-- THEOREM 14: the generated RG beta effective slope is the incidence/QCD
value `7` after the higher-loop source coordinates cancel. -/
theorem alphaStrongGeneratedThreeLoopEffectiveSlope_eq_seven :
    (threeLoopBetaCoefficientsFromExpansion
      (threeLoopRGExpansionFromSU7CountertermSource
        canonicalStructuralLoopCountertermSource)).effectiveSlope = 7 := by
  rw [threeLoopBetaCoefficientsFromSU7CountertermSource_eq_canonical]
  unfold ThreeLoopBetaCoefficients.effectiveSlope
    canonicalThreeLoopBetaCoefficients
  rw [su7RepresentationMatterHiggsNormalForm_numericalSpine.1]
  norm_num

/-- THEOREM 15: the RG mismatch vanishes from the generated counterterm
coordinates and incidence slope. -/
theorem alphaStrongGeneratedRGMismatch_eq_zero :
    rgMismatch
        (threeLoopRGStateFromBetaAndIncidence
          (threeLoopBetaCoefficientsFromExpansion
            (threeLoopRGExpansionFromSU7CountertermSource
              canonicalStructuralLoopCountertermSource))
          (betaCoeff (incidenceCarrierTraceInput .colorSU3))) = 0 := by
  exact rgMismatch_fromSU7CountertermSource_eq_zero
    canonicalStructuralLoopCountertermSource

/-! ## Higgs/extra spectrum coordinates -/

/-- The canonical generated Higgs/extra spectrum read from SU(7) incidence
orientation. -/
abbrev canonicalStructuralGeneratedHiggsExtraSpectrum :
    GeneratedHiggsExtraSpectrum :=
  generatedHiggsExtraSpectrumFromIncidenceEquiv
    (incidenceEquivFromOrientationCertificate
      su7IncidenceOrientationUniquenessCertificate)

/-- THEOREM 16: the incidence side of the generated Higgs/extra spectrum has
six slots. -/
theorem alphaStrongHiggsExtra_incidenceSlotCount_eq_six :
    canonicalStructuralGeneratedHiggsExtraSpectrum.incidenceSlotCount = 6 := by
  unfold canonicalStructuralGeneratedHiggsExtraSpectrum
    generatedHiggsExtraSpectrumFromIncidenceEquiv
  norm_num [SU7BlockIncidence.card]

/-- THEOREM 17: the generated matter/Higgs side of the spectrum also has six
slots. -/
theorem alphaStrongHiggsExtra_generatedSlotCount_eq_six :
    canonicalStructuralGeneratedHiggsExtraSpectrum.generatedSpectrumSlotCount =
      6 := by
  unfold canonicalStructuralGeneratedHiggsExtraSpectrum
    generatedHiggsExtraSpectrumFromIncidenceEquiv
  norm_num [SU7GeneratedCarrierSlot.card]

/-- THEOREM 18: the Higgs/extra mismatch vanishes by subtracting the generated
spectrum coordinates `6 - 6`. -/
theorem alphaStrongHiggsExtra_generatedSpectrumMismatch_eq_zero :
    higgsExtraMismatch canonicalStructuralGeneratedHiggsExtraSpectrum = 0 := by
  exact higgsExtraMismatch_fromIncidenceEquiv_eq_zero
    (incidenceEquivFromOrientationCertificate
      su7IncidenceOrientationUniquenessCertificate)

/-! ## Feed the explicit coordinates back into the four-source generator -/

/-- THEOREM 19: the coordinatewise structural four-source vector is explicitly
generated as `{89/10000, 0, 0, 0}` after the spectrum/counterterm coordinates
above are expanded. -/
theorem alphaStrongSpectrumResolvedFourSourceVector_normalForm :
    alphaStrongCoordinatewiseStructuralFourSourceVector
          canonicalStructuralCarrierSmoothPhysicsSourceData .su7Breaking =
        (89 : ℚ) / 10000 ∧
      alphaStrongCoordinatewiseStructuralFourSourceVector
          canonicalStructuralCarrierSmoothPhysicsSourceData .threshold = 0 ∧
        alphaStrongCoordinatewiseStructuralFourSourceVector
            canonicalStructuralCarrierSmoothPhysicsSourceData .threeLoopRG =
          0 ∧
          alphaStrongCoordinatewiseStructuralFourSourceVector
              canonicalStructuralCarrierSmoothPhysicsSourceData
                .higgsExtraRepresentation = 0 := by
  exact alphaStrongCoordinatewiseStructuralFourSourceVector_normalForm

/-- THEOREM 20: the spectrum-resolved four-source vector transports to the
exact inverse residual. -/
theorem alphaStrongSpectrumResolvedFourSourceProducer_outputs_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongCoordinatewiseStructuralFourSourceVector
            canonicalStructuralCarrierSmoothPhysicsSourceData s) =
      -((89000 : ℚ) / 128511) := by
  exact alphaStrongCoordinatewiseStructuralProducer_outputs_residual

/-! ## Bundled certificate -/

/-- P829 certificate: the alpha_s zero source coordinates are produced by
visible spectra/counterterms before the four-source vector is summed. -/
structure AlphaStrongSpectrumResolvedFourSourceProducerCertificate : Prop where
  threshold_low_trace :
    (thresholdTraceSourceFromOneLoopCarrier
        standardModelOneLoopCarrierFinalReceipt).lowEnergyColorTrace = 7
  threshold_unified_trace :
    (thresholdTraceSourceFromOneLoopCarrier
        standardModelOneLoopCarrierFinalReceipt).unifiedIncidenceColorTrace =
      7
  threshold_zero :
    thresholdContribution
        (thresholdSpectrumFromTraceSource
          (thresholdTraceSourceFromOneLoopCarrier
            standardModelOneLoopCarrierFinalReceipt)) = 0
  two_loop_raw_zero :
    su7LoopRawCoordinate canonicalStructuralLoopCountertermSource 2 = 0
  two_loop_diagram_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 2).diagram = 0
  two_loop_counterterm_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 2).counterterm = 0
  two_loop_renormalized_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 2).renormalized = 0
  three_loop_raw_zero :
    su7LoopRawCoordinate canonicalStructuralLoopCountertermSource 3 = 0
  three_loop_diagram_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 3).diagram = 0
  three_loop_counterterm_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 3).counterterm = 0
  three_loop_renormalized_zero :
    (loopCoordinateContributionFromSU7CountertermSource
      canonicalStructuralLoopCountertermSource 3).renormalized = 0
  rg_effective_slope :
    (threeLoopBetaCoefficientsFromExpansion
      (threeLoopRGExpansionFromSU7CountertermSource
        canonicalStructuralLoopCountertermSource)).effectiveSlope = 7
  rg_zero :
    rgMismatch
        (threeLoopRGStateFromBetaAndIncidence
          (threeLoopBetaCoefficientsFromExpansion
            (threeLoopRGExpansionFromSU7CountertermSource
              canonicalStructuralLoopCountertermSource))
          (betaCoeff (incidenceCarrierTraceInput .colorSU3))) = 0
  higgs_incidence_slots :
    canonicalStructuralGeneratedHiggsExtraSpectrum.incidenceSlotCount = 6
  higgs_generated_slots :
    canonicalStructuralGeneratedHiggsExtraSpectrum.generatedSpectrumSlotCount =
      6
  higgs_zero :
    higgsExtraMismatch canonicalStructuralGeneratedHiggsExtraSpectrum = 0
  four_source_normal_form :
    alphaStrongCoordinatewiseStructuralFourSourceVector
          canonicalStructuralCarrierSmoothPhysicsSourceData .su7Breaking =
        (89 : ℚ) / 10000 ∧
      alphaStrongCoordinatewiseStructuralFourSourceVector
          canonicalStructuralCarrierSmoothPhysicsSourceData .threshold = 0 ∧
        alphaStrongCoordinatewiseStructuralFourSourceVector
            canonicalStructuralCarrierSmoothPhysicsSourceData .threeLoopRG =
          0 ∧
          alphaStrongCoordinatewiseStructuralFourSourceVector
              canonicalStructuralCarrierSmoothPhysicsSourceData
                .higgsExtraRepresentation = 0
  inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (∑ s : AlphaStrongResidualSource,
          alphaStrongCoordinatewiseStructuralFourSourceVector
            canonicalStructuralCarrierSmoothPhysicsSourceData s) =
      -((89000 : ℚ) / 128511)

/-- THEOREM 21: bundled spectrum-resolved alpha_s producer certificate. -/
theorem alphaStrongSpectrumResolvedFourSourceProducerCertificate :
    AlphaStrongSpectrumResolvedFourSourceProducerCertificate where
  threshold_low_trace :=
    alphaStrongThreshold_lowEnergyColorTrace_eq_seven
  threshold_unified_trace :=
    alphaStrongThreshold_unifiedColorTrace_eq_seven
  threshold_zero :=
    alphaStrongThresholdContribution_generatedSpectrum_eq_zero
  two_loop_raw_zero :=
    alphaStrongTwoLoopRawCoordinate_eq_zero
  two_loop_diagram_zero :=
    alphaStrongTwoLoopDiagramCoordinate_eq_zero
  two_loop_counterterm_zero :=
    alphaStrongTwoLoopCountertermCoordinate_eq_zero
  two_loop_renormalized_zero :=
    alphaStrongTwoLoopRenormalizedCoordinate_eq_zero
  three_loop_raw_zero :=
    alphaStrongThreeLoopRawCoordinate_eq_zero
  three_loop_diagram_zero :=
    alphaStrongThreeLoopDiagramCoordinate_eq_zero
  three_loop_counterterm_zero :=
    alphaStrongThreeLoopCountertermCoordinate_eq_zero
  three_loop_renormalized_zero :=
    alphaStrongThreeLoopRenormalizedCoordinate_eq_zero
  rg_effective_slope :=
    alphaStrongGeneratedThreeLoopEffectiveSlope_eq_seven
  rg_zero :=
    alphaStrongGeneratedRGMismatch_eq_zero
  higgs_incidence_slots :=
    alphaStrongHiggsExtra_incidenceSlotCount_eq_six
  higgs_generated_slots :=
    alphaStrongHiggsExtra_generatedSlotCount_eq_six
  higgs_zero :=
    alphaStrongHiggsExtra_generatedSpectrumMismatch_eq_zero
  four_source_normal_form :=
    alphaStrongSpectrumResolvedFourSourceVector_normalForm
  inverse_residual :=
    alphaStrongSpectrumResolvedFourSourceProducer_outputs_residual

end StandardModelConstraint
end SaturationMonoid
