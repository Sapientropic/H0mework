import H0mework.Physics.PortCoupling.AdditiveTolerance
import H0mework.Physics.PortCoupling.CertifiedTolerance

/-!
# Source-generated coupling under additive endpoint disturbance

An arbitrary bounded, input-dependent additive disturbance is retained in the
actual implementation readout.  Quantitative source facts generate ten
channel-indexed receipts and the existing coupling crown.  A premise-free
instance uses the non-ideal LC centre together with a visible nonzero target
bias; zero disturbance is not used to inhabit the result.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open Physical.Interface

noncomputable section

def disturbedThresholdObservationAt
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (occurrence : Bool) : BidirectionalEmbodimentObservation where
  sourceBound := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .sourceBound)
  machineToNeuralWrite := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .machineToNeuralWrite)
  neuralToMachineReceipt := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .neuralToMachineReceipt)
  neuralToBodyEffect := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .neuralToBodyEffect)
  bodyToNeuralFeedback := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .bodyToNeuralFeedback)
  learnedTraceReopened := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .learnedStateTrace)
  recursiveSelfWriteBack := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .recursiveSelfWriteBack)
  generatedNext := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .generatedNext)
  authorityAndRefusalSettled := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .authorityAndRefusalSettlement)
  noPowerMintingGuard := decide ((1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) .noPowerMinting)

@[simp] theorem disturbedThresholdDecision_true
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance)
    (channel : FiniteEmbodimentChannel) :
    decide ((1 : ℝ) / 2 < targetPort
      (disturbedImplementedState linearPart disturbance (preparedState true))
      channel) = true := by
  rw [decide_eq_true_eq]
  exact activeDisturbedImplementation_allTargetsAboveHalf
    linearPart disturbance tolerant channel

@[simp] theorem disturbedThresholdDecision_false
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance)
    (channel : FiniteEmbodimentChannel) :
    decide ((1 : ℝ) / 2 < targetPort
      (disturbedImplementedState linearPart disturbance (preparedState false))
      channel) = false := by
  rw [decide_eq_false_iff_not]
  exact not_lt_of_ge
    (le_of_lt (falseDisturbedImplementation_allTargetsBelowHalf
      linearPart disturbance tolerant channel))

theorem disturbedThresholdObservationAt_injective
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance) :
    Function.Injective
      (disturbedThresholdObservationAt linearPart disturbance) := by
  intro left right sameObservation
  cases left <;> cases right
  · rfl
  · have sourceRead := congrArg
      BidirectionalEmbodimentObservation.sourceBound sameObservation
    have sourceFalse :
        (disturbedThresholdObservationAt linearPart disturbance false).sourceBound =
          false := disturbedThresholdDecision_false
            linearPart disturbance tolerant .sourceBound
    have sourceTrue :
        (disturbedThresholdObservationAt linearPart disturbance true).sourceBound =
          true := disturbedThresholdDecision_true
            linearPart disturbance tolerant .sourceBound
    exact sourceFalse.symm.trans (sourceRead.trans sourceTrue)
  · have sourceRead := congrArg
      BidirectionalEmbodimentObservation.sourceBound sameObservation
    have sourceTrue :
        (disturbedThresholdObservationAt linearPart disturbance true).sourceBound =
          true := disturbedThresholdDecision_true
            linearPart disturbance tolerant .sourceBound
    have sourceFalse :
        (disturbedThresholdObservationAt linearPart disturbance false).sourceBound =
          false := disturbedThresholdDecision_false
            linearPart disturbance tolerant .sourceBound
    exact sourceTrue.symm.trans (sourceRead.trans sourceFalse)
  · rfl

/-- A disturbance receipt contains source-side quantitative facts only. -/
structure AdditiveDisturbancePortReceiptAt
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (channel : FiniteEmbodimentChannel)
    (source occurrence : Bool) : Type where
  source_eq : source = false
  occurrence_eq : occurrence = true
  tolerance : AdditiveDisturbanceToleranceAt linearPart disturbance
  activeTargetAboveHalf : (1 : ℝ) / 2 < targetPort
    (disturbedImplementedState linearPart disturbance
      (preparedState occurrence)) channel
  interventionSensitive :
    targetPort
        (disturbedImplementedState linearPart disturbance
          (intervention channel 0)) channel ≠
      targetPort
        (disturbedImplementedState linearPart disturbance
          (intervention channel 1)) channel
  otherTargetsBelowHalf : ∀ other, other ≠ channel →
    targetPort
        (disturbedImplementedState linearPart disturbance
          (intervention channel 1)) other < (1 : ℝ) / 2

def additiveDisturbanceSeedReceipt
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance)
    (channel : FiniteEmbodimentChannel) :
    AdditiveDisturbancePortReceiptAt linearPart disturbance channel false true where
  source_eq := rfl
  occurrence_eq := rfl
  tolerance := tolerant
  activeTargetAboveHalf :=
    activeDisturbedImplementation_allTargetsAboveHalf
      linearPart disturbance tolerant channel
  interventionSensitive :=
    interventionDisturbedImplementation_sensitiveZeroToOne
      linearPart disturbance tolerant channel
  otherTargetsBelowHalf := fun other different =>
    interventionDisturbedImplementation_otherTargetBelowHalf
      linearPart disturbance tolerant
      (sourceChannel := channel) (targetChannel := other) different

theorem AdditiveDisturbancePortReceiptAt.readout_true
    {linearPart disturbance channel source occurrence}
    (receipt : AdditiveDisturbancePortReceiptAt linearPart disturbance channel
      source occurrence) :
    decide ((1 : ℝ) / 2 < targetPort
      (disturbedImplementedState linearPart disturbance
        (preparedState occurrence)) channel) = true := by
  rw [decide_eq_true_eq]
  exact receipt.activeTargetAboveHalf

noncomputable def additiveDisturbanceCertifiedTruthChildCouplingLaw
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance) :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw where
  Source := Bool
  sourceSeed := false
  truthChildSourceView := truthChildSourcePresentation
  truthChildSourceViewExact := rfl
  CouplingOccurrence := Bool
  compile := Bool.not
  observationAt := disturbedThresholdObservationAt linearPart disturbance
  observationAt_injective :=
    disturbedThresholdObservationAt_injective linearPart disturbance tolerant
  RootedCouplingSourceAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance .sourceBound
      source occurrence
  MachineToNeuralWriteAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance .machineToNeuralWrite
      source occurrence
  NeuralToMachineReceiptAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance
      .neuralToMachineReceipt source occurrence
  NeuralToBodyEffectAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance .neuralToBodyEffect
      source occurrence
  BodyToNeuralFeedbackAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance .bodyToNeuralFeedback
      source occurrence
  LearnedStateTraceAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance .learnedStateTrace
      source occurrence
  RecursiveSelfWriteBackAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance
      .recursiveSelfWriteBack source occurrence
  GeneratedNextAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance .generatedNext
      source occurrence
  AuthorityAndRefusalSettlementAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance
      .authorityAndRefusalSettlement source occurrence
  NoPowerMintingAt := fun source occurrence =>
    AdditiveDisturbancePortReceiptAt linearPart disturbance .noPowerMinting
      source occurrence
  rootedCouplingSource :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant .sourceBound
  machineToNeuralWrite :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant
      .machineToNeuralWrite
  neuralToMachineReceipt :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant
      .neuralToMachineReceipt
  neuralToBodyEffect :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant
      .neuralToBodyEffect
  bodyToNeuralFeedback :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant
      .bodyToNeuralFeedback
  learnedStateTrace :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant
      .learnedStateTrace
  recursiveSelfWriteBack :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant
      .recursiveSelfWriteBack
  generatedNext :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant .generatedNext
  authorityAndRefusalSettlement :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant
      .authorityAndRefusalSettlement
  noPowerMinting :=
    additiveDisturbanceSeedReceipt linearPart disturbance tolerant .noPowerMinting
  rootedCouplingSource_read_exact := fun receipt => receipt.readout_true
  machineToNeuralWrite_read_exact := fun receipt => receipt.readout_true
  neuralToMachineReceipt_read_exact := fun receipt => receipt.readout_true
  neuralToBodyEffect_read_exact := fun receipt => receipt.readout_true
  bodyToNeuralFeedback_read_exact := fun receipt => receipt.readout_true
  learnedStateTrace_read_exact := fun receipt => receipt.readout_true
  recursiveSelfWriteBack_read_exact := fun receipt => receipt.readout_true
  generatedNext_read_exact := fun receipt => receipt.readout_true
  authorityAndRefusalSettlement_read_exact := fun receipt => receipt.readout_true
  noPowerMinting_read_exact := fun receipt => receipt.readout_true
  occurrenceSourceAt := Bool.not
  occurrenceSource_compiles := by intro source; cases source <;> rfl
  PersonalLineage := Bool
  lineageOf := id

theorem everyAdditiveDisturbanceWithinTolerance_generatesCouplingCrown
    (linearPart : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState)
    (disturbance : EndpointDisturbance)
    (tolerant : AdditiveDisturbanceToleranceAt linearPart disturbance) :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      (additiveDisturbanceCertifiedTruthChildCouplingLaw
        linearPart disturbance tolerant) :=
  (additiveDisturbanceCertifiedTruthChildCouplingLaw
    linearPart disturbance tolerant).sourceGeneratedTruthChildNeuralBodyCouplingCrown

theorem norm_encodeHilbert_evolvedIntervention_one :
    ‖encodeHilbert (evolve (intervention .sourceBound 1))‖ = 1 := by
  have square :
      ‖encodeHilbert (evolve (intervention .sourceBound 1))‖ ^ 2 = 1 := by
    rw [← energy_eq_encodeHilbert_norm_sq,
      evolve_energy_conserved, energy_intervention_one]
  nlinarith [norm_nonneg
    (encodeHilbert (evolve (intervention .sourceBound 1)))]

/-- A visible target-coordinate bias, constant only for the premise-free
example.  The uniform theorem permits arbitrary input dependence. -/
def smallNonzeroConstantBias : EndpointDisturbance :=
  fun _state => ((1 : ℂ) / 1000) •
    encodeHilbert (evolve (intervention .sourceBound 1))

theorem smallNonzeroConstantBias_bound (state : FiniteEmbodimentState) :
    ‖smallNonzeroConstantBias state‖ < (1 : ℝ) / 8 := by
  rw [smallNonzeroConstantBias, norm_smul,
    norm_encodeHilbert_evolvedIntervention_one]
  norm_num

theorem smallNonzeroConstantBias_ne_zero :
    smallNonzeroConstantBias ≠ 0 := by
  intro zeroBias
  have atZero := congrFun zeroBias (preparedState false)
  have coordinateZero := congrArg
    (fun state : HilbertEmbodimentState => (state .sourceBound).re) atZero
  norm_num [smallNonzeroConstantBias, encodeHilbert, encodeComplex, encodePort,
    evolve, intervention] at coordinateZero

theorem smallBias_falseSourceTarget_eq_oneThousandth :
    targetPort
        (disturbedImplementedState
          (compiledLCTransducerQuarterOperator
            ninetyNinePercentUnitLCTransducerDesign)
          smallNonzeroConstantBias (preparedState false)) .sourceBound =
      (1 : ℝ) / 1000 := by
  have inputZero : encodeHilbert (preparedState false) = 0 := by
    ext channel
    simp [encodeHilbert, encodeComplex, encodePort, preparedState]
  unfold disturbedImplementedState targetPort decodeHilbert decodeComplex
  rw [inputZero, map_zero, zero_add]
  simp [smallNonzeroConstantBias, encodeHilbert, encodeComplex, encodePort,
    evolve, intervention]

theorem nonidealCentreWithBias_tolerant :
    AdditiveDisturbanceToleranceAt
      (compiledLCTransducerQuarterOperator
        ninetyNinePercentUnitLCTransducerDesign)
      smallNonzeroConstantBias where
  linearPartTolerance :=
    lt_of_le_of_lt ninetyNinePercentCenter_error_le_oneHundredth (by norm_num)
  disturbanceBound := smallNonzeroConstantBias_bound

/-- Premise-free nonzero-disturbance synthesis. -/
theorem finiteNonzeroDisturbanceCoupling_constructible :
    smallNonzeroConstantBias ≠ 0 ∧
      targetPort
          (disturbedImplementedState
            (compiledLCTransducerQuarterOperator
              ninetyNinePercentUnitLCTransducerDesign)
            smallNonzeroConstantBias (preparedState false)) .sourceBound =
        (1 : ℝ) / 1000 ∧
      AdditiveDisturbanceToleranceAt
        (compiledLCTransducerQuarterOperator
          ninetyNinePercentUnitLCTransducerDesign)
        smallNonzeroConstantBias ∧
      SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
        (additiveDisturbanceCertifiedTruthChildCouplingLaw
          (compiledLCTransducerQuarterOperator
            ninetyNinePercentUnitLCTransducerDesign)
          smallNonzeroConstantBias nonidealCentreWithBias_tolerant) :=
  ⟨smallNonzeroConstantBias_ne_zero,
    smallBias_falseSourceTarget_eq_oneThousandth,
    nonidealCentreWithBias_tolerant,
    everyAdditiveDisturbanceWithinTolerance_generatesCouplingCrown _ _ _⟩

end

end Producer
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.disturbedThresholdObservationAt_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyAdditiveDisturbanceWithinTolerance_generatesCouplingCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteNonzeroDisturbanceCoupling_constructible
