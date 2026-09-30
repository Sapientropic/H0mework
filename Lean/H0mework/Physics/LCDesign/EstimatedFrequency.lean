import H0mework.Physics.LCDesign.FrequencyDisturbance

/-!
# Estimated-frequency scheduling with additive disturbance

The controller no longer receives the exact component frequency.  A positive
frequency estimate with relative error below `1/1000` generates its own
quarter-period schedule.  The resulting accumulated-phase error is below
`1/400`; together with reference gain this places the linear endpoint below
the `1/80` gate required by the arbitrary additive-disturbance theorem.

`estimated` is deliberately not called `measured`: empirical measurement and
its provenance remain a separate source incidence.
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

def estimatedQuarterDuration (estimatedOmega : ℝ) : ℝ :=
  (Real.pi / 2) / estimatedOmega

/-- Upstream calibration coordinates only. -/
structure EstimatedFrequencyCalibrationAt
    (design : UniformFiniteLCTransducerNetworkDesign)
    (estimatedOmega : ℝ) : Prop where
  componentAdmissible : LCTransducerComponentAdmissibleAt design
  referenceGain : design.branch.transferGain = (99 : ℝ) / 100
  estimatedFrequencyPositive : 0 < estimatedOmega
  relativeFrequencyError :
    |normalizedLCAngularFrequency design / estimatedOmega - 1| <
      (1 : ℝ) / 1000

theorem estimatedQuarterDuration_pos
    {design : UniformFiniteLCTransducerNetworkDesign}
    {estimatedOmega : ℝ}
    (calibration : EstimatedFrequencyCalibrationAt design estimatedOmega) :
    0 < estimatedQuarterDuration estimatedOmega := by
  exact div_pos (half_pos Real.pi_pos) calibration.estimatedFrequencyPositive

theorem estimatedFrequency_accumulatedPhaseError
    {design : UniformFiniteLCTransducerNetworkDesign}
    {estimatedOmega : ℝ}
    (calibration : EstimatedFrequencyCalibrationAt design estimatedOmega) :
    |normalizedLCAngularFrequency design *
        estimatedQuarterDuration estimatedOmega - Real.pi / 2| <
      (1 : ℝ) / 400 := by
  have estimatedNe : estimatedOmega ≠ 0 :=
    ne_of_gt calibration.estimatedFrequencyPositive
  have phaseFactor :
      normalizedLCAngularFrequency design *
          estimatedQuarterDuration estimatedOmega - Real.pi / 2 =
        (Real.pi / 2) *
          (normalizedLCAngularFrequency design / estimatedOmega - 1) := by
    unfold estimatedQuarterDuration
    field_simp [estimatedNe]
  rw [phaseFactor, abs_mul]
  have piHalfPositive : 0 < Real.pi / 2 := half_pos Real.pi_pos
  rw [abs_of_pos piHalfPositive]
  calc
    Real.pi / 2 *
        |normalizedLCAngularFrequency design / estimatedOmega - 1| <
      Real.pi / 2 * ((1 : ℝ) / 1000) :=
        mul_lt_mul_of_pos_left calibration.relativeFrequencyError
          piHalfPositive
    _ < (1 : ℝ) / 400 := by
      nlinarith [Real.pi_lt_four]

theorem estimatedFrequency_generatesRunTolerance
    {design : UniformFiniteLCTransducerNetworkDesign}
    {estimatedOmega : ℝ}
    (calibration : EstimatedFrequencyCalibrationAt design estimatedOmega) :
    CalibratedLCTransducerRunToleranceAt design
      (estimatedQuarterDuration estimatedOmega) where
  componentAdmissible := calibration.componentAdmissible
  transferGainError := by rw [calibration.referenceGain]; norm_num
  accumulatedPhaseError :=
    estimatedFrequency_accumulatedPhaseError calibration

theorem estimatedFrequencyReferenceGain_linearTolerance
    {design : UniformFiniteLCTransducerNetworkDesign}
    {estimatedOmega : ℝ}
    (calibration : EstimatedFrequencyCalibrationAt design estimatedOmega) :
    ‖compiledLCTransducerOperator design
          (estimatedQuarterDuration estimatedOmega) - idealQuarterOperator‖ <
      (1 : ℝ) / 80 := by
  have distanceToCentre := norm_compiledLCTransducerOperator_sub_le
    design ninetyNinePercentUnitLCTransducerDesign
    (estimatedQuarterDuration estimatedOmega) (Real.pi / 2)
  have referenceDesignGain :
      ninetyNinePercentUnitLCTransducerDesign.branch.transferGain =
        (99 : ℝ) / 100 := rfl
  rw [calibration.referenceGain, referenceDesignGain,
    ninetyNinePercentUnitLC_frequency_eq_one] at distanceToCentre
  norm_num at distanceToCentre
  have phaseError := estimatedFrequency_accumulatedPhaseError calibration
  have centreDistanceLt :
      ‖compiledLCTransducerOperator design
          (estimatedQuarterDuration estimatedOmega) -
        compiledLCTransducerQuarterOperator
          ninetyNinePercentUnitLCTransducerDesign‖ <
        (99 : ℝ) / 100 * ((1 : ℝ) / 400) := by
    unfold compiledLCTransducerQuarterOperator
    calc
      _ ≤ (99 : ℝ) / 100 *
          |normalizedLCAngularFrequency design *
            estimatedQuarterDuration estimatedOmega - Real.pi / 2| := by
        simpa using distanceToCentre
      _ < (99 : ℝ) / 100 * ((1 : ℝ) / 400) :=
        mul_lt_mul_of_pos_left phaseError (by norm_num)
  calc
    ‖compiledLCTransducerOperator design
          (estimatedQuarterDuration estimatedOmega) - idealQuarterOperator‖ =
      ‖(compiledLCTransducerOperator design
            (estimatedQuarterDuration estimatedOmega) -
          compiledLCTransducerQuarterOperator
            ninetyNinePercentUnitLCTransducerDesign) +
        (compiledLCTransducerQuarterOperator
            ninetyNinePercentUnitLCTransducerDesign -
          idealQuarterOperator)‖ := by congr 1; abel
    _ ≤ ‖compiledLCTransducerOperator design
            (estimatedQuarterDuration estimatedOmega) -
          compiledLCTransducerQuarterOperator
            ninetyNinePercentUnitLCTransducerDesign‖ +
        ‖compiledLCTransducerQuarterOperator
            ninetyNinePercentUnitLCTransducerDesign -
          idealQuarterOperator‖ := norm_add_le _ _
    _ < (99 : ℝ) / 100 * ((1 : ℝ) / 400) + (1 : ℝ) / 100 :=
      add_lt_add_of_lt_of_le centreDistanceLt
        ninetyNinePercentCenter_error_le_oneHundredth
    _ < (1 : ℝ) / 80 := by norm_num

structure EstimatedFrequencyAdditiveDisturbanceCrownAt
    (design : UniformFiniteLCTransducerNetworkDesign)
    (estimatedOmega : ℝ) (disturbance : EndpointDisturbance) : Prop where
  calibration : EstimatedFrequencyCalibrationAt design estimatedOmega
  disturbanceBound : ∀ state, ‖disturbance state‖ < (1 : ℝ) / 8
  durationPositive : 0 < estimatedQuarterDuration estimatedOmega
  accumulatedPhaseError :
    |normalizedLCAngularFrequency design *
        estimatedQuarterDuration estimatedOmega - Real.pi / 2| <
      (1 : ℝ) / 400
  generatedCouplingCrown :
    let tolerant : AdditiveDisturbanceToleranceAt
        (compiledLCTransducerOperator design
          (estimatedQuarterDuration estimatedOmega)) disturbance := {
      linearPartTolerance :=
        estimatedFrequencyReferenceGain_linearTolerance calibration
      disturbanceBound := disturbanceBound
    }
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      (additiveDisturbanceCertifiedTruthChildCouplingLaw
        (compiledLCTransducerOperator design
          (estimatedQuarterDuration estimatedOmega)) disturbance tolerant)

theorem estimatedFrequencyWithBoundedDisturbance_generatesCouplingCrown
    {design : UniformFiniteLCTransducerNetworkDesign}
    {estimatedOmega : ℝ}
    (calibration : EstimatedFrequencyCalibrationAt design estimatedOmega)
    (disturbance : EndpointDisturbance)
    (disturbanceBound : ∀ state, ‖disturbance state‖ < (1 : ℝ) / 8) :
    EstimatedFrequencyAdditiveDisturbanceCrownAt
      design estimatedOmega disturbance := by
  let tolerant : AdditiveDisturbanceToleranceAt
      (compiledLCTransducerOperator design
        (estimatedQuarterDuration estimatedOmega)) disturbance := {
    linearPartTolerance :=
      estimatedFrequencyReferenceGain_linearTolerance calibration
    disturbanceBound := disturbanceBound
  }
  exact {
    calibration := calibration
    disturbanceBound := disturbanceBound
    durationPositive := estimatedQuarterDuration_pos calibration
    accumulatedPhaseError :=
      estimatedFrequency_accumulatedPhaseError calibration
    generatedCouplingCrown :=
      everyAdditiveDisturbanceWithinTolerance_generatesCouplingCrown _ _ tolerant
  }

def fourUnitReferenceGainDesign : UniformFiniteLCTransducerNetworkDesign :=
  lcDesignOfParameters 4 4 ((99 : ℝ) / 100)

def perturbedFrequencyEstimate : ℝ := (1001 : ℝ) / 4000

theorem fourUnitReferenceGain_actualFrequency_eq_quarter :
    normalizedLCAngularFrequency fourUnitReferenceGainDesign =
      (1 : ℝ) / 4 := by
  norm_num [fourUnitReferenceGainDesign, lcDesignOfParameters,
    normalizedLCAngularFrequency]

theorem perturbedFrequencyEstimate_ne_actual :
    perturbedFrequencyEstimate ≠
      normalizedLCAngularFrequency fourUnitReferenceGainDesign := by
  rw [fourUnitReferenceGain_actualFrequency_eq_quarter]
  norm_num [perturbedFrequencyEstimate]

theorem fourUnitPerturbedFrequencyCalibration :
    EstimatedFrequencyCalibrationAt
      fourUnitReferenceGainDesign perturbedFrequencyEstimate where
  componentAdmissible := {
    inductancePositive := by
      norm_num [fourUnitReferenceGainDesign, lcDesignOfParameters]
    capacitancePositive := by
      norm_num [fourUnitReferenceGainDesign, lcDesignOfParameters]
    transferGainPositive := by
      norm_num [fourUnitReferenceGainDesign, lcDesignOfParameters]
    transferGainPassive := by
      norm_num [fourUnitReferenceGainDesign, lcDesignOfParameters]
  }
  referenceGain := rfl
  estimatedFrequencyPositive := by norm_num [perturbedFrequencyEstimate]
  relativeFrequencyError := by
    rw [fourUnitReferenceGain_actualFrequency_eq_quarter]
    norm_num [perturbedFrequencyEstimate, abs_of_nonpos]

theorem perturbedEstimate_duration_eq :
    estimatedQuarterDuration perturbedFrequencyEstimate =
      (2000 : ℝ) * Real.pi / 1001 := by
  unfold estimatedQuarterDuration perturbedFrequencyEstimate
  ring

theorem perturbedEstimate_signedPhaseResidual_eq :
    normalizedLCAngularFrequency fourUnitReferenceGainDesign *
        estimatedQuarterDuration perturbedFrequencyEstimate - Real.pi / 2 =
      -Real.pi / 2002 := by
  rw [fourUnitReferenceGain_actualFrequency_eq_quarter,
    perturbedEstimate_duration_eq]
  ring

structure PerturbedFrequencyVisibleBiasCrown : Prop where
  estimateDiffersFromActual : perturbedFrequencyEstimate ≠
    normalizedLCAngularFrequency fourUnitReferenceGainDesign
  durationIdentity : estimatedQuarterDuration perturbedFrequencyEstimate =
    (2000 : ℝ) * Real.pi / 1001
  signedPhaseResidual :
    normalizedLCAngularFrequency fourUnitReferenceGainDesign *
        estimatedQuarterDuration perturbedFrequencyEstimate - Real.pi / 2 =
      -Real.pi / 2002
  visibleFalseSourceTarget :
    targetPort
        (disturbedImplementedState
          (compiledLCTransducerOperator fourUnitReferenceGainDesign
            (estimatedQuarterDuration perturbedFrequencyEstimate))
          smallNonzeroConstantBias (preparedState false)) .sourceBound =
      (1 : ℝ) / 1000
  coupling : EstimatedFrequencyAdditiveDisturbanceCrownAt
    fourUnitReferenceGainDesign perturbedFrequencyEstimate
    smallNonzeroConstantBias

theorem perturbedFrequencyEstimateWithVisibleBias_constructible :
    PerturbedFrequencyVisibleBiasCrown where
  estimateDiffersFromActual := perturbedFrequencyEstimate_ne_actual
  durationIdentity := perturbedEstimate_duration_eq
  signedPhaseResidual := perturbedEstimate_signedPhaseResidual_eq
  visibleFalseSourceTarget :=
    smallBias_falseSourceTarget_eq_oneThousandth_for _
  coupling := estimatedFrequencyWithBoundedDisturbance_generatesCouplingCrown
    fourUnitPerturbedFrequencyCalibration smallNonzeroConstantBias
    smallNonzeroConstantBias_bound

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.estimatedFrequency_accumulatedPhaseError
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.estimatedFrequencyReferenceGain_linearTolerance
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.estimatedFrequencyWithBoundedDisturbance_generatesCouplingCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.perturbedFrequencyEstimateWithVisibleBias_constructible
