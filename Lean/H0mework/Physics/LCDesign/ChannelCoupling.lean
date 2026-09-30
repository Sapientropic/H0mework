import H0mework.Physics.LCDesign.Channels
import H0mework.Physics.LCDesign.ExecutedDuration

/-!
# Source-generated channelwise LC/transducer coupling

Two upstream mouths feed the same nonuniform diagonal compiler.  The first
accepts independent component gain and phase bounds at every channel.  The
second directly applies the existing estimated-frequency/executed-duration
certificate at every channel.  Both generate the existing additive-disturbance
coupling crown without a uniform-design adapter.
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

open _root_.SaturationMonoid.AffineRelaxation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open Physical.Interface
open scoped Matrix.Norms.L2Operator

noncomputable section

structure ChannelwiseLCTransducerDisturbanceCrownAt
    (design : ChannelwiseFiniteLCTransducerNetworkDesign)
    (duration : ℝ) (disturbance : EndpointDisturbance) : Prop where
  calibration : ChannelwiseLCTransducerRunCalibrationAt design duration
  disturbanceBound : ∀ state, ‖disturbance state‖ < (1 : ℝ) / 8
  durationPositive : 0 < duration
  linearTolerance :
    ‖compiledChannelwiseLCTransducerOperator design duration -
        idealQuarterOperator‖ < (1 : ℝ) / 80
  generatedCouplingCrown :
    let tolerant : AdditiveDisturbanceToleranceAt
        (compiledChannelwiseLCTransducerOperator design duration)
        disturbance := {
      linearPartTolerance := linearTolerance
      disturbanceBound := disturbanceBound
    }
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      (additiveDisturbanceCertifiedTruthChildCouplingLaw
        (compiledChannelwiseLCTransducerOperator design duration)
        disturbance tolerant)

theorem everyChannelwiseCalibratedRunWithBoundedDisturbance_generatesCrown
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {duration : ℝ}
    (calibration : ChannelwiseLCTransducerRunCalibrationAt design duration)
    (disturbance : EndpointDisturbance)
    (disturbanceBound : ∀ state, ‖disturbance state‖ < (1 : ℝ) / 8) :
    ChannelwiseLCTransducerDisturbanceCrownAt design duration disturbance := by
  let tolerant : AdditiveDisturbanceToleranceAt
      (compiledChannelwiseLCTransducerOperator design duration)
      disturbance := {
    linearPartTolerance := channelwiseRun_linearTolerance calibration
    disturbanceBound := disturbanceBound
  }
  exact {
    calibration := calibration
    disturbanceBound := disturbanceBound
    durationPositive := channelwiseRun_duration_pos calibration
    linearTolerance := channelwiseRun_linearTolerance calibration
    generatedCouplingCrown :=
      everyAdditiveDisturbanceWithinTolerance_generatesCouplingCrown _ _ tolerant
  }

/-! ## Per-channel consumption of the estimated-frequency executed-run law -/

/-- Each channel owns its component branch and frequency estimate; all channels
share the same independently executed duration. -/
structure ChannelwiseEstimatedExecutedRunCalibrationAt
    (design : ChannelwiseFiniteLCTransducerNetworkDesign)
    (estimatedOmega : FiniteEmbodimentChannel → ℝ)
    (actualDuration : ℝ) : Prop where
  runAt : ∀ channel,
    EstimatedFrequencyExecutedRunCalibrationAt
      (channelDesign design channel) (estimatedOmega channel) actualDuration

theorem channelwiseExecutedRun_coefficient_sub_reference_lt
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {estimatedOmega : FiniteEmbodimentChannel → ℝ}
    {actualDuration : ℝ}
    (calibration : ChannelwiseEstimatedExecutedRunCalibrationAt
      design estimatedOmega actualDuration)
    (channel : FiniteEmbodimentChannel) :
    ‖channelwiseTransducerCoefficient design actualDuration channel -
        channelwiseTransducerCoefficient referenceChannelwiseDesign
          (Real.pi / 2) channel‖ < (1 : ℝ) / 400 := by
  let run := calibration.runAt channel
  have gain := run.frequencyCalibration.referenceGain
  have branchGain : (design.branchAt channel).transferGain =
      (99 : ℝ) / 100 := by
    simpa [channelDesign] using gain
  have phaseError := executedRun_accumulatedPhaseError run
  have bound := transducerCoefficient_sub_norm_le
    (design.branchAt channel).transferGain ((99 : ℝ) / 100)
    (normalizedLCAngularFrequency (channelDesign design channel))
    actualDuration 1 (Real.pi / 2)
  rw [branchGain] at bound
  norm_num at bound
  calc
    _ ≤ (99 : ℝ) / 100 *
        |normalizedLCAngularFrequency (channelDesign design channel) *
            actualDuration - Real.pi / 2| := by
      simpa [channelwiseTransducerCoefficient, referenceChannelwiseDesign,
        channelDesign, ninetyNinePercentUnitLCTransducerDesign,
        normalizedLCAngularFrequency, branchGain] using bound
    _ < (99 : ℝ) / 100 * ((1 : ℝ) / 400) :=
      mul_lt_mul_of_pos_left phaseError (by norm_num)
    _ < (1 : ℝ) / 400 := by norm_num

theorem channelwiseEstimatedExecutedRun_operatorDistanceToReference_lt
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {estimatedOmega : FiniteEmbodimentChannel → ℝ}
    {actualDuration : ℝ}
    (calibration : ChannelwiseEstimatedExecutedRunCalibrationAt
      design estimatedOmega actualDuration) :
    ‖compiledChannelwiseLCTransducerOperator design actualDuration -
        compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2)‖ < (1 : ℝ) / 400 := by
  rw [norm_compiledChannelwise_sub_reference_eq]
  exact (pi_norm_lt_iff (by norm_num)).2
    (channelwiseExecutedRun_coefficient_sub_reference_lt calibration)

theorem channelwiseEstimatedExecutedRun_linearTolerance
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {estimatedOmega : FiniteEmbodimentChannel → ℝ}
    {actualDuration : ℝ}
    (calibration : ChannelwiseEstimatedExecutedRunCalibrationAt
      design estimatedOmega actualDuration) :
    ‖compiledChannelwiseLCTransducerOperator design actualDuration -
        idealQuarterOperator‖ < (1 : ℝ) / 80 := by
  have toReference :=
    channelwiseEstimatedExecutedRun_operatorDistanceToReference_lt calibration
  have referenceToIdeal :
      ‖compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2) - idealQuarterOperator‖ ≤ (1 : ℝ) / 100 := by
    rw [compiledChannelwise_reference_eq_centre]
    exact ninetyNinePercentCenter_error_le_oneHundredth
  calc
    ‖compiledChannelwiseLCTransducerOperator design actualDuration -
        idealQuarterOperator‖ =
      ‖(compiledChannelwiseLCTransducerOperator design actualDuration -
          compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
            (Real.pi / 2)) +
        (compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
            (Real.pi / 2) - idealQuarterOperator)‖ := by congr 1; abel
    _ ≤ ‖compiledChannelwiseLCTransducerOperator design actualDuration -
          compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
            (Real.pi / 2)‖ +
        ‖compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
            (Real.pi / 2) - idealQuarterOperator‖ := norm_add_le _ _
    _ < (1 : ℝ) / 400 + (1 : ℝ) / 100 :=
      add_lt_add_of_lt_of_le toReference referenceToIdeal
    _ = (1 : ℝ) / 80 := by norm_num

theorem channelwiseEstimatedExecutedRun_duration_pos
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {estimatedOmega : FiniteEmbodimentChannel → ℝ}
    {actualDuration : ℝ}
    (calibration : ChannelwiseEstimatedExecutedRunCalibrationAt
      design estimatedOmega actualDuration) :
    0 < actualDuration :=
  executedRun_duration_pos (calibration.runAt .sourceBound)

structure ChannelwiseEstimatedExecutedRunDisturbanceCrownAt
    (design : ChannelwiseFiniteLCTransducerNetworkDesign)
    (estimatedOmega : FiniteEmbodimentChannel → ℝ)
    (actualDuration : ℝ) (disturbance : EndpointDisturbance) : Prop where
  calibration : ChannelwiseEstimatedExecutedRunCalibrationAt
    design estimatedOmega actualDuration
  disturbanceBound : ∀ state, ‖disturbance state‖ < (1 : ℝ) / 8
  durationPositive : 0 < actualDuration
  linearTolerance :
    ‖compiledChannelwiseLCTransducerOperator design actualDuration -
        idealQuarterOperator‖ < (1 : ℝ) / 80
  generatedCouplingCrown :
    let tolerant : AdditiveDisturbanceToleranceAt
        (compiledChannelwiseLCTransducerOperator design actualDuration)
        disturbance := {
      linearPartTolerance := linearTolerance
      disturbanceBound := disturbanceBound
    }
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      (additiveDisturbanceCertifiedTruthChildCouplingLaw
        (compiledChannelwiseLCTransducerOperator design actualDuration)
        disturbance tolerant)

theorem channelwiseEstimatedExecutedRunWithBoundedDisturbance_generatesCrown
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {estimatedOmega : FiniteEmbodimentChannel → ℝ}
    {actualDuration : ℝ}
    (calibration : ChannelwiseEstimatedExecutedRunCalibrationAt
      design estimatedOmega actualDuration)
    (disturbance : EndpointDisturbance)
    (disturbanceBound : ∀ state, ‖disturbance state‖ < (1 : ℝ) / 8) :
    ChannelwiseEstimatedExecutedRunDisturbanceCrownAt
      design estimatedOmega actualDuration disturbance := by
  let tolerant : AdditiveDisturbanceToleranceAt
      (compiledChannelwiseLCTransducerOperator design actualDuration)
      disturbance := {
    linearPartTolerance :=
      channelwiseEstimatedExecutedRun_linearTolerance calibration
    disturbanceBound := disturbanceBound
  }
  exact {
    calibration := calibration
    disturbanceBound := disturbanceBound
    durationPositive :=
      channelwiseEstimatedExecutedRun_duration_pos calibration
    linearTolerance :=
      channelwiseEstimatedExecutedRun_linearTolerance calibration
    generatedCouplingCrown :=
      everyAdditiveDisturbanceWithinTolerance_generatesCouplingCrown _ _ tolerant
  }

/-! ## A genuinely nonuniform accepted implementation -/

def genuinelyNonuniformChannelwiseDesign :
    ChannelwiseFiniteLCTransducerNetworkDesign where
  branchAt
    | .sourceBound => ⟨4, (1 : ℝ) / 4, (1979 : ℝ) / 2000⟩
    | _ => ⟨1, 1, (99 : ℝ) / 100⟩

theorem genuinelyNonuniformChannelwiseDesign_admissible
    (channel : FiniteEmbodimentChannel) :
    LCTransducerComponentAdmissibleAt
      (channelDesign genuinelyNonuniformChannelwiseDesign channel) := by
  cases channel <;>
    constructor <;>
    norm_num [channelDesign, genuinelyNonuniformChannelwiseDesign]

theorem genuinelyNonuniformChannelwiseDesign_calibrated :
    ChannelwiseLCTransducerRunCalibrationAt
      genuinelyNonuniformChannelwiseDesign (Real.pi / 2) where
  componentAdmissible := genuinelyNonuniformChannelwiseDesign_admissible
  transferGainError := by
    intro channel
    cases channel <;>
      norm_num [genuinelyNonuniformChannelwiseDesign]
  accumulatedPhaseError := by
    intro channel
    cases channel <;>
      norm_num [channelDesign, genuinelyNonuniformChannelwiseDesign,
        normalizedLCAngularFrequency]

theorem genuinelyNonuniformChannelwiseDesign_hasDistinctBranches :
    genuinelyNonuniformChannelwiseDesign.branchAt .sourceBound ≠
      genuinelyNonuniformChannelwiseDesign.branchAt .machineToNeuralWrite := by
  intro same
  have inductanceSame := congrArg LCTransducerBranchDesign.inductance same
  norm_num [genuinelyNonuniformChannelwiseDesign] at inductanceSame

theorem genuinelyNonuniformCompiledOperator_ne_reference :
    compiledChannelwiseLCTransducerOperator
        genuinelyNonuniformChannelwiseDesign (Real.pi / 2) ≠
      compiledChannelwiseLCTransducerOperator
        referenceChannelwiseDesign (Real.pi / 2) := by
  intro same
  have matrixSame :=
    (Matrix.toEuclideanCLM
      (n := FiniteEmbodimentChannel) (𝕜 := ℂ)).injective same
  have entrySame := congrArg
    (fun matrix : Matrix FiniteEmbodimentChannel FiniteEmbodimentChannel ℂ =>
      matrix .sourceBound .sourceBound) matrixSame
  simp only [Matrix.diagonal_apply_eq] at entrySame
  simp only [channelwiseTransducerCoefficient,
    genuinelyNonuniformChannelwiseDesign, referenceChannelwiseDesign,
    channelDesign, ninetyNinePercentUnitLCTransducerDesign,
    normalizedLCAngularFrequency] at entrySame
  norm_num at entrySame
  have phaseNe : schrodingerScalarPhase 1 (Real.pi / 2) ≠ 0 := by
    intro phaseZero
    have phaseNorm := schrodingerScalarPhase_norm 1 (Real.pi / 2)
    rw [phaseZero, norm_zero] at phaseNorm
    norm_num at phaseNorm
  exact phaseNe entrySame

structure GenuinelyNonuniformChannelwiseVisibleBiasCrown : Prop where
  distinctBranches :
    genuinelyNonuniformChannelwiseDesign.branchAt .sourceBound ≠
      genuinelyNonuniformChannelwiseDesign.branchAt .machineToNeuralWrite
  componentSlotCount : Fintype.card FiniteLCTransducerComponentSlot = 30
  compiledOperatorNonuniform :
    compiledChannelwiseLCTransducerOperator
        genuinelyNonuniformChannelwiseDesign (Real.pi / 2) ≠
      compiledChannelwiseLCTransducerOperator
        referenceChannelwiseDesign (Real.pi / 2)
  disturbanceNonzero : smallNonzeroConstantBias ≠ 0
  visibleFalseSourceTarget :
    targetPort
        (disturbedImplementedState
          (compiledChannelwiseLCTransducerOperator
            genuinelyNonuniformChannelwiseDesign (Real.pi / 2))
          smallNonzeroConstantBias (preparedState false)) .sourceBound =
      (1 : ℝ) / 1000
  coupling : ChannelwiseLCTransducerDisturbanceCrownAt
    genuinelyNonuniformChannelwiseDesign (Real.pi / 2)
    smallNonzeroConstantBias

theorem genuinelyNonuniformChannelwiseVisibleBias_constructible :
    GenuinelyNonuniformChannelwiseVisibleBiasCrown where
  distinctBranches :=
    genuinelyNonuniformChannelwiseDesign_hasDistinctBranches
  componentSlotCount := finiteLCTransducerComponentSlot_cardinality
  compiledOperatorNonuniform :=
    genuinelyNonuniformCompiledOperator_ne_reference
  disturbanceNonzero := smallNonzeroConstantBias_ne_zero
  visibleFalseSourceTarget :=
    smallBias_falseSourceTarget_eq_oneThousandth_for _
  coupling :=
    everyChannelwiseCalibratedRunWithBoundedDisturbance_generatesCrown
      genuinelyNonuniformChannelwiseDesign_calibrated
      smallNonzeroConstantBias smallNonzeroConstantBias_bound

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyChannelwiseCalibratedRunWithBoundedDisturbance_generatesCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.channelwiseEstimatedExecutedRun_linearTolerance
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.channelwiseEstimatedExecutedRunWithBoundedDisturbance_generatesCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.genuinelyNonuniformCompiledOperator_ne_reference
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.genuinelyNonuniformChannelwiseVisibleBias_constructible
