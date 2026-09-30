import Mathlib.Analysis.CStarAlgebra.Matrix
import H0mework.Physics.LCDesign.FrequencyFamily

/-!
# Channelwise LC/transducer design kernel

The ten channels no longer share one definitionally identical branch.  Each
typed channel owns its own `L`, `C` and gain, and the compiler is the diagonal
operator of the ten generated complex transfer coefficients.

The matrix `L2` operator norm proves that the global error is exactly the
maximum channel error: there is no dimension, square-root or sum loss.  Thus
independent per-channel component and phase tolerances generate the existing
global operator tolerance.
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
open Physical.Interface
open scoped Matrix.Norms.L2Operator

noncomputable section

structure ChannelwiseFiniteLCTransducerNetworkDesign where
  branchAt : FiniteEmbodimentChannel → LCTransducerBranchDesign

def channelDesign (design : ChannelwiseFiniteLCTransducerNetworkDesign)
    (channel : FiniteEmbodimentChannel) : UniformFiniteLCTransducerNetworkDesign :=
  ⟨design.branchAt channel⟩

def channelwiseTransducerCoefficient
    (design : ChannelwiseFiniteLCTransducerNetworkDesign) (duration : ℝ)
    (channel : FiniteEmbodimentChannel) : ℂ :=
  (design.branchAt channel).transferGain *
    schrodingerScalarPhase
      (normalizedLCAngularFrequency (channelDesign design channel)) duration

def compiledChannelwiseLCTransducerOperator
    (design : ChannelwiseFiniteLCTransducerNetworkDesign) (duration : ℝ) :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  Matrix.toEuclideanCLM
    (n := FiniteEmbodimentChannel) (𝕜 := ℂ)
    (Matrix.diagonal (channelwiseTransducerCoefficient design duration))

theorem compiledChannelwiseLCTransducerOperator_apply
    (design : ChannelwiseFiniteLCTransducerNetworkDesign) (duration : ℝ)
    (state : HilbertEmbodimentState) (channel : FiniteEmbodimentChannel) :
    compiledChannelwiseLCTransducerOperator design duration state channel =
      channelwiseTransducerCoefficient design duration channel *
        state channel := by
  classical
  simp [compiledChannelwiseLCTransducerOperator, Matrix.mulVec_diagonal]

/-- The device compiler itself cannot broadcast one channel into another. -/
theorem compiledChannelwiseLCTransducerOperator_noCrossChannelCapture
    (design : ChannelwiseFiniteLCTransducerNetworkDesign) (duration : ℝ)
    (source target : FiniteEmbodimentChannel) (different : source ≠ target)
    (value : ℂ) :
    compiledChannelwiseLCTransducerOperator design duration
        (WithLp.toLp 2 (Pi.single source value)) target = 0 := by
  rw [compiledChannelwiseLCTransducerOperator_apply]
  simp [Ne.symm different]

def idealChannelwiseDesign : ChannelwiseFiniteLCTransducerNetworkDesign :=
  ⟨fun _ => ⟨1, 1, 1⟩⟩

theorem compiledChannelwise_ideal_eq_idealQuarterOperator :
    compiledChannelwiseLCTransducerOperator idealChannelwiseDesign
        (Real.pi / 2) = idealQuarterOperator := by
  calc
    compiledChannelwiseLCTransducerOperator idealChannelwiseDesign
        (Real.pi / 2) = scalarPhaseOperator 1 (Real.pi / 2) := by
      classical
      ext state channel
      simp [compiledChannelwiseLCTransducerOperator, Matrix.mulVec_diagonal,
        channelwiseTransducerCoefficient, idealChannelwiseDesign,
        channelDesign, scalarPhaseOperator, normalizedLCAngularFrequency]
    _ = scalarPhaseOperator
          (normalizedLCAngularFrequency
            ninetyNinePercentUnitLCTransducerDesign) (Real.pi / 2) := by
      rw [ninetyNinePercentUnitLC_frequency_eq_one]
    _ = compiledLCResonatorOperator
        ninetyNinePercentUnitLCTransducerDesign (Real.pi / 2) :=
      (compiledLCResonatorOperator_eq_scalarPhaseOperator
        ninetyNinePercentUnitLCTransducerDesign (Real.pi / 2)).symm
    _ = idealQuarterOperator := by
      unfold compiledLCResonatorOperator idealQuarterOperator
      rw [ninetyNinePercentUnitLC_frequency_eq_one]

def referenceChannelwiseDesign : ChannelwiseFiniteLCTransducerNetworkDesign :=
  ⟨fun _ => ninetyNinePercentUnitLCTransducerDesign.branch⟩

theorem compiledChannelwise_reference_eq_centre :
    compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
        (Real.pi / 2) =
      compiledLCTransducerQuarterOperator
        ninetyNinePercentUnitLCTransducerDesign := by
  classical
  ext state channel
  simp [compiledChannelwiseLCTransducerOperator, Matrix.mulVec_diagonal,
    channelwiseTransducerCoefficient, referenceChannelwiseDesign,
    channelDesign, compiledLCTransducerQuarterOperator,
    compiledLCTransducerOperator_eq_scalarPhaseOperator]

theorem compiledChannelwise_sub_reference_eq_diagonal
    (design : ChannelwiseFiniteLCTransducerNetworkDesign) (duration : ℝ) :
    compiledChannelwiseLCTransducerOperator design duration -
        compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2) =
      Matrix.toEuclideanCLM
        (n := FiniteEmbodimentChannel) (𝕜 := ℂ)
        (Matrix.diagonal (fun channel =>
          channelwiseTransducerCoefficient design duration channel -
            channelwiseTransducerCoefficient referenceChannelwiseDesign
              (Real.pi / 2) channel)) := by
  classical
  ext state channel
  simp [compiledChannelwiseLCTransducerOperator, Matrix.mulVec_diagonal,
    sub_mul]

theorem norm_compiledChannelwise_sub_eq
    (leftDesign rightDesign : ChannelwiseFiniteLCTransducerNetworkDesign)
    (leftDuration rightDuration : ℝ) :
    ‖compiledChannelwiseLCTransducerOperator leftDesign leftDuration -
        compiledChannelwiseLCTransducerOperator rightDesign rightDuration‖ =
      ‖fun channel =>
        channelwiseTransducerCoefficient leftDesign leftDuration channel -
          channelwiseTransducerCoefficient rightDesign rightDuration channel‖ := by
  have diagonalDifference :
      compiledChannelwiseLCTransducerOperator leftDesign leftDuration -
          compiledChannelwiseLCTransducerOperator rightDesign rightDuration =
        Matrix.toEuclideanCLM
          (n := FiniteEmbodimentChannel) (𝕜 := ℂ)
          (Matrix.diagonal (fun channel =>
            channelwiseTransducerCoefficient leftDesign leftDuration channel -
              channelwiseTransducerCoefficient rightDesign rightDuration
                channel)) := by
    classical
    ext state channel
    simp [compiledChannelwiseLCTransducerOperator, Matrix.mulVec_diagonal,
      sub_mul]
  rw [diagonalDifference, Matrix.l2_opNorm_toEuclideanCLM,
    Matrix.l2_opNorm_diagonal]

/-- Exact global error: the norm is the finite maximum of the ten coefficient
errors, not a sum over channels. -/
theorem norm_compiledChannelwise_sub_reference_eq
    (design : ChannelwiseFiniteLCTransducerNetworkDesign) (duration : ℝ) :
    ‖compiledChannelwiseLCTransducerOperator design duration -
        compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2)‖ =
      ‖fun channel =>
        channelwiseTransducerCoefficient design duration channel -
          channelwiseTransducerCoefficient referenceChannelwiseDesign
            (Real.pi / 2) channel‖ := by
  rw [compiledChannelwise_sub_reference_eq_diagonal]
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]

/-- Independent source coordinates for every typed branch at one shared run
duration.  No target readout or global operator norm is a field. -/
structure ChannelwiseLCTransducerRunCalibrationAt
    (design : ChannelwiseFiniteLCTransducerNetworkDesign)
    (duration : ℝ) : Prop where
  componentAdmissible : ∀ channel,
    LCTransducerComponentAdmissibleAt (channelDesign design channel)
  transferGainError : ∀ channel,
    |(design.branchAt channel).transferGain - (99 : ℝ) / 100| <
      (1 : ℝ) / 800
  accumulatedPhaseError : ∀ channel,
    |normalizedLCAngularFrequency (channelDesign design channel) * duration -
        Real.pi / 2| < (1 : ℝ) / 800

theorem channelwiseTransducerCoefficient_sub_reference_lt
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {duration : ℝ}
    (calibration : ChannelwiseLCTransducerRunCalibrationAt design duration)
    (channel : FiniteEmbodimentChannel) :
    ‖channelwiseTransducerCoefficient design duration channel -
        channelwiseTransducerCoefficient referenceChannelwiseDesign
          (Real.pi / 2) channel‖ < (1 : ℝ) / 400 := by
  have bound := transducerCoefficient_sub_norm_le
    (design.branchAt channel).transferGain ((99 : ℝ) / 100)
    (normalizedLCAngularFrequency (channelDesign design channel)) duration
    1 (Real.pi / 2)
  norm_num at bound
  have phaseContribution :
      (99 : ℝ) / 100 *
          |normalizedLCAngularFrequency (channelDesign design channel) *
              duration - Real.pi / 2| <
        (99 : ℝ) / 100 * ((1 : ℝ) / 800) :=
    mul_lt_mul_of_pos_left (calibration.accumulatedPhaseError channel)
      (by norm_num)
  have coefficientBound :
      ‖channelwiseTransducerCoefficient design duration channel -
          channelwiseTransducerCoefficient referenceChannelwiseDesign
            (Real.pi / 2) channel‖ ≤
        |(design.branchAt channel).transferGain - (99 : ℝ) / 100| +
          (99 : ℝ) / 100 *
            |normalizedLCAngularFrequency (channelDesign design channel) *
                duration - Real.pi / 2| := by
    simpa [channelwiseTransducerCoefficient, referenceChannelwiseDesign,
      channelDesign, ninetyNinePercentUnitLCTransducerDesign,
      normalizedLCAngularFrequency] using bound
  calc
    _ ≤ _ := coefficientBound
    _ < (1 : ℝ) / 800 +
        (99 : ℝ) / 100 * ((1 : ℝ) / 800) :=
      add_lt_add (calibration.transferGainError channel) phaseContribution
    _ < (1 : ℝ) / 400 := by norm_num

theorem channelwiseRun_operatorDistanceToReference_lt
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {duration : ℝ}
    (calibration : ChannelwiseLCTransducerRunCalibrationAt design duration) :
    ‖compiledChannelwiseLCTransducerOperator design duration -
        compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2)‖ < (1 : ℝ) / 400 := by
  rw [norm_compiledChannelwise_sub_reference_eq]
  exact (pi_norm_lt_iff (by norm_num)).2
    (channelwiseTransducerCoefficient_sub_reference_lt calibration)

theorem channelwiseRun_linearTolerance
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {duration : ℝ}
    (calibration : ChannelwiseLCTransducerRunCalibrationAt design duration) :
    ‖compiledChannelwiseLCTransducerOperator design duration -
        idealQuarterOperator‖ < (1 : ℝ) / 80 := by
  have toReference := channelwiseRun_operatorDistanceToReference_lt calibration
  have referenceToIdeal :
      ‖compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2) - idealQuarterOperator‖ ≤ (1 : ℝ) / 100 := by
    rw [compiledChannelwise_reference_eq_centre]
    exact ninetyNinePercentCenter_error_le_oneHundredth
  calc
    ‖compiledChannelwiseLCTransducerOperator design duration -
        idealQuarterOperator‖ =
      ‖(compiledChannelwiseLCTransducerOperator design duration -
          compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
            (Real.pi / 2)) +
        (compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
            (Real.pi / 2) - idealQuarterOperator)‖ := by congr 1; abel
    _ ≤ ‖compiledChannelwiseLCTransducerOperator design duration -
          compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
            (Real.pi / 2)‖ +
        ‖compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
            (Real.pi / 2) - idealQuarterOperator‖ := norm_add_le _ _
    _ < (1 : ℝ) / 400 + (1 : ℝ) / 100 :=
      add_lt_add_of_lt_of_le toReference referenceToIdeal
    _ = (1 : ℝ) / 80 := by norm_num

theorem channelwiseRun_duration_pos
    {design : ChannelwiseFiniteLCTransducerNetworkDesign}
    {duration : ℝ}
    (calibration : ChannelwiseLCTransducerRunCalibrationAt design duration) :
    0 < duration := by
  let channel : FiniteEmbodimentChannel := .sourceBound
  let omega := normalizedLCAngularFrequency (channelDesign design channel)
  have omegaPositive : 0 < omega :=
    normalizedLCAngularFrequency_pos _
      (calibration.componentAdmissible channel)
  have phaseError := calibration.accumulatedPhaseError channel
  have phaseLower := (abs_lt.mp phaseError).1
  have phaseProductPositive : 0 < omega * duration := by
    dsimp [omega, channel] at phaseLower ⊢
    nlinarith [Real.pi_gt_three]
  by_contra notPositive
  have durationNonpositive : duration ≤ 0 := le_of_not_gt notPositive
  have productNonpositive : omega * duration ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt omegaPositive)
      durationNonpositive
  exact (not_lt_of_ge productNonpositive) phaseProductPositive

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.compiledChannelwiseLCTransducerOperator_noCrossChannelCapture
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.norm_compiledChannelwise_sub_reference_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.channelwiseRun_operatorDistanceToReference_lt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.channelwiseRun_linearTolerance
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.channelwiseRun_duration_pos
