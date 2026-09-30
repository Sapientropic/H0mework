import H0mework.Physics.LCDesign.ChannelCoupling

/-!
# Finite quantized channelwise LC compiler

Twenty finite ternary coordinates -- one frequency offset and one gain offset
for each of ten typed channels -- generate component parameters before any
operator or coupling verdict exists.  Every one of the `3^20` code words is
proved to enter the current channelwise tolerance and disturbed coupling crown.

The frequency code is realized by an explicit positive LC branch
`L = omega⁻², C = 1`; this file proves that the component compiler reads back
exactly the generated frequency rather than postulating it as a field.
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

inductive TernaryCalibrationOffset where
  | negative
  | zero
  | positive
  deriving DecidableEq, Repr, FintypeViaProxy

def ternaryOffsetValue : TernaryCalibrationOffset → ℝ
  | .negative => -1
  | .zero => 0
  | .positive => 1

theorem ternaryOffsetValue_injective :
    Function.Injective ternaryOffsetValue := by
  intro left right same
  cases left <;> cases right
  all_goals try rfl
  all_goals norm_num [ternaryOffsetValue] at same

/-- Ten frequency codes and ten gain codes. -/
abbrev FiniteQuantizedChannelLCCode :=
  (FiniteEmbodimentChannel → TernaryCalibrationOffset) ×
    (FiniteEmbodimentChannel → TernaryCalibrationOffset)

def quantizedChannelFrequency
    (code : FiniteQuantizedChannelLCCode)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  1 + ternaryOffsetValue (code.1 channel) / 100000

def quantizedChannelGain
    (code : FiniteQuantizedChannelLCCode)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  (99 : ℝ) / 100 + ternaryOffsetValue (code.2 channel) / 10000

def lcBranchRealizingFrequency (omega gain : ℝ) : LCTransducerBranchDesign :=
  ⟨(omega⁻¹) ^ 2, 1, gain⟩

theorem lcBranchRealizingFrequency_exact
    {omega gain : ℝ} (omegaPositive : 0 < omega) :
    normalizedLCAngularFrequency
        ⟨lcBranchRealizingFrequency omega gain⟩ = omega := by
  unfold normalizedLCAngularFrequency lcBranchRealizingFrequency
  rw [mul_one, Real.sqrt_sq_eq_abs,
    abs_of_pos (inv_pos.mpr omegaPositive), inv_inv]

def finiteQuantizedChannelwiseDesign
    (code : FiniteQuantizedChannelLCCode) :
    ChannelwiseFiniteLCTransducerNetworkDesign where
  branchAt channel := lcBranchRealizingFrequency
    (quantizedChannelFrequency code channel)
    (quantizedChannelGain code channel)

theorem quantizedChannelFrequency_pos
    (code : FiniteQuantizedChannelLCCode)
    (channel : FiniteEmbodimentChannel) :
    0 < quantizedChannelFrequency code channel := by
  cases h : code.1 channel <;>
    norm_num [quantizedChannelFrequency, ternaryOffsetValue, h]

theorem finiteQuantizedChannelwise_frequency_exact
    (code : FiniteQuantizedChannelLCCode)
    (channel : FiniteEmbodimentChannel) :
    normalizedLCAngularFrequency
        (channelDesign (finiteQuantizedChannelwiseDesign code) channel) =
      quantizedChannelFrequency code channel := by
  exact lcBranchRealizingFrequency_exact
    (quantizedChannelFrequency_pos code channel)

theorem finiteQuantizedChannelwise_componentAdmissible
    (code : FiniteQuantizedChannelLCCode)
    (channel : FiniteEmbodimentChannel) :
    LCTransducerComponentAdmissibleAt
      (channelDesign (finiteQuantizedChannelwiseDesign code) channel) := by
  cases hf : code.1 channel <;>
    cases hg : code.2 channel <;>
    constructor <;>
    norm_num [channelDesign, finiteQuantizedChannelwiseDesign,
      lcBranchRealizingFrequency, quantizedChannelFrequency,
      quantizedChannelGain, ternaryOffsetValue, hf, hg]

theorem finiteQuantizedChannelwise_gainError
    (code : FiniteQuantizedChannelLCCode)
    (channel : FiniteEmbodimentChannel) :
    |((finiteQuantizedChannelwiseDesign code).branchAt channel).transferGain -
        (99 : ℝ) / 100| < (1 : ℝ) / 800 := by
  cases hg : code.2 channel <;>
    norm_num [finiteQuantizedChannelwiseDesign, lcBranchRealizingFrequency,
      quantizedChannelGain, ternaryOffsetValue, hg]

theorem finiteQuantizedChannelwise_phaseError
    (code : FiniteQuantizedChannelLCCode)
    (channel : FiniteEmbodimentChannel) :
    |normalizedLCAngularFrequency
          (channelDesign (finiteQuantizedChannelwiseDesign code) channel) *
        (Real.pi / 2) - Real.pi / 2| < (1 : ℝ) / 800 := by
  rw [finiteQuantizedChannelwise_frequency_exact]
  cases hf : code.1 channel
  · rw [show quantizedChannelFrequency code channel * (Real.pi / 2) -
        Real.pi / 2 = -Real.pi / 200000 by
      simp [quantizedChannelFrequency, ternaryOffsetValue, hf]
      ring]
    rw [show -Real.pi / 200000 = -(Real.pi / 200000) by ring,
      abs_neg, abs_of_pos (div_pos Real.pi_pos (by norm_num))]
    nlinarith [Real.pi_lt_four]
  · norm_num [quantizedChannelFrequency, ternaryOffsetValue, hf]
  · rw [show quantizedChannelFrequency code channel * (Real.pi / 2) -
        Real.pi / 2 = Real.pi / 200000 by
      simp [quantizedChannelFrequency, ternaryOffsetValue, hf]
      ring]
    rw [abs_of_pos (div_pos Real.pi_pos (by norm_num))]
    nlinarith [Real.pi_lt_four]

theorem everyFiniteQuantizedCode_calibrated
    (code : FiniteQuantizedChannelLCCode) :
    ChannelwiseLCTransducerRunCalibrationAt
      (finiteQuantizedChannelwiseDesign code) (Real.pi / 2) where
  componentAdmissible := finiteQuantizedChannelwise_componentAdmissible code
  transferGainError := finiteQuantizedChannelwise_gainError code
  accumulatedPhaseError := finiteQuantizedChannelwise_phaseError code

/-- No two finite code words collapse to the same component design. -/
theorem finiteQuantizedChannelwiseDesign_injective :
    Function.Injective finiteQuantizedChannelwiseDesign := by
  intro left right designSame
  apply Prod.ext
  · funext channel
    have branchSame := congrArg
      (fun design : ChannelwiseFiniteLCTransducerNetworkDesign =>
        design.branchAt channel) designSame
    have inductanceSame := congrArg LCTransducerBranchDesign.inductance
      branchSame
    change (quantizedChannelFrequency left channel)⁻¹ ^ 2 =
      (quantizedChannelFrequency right channel)⁻¹ ^ 2 at inductanceSame
    have sqrtSame := congrArg Real.sqrt inductanceSame
    have inverseSame : (quantizedChannelFrequency left channel)⁻¹ =
        (quantizedChannelFrequency right channel)⁻¹ := by
      rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at sqrtSame
      rw [abs_of_pos (inv_pos.mpr
          (quantizedChannelFrequency_pos left channel)),
        abs_of_pos (inv_pos.mpr
          (quantizedChannelFrequency_pos right channel))] at sqrtSame
      exact sqrtSame
    have frequencySame : quantizedChannelFrequency left channel =
        quantizedChannelFrequency right channel := inv_injective inverseSame
    cases leftOffset : left.1 channel <;>
      cases rightOffset : right.1 channel
    all_goals try rfl
    all_goals
      norm_num [quantizedChannelFrequency, ternaryOffsetValue,
        leftOffset, rightOffset] at frequencySame
  · funext channel
    have branchSame := congrArg
      (fun design : ChannelwiseFiniteLCTransducerNetworkDesign =>
        design.branchAt channel) designSame
    have gainSame := congrArg LCTransducerBranchDesign.transferGain branchSame
    change quantizedChannelGain left channel =
      quantizedChannelGain right channel at gainSame
    cases leftOffset : left.2 channel <;>
      cases rightOffset : right.2 channel
    all_goals try rfl
    all_goals
      norm_num [quantizedChannelGain, ternaryOffsetValue,
        leftOffset, rightOffset] at gainSame

theorem ternaryCalibrationOffset_card :
    Fintype.card TernaryCalibrationOffset = 3 := by decide

theorem finiteQuantizedChannelLCCode_card :
    Fintype.card FiniteQuantizedChannelLCCode = 3486784401 := by
  simp [FiniteQuantizedChannelLCCode, ternaryCalibrationOffset_card,
    channel_cardinality]

/-- Every code word in the complete finite configuration space generates the
existing typed coupling crown under the same visible nonzero disturbance. -/
theorem everyFiniteQuantizedChannelCodeWithVisibleBias_constructible
    (code : FiniteQuantizedChannelLCCode) :
    ChannelwiseLCTransducerDisturbanceCrownAt
      (finiteQuantizedChannelwiseDesign code) (Real.pi / 2)
      smallNonzeroConstantBias :=
  everyChannelwiseCalibratedRunWithBoundedDisturbance_generatesCrown
    (everyFiniteQuantizedCode_calibrated code) smallNonzeroConstantBias
    smallNonzeroConstantBias_bound

/-- Raw configuration parsing is source-owned; values outside the declared
three-symbol language are rejected rather than silently clamped. -/
def decodeRawTernaryCalibrationOffset (raw : ℤ) :
    Option TernaryCalibrationOffset :=
  if raw = -1 then some .negative
  else if raw = 0 then some .zero
  else if raw = 1 then some .positive
  else none

theorem rawTernaryOffset_two_isRejected :
    decodeRawTernaryCalibrationOffset 2 = none := by
  norm_num [decodeRawTernaryCalibrationOffset]

/-- A raw gain offset of `13` is not merely outside the ternary grammar: if it
bypassed parsing, it would violate the quantitative calibration window. -/
theorem rawGainOffset_thirteen_isOutsideCalibrationBudget :
    ¬ |((99 : ℝ) / 100 + (13 : ℝ) / 10000) -
      (99 : ℝ) / 100| < (1 : ℝ) / 800 := by
  norm_num

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.lcBranchRealizingFrequency_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteQuantizedChannelwise_frequency_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyFiniteQuantizedCode_calibrated
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteQuantizedChannelwiseDesign_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteQuantizedChannelLCCode_card
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyFiniteQuantizedChannelCodeWithVisibleBias_constructible
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.rawTernaryOffset_two_isRejected
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.rawGainOffset_thirteen_isOutsideCalibrationBudget
