import Mathlib.Analysis.Real.Pi.Bounds
import H0mework.Physics.LCQuantization.Components

/-!
# Finite quantized channelwise LC run compiler

The component code is extended by one finite clock symbol.  Its executed
duration is a purely rational `355/226` centre plus a ternary microtick; none
of the three generated durations is definitionally or propositionally `pi/2`.
Tight certified bounds on `pi` prove that all `3^21` component/run code words
still generate the existing channelwise disturbed coupling crown.
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

abbrev FiniteQuantizedChannelLCRunCode :=
  FiniteQuantizedChannelLCCode × TernaryCalibrationOffset

def rationalClockCentre : ℝ := (355 : ℝ) / 226

def quantizedExecutedDuration
    (code : FiniteQuantizedChannelLCRunCode) : ℝ :=
  rationalClockCentre + ternaryOffsetValue code.2 / 1000000

/-- The source-visible configuration consists of its generated component
design and generated rational execution duration. -/
def finiteQuantizedChannelLCRunConfiguration
    (code : FiniteQuantizedChannelLCRunCode) :=
  (finiteQuantizedChannelwiseDesign code.1, quantizedExecutedDuration code)

theorem quantizedExecutedDuration_pos
    (code : FiniteQuantizedChannelLCRunCode) :
    0 < quantizedExecutedDuration code := by
  cases h : code.2 <;>
    norm_num [quantizedExecutedDuration, rationalClockCentre,
      ternaryOffsetValue, h]

/-- No exact irrational quarter-period is hidden in the finite clock code. -/
theorem quantizedExecutedDuration_ne_pi_div_two
    (code : FiniteQuantizedChannelLCRunCode) :
    quantizedExecutedDuration code ≠ Real.pi / 2 := by
  cases h : code.2 <;>
    intro equal
  all_goals
    norm_num [quantizedExecutedDuration, rationalClockCentre,
      ternaryOffsetValue, h] at equal
  · nlinarith [Real.pi_gt_d20]
  · nlinarith [Real.pi_lt_d20]
  · nlinarith [Real.pi_lt_d20]

theorem finiteQuantizedChannelLCRun_phaseError
    (code : FiniteQuantizedChannelLCRunCode)
    (channel : FiniteEmbodimentChannel) :
    |normalizedLCAngularFrequency
          (channelDesign (finiteQuantizedChannelwiseDesign code.1) channel) *
        quantizedExecutedDuration code - Real.pi / 2| <
      (1 : ℝ) / 800 := by
  rw [finiteQuantizedChannelwise_frequency_exact]
  cases hf : code.1.1 channel <;>
    cases ht : code.2
  all_goals
    rw [abs_lt]
    constructor <;>
      norm_num [quantizedChannelFrequency, quantizedExecutedDuration,
        rationalClockCentre, ternaryOffsetValue, hf, ht] <;>
      nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]

theorem everyFiniteQuantizedChannelLCRunCode_calibrated
    (code : FiniteQuantizedChannelLCRunCode) :
    ChannelwiseLCTransducerRunCalibrationAt
      (finiteQuantizedChannelwiseDesign code.1)
      (quantizedExecutedDuration code) where
  componentAdmissible :=
    finiteQuantizedChannelwise_componentAdmissible code.1
  transferGainError := finiteQuantizedChannelwise_gainError code.1
  accumulatedPhaseError := finiteQuantizedChannelLCRun_phaseError code

theorem finiteQuantizedChannelLCRunCode_card :
    Fintype.card FiniteQuantizedChannelLCRunCode = 10460353203 := by
  simp [FiniteQuantizedChannelLCRunCode, FiniteQuantizedChannelLCCode,
    ternaryCalibrationOffset_card, channel_cardinality]

/-- The complete `3^21` source code is recoverable from the generated
component-design/executed-duration pair. -/
theorem finiteQuantizedChannelLCRunConfiguration_injective :
    Function.Injective finiteQuantizedChannelLCRunConfiguration := by
  intro left right configurationSame
  have designSame := congrArg Prod.fst configurationSame
  have componentCodeSame :=
    finiteQuantizedChannelwiseDesign_injective designSame
  have durationSame := congrArg Prod.snd configurationSame
  apply Prod.ext componentCodeSame
  apply ternaryOffsetValue_injective
  unfold finiteQuantizedChannelLCRunConfiguration
    quantizedExecutedDuration at durationSame
  linarith

/-- Every finite component/run word directly returns the existing channelwise
crown; there is no quantized-run wrapper or caller-provided tolerance proof. -/
theorem everyFiniteQuantizedChannelLCRunCodeWithVisibleBias_constructible
    (code : FiniteQuantizedChannelLCRunCode) :
    ChannelwiseLCTransducerDisturbanceCrownAt
      (finiteQuantizedChannelwiseDesign code.1)
      (quantizedExecutedDuration code) smallNonzeroConstantBias :=
  everyChannelwiseCalibratedRunWithBoundedDisturbance_generatesCrown
    (everyFiniteQuantizedChannelLCRunCode_calibrated code)
    smallNonzeroConstantBias smallNonzeroConstantBias_bound

def rawClockDuration (offset : ℤ) : ℝ :=
  rationalClockCentre + offset / 1000000

/-- A raw two-thousand-microtick execution that bypasses the ternary parser
exceeds the quantitative phase budget at every allowed frequency code. -/
theorem rawClockOffset_twoThousand_breaksEveryTernaryFrequency
    (frequencyOffset : TernaryCalibrationOffset) :
    ¬ |(1 + ternaryOffsetValue frequencyOffset / 100000) *
          rawClockDuration 2000 - Real.pi / 2| < (1 : ℝ) / 800 := by
  intro allegedlyInside
  rw [abs_lt] at allegedlyInside
  cases hf : frequencyOffset
  all_goals
    norm_num [rawClockDuration, rationalClockCentre,
      ternaryOffsetValue, hf] at allegedlyInside
  all_goals nlinarith [Real.pi_lt_d20]

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.quantizedExecutedDuration_ne_pi_div_two
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteQuantizedChannelLCRun_phaseError
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyFiniteQuantizedChannelLCRunCode_calibrated
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteQuantizedChannelLCRunCode_card
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteQuantizedChannelLCRunConfiguration_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyFiniteQuantizedChannelLCRunCodeWithVisibleBias_constructible
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.rawClockOffset_twoThousand_breaksEveryTernaryFrequency
