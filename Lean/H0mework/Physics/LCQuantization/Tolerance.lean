import H0mework.Physics.LCQuantization.Run

/-!
# Finite quantized crosstalk tolerance kernel

The rational-clock component family leaves enough certified margin for a
genuinely off-diagonal linear parasitic.  A rank-one machine-to-neural to
neural-to-body crosstalk operator is constructed explicitly, norm-bounded, and
quantized by one further ternary code.  Every resulting linear implementation
remains inside the existing `1/80` additive-disturbance gate.
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

/-! ## Tight margin of the finite component/run family -/

theorem finiteQuantizedChannelLCRun_phaseError_tight
    (code : FiniteQuantizedChannelLCRunCode)
    (channel : FiniteEmbodimentChannel) :
    |normalizedLCAngularFrequency
          (channelDesign (finiteQuantizedChannelwiseDesign code.1) channel) *
        quantizedExecutedDuration code - Real.pi / 2| <
      (1 : ℝ) / 50000 := by
  rw [finiteQuantizedChannelwise_frequency_exact]
  cases hf : code.1.1 channel <;>
    cases ht : code.2
  all_goals
    rw [abs_lt]
    constructor <;>
      norm_num [quantizedChannelFrequency, quantizedExecutedDuration,
        rationalClockCentre, ternaryOffsetValue, hf, ht] <;>
      nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]

theorem finiteQuantizedChannelLCRun_gainError_tight
    (code : FiniteQuantizedChannelLCRunCode)
    (channel : FiniteEmbodimentChannel) :
    |((finiteQuantizedChannelwiseDesign code.1).branchAt channel).transferGain -
        (99 : ℝ) / 100| < (1 : ℝ) / 5000 := by
  cases hg : code.1.2 channel <;>
    norm_num [finiteQuantizedChannelwiseDesign, lcBranchRealizingFrequency,
      quantizedChannelGain, ternaryOffsetValue, hg]

theorem finiteQuantizedChannelLCRun_coefficientToReference_tight
    (code : FiniteQuantizedChannelLCRunCode)
    (channel : FiniteEmbodimentChannel) :
    ‖channelwiseTransducerCoefficient
          (finiteQuantizedChannelwiseDesign code.1)
          (quantizedExecutedDuration code) channel -
        channelwiseTransducerCoefficient referenceChannelwiseDesign
          (Real.pi / 2) channel‖ < (1 : ℝ) / 4000 := by
  have bound := transducerCoefficient_sub_norm_le
    ((finiteQuantizedChannelwiseDesign code.1).branchAt channel).transferGain
    ((99 : ℝ) / 100)
    (normalizedLCAngularFrequency
      (channelDesign (finiteQuantizedChannelwiseDesign code.1) channel))
    (quantizedExecutedDuration code) 1 (Real.pi / 2)
  norm_num at bound
  have phaseContribution :
      (99 : ℝ) / 100 *
        |normalizedLCAngularFrequency
            (channelDesign (finiteQuantizedChannelwiseDesign code.1) channel) *
          quantizedExecutedDuration code - Real.pi / 2| <
      (99 : ℝ) / 100 * ((1 : ℝ) / 50000) :=
    mul_lt_mul_of_pos_left
      (finiteQuantizedChannelLCRun_phaseError_tight code channel)
      (by norm_num)
  have coefficientBound :
      ‖channelwiseTransducerCoefficient
            (finiteQuantizedChannelwiseDesign code.1)
            (quantizedExecutedDuration code) channel -
          channelwiseTransducerCoefficient referenceChannelwiseDesign
            (Real.pi / 2) channel‖ ≤
        |((finiteQuantizedChannelwiseDesign code.1).branchAt channel).transferGain -
            (99 : ℝ) / 100| +
          (99 : ℝ) / 100 *
            |normalizedLCAngularFrequency
                (channelDesign (finiteQuantizedChannelwiseDesign code.1) channel) *
              quantizedExecutedDuration code - Real.pi / 2| := by
    simpa [channelwiseTransducerCoefficient, referenceChannelwiseDesign,
      channelDesign, ninetyNinePercentUnitLCTransducerDesign,
      normalizedLCAngularFrequency] using bound
  calc
    _ ≤ _ := coefficientBound
    _ < (1 : ℝ) / 5000 +
        (99 : ℝ) / 100 * ((1 : ℝ) / 50000) :=
      add_lt_add
        (finiteQuantizedChannelLCRun_gainError_tight code channel)
        phaseContribution
    _ < (1 : ℝ) / 4000 := by norm_num

theorem finiteQuantizedChannelLCRun_operatorToReference_tight
    (code : FiniteQuantizedChannelLCRunCode) :
    ‖compiledChannelwiseLCTransducerOperator
          (finiteQuantizedChannelwiseDesign code.1)
          (quantizedExecutedDuration code) -
        compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2)‖ < (1 : ℝ) / 4000 := by
  rw [norm_compiledChannelwise_sub_reference_eq]
  exact (pi_norm_lt_iff (by norm_num)).2
    (finiteQuantizedChannelLCRun_coefficientToReference_tight code)

theorem finiteQuantizedChannelLCRun_operatorToIdeal_tight
    (code : FiniteQuantizedChannelLCRunCode) :
    ‖compiledChannelwiseLCTransducerOperator
          (finiteQuantizedChannelwiseDesign code.1)
          (quantizedExecutedDuration code) - idealQuarterOperator‖ <
      (41 : ℝ) / 4000 := by
  have base := finiteQuantizedChannelLCRun_operatorToReference_tight code
  have reference :
      ‖compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2) - idealQuarterOperator‖ ≤ (1 : ℝ) / 100 := by
    rw [compiledChannelwise_reference_eq_centre]
    exact ninetyNinePercentCenter_error_le_oneHundredth
  calc
    _ = ‖(compiledChannelwiseLCTransducerOperator
          (finiteQuantizedChannelwiseDesign code.1)
          (quantizedExecutedDuration code) -
        compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2)) +
      (compiledChannelwiseLCTransducerOperator referenceChannelwiseDesign
          (Real.pi / 2) - idealQuarterOperator)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ < (1 : ℝ) / 4000 + (1 : ℝ) / 100 :=
      add_lt_add_of_lt_of_le base reference
    _ = (41 : ℝ) / 4000 := by norm_num

/-! ## Explicit rank-one off-diagonal parasitic -/

def rankOneCrosstalkMatrix :
    Matrix FiniteEmbodimentChannel FiniteEmbodimentChannel ℂ :=
  fun row column =>
    if row = .neuralToBodyEffect then
      if column = .machineToNeuralWrite then 1 else 0
    else 0

def rankOneCrosstalkOperator :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  Matrix.toEuclideanCLM (n := FiniteEmbodimentChannel) (𝕜 := ℂ)
    rankOneCrosstalkMatrix

theorem rankOneCrosstalkOperator_apply
    (state : HilbertEmbodimentState) :
    rankOneCrosstalkOperator state =
      WithLp.toLp 2 (Pi.single .neuralToBodyEffect
        (state .machineToNeuralWrite)) := by
  classical
  ext channel
  by_cases target : channel = .neuralToBodyEffect
  · subst channel
    simp [rankOneCrosstalkOperator, rankOneCrosstalkMatrix,
      Matrix.mulVec, dotProduct]
  · simp [rankOneCrosstalkOperator, rankOneCrosstalkMatrix,
      Matrix.mulVec, dotProduct, target]

theorem rankOneCrosstalkOperator_norm_le_one :
    ‖rankOneCrosstalkOperator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro state
  rw [rankOneCrosstalkOperator_apply]
  change ‖(PiLp.single 2 FiniteEmbodimentChannel.neuralToBodyEffect
      (state .machineToNeuralWrite) : HilbertEmbodimentState)‖ ≤ 1 * ‖state‖
  rw [PiLp.norm_single]
  simpa using PiLp.norm_apply_le state .machineToNeuralWrite

abbrev FiniteQuantizedChannelLCRunCrosstalkCode :=
  FiniteQuantizedChannelLCRunCode × TernaryCalibrationOffset

def quantizedCrosstalkAmplitude
    (code : FiniteQuantizedChannelLCRunCrosstalkCode) : ℝ :=
  ternaryOffsetValue code.2 / 1000

def finiteQuantizedCrosstalkImplementation
    (code : FiniteQuantizedChannelLCRunCrosstalkCode) :
    HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState :=
  compiledChannelwiseLCTransducerOperator
      (finiteQuantizedChannelwiseDesign code.1.1)
      (quantizedExecutedDuration code.1) +
    (quantizedCrosstalkAmplitude code : ℂ) • rankOneCrosstalkOperator

theorem quantizedCrosstalkOperator_norm_le
    (code : FiniteQuantizedChannelLCRunCrosstalkCode) :
    ‖(quantizedCrosstalkAmplitude code : ℂ) •
        rankOneCrosstalkOperator‖ ≤ (1 : ℝ) / 1000 := by
  rw [norm_smul]
  have amplitudeBound : ‖(quantizedCrosstalkAmplitude code : ℂ)‖ ≤
      (1 : ℝ) / 1000 := by
    cases h : code.2 <;>
      norm_num [quantizedCrosstalkAmplitude, ternaryOffsetValue, h]
  calc
    _ ≤ (1 : ℝ) / 1000 * 1 :=
      mul_le_mul amplitudeBound rankOneCrosstalkOperator_norm_le_one
        (norm_nonneg _) (by norm_num)
    _ = (1 : ℝ) / 1000 := by norm_num

theorem everyFiniteQuantizedCrosstalkImplementation_linearTolerance
    (code : FiniteQuantizedChannelLCRunCrosstalkCode) :
    ‖finiteQuantizedCrosstalkImplementation code - idealQuarterOperator‖ <
      (1 : ℝ) / 80 := by
  have base := finiteQuantizedChannelLCRun_operatorToIdeal_tight code.1
  have cross := quantizedCrosstalkOperator_norm_le code
  calc
    ‖finiteQuantizedCrosstalkImplementation code - idealQuarterOperator‖ =
      ‖(compiledChannelwiseLCTransducerOperator
          (finiteQuantizedChannelwiseDesign code.1.1)
          (quantizedExecutedDuration code.1) - idealQuarterOperator) +
        (quantizedCrosstalkAmplitude code : ℂ) •
          rankOneCrosstalkOperator‖ := by
      unfold finiteQuantizedCrosstalkImplementation
      congr 1
      abel
    _ ≤ ‖compiledChannelwiseLCTransducerOperator
          (finiteQuantizedChannelwiseDesign code.1.1)
          (quantizedExecutedDuration code.1) - idealQuarterOperator‖ +
        ‖(quantizedCrosstalkAmplitude code : ℂ) •
          rankOneCrosstalkOperator‖ := norm_add_le _ _
    _ < (41 : ℝ) / 4000 + (1 : ℝ) / 1000 :=
      add_lt_add_of_lt_of_le base cross
    _ < (1 : ℝ) / 80 := by norm_num

def finiteQuantizedChannelLCRunCrosstalkConfiguration
    (code : FiniteQuantizedChannelLCRunCrosstalkCode) :=
  (finiteQuantizedChannelLCRunConfiguration code.1,
    quantizedCrosstalkAmplitude code)

theorem finiteQuantizedChannelLCRunCrosstalkConfiguration_injective :
    Function.Injective finiteQuantizedChannelLCRunCrosstalkConfiguration := by
  intro left right configurationSame
  have runSame := congrArg Prod.fst configurationSame
  have runCodeSame := finiteQuantizedChannelLCRunConfiguration_injective runSame
  have amplitudeSame := congrArg Prod.snd configurationSame
  apply Prod.ext runCodeSame
  apply ternaryOffsetValue_injective
  unfold finiteQuantizedChannelLCRunCrosstalkConfiguration
    quantizedCrosstalkAmplitude at amplitudeSame
  linarith

theorem finiteQuantizedChannelLCRunCrosstalkCode_card :
    Fintype.card FiniteQuantizedChannelLCRunCrosstalkCode = 31381059609 := by
  simp [FiniteQuantizedChannelLCRunCrosstalkCode,
    FiniteQuantizedChannelLCRunCode, FiniteQuantizedChannelLCCode,
    ternaryCalibrationOffset_card, channel_cardinality]

def crosstalkSourceUnit : HilbertEmbodimentState :=
  WithLp.toLp 2 (Pi.single .machineToNeuralWrite (1 : ℂ))

theorem positiveQuantizedCrosstalk_writesOffDiagonal
    (runCode : FiniteQuantizedChannelLCRunCode) :
    finiteQuantizedCrosstalkImplementation (runCode, .positive)
        crosstalkSourceUnit .neuralToBodyEffect = (1 : ℂ) / 1000 := by
  unfold finiteQuantizedCrosstalkImplementation
  simp only [add_apply, smul_apply]
  unfold crosstalkSourceUnit
  rw [PiLp.add_apply, PiLp.smul_apply]
  rw [compiledChannelwiseLCTransducerOperator_noCrossChannelCapture
    _ _ _ _ (by decide)]
  rw [rankOneCrosstalkOperator_apply]
  norm_num [quantizedCrosstalkAmplitude, ternaryOffsetValue,
    PiLp.single_apply]

/-- The off-diagonal probe reads the generated crosstalk amplitude exactly;
the diagonal LC part contributes no value at this source/target pair. -/
theorem quantizedCrosstalk_writesOffDiagonal
    (code : FiniteQuantizedChannelLCRunCrosstalkCode) :
    finiteQuantizedCrosstalkImplementation code crosstalkSourceUnit
        .neuralToBodyEffect = (quantizedCrosstalkAmplitude code : ℂ) := by
  unfold finiteQuantizedCrosstalkImplementation
  simp only [add_apply, smul_apply]
  unfold crosstalkSourceUnit
  rw [PiLp.add_apply, PiLp.smul_apply]
  rw [compiledChannelwiseLCTransducerOperator_noCrossChannelCapture
    _ _ _ _ (by decide)]
  rw [rankOneCrosstalkOperator_apply]
  norm_num [PiLp.single_apply]

/-- Every nonzero code word is a genuinely non-diagonal implementation, not
another diagonal channelwise LC design in disguise. -/
theorem nonzeroQuantizedCrosstalk_isGenuinelyOffDiagonal
    (runCode : FiniteQuantizedChannelLCRunCode)
    (offset : TernaryCalibrationOffset) (nonzero : offset ≠ .zero)
    (design : ChannelwiseFiniteLCTransducerNetworkDesign) (duration : ℝ) :
    finiteQuantizedCrosstalkImplementation (runCode, offset) ≠
      compiledChannelwiseLCTransducerOperator design duration := by
  intro allegedlyDiagonal
  have outputSame := congrArg
    (fun operator : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState =>
      operator crosstalkSourceUnit .neuralToBodyEffect) allegedlyDiagonal
  rw [quantizedCrosstalk_writesOffDiagonal] at outputSame
  unfold crosstalkSourceUnit at outputSame
  rw [compiledChannelwiseLCTransducerOperator_noCrossChannelCapture
    _ _ _ _ (by decide)] at outputSame
  cases offset <;>
    simp_all [quantizedCrosstalkAmplitude, ternaryOffsetValue]

theorem positiveQuantizedCrosstalk_isGenuinelyOffDiagonal
    (runCode : FiniteQuantizedChannelLCRunCode)
    (design : ChannelwiseFiniteLCTransducerNetworkDesign) (duration : ℝ) :
    finiteQuantizedCrosstalkImplementation (runCode, .positive) ≠
      compiledChannelwiseLCTransducerOperator design duration := by
  intro allegedlyDiagonal
  have outputSame := congrArg
    (fun operator : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState =>
      operator crosstalkSourceUnit .neuralToBodyEffect) allegedlyDiagonal
  rw [positiveQuantizedCrosstalk_writesOffDiagonal] at outputSame
  unfold crosstalkSourceUnit at outputSame
  rw [compiledChannelwiseLCTransducerOperator_noCrossChannelCapture
    _ _ _ _ (by decide)] at outputSame
  norm_num at outputSame

/-- The complete source code is recoverable even when the final observable is
the actual linear implementation rather than the scalar crosstalk amplitude. -/
def finiteQuantizedChannelLCRunCrosstalkPhysicalConfiguration
    (code : FiniteQuantizedChannelLCRunCrosstalkCode) :=
  (finiteQuantizedChannelLCRunConfiguration code.1,
    finiteQuantizedCrosstalkImplementation code)

theorem finiteQuantizedChannelLCRunCrosstalkPhysicalConfiguration_injective :
    Function.Injective
      finiteQuantizedChannelLCRunCrosstalkPhysicalConfiguration := by
  intro left right configurationSame
  have runSame := congrArg (fun configuration => configuration.1)
    configurationSame
  have runCodeSame := finiteQuantizedChannelLCRunConfiguration_injective runSame
  have implementationSame := congrArg (fun configuration => configuration.2)
    configurationSame
  change finiteQuantizedCrosstalkImplementation left =
    finiteQuantizedCrosstalkImplementation right at implementationSame
  have amplitudeSameComplex :
      (quantizedCrosstalkAmplitude left : ℂ) =
        (quantizedCrosstalkAmplitude right : ℂ) := by
    have outputSame := congrArg
      (fun operator : HilbertEmbodimentState →L[ℂ] HilbertEmbodimentState =>
        operator crosstalkSourceUnit .neuralToBodyEffect) implementationSame
    rw [quantizedCrosstalk_writesOffDiagonal,
      quantizedCrosstalk_writesOffDiagonal] at outputSame
    exact outputSame
  have amplitudeSame :
      quantizedCrosstalkAmplitude left = quantizedCrosstalkAmplitude right := by
    exact Complex.ofReal_injective amplitudeSameComplex
  apply Prod.ext runCodeSame
  apply ternaryOffsetValue_injective
  unfold quantizedCrosstalkAmplitude at amplitudeSame
  linarith

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteQuantizedChannelLCRun_phaseError_tight
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.rankOneCrosstalkOperator_norm_le_one
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.everyFiniteQuantizedCrosstalkImplementation_linearTolerance
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteQuantizedChannelLCRunCrosstalkConfiguration_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.positiveQuantizedCrosstalk_isGenuinelyOffDiagonal
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.nonzeroQuantizedCrosstalk_isGenuinelyOffDiagonal
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer.finiteQuantizedChannelLCRunCrosstalkPhysicalConfiguration_injective
