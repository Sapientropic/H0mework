import H0mework.Computation.ADCWire.DigitalReadback
import H0mework.Computation.ADC.EnergyArithmetic

/-!
# Executable energy readback from finite ADC words

The resistor and inductor rows are physical quadratures.  This receiver first
calibrates each row using only its zero/span/operational integer words, then
tests the sum of the two squared rational ratios.  The test is executable: it
does not evaluate real sine or cosine and does not inspect the source command.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface Physical.Producer
open Physical.Units.Interface

/-- Integer difference between one frame and the same leg's zero reference. -/
def finiteADCDigitalWordDifference
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source)
    (frame : FiniteAffineMeterFrame) (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : ℤ :=
  (sample.wordsAt frame leg channel).val -
    (sample.wordsAt .zeroReference leg channel).val

/-- Executable calibrated leg value.  Division is in `ℚ`, not `ℝ`. -/
def finiteADCDigitalLegRatio
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source)
    (leg : SynchronousSenseLeg) (channel : FiniteEmbodimentChannel) : ℚ :=
  (finiteADCDigitalWordDifference sample .operational leg channel : ℚ) /
    (finiteADCDigitalWordDifference sample .spanReference leg channel : ℚ)

/-- Squared quadrature envelope, computed exactly in `ℚ`. -/
def finiteADCDigitalChannelEnergy
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source)
    (channel : FiniteEmbodimentChannel) : ℚ :=
  finiteADCDigitalLegRatio sample .resistor channel ^ 2 +
    finiteADCDigitalLegRatio sample .inductor channel ^ 2

/-- A total executable receiver.  Nonpositive calibration spans are rejected
at the affected address. -/
def decodeFiniteADCEnergySample
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source) : FiniteBinaryDrive :=
  fun channel => finiteADCEnergyIntegerAboveQuarter
    (finiteADCDigitalWordDifference sample .operational .resistor channel)
    (finiteADCDigitalWordDifference sample .spanReference .resistor channel)
    (finiteADCDigitalWordDifference sample .operational .inductor channel)
    (finiteADCDigitalWordDifference sample .spanReference .inductor channel)

theorem finiteADCDigitalWordDifference_span_pos
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    0 < finiteADCDigitalWordDifference
      (compiledADCDigitalSample source drive) .spanReference leg channel := by
  have gainEq :
      decodedFiniteAffineMeterGain
          (finiteADCClockedDecodedVoltageAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample
              source drive).adcCode
            (compileFiniteADCClockedNoisyMeteredSynchronousSample
              source drive).adcWordAt .zeroReference leg channel)
          (finiteADCClockedDecodedVoltageAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample
              source drive).adcCode
            (compileFiniteADCClockedNoisyMeteredSynchronousSample
              source drive).adcWordAt .spanReference leg channel)
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel) =
        finiteAffineMeterGainAt source.meteredSource.meterCode leg channel := by
    rw [compiledFiniteADCClockedZeroReference_exact,
      compiledFiniteADCClockedSpanReference_exact]
    exact decodedFiniteAffineMeterGain_eq_generated _ _ _ _
  have scalePos := finiteAffineMeterSenseScale_pos
    source.meteredSource.fixture.coreSource leg channel
  have stepPos := finiteADCNormalizedStep_pos
    (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive).adcCode
  have gainPos := finiteAffineMeterGain_pos
    source.meteredSource.meterCode leg channel
  unfold decodedFiniteAffineMeterGain finiteADCClockedDecodedVoltageAt
    finiteADCDecodeVoltage finiteADCDecodeNormalized at gainEq
  simp only [SIQuantity.sub_value, SIQuantity.smul_value] at gainEq
  change 0 <
    ((compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).adcWordAt .spanReference leg channel).val -
      ((compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).adcWordAt .zeroReference leg channel).val
  have castPositive :
      (0 : ℝ) <
        (((compileFiniteADCClockedNoisyMeteredSynchronousSample
              source drive).adcWordAt .spanReference leg channel).val : ℝ) -
          (((compileFiniteADCClockedNoisyMeteredSynchronousSample
              source drive).adcWordAt .zeroReference leg channel).val : ℝ) := by
    field_simp [ne_of_gt scalePos] at gainEq
    nlinarith
  exact_mod_cast castPositive

theorem finiteADCDigitalLegRatio_cast_eq
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (sample : FiniteADCDigitalSample source) (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel)
    (span_ne : finiteADCDigitalWordDifference sample .spanReference leg channel ≠ 0) :
    ((finiteADCDigitalLegRatio sample leg channel : ℚ) : ℝ) =
      digitalSampleLeg source sample leg channel := by
  have scale_ne := ne_of_gt (finiteAffineMeterSenseScale_pos
    source.meteredSource.fixture.coreSource leg channel)
  have step_ne := ne_of_gt (finiteADCNormalizedStep_pos source.adcCode)
  have span_cast_ne :
      (((finiteADCDigitalWordDifference sample .spanReference leg channel : ℤ) : ℝ)) ≠ 0 := by
    exact_mod_cast span_ne
  unfold finiteADCDigitalLegRatio digitalSampleLeg
    decodedFiniteAffineMeterNormalizedRead decodedFiniteAffineMeterGain
    finiteADCClockedDecodedVoltageAt finiteADCDecodeVoltage
    finiteADCDecodeNormalized finiteADCDigitalWordDifference
  simp only [Rat.cast_div, Rat.cast_intCast, SIQuantity.sub_value,
    SIQuantity.smul_value]
  push_cast
  field_simp

theorem finiteADCDigitalChannelEnergy_cast_eq
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (sample : FiniteADCDigitalSample source) (channel : FiniteEmbodimentChannel)
    (resistor_span_ne :
      finiteADCDigitalWordDifference sample .spanReference .resistor channel ≠ 0)
    (inductor_span_ne :
      finiteADCDigitalWordDifference sample .spanReference .inductor channel ≠ 0) :
    ((finiteADCDigitalChannelEnergy sample channel : ℚ) : ℝ) =
      digitalSampleLeg source sample .resistor channel ^ 2 +
        digitalSampleLeg source sample .inductor channel ^ 2 := by
  simp only [finiteADCDigitalChannelEnergy, Rat.cast_add, Rat.cast_pow]
  rw [finiteADCDigitalLegRatio_cast_eq source sample .resistor channel resistor_span_ne,
    finiteADCDigitalLegRatio_cast_eq source sample .inductor channel inductor_span_ne]

theorem digitalSampleLeg_energy_eq_state_channelEnergy
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (sample : FiniteADCDigitalSample source) (channel : FiniteEmbodimentChannel) :
    digitalSampleLeg source sample .resistor channel ^ 2 +
        digitalSampleLeg source sample .inductor channel ^ 2 =
      channelEnergy (digitalSampleState source sample) channel := by
  have rotated := synchronousDemodulatedPort_sub_energy_eq
    (resonantSynchronousPhaseAt source.meteredSource.fixture.coreSource channel
      ((sample.sampleTick : ℝ) • finiteSamplingClockTickPeriod
        source.meteredSource.fixture.coreSource source.clockCode))
    (digitalSampleLeg source sample .resistor channel)
    (digitalSampleLeg source sample .inductor channel) 0 0
  simpa [digitalSampleState, channelEnergy, sourcePort, targetPort,
    synchronousDemodulatedPortAt] using rotated.symm

private theorem sourcePort_error_le_hilbertError
    (candidate expected : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    |sourcePort candidate channel - sourcePort expected channel| ≤
      ‖encodeHilbert candidate - encodeHilbert expected‖ := by
  calc
    |sourcePort candidate channel - sourcePort expected channel| =
        |((encodeHilbert candidate - encodeHilbert expected) channel).im| := by
          simp [encodeHilbert, encodeComplex, encodePort, sourcePort]
    _ ≤ ‖(encodeHilbert candidate - encodeHilbert expected) channel‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ‖encodeHilbert candidate - encodeHilbert expected‖ :=
      PiLp.norm_apply_le _ _

theorem finiteADCDigitalChannelEnergy_false_lt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (channel : FiniteEmbodimentChannel)
    (bit : drive channel = false) :
    finiteADCDigitalChannelEnergy (compiledADCDigitalSample source drive) channel <
      (1 : ℚ) / 32 := by
  have resistorSpanPos := finiteADCDigitalWordDifference_span_pos
    source drive .resistor channel
  have inductorSpanPos := finiteADCDigitalWordDifference_span_pos
    source drive .inductor channel
  have endpoint := compiledFiniteADCClockedHilbertError_lt source drive
  rw [idealQuarterOperator_apply] at endpoint
  have endpoint' :
      ‖encodeHilbert
            (digitalSampleState source (compiledADCDigitalSample source drive)) -
          encodeHilbert (harmonicFlow (Real.pi / 2) (binaryDriveState drive))‖ <
        (1 : ℝ) / 8 := by
    simpa [digitalSampleState_commutes,
      finiteADCClockedDecodedHilbertOutputAt] using endpoint
  have sourceError := lt_of_le_of_lt
    (sourcePort_error_le_hilbertError
      (digitalSampleState source (compiledADCDigitalSample source drive))
      (harmonicFlow (Real.pi / 2) (binaryDriveState drive)) channel) endpoint'
  have targetError := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (digitalSampleState source (compiledADCDigitalSample source drive))
      (harmonicFlow (Real.pi / 2) (binaryDriveState drive)) channel) endpoint'
  have sourceAbs :
      |sourcePort (digitalSampleState source
          (compiledADCDigitalSample source drive)) channel| < (1 : ℝ) / 8 := by
    simpa [harmonicFlow, sourcePort, binaryDriveState, bit] using sourceError
  have targetAbs :
      |targetPort (digitalSampleState source
          (compiledADCDigitalSample source drive)) channel| < (1 : ℝ) / 8 := by
    simpa [harmonicFlow, targetPort, sourcePort, binaryDriveState, bit] using targetError
  have stateEnergyLt :
      channelEnergy
          (digitalSampleState source (compiledADCDigitalSample source drive)) channel <
        (1 : ℝ) / 32 := by
    rw [channelEnergy]
    have sourceBounds := abs_lt.mp sourceAbs
    have targetBounds := abs_lt.mp targetAbs
    nlinarith
  have legEnergyLt :
      digitalSampleLeg source (compiledADCDigitalSample source drive)
            .resistor channel ^ 2 +
          digitalSampleLeg source (compiledADCDigitalSample source drive)
            .inductor channel ^ 2 <
        (1 : ℝ) / 32 := by
    rw [digitalSampleLeg_energy_eq_state_channelEnergy]
    exact stateEnergyLt
  have castEq := finiteADCDigitalChannelEnergy_cast_eq source
    (compiledADCDigitalSample source drive) channel
    (ne_of_gt resistorSpanPos) (ne_of_gt inductorSpanPos)
  have castLt :
      ((finiteADCDigitalChannelEnergy
          (compiledADCDigitalSample source drive) channel : ℚ) : ℝ) <
        (((1 : ℚ) / 32 : ℚ) : ℝ) := by
    rw [castEq]
    norm_num
    exact legEnergyLt
  exact_mod_cast castLt

theorem finiteADCDigitalChannelEnergy_true_gt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (channel : FiniteEmbodimentChannel)
    (bit : drive channel = true) :
    (49 : ℚ) / 64 <
      finiteADCDigitalChannelEnergy (compiledADCDigitalSample source drive) channel := by
  have resistorSpanPos := finiteADCDigitalWordDifference_span_pos
    source drive .resistor channel
  have inductorSpanPos := finiteADCDigitalWordDifference_span_pos
    source drive .inductor channel
  have bounded := digitalSample_target_error_lt source drive channel
  rw [bit, if_pos rfl] at bounded
  have targetLower :
      (7 : ℝ) / 8 < targetPort
        (digitalSampleState source (compiledADCDigitalSample source drive)) channel := by
    have lower := (abs_lt.mp bounded).1
    linarith
  have stateEnergyGt :
      (49 : ℝ) / 64 <
        channelEnergy
          (digitalSampleState source (compiledADCDigitalSample source drive)) channel := by
    rw [channelEnergy]
    nlinarith [sq_nonneg
      (sourcePort (digitalSampleState source
        (compiledADCDigitalSample source drive)) channel)]
  have legEnergyGt :
      (49 : ℝ) / 64 <
        digitalSampleLeg source (compiledADCDigitalSample source drive)
            .resistor channel ^ 2 +
          digitalSampleLeg source (compiledADCDigitalSample source drive)
            .inductor channel ^ 2 := by
    rw [digitalSampleLeg_energy_eq_state_channelEnergy]
    exact stateEnergyGt
  have castEq := finiteADCDigitalChannelEnergy_cast_eq source
    (compiledADCDigitalSample source drive) channel
    (ne_of_gt resistorSpanPos) (ne_of_gt inductorSpanPos)
  have castGt :
      (((49 : ℚ) / 64 : ℚ) : ℝ) <
        ((finiteADCDigitalChannelEnergy
          (compiledADCDigitalSample source drive) channel : ℚ) : ℝ) := by
    rw [castEq]
    norm_num
    exact legEnergyGt
  exact_mod_cast castGt

/-- All 1024 independently addressed commands are recovered by the executable
integer envelope receiver. -/
theorem decodeFiniteADCEnergySample_compiled
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    decodeFiniteADCEnergySample (compiledADCDigitalSample source drive) = drive := by
  funext channel
  have resistorSpanPos := finiteADCDigitalWordDifference_span_pos
    source drive .resistor channel
  have inductorSpanPos := finiteADCDigitalWordDifference_span_pos
    source drive .inductor channel
  have correctness := finiteADCEnergyIntegerAboveQuarter_correct
    (finiteADCDigitalWordDifference (compiledADCDigitalSample source drive)
      .operational .resistor channel)
    (finiteADCDigitalWordDifference (compiledADCDigitalSample source drive)
      .spanReference .resistor channel)
    (finiteADCDigitalWordDifference (compiledADCDigitalSample source drive)
      .operational .inductor channel)
    (finiteADCDigitalWordDifference (compiledADCDigitalSample source drive)
      .spanReference .inductor channel)
    resistorSpanPos inductorSpanPos
  change finiteADCEnergyIntegerAboveQuarter
      (finiteADCDigitalWordDifference (compiledADCDigitalSample source drive)
        .operational .resistor channel)
      (finiteADCDigitalWordDifference (compiledADCDigitalSample source drive)
        .spanReference .resistor channel)
      (finiteADCDigitalWordDifference (compiledADCDigitalSample source drive)
        .operational .inductor channel)
      (finiteADCDigitalWordDifference (compiledADCDigitalSample source drive)
        .spanReference .inductor channel) = drive channel
  cases bit : drive channel
  · apply Bool.eq_false_iff.mpr
    intro receiverTrue
    have aboveQuarter := correctness.mp receiverTrue
    have belowThirtySecond := finiteADCDigitalChannelEnergy_false_lt
      source drive channel bit
    change (1 : ℚ) / 4 < finiteADCDigitalChannelEnergy
      (compiledADCDigitalSample source drive) channel at aboveQuarter
    linarith
  · apply correctness.mpr
    have aboveFortyNineSixtyFourth := finiteADCDigitalChannelEnergy_true_gt
      source drive channel bit
    change (1 : ℚ) / 4 < finiteADCDigitalChannelEnergy
      (compiledADCDigitalSample source drive) channel
    linarith

theorem compiledADCDigitalSample_injective_viaEnergyReceiver
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    Function.Injective (compiledADCDigitalSample source) :=
  Function.LeftInverse.injective (decodeFiniteADCEnergySample_compiled source)

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
