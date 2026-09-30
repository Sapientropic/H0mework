import H0mework.Physics.ADCSource.ClockedNoisyMeteredSynchronousOccurrenceSource

/-!
# Finite-ADC no-saturation and calibrated-leg kernel

For every independently addressed binary command, the source-generated settling time bounds
the analog response, every zero/span/operational frame is proved inside the
literal finite ADC range, zero/span words round-trip exactly, and the decoded
operational leg receives a strict calibrated quantization bound.
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
namespace Netlist
namespace Dissipative
namespace Dimensioned
namespace Driven
namespace Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

theorem finiteAffineMeterGain_le_two
    (code : FiniteAffineMeterCode)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteAffineMeterGainAt code leg channel ≤ 2 := by
  cases gainCode : (code leg channel).1 <;>
    norm_num [finiteAffineMeterGainAt, ternaryOffsetValue, gainCode]

theorem finiteAffineMeterOffsetNormalized_abs_le_one
    (code : FiniteAffineMeterCode)
    (source : ResonantDrivenCoreSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    |(finiteAffineMeterOffsetAt code source leg channel).value /
        (finiteAffineMeterSenseScaleAt source leg channel).value| ≤ 1 := by
  have scaleNonzero := ne_of_gt
    (finiteAffineMeterSenseScale_pos source leg channel)
  unfold finiteAffineMeterOffsetAt
  simp only [SIQuantity.smul_value]
  rw [mul_div_cancel_right₀ _ scaleNonzero]
  cases offsetCode : (code leg channel).2 <;>
    norm_num [ternaryOffsetValue, offsetCode]

theorem channelEnergy_le_energy
    (state : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    channelEnergy state channel ≤ energy state := by
  unfold energy
  apply Finset.single_le_sum
  · intro other _
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact Finset.mem_univ channel

theorem resonantNormalizedError_abs_le_hilbertNorm
    (source : ResonantDrivenCoreSource)
    (input : FiniteEmbodimentState)
    (initial : FiniteDimensionedSeriesRLCPortState)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    |(match leg with
      | .resistor => resonantNormalizedResistorErrorAt
          source input initial channel physicalTime
      | .inductor => resonantNormalizedInductorErrorAt
          source input initial channel physicalTime)| ≤
      ‖encodeHilbert (resonantSynchronousStateErrorAt
        source input initial physicalTime)‖ := by
  have channelLe := channelEnergy_le_energy
    (resonantSynchronousStateErrorAt source input initial physicalTime) channel
  rw [resonantSynchronousStateError_channelEnergy_eq,
    energy_eq_encodeHilbert_norm_sq] at channelLe
  cases leg
  · have squareLe :
        resonantNormalizedResistorErrorAt
            source input initial channel physicalTime ^ 2 ≤
          ‖encodeHilbert (resonantSynchronousStateErrorAt
            source input initial physicalTime)‖ ^ 2 := by
      linarith [sq_nonneg (resonantNormalizedInductorErrorAt
        source input initial channel physicalTime)]
    have absolute := (sq_le_sq).mp squareLe
    simpa [abs_of_nonneg (norm_nonneg _)] using absolute
  · have squareLe :
        resonantNormalizedInductorErrorAt
            source input initial channel physicalTime ^ 2 ≤
          ‖encodeHilbert (resonantSynchronousStateErrorAt
            source input initial physicalTime)‖ ^ 2 := by
      linarith [sq_nonneg (resonantNormalizedResistorErrorAt
        source input initial channel physicalTime)]
    have absolute := (sq_le_sq).mp squareLe
    simpa [abs_of_nonneg (norm_nonneg _)] using absolute

theorem resonantPeriodicBinaryDriveLeg_abs_le_one
    (source : ResonantDrivenCoreSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) :
    |(match leg with
      | .resistor => resonantPeriodicNormalizedResistorAt source
          (binaryDriveState drive) channel physicalTime
      | .inductor => resonantPeriodicNormalizedInductorAt source
          (binaryDriveState drive) channel physicalTime)| ≤ 1 := by
  cases hbit : drive channel <;> cases leg
  · simp [resonantPeriodicNormalizedResistor_eq,
      binaryDriveState, sourcePort, targetPort, hbit]
  · simp [resonantPeriodicNormalizedInductor_eq,
      binaryDriveState, sourcePort, targetPort, hbit]
  · simpa [resonantPeriodicNormalizedResistor_eq,
      binaryDriveState, sourcePort, targetPort, hbit] using
      Real.abs_sin_le_one
        (resonantSynchronousPhaseAt source channel physicalTime)
  · simpa [resonantPeriodicNormalizedInductor_eq,
      binaryDriveState, sourcePort, targetPort, hbit] using
      Real.abs_cos_le_one
        (resonantSynchronousPhaseAt source channel physicalTime)

theorem finiteADCClockedActualLeg_abs_lt_two
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    |(match leg with
      | .resistor => resonantActualNormalizedResistorAt
          source.meteredSource.fixture.coreSource (binaryDriveState drive)
          source.meteredSource.fixture.initial channel
          (finiteADCClockedSampleTime source drive)
      | .inductor => resonantActualNormalizedInductorAt
          source.meteredSource.fixture.coreSource (binaryDriveState drive)
          source.meteredSource.fixture.initial channel
          (finiteADCClockedSampleTime source drive))| < 2 := by
  have transient := resonantSynchronous_afterGeneratedDurationFor_error_lt
    (finiteADCClockedTransientTolerance source)
    (finiteADCClockedTransientTolerance_pos source)
    source.meteredSource.fixture.coreSource (binaryDriveState drive)
    source.meteredSource.fixture.initial
    (finiteADCClockedSampleTime source drive)
    (finiteADCClocked_required_le_sampleTime source drive)
  rw [resonantActualSynchronousHilbertError_eq_stateError] at transient
  have errorLe := resonantNormalizedError_abs_le_hilbertNorm
    source.meteredSource.fixture.coreSource (binaryDriveState drive)
    source.meteredSource.fixture.initial leg channel
    (finiteADCClockedSampleTime source drive)
  have toleranceLtOne : finiteADCClockedTransientTolerance source < 1 := by
    have noiseNonnegative := finiteHalfPowerBandNoiseBudget_nonneg
      source.meteredSource.noiseCode
    have adcPositive := finiteADCWholeHilbertBudget_pos
    unfold finiteADCClockedTransientTolerance
    linarith
  have errorLtOne := lt_of_le_of_lt errorLe
    (lt_trans transient toleranceLtOne)
  have periodicLe := resonantPeriodicBinaryDriveLeg_abs_le_one
    source.meteredSource.fixture.coreSource drive leg channel
    (finiteADCClockedSampleTime source drive)
  cases leg
  · simp only at errorLtOne periodicLe ⊢
    rw [show resonantActualNormalizedResistorAt
          source.meteredSource.fixture.coreSource (binaryDriveState drive)
          source.meteredSource.fixture.initial channel
          (finiteADCClockedSampleTime source drive) =
        resonantPeriodicNormalizedResistorAt
            source.meteredSource.fixture.coreSource (binaryDriveState drive)
            channel (finiteADCClockedSampleTime source drive) +
          resonantNormalizedResistorErrorAt
            source.meteredSource.fixture.coreSource (binaryDriveState drive)
            source.meteredSource.fixture.initial channel
            (finiteADCClockedSampleTime source drive) by
          unfold resonantNormalizedResistorErrorAt
          ring]
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)
  · simp only at errorLtOne periodicLe ⊢
    rw [show resonantActualNormalizedInductorAt
          source.meteredSource.fixture.coreSource (binaryDriveState drive)
          source.meteredSource.fixture.initial channel
          (finiteADCClockedSampleTime source drive) =
        resonantPeriodicNormalizedInductorAt
            source.meteredSource.fixture.coreSource (binaryDriveState drive)
            channel (finiteADCClockedSampleTime source drive) +
          resonantNormalizedInductorErrorAt
            source.meteredSource.fixture.coreSource (binaryDriveState drive)
            source.meteredSource.fixture.initial channel
            (finiteADCClockedSampleTime source drive) by
          unfold resonantNormalizedInductorErrorAt
          ring]
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)

def finiteADCClockedAnalogLegAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  (finiteNoisyMeteredOperationalVoltageAt source.meteredSource
      (binaryDriveState drive) leg channel
      (finiteADCClockedSampleTime source drive)).value /
    (finiteAffineMeterSenseScaleAt
      source.meteredSource.fixture.coreSource leg channel).value

theorem finiteADCClockedAnalogLeg_eq_actual_add_noise
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteADCClockedAnalogLegAt source drive leg channel =
      (match leg with
      | .resistor => resonantActualNormalizedResistorAt
          source.meteredSource.fixture.coreSource (binaryDriveState drive)
          source.meteredSource.fixture.initial channel
          (finiteADCClockedSampleTime source drive)
      | .inductor => resonantActualNormalizedInductorAt
          source.meteredSource.fixture.coreSource (binaryDriveState drive)
          source.meteredSource.fixture.initial channel
          (finiteADCClockedSampleTime source drive)) +
        finiteHalfPowerBandNoiseAt source.meteredSource.noiseCode leg
          source.meteredSource.fixture.coreSource channel
          (finiteADCClockedSampleTime source drive) := by
  cases leg
  · unfold finiteADCClockedAnalogLegAt
      finiteNoisyMeteredOperationalVoltageAt
      finiteNoisyMeteredActualSenseVoltageAt
      finiteNoisyMeteredPhysicalNoiseAt
      finiteAffineMeterSenseScaleAt resonantActualNormalizedResistorAt
    simp only [SIQuantity.add_value, SIQuantity.smul_value]
    field_simp [source.meteredSource.fixture.coreSource.2.voltageScale_ne]
  · unfold finiteADCClockedAnalogLegAt
      finiteNoisyMeteredOperationalVoltageAt
      finiteNoisyMeteredActualSenseVoltageAt
      finiteNoisyMeteredPhysicalNoiseAt
      finiteAffineMeterSenseScaleAt resonantActualNormalizedInductorAt
    simp only [SIQuantity.add_value, SIQuantity.smul_value]
    field_simp [ne_of_gt (resonantInductorOutputScale_pos
      (resonantDrivenCoreDimensionedSource
        source.meteredSource.fixture.coreSource) channel)]

theorem finiteADCClockedAnalogLeg_abs_lt_three
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    |finiteADCClockedAnalogLegAt source drive leg channel| < 3 := by
  rw [finiteADCClockedAnalogLeg_eq_actual_add_noise]
  have actual := finiteADCClockedActualLeg_abs_lt_two
    source drive leg channel
  have noiseEnvelope := finiteHalfPowerBandNoise_abs_le_envelope
    source.meteredSource.noiseCode leg
    source.meteredSource.fixture.coreSource channel
    (finiteADCClockedSampleTime source drive)
  have envelopeLe := finiteHalfPowerBandLegEnvelope_le_sixQuantum
    source.meteredSource.noiseCode leg channel
  have noiseLtOne :
      |finiteHalfPowerBandNoiseAt source.meteredSource.noiseCode leg
        source.meteredSource.fixture.coreSource channel
        (finiteADCClockedSampleTime source drive)| < 1 := by
    calc
      _ ≤ finiteHalfPowerBandLegEnvelopeAt
          source.meteredSource.noiseCode leg channel := noiseEnvelope
      _ ≤ 6 * finiteHalfPowerBandNoiseQuantum := envelopeLe
      _ < 1 := by norm_num [finiteHalfPowerBandNoiseQuantum]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)

theorem finiteADCClockedOperationalRawNormalized_abs_lt_seven
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    |(finiteADCClockedRawVoltageAt source drive .operational leg channel).value /
        (finiteAffineMeterSenseScaleAt
          source.meteredSource.fixture.coreSource leg channel).value| < 7 := by
  have scaleNonzero := ne_of_gt (finiteAffineMeterSenseScale_pos
    source.meteredSource.fixture.coreSource leg channel)
  have gainPositive := finiteAffineMeterGain_pos
    source.meteredSource.meterCode leg channel
  have gainLe := finiteAffineMeterGain_le_two
    source.meteredSource.meterCode leg channel
  have analogLt := finiteADCClockedAnalogLeg_abs_lt_three
    source drive leg channel
  have offsetLe := finiteAffineMeterOffsetNormalized_abs_le_one
    source.meteredSource.meterCode source.meteredSource.fixture.coreSource
    leg channel
  have normalizedRaw :
      (finiteADCClockedRawVoltageAt source drive .operational leg channel).value /
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel).value =
        finiteAffineMeterGainAt source.meteredSource.meterCode leg channel *
            finiteADCClockedAnalogLegAt source drive leg channel +
          (finiteAffineMeterOffsetAt source.meteredSource.meterCode
              source.meteredSource.fixture.coreSource leg channel).value /
            (finiteAffineMeterSenseScaleAt
              source.meteredSource.fixture.coreSource leg channel).value := by
    unfold finiteADCClockedRawVoltageAt finiteNoisyMeteredRawVoltageAt
      finiteAffineMeterRawAt finiteADCClockedAnalogLegAt
    simp only [SIQuantity.add_value, SIQuantity.smul_value]
    field_simp [scaleNonzero]
  rw [normalizedRaw]
  apply lt_of_le_of_lt (abs_add_le _ _)
  rw [abs_mul, abs_of_pos gainPositive]
  have productLt :
      finiteAffineMeterGainAt source.meteredSource.meterCode leg channel *
          |finiteADCClockedAnalogLegAt source drive leg channel| < 6 := by
    calc
      _ ≤ 2 * |finiteADCClockedAnalogLegAt source drive leg channel| :=
        mul_le_mul_of_nonneg_right gainLe (abs_nonneg _)
      _ < 2 * 3 := mul_lt_mul_of_pos_left analogLt (by norm_num)
      _ = 6 := by norm_num
  linarith

theorem finiteADCClockedRawVoltage_inRange
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (frame : FiniteAffineMeterFrame)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    (-16 : ℝ) ≤
        (finiteADCClockedRawVoltageAt source drive frame leg channel).value /
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel).value ∧
      (finiteADCClockedRawVoltageAt source drive frame leg channel).value /
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel).value < 16 := by
  have scaleNonzero := ne_of_gt (finiteAffineMeterSenseScale_pos
    source.meteredSource.fixture.coreSource leg channel)
  cases frame
  · have normalized :
        (finiteADCClockedRawVoltageAt source drive .zeroReference leg channel).value /
            (finiteAffineMeterSenseScaleAt
              source.meteredSource.fixture.coreSource leg channel).value =
          ternaryOffsetValue (source.meteredSource.meterCode leg channel).2 /
            1000 := by
      unfold finiteADCClockedRawVoltageAt finiteNoisyMeteredRawVoltageAt
        finiteAffineMeterZeroReferenceAt finiteAffineMeterRawAt
        finiteAffineMeterOffsetAt
      simp only [SIQuantity.add_value, SIQuantity.smul_value,
        SIQuantity.zero_value, mul_zero, zero_add]
      field_simp [scaleNonzero]
    rw [normalized]
    cases (source.meteredSource.meterCode leg channel).2 <;>
      norm_num [ternaryOffsetValue]
  · have normalized :
        (finiteADCClockedRawVoltageAt source drive .spanReference leg channel).value /
            (finiteAffineMeterSenseScaleAt
              source.meteredSource.fixture.coreSource leg channel).value =
          1 + ternaryOffsetValue
                (source.meteredSource.meterCode leg channel).1 / 1000 +
            ternaryOffsetValue
                (source.meteredSource.meterCode leg channel).2 / 1000 := by
      unfold finiteADCClockedRawVoltageAt finiteNoisyMeteredRawVoltageAt
        finiteAffineMeterSpanReferenceAt finiteAffineMeterRawAt
        finiteAffineMeterOffsetAt finiteAffineMeterGainAt
      simp only [SIQuantity.add_value, SIQuantity.smul_value]
      field_simp [scaleNonzero]
    rw [normalized]
    cases (source.meteredSource.meterCode leg channel).1 <;>
      cases (source.meteredSource.meterCode leg channel).2 <;>
      norm_num [ternaryOffsetValue]
  · have bounded := finiteADCClockedOperationalRawNormalized_abs_lt_seven
      source drive leg channel
    constructor
    · exact le_trans (by norm_num : (-16 : ℝ) ≤ -7)
        (neg_le_of_abs_le (le_of_lt bounded))
    · exact lt_trans (lt_of_abs_lt bounded) (by norm_num)

def finiteADCClockedDecodedLegAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (run : FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  decodedFiniteAffineMeterNormalizedRead
    (finiteADCClockedDecodedVoltageAt source run.adcCode run.adcWordAt
      .zeroReference leg channel)
    (finiteADCClockedDecodedVoltageAt source run.adcCode run.adcWordAt
      .spanReference leg channel)
    (finiteADCClockedDecodedVoltageAt source run.adcCode run.adcWordAt
      .operational leg channel)
    (finiteAffineMeterSenseScaleAt
      source.meteredSource.fixture.coreSource leg channel)

def finiteADCClockedDecodedStateAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (run : FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence) :
    FiniteEmbodimentState :=
  fun channel => synchronousDemodulatedPortAt
    (resonantSynchronousPhaseAt source.meteredSource.fixture.coreSource channel
      run.executedDuration)
    (finiteADCClockedDecodedLegAt source run .resistor channel)
    (finiteADCClockedDecodedLegAt source run .inductor channel)

def finiteADCClockedDecodedHilbertOutputAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (run : FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence) :
    HilbertEmbodimentState :=
  encodeHilbert (finiteADCClockedDecodedStateAt source run)

theorem finiteAffineMeterGain_ge_nineNineNineThousandths
    (code : FiniteAffineMeterCode)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    (999 : ℝ) / 1000 ≤ finiteAffineMeterGainAt code leg channel := by
  cases gainCode : (code leg channel).1 <;>
    norm_num [finiteAffineMeterGainAt, ternaryOffsetValue, gainCode]

theorem compiledFiniteADCClockedZeroReference_exact
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteADCClockedDecodedVoltageAt source
        (compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).adcCode
        (compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).adcWordAt .zeroReference leg channel =
      finiteAffineMeterZeroReferenceAt source.meteredSource.meterCode
        source.meteredSource.fixture.coreSource leg channel := by
  simpa [finiteADCClockedDecodedVoltageAt,
    compileFiniteADCClockedNoisyMeteredSynchronousSample,
    finiteADCClockedWordAt, finiteADCClockedRawVoltageAt,
    finiteNoisyMeteredRawVoltageAt] using
    finiteADCDecodeEncodeMeterZeroReference_exact source.adcCode
      source.meteredSource.meterCode
      source.meteredSource.fixture.coreSource leg channel

theorem compiledFiniteADCClockedSpanReference_exact
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteADCClockedDecodedVoltageAt source
        (compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).adcCode
        (compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).adcWordAt .spanReference leg channel =
      finiteAffineMeterSpanReferenceAt source.meteredSource.meterCode
        source.meteredSource.fixture.coreSource leg channel := by
  simpa [finiteADCClockedDecodedVoltageAt,
    compileFiniteADCClockedNoisyMeteredSynchronousSample,
    finiteADCClockedWordAt, finiteADCClockedRawVoltageAt,
    finiteNoisyMeteredRawVoltageAt] using
    finiteADCDecodeEncodeMeterSpanReference_exact source.adcCode
      source.meteredSource.meterCode
      source.meteredSource.fixture.coreSource leg channel

theorem compiledFiniteADCClockedOperationalRaw_normalizedError_lt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    |(finiteADCClockedDecodedVoltageAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample
            source drive).adcCode
          (compileFiniteADCClockedNoisyMeteredSynchronousSample
            source drive).adcWordAt .operational leg channel).value /
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel).value -
        (finiteADCClockedRawVoltageAt source drive .operational leg channel).value /
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel).value| <
      finiteADCNormalizedStep source.adcCode := by
  have range := finiteADCClockedRawVoltage_inRange
    source drive .operational leg channel
  simpa [finiteADCClockedDecodedVoltageAt,
    compileFiniteADCClockedNoisyMeteredSynchronousSample,
    finiteADCClockedWordAt] using
    finiteADCDecodeEncodeVoltage_normalizedError_lt source.adcCode
      (finiteAffineMeterSenseScaleAt
        source.meteredSource.fixture.coreSource leg channel)
      (finiteADCClockedRawVoltageAt source drive .operational leg channel)
      (finiteAffineMeterSenseScale_pos
        source.meteredSource.fixture.coreSource leg channel)
      range.1 range.2

theorem compiledFiniteADCClockedDecodedLeg_sub_analog_eq
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteADCClockedDecodedLegAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
          leg channel -
        finiteADCClockedAnalogLegAt source drive leg channel =
      (((finiteADCClockedDecodedVoltageAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample
              source drive).adcCode
            (compileFiniteADCClockedNoisyMeteredSynchronousSample
              source drive).adcWordAt .operational leg channel).value /
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel).value) -
        (finiteADCClockedRawVoltageAt source drive .operational leg channel).value /
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel).value) /
        finiteAffineMeterGainAt source.meteredSource.meterCode leg channel := by
  rw [finiteADCClockedDecodedLegAt]
  rw [compiledFiniteADCClockedZeroReference_exact,
    compiledFiniteADCClockedSpanReference_exact]
  have analogExact := decodedFiniteAffineMeterNormalizedRead_eq_physical
    source.meteredSource.meterCode
    source.meteredSource.fixture.coreSource leg channel
    (finiteNoisyMeteredOperationalVoltageAt source.meteredSource
      (binaryDriveState drive) leg channel
      (finiteADCClockedSampleTime source drive))
  change _ - finiteADCClockedAnalogLegAt source drive leg channel = _
  unfold finiteADCClockedAnalogLegAt
  rw [← analogExact]
  unfold decodedFiniteAffineMeterNormalizedRead
  rw [decodedFiniteAffineMeterGain_eq_generated]
  have scaleNonzero := ne_of_gt (finiteAffineMeterSenseScale_pos
    source.meteredSource.fixture.coreSource leg channel)
  have gainNonzero := ne_of_gt (finiteAffineMeterGain_pos
    source.meteredSource.meterCode leg channel)
  unfold finiteADCClockedRawVoltageAt
    finiteNoisyMeteredRawVoltageAt
  simp only [SIQuantity.sub_value]
  field_simp [scaleNonzero, gainNonzero]
  ring

theorem compiledFiniteADCClockedDecodedLeg_error_lt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    |finiteADCClockedDecodedLegAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
          leg channel -
        finiteADCClockedAnalogLegAt source drive leg channel| <
      (1 : ℝ) / 249750 := by
  rw [compiledFiniteADCClockedDecodedLeg_sub_analog_eq, abs_div,
    abs_of_pos (finiteAffineMeterGain_pos
      source.meteredSource.meterCode leg channel)]
  apply (div_lt_iff₀ (finiteAffineMeterGain_pos
    source.meteredSource.meterCode leg channel)).2
  have rawError := compiledFiniteADCClockedOperationalRaw_normalizedError_lt
    source drive leg channel
  have stepLe := finiteADCNormalizedStep_le_coarse source.adcCode
  calc
    _ < (1 : ℝ) / 250000 := lt_of_lt_of_le rawError stepLe
    _ ≤ (1 / 249750) *
        finiteAffineMeterGainAt source.meteredSource.meterCode leg channel := by
      have gainLower := finiteAffineMeterGain_ge_nineNineNineThousandths
        source.meteredSource.meterCode leg channel
      nlinarith

end

end Producer
end Driven
end Dimensioned
end Dissipative
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid
