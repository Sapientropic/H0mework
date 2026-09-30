import H0mework.Physics.ADCSource.ClockedNoSaturationKernel

/-!
# Source-generated finite-ADC, clocked noisy synchronous run

The calibrated per-leg ADC residual is transported through the exact
synchronous rotation, summed over all ten ports, and bounded below 1/40000.
The transient duration was regenerated with separate noise and ADC margins;
sampling at the generated ceiling clock tick then gives the final 1/8
endpoint bound and the source-generated run certificate.
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

def finiteADCClockedAnalogStateAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) : FiniteEmbodimentState :=
  fun channel => synchronousDemodulatedPortAt
    (resonantSynchronousPhaseAt source.meteredSource.fixture.coreSource channel
      (finiteADCClockedSampleTime source drive))
    (finiteADCClockedAnalogLegAt source drive .resistor channel)
    (finiteADCClockedAnalogLegAt source drive .inductor channel)

def finiteADCClockedAnalogHilbertOutputAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) : HilbertEmbodimentState :=
  encodeHilbert (finiteADCClockedAnalogStateAt source drive)

theorem synchronousDemodulatedPort_sub_energy_eq
    (angle decodedResistor decodedInductor analogResistor analogInductor : ℝ) :
    ((synchronousDemodulatedPortAt angle decodedResistor decodedInductor).1 -
        (synchronousDemodulatedPortAt angle
          analogResistor analogInductor).1) ^ 2 +
      ((synchronousDemodulatedPortAt angle decodedResistor decodedInductor).2 -
        (synchronousDemodulatedPortAt angle
          analogResistor analogInductor).2) ^ 2 =
      (decodedResistor - analogResistor) ^ 2 +
        (decodedInductor - analogInductor) ^ 2 := by
  have circle := Real.sin_sq_add_cos_sq angle
  unfold synchronousDemodulatedPortAt
  dsimp only
  calc
    _ = (Real.sin angle ^ 2 + Real.cos angle ^ 2) *
        ((decodedResistor - analogResistor) ^ 2 +
          (decodedInductor - analogInductor) ^ 2) := by ring
    _ = _ := by rw [circle]; ring

theorem compiledFiniteADCClockedADCError_channelEnergy_eq
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (channel : FiniteEmbodimentChannel) :
    channelEnergy
        (finiteADCClockedDecodedStateAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
          finiteADCClockedAnalogStateAt source drive) channel =
      (finiteADCClockedDecodedLegAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
          .resistor channel -
        finiteADCClockedAnalogLegAt source drive .resistor channel) ^ 2 +
      (finiteADCClockedDecodedLegAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
          .inductor channel -
        finiteADCClockedAnalogLegAt source drive .inductor channel) ^ 2 := by
  change
    ((synchronousDemodulatedPortAt
          (resonantSynchronousPhaseAt
            source.meteredSource.fixture.coreSource channel
            (finiteADCClockedSampleTime source drive))
          (finiteADCClockedDecodedLegAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
            .resistor channel)
          (finiteADCClockedDecodedLegAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
            .inductor channel)).1 -
      (synchronousDemodulatedPortAt
          (resonantSynchronousPhaseAt
            source.meteredSource.fixture.coreSource channel
            (finiteADCClockedSampleTime source drive))
          (finiteADCClockedAnalogLegAt source drive .resistor channel)
          (finiteADCClockedAnalogLegAt source drive .inductor channel)).1) ^ 2 +
    ((synchronousDemodulatedPortAt
          (resonantSynchronousPhaseAt
            source.meteredSource.fixture.coreSource channel
            (finiteADCClockedSampleTime source drive))
          (finiteADCClockedDecodedLegAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
            .resistor channel)
          (finiteADCClockedDecodedLegAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
            .inductor channel)).2 -
      (synchronousDemodulatedPortAt
          (resonantSynchronousPhaseAt
            source.meteredSource.fixture.coreSource channel
            (finiteADCClockedSampleTime source drive))
          (finiteADCClockedAnalogLegAt source drive .resistor channel)
          (finiteADCClockedAnalogLegAt source drive .inductor channel)).2) ^ 2 = _
  exact synchronousDemodulatedPort_sub_energy_eq _ _ _ _ _

theorem compiledFiniteADCClockedADCError_energy_le
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    energy
        (finiteADCClockedDecodedStateAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
          finiteADCClockedAnalogStateAt source drive) ≤
      20 * ((1 : ℝ) / 249750) ^ 2 := by
  unfold energy
  calc
    ∑ channel : FiniteEmbodimentChannel,
        channelEnergy
          (finiteADCClockedDecodedStateAt source
              (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
            finiteADCClockedAnalogStateAt source drive) channel =
      ∑ channel : FiniteEmbodimentChannel,
        ((finiteADCClockedDecodedLegAt source
              (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
              .resistor channel -
            finiteADCClockedAnalogLegAt source drive .resistor channel) ^ 2 +
          (finiteADCClockedDecodedLegAt source
              (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
              .inductor channel -
            finiteADCClockedAnalogLegAt source drive .inductor channel) ^ 2) := by
        apply Finset.sum_congr rfl
        intro channel _
        exact compiledFiniteADCClockedADCError_channelEnergy_eq
          source drive channel
    _ ≤ ∑ _channel : FiniteEmbodimentChannel,
        (2 * ((1 : ℝ) / 249750) ^ 2) := by
      apply Finset.sum_le_sum
      intro channel _
      have resistor := compiledFiniteADCClockedDecodedLeg_error_lt
        source drive .resistor channel
      have inductor := compiledFiniteADCClockedDecodedLeg_error_lt
        source drive .inductor channel
      have boundNonnegative : 0 ≤ (1 : ℝ) / 249750 := by norm_num
      have resistorSquare :
          (finiteADCClockedDecodedLegAt source
                (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
                .resistor channel -
              finiteADCClockedAnalogLegAt source drive .resistor channel) ^ 2 ≤
            ((1 : ℝ) / 249750) ^ 2 := (sq_le_sq).2 (by
        rw [abs_of_nonneg boundNonnegative]
        exact resistor.le)
      have inductorSquare :
          (finiteADCClockedDecodedLegAt source
                (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive)
                .inductor channel -
              finiteADCClockedAnalogLegAt source drive .inductor channel) ^ 2 ≤
            ((1 : ℝ) / 249750) ^ 2 := (sq_le_sq).2 (by
        rw [abs_of_nonneg boundNonnegative]
        exact inductor.le)
      nlinarith [resistorSquare, inductorSquare]
    _ = 20 * ((1 : ℝ) / 249750) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_num [show Fintype.card FiniteEmbodimentChannel = 10 from
        channel_cardinality]

theorem compiledFiniteADCClockedADCError_norm_lt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    ‖finiteADCClockedDecodedHilbertOutputAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
        finiteADCClockedAnalogHilbertOutputAt source drive‖ <
      finiteADCWholeHilbertBudget := by
  have energyBound := compiledFiniteADCClockedADCError_energy_le source drive
  rw [energy_eq_encodeHilbert_norm_sq] at energyBound
  have encodedDifference :
      encodeHilbert
          (finiteADCClockedDecodedStateAt source
              (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
            finiteADCClockedAnalogStateAt source drive) =
        finiteADCClockedDecodedHilbertOutputAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
          finiteADCClockedAnalogHilbertOutputAt source drive := by
    unfold finiteADCClockedDecodedHilbertOutputAt
      finiteADCClockedAnalogHilbertOutputAt
    simpa only [complexHilbertPortEquiv_apply] using
      map_sub complexHilbertPortEquiv
        (finiteADCClockedDecodedStateAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive))
        (finiteADCClockedAnalogStateAt source drive)
  rw [encodedDifference] at energyBound
  have numeric :
      20 * ((1 : ℝ) / 249750) ^ 2 <
        finiteADCWholeHilbertBudget ^ 2 := by
    norm_num [finiteADCWholeHilbertBudget]
  nlinarith [norm_nonneg
    (finiteADCClockedDecodedHilbertOutputAt source
        (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
      finiteADCClockedAnalogHilbertOutputAt source drive),
    finiteADCWholeHilbertBudget_pos]

theorem finiteADCClockedAnalogState_eq_actual_add_noise
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    finiteADCClockedAnalogStateAt source drive =
      resonantActualSynchronousStateAt
          source.meteredSource.fixture.coreSource (binaryDriveState drive)
          source.meteredSource.fixture.initial
          (finiteADCClockedSampleTime source drive) +
        finiteHalfPowerBandSynchronousNoiseStateAt
          source.meteredSource.noiseCode
          source.meteredSource.fixture.coreSource
          (finiteADCClockedSampleTime source drive) := by
  funext channel
  unfold finiteADCClockedAnalogStateAt
    resonantActualSynchronousStateAt
    finiteHalfPowerBandSynchronousNoiseStateAt
    synchronousDemodulatedPortAt
  rw [finiteADCClockedAnalogLeg_eq_actual_add_noise,
    finiteADCClockedAnalogLeg_eq_actual_add_noise]
  apply Prod.ext <;> dsimp <;> ring

theorem finiteADCClockedAnalogHilbertError_eq
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    finiteADCClockedAnalogHilbertOutputAt source drive -
        idealQuarterOperator (encodeHilbert (binaryDriveState drive)) =
      (resonantActualSynchronousHilbertOutputAt
            source.meteredSource.fixture.coreSource (binaryDriveState drive)
            source.meteredSource.fixture.initial
            (finiteADCClockedSampleTime source drive) -
          idealQuarterOperator (encodeHilbert (binaryDriveState drive))) +
        finiteHalfPowerBandSynchronousHilbertNoiseAt
          source.meteredSource.noiseCode
          source.meteredSource.fixture.coreSource
          (finiteADCClockedSampleTime source drive) := by
  unfold finiteADCClockedAnalogHilbertOutputAt
  rw [finiteADCClockedAnalogState_eq_actual_add_noise]
  rw [← complexHilbertPortEquiv_apply,
    map_add, complexHilbertPortEquiv_apply, complexHilbertPortEquiv_apply]
  unfold resonantActualSynchronousHilbertOutputAt
    finiteHalfPowerBandSynchronousHilbertNoiseAt
  abel

theorem finiteADCClockedAnalogHilbertError_lt_remaining
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    ‖finiteADCClockedAnalogHilbertOutputAt source drive -
        idealQuarterOperator (encodeHilbert (binaryDriveState drive))‖ <
      (1 : ℝ) / 8 - finiteADCWholeHilbertBudget := by
  rw [finiteADCClockedAnalogHilbertError_eq]
  have transient := resonantSynchronous_afterGeneratedDurationFor_error_lt
    (finiteADCClockedTransientTolerance source)
    (finiteADCClockedTransientTolerance_pos source)
    source.meteredSource.fixture.coreSource (binaryDriveState drive)
    source.meteredSource.fixture.initial
    (finiteADCClockedSampleTime source drive)
    (finiteADCClocked_required_le_sampleTime source drive)
  have noise := finiteHalfPowerBandSynchronousHilbertNoise_norm_le_budget
    source.meteredSource.noiseCode
    source.meteredSource.fixture.coreSource
    (finiteADCClockedSampleTime source drive)
  exact lt_of_le_of_lt (norm_add_le _ _) (by
    unfold finiteADCClockedTransientTolerance at transient
    linarith)

theorem compiledFiniteADCClockedHilbertError_lt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    ‖finiteADCClockedDecodedHilbertOutputAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
        idealQuarterOperator (encodeHilbert (binaryDriveState drive))‖ <
      (1 : ℝ) / 8 := by
  have adc := compiledFiniteADCClockedADCError_norm_lt source drive
  have analog := finiteADCClockedAnalogHilbertError_lt_remaining source drive
  have decomposition :
      finiteADCClockedDecodedHilbertOutputAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
        idealQuarterOperator (encodeHilbert (binaryDriveState drive)) =
      (finiteADCClockedDecodedHilbertOutputAt source
            (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
          finiteADCClockedAnalogHilbertOutputAt source drive) +
        (finiteADCClockedAnalogHilbertOutputAt source drive -
          idealQuarterOperator (encodeHilbert (binaryDriveState drive))) := by
    abel
  rw [decomposition]
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)

structure SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) : Prop where
  requestCompilerInjective : Function.Injective
    compileFiniteADCClockedNoisyMeteredSynchronousRequest
  totalResponse : SourceGeneratedDrivenTotalResponseAt
    (resonantDrivenCoreDimensionedSource
      source.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenFrequencyAt
      source.meteredSource.fixture.coreSource)
    (sourceOwnedResonantDrivenDriveAt
      source.meteredSource.fixture.coreSource (binaryDriveState drive))
    source.meteredSource.fixture.initial
  halfPowerBand : ∀ channel,
    SourceGeneratedExactHalfPowerBandwidthAt
      (resonantDrivenCoreDimensionedSource
        source.meteredSource.fixture.coreSource) channel
  metrology : ∀ leg channel,
    SourceGeneratedFiniteAffineVoltageMetrologyAt
      source.meteredSource.meterCode
      source.meteredSource.fixture.coreSource leg channel
  adcAlphabetFinite : Finite (FiniteADCWord source.adcCode)
  adcStepPositive : 0 < finiteADCNormalizedStep source.adcCode
  clockTickPositive :
    0 < (compileFiniteADCClockedNoisyMeteredSynchronousSample
      source drive).clockTick.value
  requestedDurationPositive :
    0 < (compileFiniteADCClockedNoisyMeteredSynchronousSample
      source drive).requestedDuration.value
  executedDurationPositive :
    0 < (compileFiniteADCClockedNoisyMeteredSynchronousSample
      source drive).executedDuration.value
  executedDurationIsClockTick :
    (compileFiniteADCClockedNoisyMeteredSynchronousSample
        source drive).executedDuration =
      ((compileFiniteADCClockedNoisyMeteredSynchronousSample
        source drive).sampleTick : ℝ) •
        (compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).clockTick
  requestedBeforeExecuted :
    (compileFiniteADCClockedNoisyMeteredSynchronousSample
        source drive).requestedDuration.value ≤
      (compileFiniteADCClockedNoisyMeteredSynchronousSample
        source drive).executedDuration.value
  clockOvershootLtTick :
    (compileFiniteADCClockedNoisyMeteredSynchronousSample
        source drive).executedDuration.value <
      (compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).requestedDuration.value +
        (compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).clockTick.value
  rawFramesGenerated :
    (compileFiniteADCClockedNoisyMeteredSynchronousSample
      source drive).rawVoltageAt = finiteADCClockedRawVoltageAt source drive
  adcWordsGenerated :
    (compileFiniteADCClockedNoisyMeteredSynchronousSample
      source drive).adcWordAt = finiteADCClockedWordAt source drive
  noActualSaturation : ∀ frame leg channel,
    (-16 : ℝ) ≤
        ((compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).rawVoltageAt frame leg channel).value /
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel).value ∧
      ((compileFiniteADCClockedNoisyMeteredSynchronousSample
          source drive).rawVoltageAt frame leg channel).value /
          (finiteAffineMeterSenseScaleAt
            source.meteredSource.fixture.coreSource leg channel).value < 16
  zeroReferenceRoundTrip : ∀ leg channel,
    type_of% (compiledFiniteADCClockedZeroReference_exact
      source drive leg channel)
  spanReferenceRoundTrip : ∀ leg channel,
    type_of% (compiledFiniteADCClockedSpanReference_exact
      source drive leg channel)
  operationalQuantizationError : ∀ leg channel,
    type_of% (compiledFiniteADCClockedOperationalRaw_normalizedError_lt
      source drive leg channel)
  wholeADCError :
    ‖finiteADCClockedDecodedHilbertOutputAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
        finiteADCClockedAnalogHilbertOutputAt source drive‖ <
      finiteADCWholeHilbertBudget
  endpointHilbertError :
    ‖finiteADCClockedDecodedHilbertOutputAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source drive) -
        idealQuarterOperator (encodeHilbert (binaryDriveState drive))‖ <
      (1 : ℝ) / 8

theorem sourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSample
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
      source drive where
  requestCompilerInjective :=
    compileFiniteADCClockedNoisyMeteredSynchronousRequest_injective
  totalResponse := everyResonantDrivenCoreSource_generatesTotalResponse
    source.meteredSource.fixture.coreSource (binaryDriveState drive)
    source.meteredSource.fixture.initial
  halfPowerBand := sourceGeneratedExactHalfPowerBandwidth
    (resonantDrivenCoreDimensionedSource
      source.meteredSource.fixture.coreSource)
  metrology := sourceGeneratedFiniteAffineVoltageMetrology
    source.meteredSource.meterCode source.meteredSource.fixture.coreSource
  adcAlphabetFinite := inferInstance
  adcStepPositive := finiteADCNormalizedStep_pos source.adcCode
  clockTickPositive := by
    exact finiteSamplingClockTickPeriod_pos
      source.meteredSource.fixture.coreSource source.clockCode
  requestedDurationPositive := finiteADCClockedRequiredDuration_pos source drive
  executedDurationPositive := finiteADCClockedSampleTime_pos source drive
  executedDurationIsClockTick := by
    rfl
  requestedBeforeExecuted := finiteADCClocked_required_le_sampleTime source drive
  clockOvershootLtTick :=
    finiteADCClocked_sampleTime_lt_required_add_tick source drive
  rawFramesGenerated := rfl
  adcWordsGenerated := rfl
  noActualSaturation := by
    intro frame leg channel
    exact finiteADCClockedRawVoltage_inRange source drive frame leg channel
  zeroReferenceRoundTrip := compiledFiniteADCClockedZeroReference_exact
    source drive
  spanReferenceRoundTrip := compiledFiniteADCClockedSpanReference_exact
    source drive
  operationalQuantizationError :=
    compiledFiniteADCClockedOperationalRaw_normalizedError_lt source drive
  wholeADCError := compiledFiniteADCClockedADCError_norm_lt source drive
  endpointHilbertError := compiledFiniteADCClockedHilbertError_lt source drive

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
