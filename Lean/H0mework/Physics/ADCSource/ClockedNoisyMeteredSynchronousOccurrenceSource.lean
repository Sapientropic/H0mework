import H0mework.Computation.ADCWire.FiniteBinaryDrive
import H0mework.Physics.Measurement.ADC
import H0mework.Physics.ADCSource.NoisyMeteredRunSource

/-!
# Finite-ADC clocked noisy-metered occurrence

This file owns the source vocabulary, regenerated settling margin, discrete
clock schedule, bounded ADC word table, independently addressed occurrence, and injective request
compiler.  It stores no decoded endpoint, tolerance verdict, receipt, or crown.
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
@[ext] structure FiniteADCClockedNoisyMeteredSynchronousFixtureSource where
  meteredSource : FiniteNoisyMeteredSynchronousFixtureSource
  adcCode : FiniteADCResolutionCode
  clockCode : FiniteSamplingClockCode

def finiteADCWholeHilbertBudget : ℝ := (1 : ℝ) / 40000

theorem finiteADCWholeHilbertBudget_pos :
    0 < finiteADCWholeHilbertBudget := by
  norm_num [finiteADCWholeHilbertBudget]

def finiteADCClockedTransientTolerance
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) : ℝ :=
  (1 : ℝ) / 8 -
    finiteHalfPowerBandNoiseBudget source.meteredSource.noiseCode -
    finiteADCWholeHilbertBudget

theorem finiteADCClockedTransientTolerance_pos
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    0 < finiteADCClockedTransientTolerance source := by
  have noise := finiteHalfPowerBandNoiseBudget_lt_sixteenth
    source.meteredSource.noiseCode
  unfold finiteADCClockedTransientTolerance finiteADCWholeHilbertBudget
  linarith

def finiteADCClockedRequiredDuration
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) : SISecond :=
  resonantSynchronousSettlingDurationFor
    (finiteADCClockedTransientTolerance source)
    source.meteredSource.fixture.coreSource
    (binaryDriveState drive) source.meteredSource.fixture.initial

theorem finiteADCClockedRequiredDuration_pos
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    0 < (finiteADCClockedRequiredDuration source drive).value :=
  resonantSynchronousSettlingDurationFor_pos
    (finiteADCClockedTransientTolerance source)
    (finiteADCClockedTransientTolerance_pos source)
    source.meteredSource.fixture.coreSource
    (binaryDriveState drive) source.meteredSource.fixture.initial

def finiteADCClockedSampleTick
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) : ℕ :=
  finiteSamplingClockTickCount source.meteredSource.fixture.coreSource
    source.clockCode (finiteADCClockedRequiredDuration source drive)

def finiteADCClockedSampleTime
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) : SISecond :=
  finiteSamplingClockSampleTime source.meteredSource.fixture.coreSource
    source.clockCode (finiteADCClockedRequiredDuration source drive)

theorem finiteADCClocked_required_le_sampleTime
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    (finiteADCClockedRequiredDuration source drive).value ≤
      (finiteADCClockedSampleTime source drive).value :=
  finiteSamplingClock_requested_le_sampleTime
    source.meteredSource.fixture.coreSource source.clockCode
    (finiteADCClockedRequiredDuration source drive)

theorem finiteADCClocked_sampleTime_lt_required_add_tick
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    (finiteADCClockedSampleTime source drive).value <
      (finiteADCClockedRequiredDuration source drive).value +
        (finiteSamplingClockTickPeriod
          source.meteredSource.fixture.coreSource source.clockCode).value :=
  finiteSamplingClock_sampleTime_lt_requested_add_tick
    source.meteredSource.fixture.coreSource source.clockCode
    (finiteADCClockedRequiredDuration source drive)
    (finiteADCClockedRequiredDuration_pos source drive).le

theorem finiteADCClockedSampleTime_pos
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    0 < (finiteADCClockedSampleTime source drive).value :=
  lt_of_lt_of_le (finiteADCClockedRequiredDuration_pos source drive)
    (finiteADCClocked_required_le_sampleTime source drive)

def finiteADCClockedRawVoltageAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (frame : FiniteAffineMeterFrame)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  finiteNoisyMeteredRawVoltageAt source.meteredSource (binaryDriveState drive)
    (finiteADCClockedSampleTime source drive) frame leg channel

def finiteADCClockedWordAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive)
    (frame : FiniteAffineMeterFrame)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : FiniteADCWord source.adcCode :=
  finiteADCEncodeVoltage source.adcCode
    (finiteAffineMeterSenseScaleAt
      source.meteredSource.fixture.coreSource leg channel)
    (finiteADCClockedRawVoltageAt source drive frame leg channel)

def finiteADCClockedDecodedVoltageAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (adcCode : FiniteADCResolutionCode)
    (wordAt : FiniteAffineMeterFrame → SynchronousSenseLeg →
      FiniteEmbodimentChannel → FiniteADCWord adcCode)
    (frame : FiniteAffineMeterFrame)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  finiteADCDecodeVoltage adcCode
    (finiteAffineMeterSenseScaleAt
      source.meteredSource.fixture.coreSource leg channel)
    (wordAt frame leg channel)

@[ext] structure FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence where
  drivenRun : FiniteResonantDrivenSeriesRLCRunOccurrence
  drive : FiniteBinaryDrive
  driveState : FiniteEmbodimentState
  initial : FiniteDimensionedSeriesRLCPortState
  noiseCode : FiniteHalfPowerBandNoiseCode
  meterCode : FiniteAffineMeterCode
  adcCode : FiniteADCResolutionCode
  clockCode : FiniteSamplingClockCode
  requestedDuration : SISecond
  clockTick : SISecond
  sampleTick : ℕ
  executedDuration : SISecond
  rawVoltageAt : FiniteAffineMeterFrame → SynchronousSenseLeg →
    FiniteEmbodimentChannel → SIVolt
  adcWordAt : FiniteAffineMeterFrame → SynchronousSenseLeg →
    FiniteEmbodimentChannel → FiniteADCWord adcCode

def compileFiniteADCClockedNoisyMeteredSynchronousSample
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) : FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence where
  drivenRun := compileFiniteResonantDrivenSeriesRLCRun
    source.meteredSource.fixture.coreSource
  drive := drive
  driveState := binaryDriveState drive
  initial := source.meteredSource.fixture.initial
  noiseCode := source.meteredSource.noiseCode
  meterCode := source.meteredSource.meterCode
  adcCode := source.adcCode
  clockCode := source.clockCode
  requestedDuration := finiteADCClockedRequiredDuration source drive
  clockTick := finiteSamplingClockTickPeriod
    source.meteredSource.fixture.coreSource source.clockCode
  sampleTick := finiteADCClockedSampleTick source drive
  executedDuration := finiteADCClockedSampleTime source drive
  rawVoltageAt := finiteADCClockedRawVoltageAt source drive
  adcWordAt := finiteADCClockedWordAt source drive

def compileFiniteADCClockedNoisyMeteredSynchronousRequest :
    FiniteADCClockedNoisyMeteredSynchronousFixtureSource × FiniteBinaryDrive →
      FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence :=
  fun request =>
    compileFiniteADCClockedNoisyMeteredSynchronousSample request.1 request.2

theorem compileFiniteADCClockedNoisyMeteredSynchronousRequest_injective :
    Function.Injective
      compileFiniteADCClockedNoisyMeteredSynchronousRequest := by
  rintro ⟨leftSource, leftDrive⟩ ⟨rightSource, rightDrive⟩ sameRun
  apply Prod.ext
  · apply FiniteADCClockedNoisyMeteredSynchronousFixtureSource.ext
    · apply FiniteNoisyMeteredSynchronousFixtureSource.ext
      · apply ResonantDrivenSynchronousFixtureSource.ext
        · apply compileFiniteResonantDrivenSeriesRLCRun_injective
          exact congrArg
            FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.drivenRun
            sameRun
        · exact congrArg
            FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.initial
            sameRun
      · exact congrArg
          FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.noiseCode
          sameRun
      · exact congrArg
          FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.meterCode
          sameRun
    · exact congrArg
        FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode sameRun
    · exact congrArg
        FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.clockCode sameRun
  · exact congrArg
      FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.drive sameRun

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
