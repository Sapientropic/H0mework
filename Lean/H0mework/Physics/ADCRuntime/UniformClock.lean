import H0mework.Physics.ADCRuntime.SuccessorEnvelope

/-!
# One finite clock width for an endpoint-seeded ADC runtime

The chosen boot initial contributes one finite command census.  Every later
initial is an actual completed endpoint and is covered by the core-only
successor envelope.  Their maximum therefore generates one counter width for
the boot frame and every finite iterate of the physical successor.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface
open Netlist.Dissipative.Dimensioned.Driven.Interface
open Physical.Units.Interface

noncomputable section

def finiteADCPhysicalSuccessorDurationBound
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) : SISecond :=
  let core := hardware.meteredSource.fixture.coreSource
  ⟨positiveExponentialSettlingTime
    (drivenCommonPhysicalDampingRate (finiteADCCorePhysicalSource core))
    (finiteADCSuccessorEnvelopeBound core)
    (finiteADCClockedTransientTolerance hardware)⟩

theorem finiteADCPhysicalSuccessorDurationBound_pos
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    0 < (finiteADCPhysicalSuccessorDurationBound hardware).value := by
  unfold finiteADCPhysicalSuccessorDurationBound
  dsimp only
  exact positiveExponentialSettlingTime_pos
    (drivenCommonPhysicalDampingRate_pos _)
    (Real.sqrt_nonneg _)
    (finiteADCClockedTransientTolerance_pos hardware)

theorem finiteADCGeneratedEndpoint_nextRequiredDuration_le
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive nextDrive : FiniteBinaryDrive) (processingTicks : Nat := 0) :
    (finiteADCClockedRequiredDuration
      (finiteADCFixtureWithInitial source
        (finiteADCGeneratedPhysicalEndpointAt
          source drive processingTicks)) nextDrive).value ≤
      (finiteADCPhysicalSuccessorDurationBound source).value := by
  have envelopeLe := finiteADCGeneratedEndpoint_nextEnvelope_le
    source drive nextDrive processingTicks
  dsimp only at envelopeLe
  have tolerancePos := finiteADCClockedTransientTolerance_pos source
  have dampingPos := drivenCommonPhysicalDampingRate_pos
    (finiteADCCorePhysicalSource source.meteredSource.fixture.coreSource)
  unfold finiteADCClockedRequiredDuration
    resonantSynchronousSettlingDurationFor
    finiteADCPhysicalSuccessorDurationBound
    positiveExponentialSettlingTime
  dsimp only
  simp only [finiteADCFixtureWithInitial, finiteADCClockedTransientTolerance]
  apply div_le_div_of_nonneg_right _ dampingPos.le
  have ratioLe := div_le_div_of_nonneg_right envelopeLe tolerancePos.le
  unfold finiteADCClockedTransientTolerance at ratioLe
  linarith

def finiteADCPhysicalSuccessorTickBound
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) : Nat :=
  finiteSamplingClockTickCount hardware.meteredSource.fixture.coreSource
    hardware.clockCode (finiteADCPhysicalSuccessorDurationBound hardware)

theorem finiteADCGeneratedEndpoint_nextSampleTick_le
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive nextDrive : FiniteBinaryDrive) (processingTicks : Nat := 0) :
    finiteADCClockedSampleTick
        (finiteADCFixtureWithInitial source
          (finiteADCGeneratedPhysicalEndpointAt
            source drive processingTicks)) nextDrive ≤
      finiteADCPhysicalSuccessorTickBound source := by
  have durationLe := finiteADCGeneratedEndpoint_nextRequiredDuration_le
    source drive nextDrive processingTicks
  have tickPos := finiteSamplingClockTickPeriod_pos
    source.meteredSource.fixture.coreSource source.clockCode
  unfold finiteADCClockedSampleTick finiteADCPhysicalSuccessorTickBound
    finiteSamplingClockTickCount
  simp only [finiteADCFixtureWithInitial]
  exact Nat.ceil_mono
    (div_le_div_of_nonneg_right durationLe tickPos.le)

theorem finiteADCPhysicalEndpoint_commutes_generated
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    finiteADCPhysicalEndpoint current =
      finiteADCGeneratedPhysicalEndpointAt
        (finiteADCPhysicalCurrentSource current) current.val.drive := by
  unfold finiteADCPhysicalEndpoint
  rw [finiteADCPhysicalStateAt_commutes]
  unfold finiteADCGeneratedPhysicalEndpointAt
  have timeExact := congrArg
    FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.executedDuration
    current.property
  rw [timeExact]
  rfl

theorem finiteADCPhysicalEndpoint_nextSampleTick_le
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware)
    (nextDrive : FiniteBinaryDrive) :
    finiteADCClockedSampleTick
        (finiteADCFixtureWithInitial hardware
          (finiteADCPhysicalEndpoint current)) nextDrive ≤
      finiteADCPhysicalSuccessorTickBound hardware := by
  have bounded := finiteADCGeneratedEndpoint_nextSampleTick_le
    (finiteADCPhysicalCurrentSource current) current.val.drive nextDrive
  rw [← finiteADCPhysicalEndpoint_commutes_generated current] at bounded
  simpa [finiteADCPhysicalCurrentSource,
    finiteADCPhysicalSuccessorTickBound,
    finiteADCPhysicalSuccessorDurationBound,
    finiteADCClockedTransientTolerance,
    finiteADCFixtureWithInitial] using bounded

theorem finiteADCPhysicalSuccessor_sampleTick_le
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    (finiteADCPhysicalSuccessor current).val.sampleTick ≤
      finiteADCPhysicalSuccessorTickBound hardware := by
  change
    finiteADCClockedSampleTick
        (finiteADCFixtureWithInitial hardware (finiteADCPhysicalEndpoint current))
        (finiteADCPhysicalFeedback current) ≤
      finiteADCPhysicalSuccessorTickBound hardware
  exact finiteADCPhysicalEndpoint_nextSampleTick_le
    current (finiteADCPhysicalFeedback current)

/-- The boot source must be named: arbitrary unbounded boot initials cannot
share a finite counter width. -/
def finiteADCPhysicalRuntimeMaxTick
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) : Nat :=
  max
    (maxADCSampleTick (finiteADCFixtureWithInitial hardware bootInitial))
    (finiteADCPhysicalSuccessorTickBound hardware)

def finiteADCPhysicalRuntimeClockBits
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) : Nat :=
  Nat.log 2 (finiteADCPhysicalRuntimeMaxTick hardware bootInitial) + 1

theorem finiteADCPhysicalBoot_sampleTick_le_runtimeMax
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (drive : FiniteBinaryDrive) :
    finiteADCClockedSampleTick
        (finiteADCFixtureWithInitial hardware bootInitial) drive ≤
      finiteADCPhysicalRuntimeMaxTick hardware bootInitial :=
  le_trans
    (adcSampleTick_le_max
      (finiteADCFixtureWithInitial hardware bootInitial) drive)
    (le_max_left _ _)

theorem finiteADCPhysicalSuccessor_sampleTick_le_runtimeMax
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    (finiteADCPhysicalSuccessor current).val.sampleTick ≤
      finiteADCPhysicalRuntimeMaxTick hardware bootInitial :=
  le_trans (finiteADCPhysicalSuccessor_sampleTick_le current) (le_max_right _ _)

theorem finiteADCPhysicalIterate_sampleTick_le_runtimeMax
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (iteration : Nat) :
    ((finiteADCPhysicalSuccessor^[iteration])
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive)).val.sampleTick ≤
      finiteADCPhysicalRuntimeMaxTick hardware bootInitial := by
  cases iteration with
  | zero =>
      change
        finiteADCClockedSampleTick
            (finiteADCFixtureWithInitial hardware bootInitial) bootDrive ≤
          finiteADCPhysicalRuntimeMaxTick hardware bootInitial
      exact finiteADCPhysicalBoot_sampleTick_le_runtimeMax
        hardware bootInitial bootDrive
  | succ iteration =>
      rw [Function.iterate_succ_apply']
      exact finiteADCPhysicalSuccessor_sampleTick_le_runtimeMax bootInitial _

theorem finiteADCPhysicalIterate_sampleTick_lt_fixedCapacity
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (iteration : Nat) :
    ((finiteADCPhysicalSuccessor^[iteration])
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive)).val.sampleTick <
      2 ^ finiteADCPhysicalRuntimeClockBits hardware bootInitial := by
  exact lt_of_le_of_lt
    (finiteADCPhysicalIterate_sampleTick_le_runtimeMax
      hardware bootInitial bootDrive iteration)
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2)
      (finiteADCPhysicalRuntimeMaxTick hardware bootInitial))

end


end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
