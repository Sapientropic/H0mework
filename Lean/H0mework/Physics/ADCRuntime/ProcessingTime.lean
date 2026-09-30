import H0mework.Physics.ADCRuntime.Successor

/-!
# Source-clocked processing time after the ADC snapshot

A finite tick count is a timing parameter, not a supplied correctness proof.
The ADC words are sampled once; the old physical drive continues until the
generated switch time. Zero delay is definitionally the existing endpoint.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Units.Interface
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def finiteADCClockedSwitchTime
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (processingTicks : Nat := 0) : SISecond :=
  match processingTicks with
  | 0 => finiteADCClockedSampleTime source drive
  | ticks + 1 => finiteADCClockedSampleTime source drive +
      ((ticks + 1 : Nat) : ℝ) •
        finiteSamplingClockTickPeriod source.meteredSource.fixture.coreSource source.clockCode

@[simp] theorem finiteADCClockedSwitchTime_zero
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) :
    finiteADCClockedSwitchTime source drive 0 = finiteADCClockedSampleTime source drive := rfl

theorem finiteADCClockedSwitchTime_value
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (processingTicks : Nat) :
    (finiteADCClockedSwitchTime source drive processingTicks).value =
      (finiteADCClockedSampleTime source drive).value +
        (processingTicks : ℝ) *
          (finiteSamplingClockTickPeriod source.meteredSource.fixture.coreSource source.clockCode).value := by
  cases processingTicks <;> simp [finiteADCClockedSwitchTime]

theorem finiteADCClocked_sample_le_switchTime
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (processingTicks : Nat) :
    (finiteADCClockedSampleTime source drive).value ≤
      (finiteADCClockedSwitchTime source drive processingTicks).value := by
  rw [finiteADCClockedSwitchTime_value]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _)
    (finiteSamplingClockTickPeriod_pos source.meteredSource.fixture.coreSource source.clockCode).le)

theorem finiteADCClocked_required_le_switchTime
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (drive : FiniteBinaryDrive) (processingTicks : Nat) :
    (finiteADCClockedRequiredDuration source drive).value ≤
      (finiteADCClockedSwitchTime source drive processingTicks).value :=
  le_trans (finiteADCClocked_required_le_sampleTime source drive)
    (finiteADCClocked_sample_le_switchTime source drive processingTicks)

def finiteADCPhysicalSwitchTimeAt
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (processingTicks : Nat) : SISecond :=
  match processingTicks with
  | 0 => current.val.executedDuration
  | ticks + 1 => current.val.executedDuration + ((ticks + 1 : Nat) : ℝ) • current.val.clockTick

theorem finiteADCPhysicalSwitchTimeAt_commutes
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (processingTicks : Nat) :
    finiteADCPhysicalSwitchTimeAt current processingTicks =
      finiteADCClockedSwitchTime (finiteADCPhysicalCurrentSource current)
        current.val.drive processingTicks := by
  have timeSame := congrArg
    FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.executedDuration current.property
  have tickSame := congrArg
    FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.clockTick current.property
  cases processingTicks with
  | zero => exact timeSame
  | succ ticks =>
    change current.val.executedDuration + ((ticks + 1 : Nat) : ℝ) • current.val.clockTick = _
    rw [timeSame, tickSame]
    rfl

theorem finiteADCPhysicalSwitchTimeAt_value
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (processingTicks : Nat) :
    (finiteADCPhysicalSwitchTimeAt current processingTicks).value =
      current.val.executedDuration.value + (processingTicks : ℝ) * current.val.clockTick.value := by
  cases processingTicks <;> simp [finiteADCPhysicalSwitchTimeAt]

theorem finiteADCPhysicalSwitchTimeAt_ge_sample
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (processingTicks : Nat) :
    current.val.executedDuration.value ≤
      (finiteADCPhysicalSwitchTimeAt current processingTicks).value := by
  have sourceResult := finiteADCClocked_sample_le_switchTime
    (finiteADCPhysicalCurrentSource current) current.val.drive processingTicks
  have timeSame := congrArg
    FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.executedDuration current.property
  rw [finiteADCPhysicalSwitchTimeAt_commutes, timeSame]
  exact sourceResult

theorem finiteADCPhysicalSwitchTimeAt_strict_delay
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (processingTicks : Nat)
    (positiveTicks : 0 < processingTicks) :
    current.val.executedDuration.value <
      (finiteADCPhysicalSwitchTimeAt current processingTicks).value := by
  rw [finiteADCPhysicalSwitchTimeAt_value]
  have tickSame := congrArg
    FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.clockTick current.property
  have tickPositive : 0 < current.val.clockTick.value := by
    rw [tickSame]
    exact finiteSamplingClockTickPeriod_pos hardware.meteredSource.fixture.coreSource hardware.clockCode
  exact lt_add_of_pos_right _ (mul_pos (by exact_mod_cast positiveTicks) tickPositive)

def finiteADCPhysicalDelayedEndpoint
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (processingTicks : Nat) :
    FiniteDimensionedSeriesRLCPortState :=
  finiteADCPhysicalStateAt current (finiteADCPhysicalSwitchTimeAt current processingTicks)

@[simp] theorem finiteADCPhysicalDelayedEndpoint_zero
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) :
    finiteADCPhysicalDelayedEndpoint current 0 = finiteADCPhysicalEndpoint current := rfl

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
