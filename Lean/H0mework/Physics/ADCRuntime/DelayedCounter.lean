import H0mework.Physics.ADCRuntime.DelayedSuccessor
import H0mework.Physics.ADCRuntime.FixedCounter

/-!
# Uniform counters survive finite post-snapshot processing

The completed old drive remains within its generated envelope while processing.
Its actual switch endpoint therefore has the same successor tick bound.
The original boot-sized ADC format covers all delayed frames; the switch-time
counter additionally includes the configured processing ticks.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Units.Interface
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision

noncomputable section

theorem finiteADCPhysicalDelayedEndpoint_commutes_generated
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (processingTicks : Nat) :
    finiteADCPhysicalDelayedEndpoint current processingTicks =
      finiteADCGeneratedPhysicalEndpointAt (finiteADCPhysicalCurrentSource current)
        current.val.drive processingTicks := by
  unfold finiteADCPhysicalDelayedEndpoint
  rw [finiteADCPhysicalStateAt_commutes, finiteADCPhysicalSwitchTimeAt_commutes]
  rfl

theorem finiteADCPhysicalDelayedSuccessor_sampleTick_le
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCPhysicalRuntimeCurrent hardware) (processingTicks : Nat) :
    (finiteADCPhysicalDelayedSuccessor processingTicks current).val.sampleTick ≤
      finiteADCPhysicalSuccessorTickBound hardware := by
  change finiteADCClockedSampleTick
    (finiteADCFixtureWithInitial hardware
      (finiteADCPhysicalDelayedEndpoint current processingTicks))
    (finiteADCPhysicalFeedback current) ≤ finiteADCPhysicalSuccessorTickBound hardware
  have bounded := finiteADCGeneratedEndpoint_nextSampleTick_le
    (finiteADCPhysicalCurrentSource current) current.val.drive
    (finiteADCPhysicalFeedback current) processingTicks
  rw [← finiteADCPhysicalDelayedEndpoint_commutes_generated current processingTicks] at bounded
  simpa [finiteADCPhysicalCurrentSource, finiteADCPhysicalSuccessorTickBound,
    finiteADCPhysicalSuccessorDurationBound, finiteADCClockedTransientTolerance,
    finiteADCFixtureWithInitial] using bounded

theorem finiteADCPhysicalDelayedIterate_sampleTick_le_runtimeMax
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    (finiteADCPhysicalDelayedCurrentAfter processingTicks
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames).val.sampleTick ≤
      finiteADCPhysicalRuntimeMaxTick hardware bootInitial := by
  cases frames with
  | zero => exact finiteADCPhysicalBoot_sampleTick_le_runtimeMax hardware bootInitial bootDrive
  | succ frames =>
      rw [finiteADCPhysicalDelayedCurrentAfter_succ]
      exact le_trans (finiteADCPhysicalDelayedSuccessor_sampleTick_le _ processingTicks)
        (le_max_right _ _)

theorem finiteADCPhysicalDelayedIterate_sampleTick_lt_fixedCapacity
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    (finiteADCPhysicalDelayedCurrentAfter processingTicks
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames).val.sampleTick <
      2 ^ finiteADCPhysicalRuntimeClockBits hardware bootInitial :=
  lt_of_le_of_lt
    (finiteADCPhysicalDelayedIterate_sampleTick_le_runtimeMax
      hardware bootInitial bootDrive processingTicks frames)
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _)

/-- Sampling data keep the original fixed format even when processing takes longer. -/
def finiteADCPhysicalDelayedPacketAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    FiniteADCPhysicalRuntimePacket hardware bootInitial :=
  let current := finiteADCPhysicalDelayedCurrentAfter processingTicks
    (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames
  recordedADCWirePacket hardware current.val
    (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode current.property)
    (finiteADCPhysicalDelayedIterate_sampleTick_lt_fixedCapacity
      hardware bootInitial bootDrive processingTicks frames)

theorem finiteADCPhysicalDelayedPacketAt_received
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    receiveADC128WirePacket hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
        (finiteADCPhysicalDelayedPacketAt hardware bootInitial bootDrive processingTicks frames) =
      some (finiteADCPhysicalDelayedCurrentAfter processingTicks
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames).val.drive := by
  let current := finiteADCPhysicalDelayedCurrentAfter processingTicks
    (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames
  have received := receive_recordedADCWirePacket_current current
    (finiteADCPhysicalDelayedIterate_sampleTick_lt_fixedCapacity
      hardware bootInitial bootDrive processingTicks frames)
    (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
    (finiteADCPhysicalDelayedIterate_sampleTick_le_runtimeMax
      hardware bootInitial bootDrive processingTicks frames)
  change receiveADC128WirePacket (finiteADCFixtureWithInitial hardware current.val.initial)
      (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
      (finiteADCPhysicalDelayedPacketAt hardware bootInitial bootDrive processingTicks frames) =
        some current.val.drive at received
  rw [receiveADC128WirePacket_initial_independent] at received
  exact received

/-- The fixed receiver consumes the stored sample, not the later switch state. -/
def finiteADCPhysicalDelayedFixedFeedbackAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) : FiniteBinaryDrive :=
  match receiveADC128WirePacket hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
      (finiteADCPhysicalDelayedPacketAt hardware bootInitial bootDrive processingTicks frames) with
  | some received => fun channel => !(received channel)
  | none => uniformBinaryDrive false

theorem finiteADCPhysicalDelayedFixedFeedbackAt_commutes
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    finiteADCPhysicalDelayedFixedFeedbackAt hardware bootInitial bootDrive processingTicks frames =
      finiteADCPhysicalFeedback (finiteADCPhysicalDelayedCurrentAfter processingTicks
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames) := by
  unfold finiteADCPhysicalDelayedFixedFeedbackAt
  rw [finiteADCPhysicalDelayedPacketAt_received, finiteADCPhysicalFeedback_exact]

/-- This transition uses both the fixed packet's decision and the actual delayed endpoint. -/
def finiteADCPhysicalDelayedFixedNextAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    FiniteADCPhysicalRuntimeCurrent hardware :=
  let current := finiteADCPhysicalDelayedCurrentAfter processingTicks
    (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames
  startFiniteADCPhysicalRuntime hardware (finiteADCPhysicalDelayedEndpoint current processingTicks)
    (finiteADCPhysicalDelayedFixedFeedbackAt hardware bootInitial bootDrive processingTicks frames)

theorem finiteADCPhysicalDelayedFixedNextAt_commutes
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    finiteADCPhysicalDelayedFixedNextAt hardware bootInitial bootDrive processingTicks frames =
      finiteADCPhysicalDelayedCurrentAfter processingTicks
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) (frames + 1) := by
  unfold finiteADCPhysicalDelayedFixedNextAt
  rw [finiteADCPhysicalDelayedFixedFeedbackAt_commutes, finiteADCPhysicalDelayedCurrentAfter_succ]
  rfl

theorem finiteADCPhysicalDelayedFixedNextAt_no_reset
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    let current := finiteADCPhysicalDelayedCurrentAfter processingTicks
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames
    finiteADCPhysicalStateAt
        (finiteADCPhysicalDelayedFixedNextAt hardware bootInitial bootDrive processingTicks frames) 0 =
      finiteADCPhysicalStateAt current (finiteADCPhysicalSwitchTimeAt current processingTicks) := by
  dsimp only
  rw [finiteADCPhysicalDelayedFixedNextAt_commutes, finiteADCPhysicalDelayedCurrentAfter_succ]
  exact finiteADCPhysicalDelayedSuccessor_no_reset processingTicks _

def finiteADCPhysicalDelayedSwitchCounterBits
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) (processingTicks : Nat) : Nat :=
  Nat.log 2 (finiteADCPhysicalRuntimeMaxTick hardware bootInitial + processingTicks) + 1

/-- The same fixed switch-counter width covers every physical frame after the chosen boot. -/
def finiteADCPhysicalDelayedSwitchTickAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    QuantizedWord (finiteADCPhysicalDelayedSwitchCounterBits hardware bootInitial processingTicks) :=
  ⟨(finiteADCPhysicalDelayedCurrentAfter processingTicks
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames).val.sampleTick +
        processingTicks,
    lt_of_le_of_lt
      (Nat.add_le_add_right
        (finiteADCPhysicalDelayedIterate_sampleTick_le_runtimeMax
          hardware bootInitial bootDrive processingTicks frames) processingTicks)
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _)⟩

theorem finiteADCPhysicalDelayedSwitchTickAt_time_commutes
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (processingTicks frames : Nat) :
    let current := finiteADCPhysicalDelayedCurrentAfter processingTicks
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames
    (finiteADCPhysicalSwitchTimeAt current processingTicks).value =
      ((finiteADCPhysicalDelayedSwitchTickAt
        hardware bootInitial bootDrive processingTicks frames).val : ℝ) *
        (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource
          hardware.clockCode).value := by
  dsimp only
  let current := finiteADCPhysicalDelayedCurrentAfter processingTicks
    (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames
  have timeSame := congrArg
    FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.executedDuration current.property
  have tickSame := congrArg
    FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.sampleTick current.property
  have periodSame := congrArg
    FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.clockTick current.property
  change current.val.sampleTick = finiteADCClockedSampleTick
    (finiteADCPhysicalCurrentSource current) current.val.drive at tickSame
  rw [finiteADCPhysicalSwitchTimeAt_value, timeSame, periodSame]
  change (finiteADCClockedSampleTime (finiteADCPhysicalCurrentSource current) current.val.drive).value +
      (processingTicks : ℝ) * _ =
    ((current.val.sampleTick + processingTicks : Nat) : ℝ) * _
  unfold finiteADCClockedSampleTime finiteSamplingClockSampleTime
  simp only [SIQuantity.smul_value, Nat.cast_add, add_mul]
  rw [tickSame]
  rfl

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
