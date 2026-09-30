import H0mework.Physics.ADCRuntime.InstalledMicroCurrent
import H0mework.Computation.ADCMicro.RawMicroTiming

/-!
# Source-generated receiver microclocks drive the physical successor

The recorded packet starts the actual one-declaration receiver execution. Its
graph-generated total count fixes the processing interval, while its cached
terminal output generates the feedback command. The old drive continues until
that interval ends, and the actual switch state becomes the next initial.
This is a new delayed occurrence, not equality with the earlier eight-stage
occurrence. Physical transistor propagation is not supplied by a gate count.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Units.Interface
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

/-- One fixed receiver schedule is installed with the boot-sized packet format. -/
def finiteADCPhysicalMicroProcessingTicks
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) : Nat :=
  finiteADCRawMicroTicks hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)

theorem finiteADCPhysicalMicroProcessingTicks_pos
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) :
    0 < finiteADCPhysicalMicroProcessingTicks hardware bootInitial :=
  finiteADCRawMicroTicks_pos hardware (finiteADCPhysicalRuntimeClockBits hardware bootInitial)

/-- Frame indexing observes the actual current-driven installed transition. -/
def finiteADCPhysicalMicroCurrentAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :=
  finiteADCPhysicalInstalledMicroCurrentAt
    (compileFiniteADCPhysicalMicroInstallation hardware bootInitial) bootDrive frames

theorem finiteADCPhysicalMicroCurrentAt_erase
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    (finiteADCPhysicalMicroCurrentAt hardware bootInitial bootDrive frames).val =
      finiteADCPhysicalDelayedCurrentAfter (finiteADCPhysicalMicroProcessingTicks hardware bootInitial)
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames := by
  unfold finiteADCPhysicalMicroCurrentAt
  rw [finiteADCPhysicalInstalledMicroCurrentAt_commutes,
    FiniteADCPhysicalMicroInstallation.processingTicks_eq]
  rfl

/-- The packet records the sample before processing begins, not the later switch state. -/
def finiteADCPhysicalMicroPacketAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    FiniteADCPhysicalRuntimePacket hardware bootInitial :=
  finiteADCPhysicalInstalledMicroPacket
    (compileFiniteADCPhysicalMicroInstallation hardware bootInitial)
    (finiteADCPhysicalMicroCurrentAt hardware bootInitial bootDrive frames)

theorem finiteADCPhysicalMicroPacketAt_eq_delayed
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    finiteADCPhysicalMicroPacketAt hardware bootInitial bootDrive frames =
      finiteADCPhysicalDelayedPacketAt hardware bootInitial bootDrive
        (finiteADCPhysicalMicroProcessingTicks hardware bootInitial) frames := by
  simp only [finiteADCPhysicalMicroPacketAt, finiteADCPhysicalInstalledMicroPacket,
    finiteADCPhysicalMicroCurrentAt_erase, finiteADCPhysicalDelayedPacketAt]

/-- Actual partial-cache steps, not the old macro receiver or its final result. -/
def finiteADCPhysicalMicroExecutionAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :=
  finiteADCPhysicalInstalledMicroExecution
    (compileFiniteADCPhysicalMicroInstallation hardware bootInitial)
    (finiteADCPhysicalMicroCurrentAt hardware bootInitial bootDrive frames)

/-- The executable code face consumes this same physical snapshot and its
installed width/deadline. No substitute source or synthetic packet enters. -/
theorem finiteADCPhysicalMicroExecutionAt_code_restriction
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    finiteADCPhysicalMicroExecutionAt hardware bootInitial bootDrive frames =
      finiteADCRawMicroAfterFor hardware.adcCode
        (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
        (finiteADCPhysicalMicroPacketAt hardware bootInitial bootDrive frames)
        (finiteADCRawMicroTicksFor hardware.adcCode
          (finiteADCPhysicalRuntimeClockBits hardware bootInitial)) :=
  finiteADCRawMicroExecuteFor_eq_afterFor hardware.adcCode _ _

theorem finiteADCPhysicalMicroExecutionAt_received
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    finiteADCRawMicroOutput
        (finiteADCPhysicalMicroExecutionAt hardware bootInitial bootDrive frames) =
      some (some (finiteADCPhysicalDelayedCurrentAfter
        (finiteADCPhysicalMicroProcessingTicks hardware bootInitial)
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames).val.drive) := by
  have received := finiteADCPhysicalInstalledMicroExecution_received
    (compileFiniteADCPhysicalMicroInstallation hardware bootInitial)
    (finiteADCPhysicalMicroCurrentAt hardware bootInitial bootDrive frames)
  rw [finiteADCPhysicalMicroCurrentAt_erase] at received
  exact received

/-- Actual source packets cannot finish before the installed full graph count. -/
theorem finiteADCPhysicalMicroExecutionAt_not_completed_early
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames ticks : Nat)
    (early : ticks < finiteADCPhysicalMicroProcessingTicks hardware bootInitial) :
    finiteADCRawMicroOutput
      (finiteADCRawMicroAfter hardware (finiteADCPhysicalRuntimeMaxTick hardware bootInitial)
        (finiteADCPhysicalMicroPacketAt hardware bootInitial bootDrive frames) ticks) = none := by
  rw [finiteADCPhysicalMicroPacketAt_eq_delayed]
  exact finiteADCRawMicro_not_completed_early_of_accepted hardware _ _ _
    (finiteADCPhysicalDelayedPacketAt_received hardware bootInitial bootDrive
      (finiteADCPhysicalMicroProcessingTicks hardware bootInitial) frames) ticks early

/-- The feedback command is read directly from the microcontroller's output register. -/
def finiteADCPhysicalMicroFeedbackAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) : FiniteBinaryDrive :=
  match finiteADCRawMicroOutput
      (finiteADCPhysicalMicroExecutionAt hardware bootInitial bootDrive frames) with
  | some (some received) => fun channel => !(received channel)
  | _ => uniformBinaryDrive false

theorem finiteADCPhysicalMicroFeedbackAt_commutes
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    finiteADCPhysicalMicroFeedbackAt hardware bootInitial bootDrive frames =
      finiteADCPhysicalDelayedFixedFeedbackAt hardware bootInitial bootDrive
        (finiteADCPhysicalMicroProcessingTicks hardware bootInitial) frames := by
  unfold finiteADCPhysicalMicroFeedbackAt finiteADCPhysicalDelayedFixedFeedbackAt
  rw [finiteADCPhysicalMicroExecutionAt_received, finiteADCPhysicalDelayedPacketAt_received]

/-- Generated processing time and generated feedback meet at the same actual switch endpoint. -/
def finiteADCPhysicalMicroNextAt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) : FiniteADCPhysicalRuntimeCurrent hardware :=
  (finiteADCPhysicalInstalledMicroStep
    (compileFiniteADCPhysicalMicroInstallation hardware bootInitial)
    (finiteADCPhysicalMicroCurrentAt hardware bootInitial bootDrive frames)).val

theorem finiteADCPhysicalMicroNextAt_commutes
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    finiteADCPhysicalMicroNextAt hardware bootInitial bootDrive frames =
      finiteADCPhysicalDelayedCurrentAfter (finiteADCPhysicalMicroProcessingTicks hardware bootInitial)
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) (frames + 1) := by
  unfold finiteADCPhysicalMicroNextAt
  rw [finiteADCPhysicalInstalledMicroStep_erase, finiteADCPhysicalMicroCurrentAt_erase,
    FiniteADCPhysicalMicroInstallation.processingTicks_eq]
  exact (finiteADCPhysicalDelayedCurrentAfter_succ
    (finiteADCPhysicalMicroProcessingTicks hardware bootInitial)
    (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames).symm

theorem finiteADCPhysicalMicroNextAt_no_reset
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    let processingTicks := finiteADCPhysicalMicroProcessingTicks hardware bootInitial
    let current := finiteADCPhysicalDelayedCurrentAfter processingTicks
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames
    finiteADCPhysicalStateAt (finiteADCPhysicalMicroNextAt hardware bootInitial bootDrive frames) 0 =
      finiteADCPhysicalStateAt current (finiteADCPhysicalSwitchTimeAt current processingTicks) := by
  dsimp only
  rw [finiteADCPhysicalMicroNextAt_commutes, finiteADCPhysicalDelayedCurrentAfter_succ]
  exact finiteADCPhysicalDelayedSuccessor_no_reset
    (finiteADCPhysicalMicroProcessingTicks hardware bootInitial) _

theorem finiteADCPhysicalMicroNextAt_frontier
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    (finiteADCPhysicalDelayedExposure (finiteADCPhysicalMicroProcessingTicks hardware bootInitial)
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) (frames + 1)).frontier =
        [finiteADCPhysicalMicroNextAt hardware bootInitial bootDrive frames] := by
  rw [finiteADCPhysicalDelayedExposure_frontier, finiteADCPhysicalMicroNextAt_commutes]

theorem finiteADCPhysicalMicroNextAt_regenerates_receipt
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    let next := finiteADCPhysicalMicroNextAt hardware bootInitial bootDrive frames
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
      (finiteADCPhysicalCurrentSource next) next.val.drive :=
  finiteADCPhysicalCurrent_generates_receipt _

theorem finiteADCPhysicalMicro_sample_counter_covers
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    (finiteADCPhysicalDelayedCurrentAfter (finiteADCPhysicalMicroProcessingTicks hardware bootInitial)
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames).val.sampleTick <
        2 ^ finiteADCPhysicalRuntimeClockBits hardware bootInitial :=
  finiteADCPhysicalDelayedIterate_sampleTick_lt_fixedCapacity hardware bootInitial bootDrive
    (finiteADCPhysicalMicroProcessingTicks hardware bootInitial) frames

theorem finiteADCPhysicalMicro_switch_time_commutes
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    let processingTicks := finiteADCPhysicalMicroProcessingTicks hardware bootInitial
    let current := finiteADCPhysicalDelayedCurrentAfter processingTicks
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames
    (finiteADCPhysicalSwitchTimeAt current processingTicks).value =
      ((finiteADCPhysicalDelayedSwitchTickAt hardware bootInitial bootDrive
        processingTicks frames).val : ℝ) *
        (finiteSamplingClockTickPeriod hardware.meteredSource.fixture.coreSource
          hardware.clockCode).value :=
  finiteADCPhysicalDelayedSwitchTickAt_time_commutes hardware bootInitial bootDrive
    (finiteADCPhysicalMicroProcessingTicks hardware bootInitial) frames

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
