import H0mework.Computation.ADCMicro.RawMicroCorrectness
import H0mework.Physics.ADCRuntime.MicroInstallation

/-!
# Installed receiver steps on the actual physical current

The boot source installs one finite packet bound and one receiver program.
Each transition then records the current run's stored ADC words, executes that
same installed program, and joins its terminal feedback with the current run's
actual delayed endpoint.  No frame index, reconstructed orbit, future packet,
or expected output is stored in the runtime carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

/-- An actual generated current whose recorded tick fits the installed bound. -/
abbrev FiniteADCPhysicalInstalledMicroCurrent
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial) :=
  { current : FiniteADCPhysicalRuntimeCurrent hardware //
    current.val.sampleTick ≤ installation.lastTick.val }

/-- The boot occurrence enters the installed carrier by the source-generated census bound. -/
def finiteADCPhysicalInstalledMicroBoot
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (bootDrive : FiniteBinaryDrive) :
    FiniteADCPhysicalInstalledMicroCurrent installation :=
  ⟨startFiniteADCPhysicalRuntime hardware bootInitial bootDrive, by
    change finiteADCClockedSampleTick
      (finiteADCFixtureWithInitial hardware bootInitial) bootDrive ≤
        installation.lastTick.val
    rw [installation.lastTick_exact]
    exact finiteADCPhysicalBoot_sampleTick_le_runtimeMax hardware bootInitial bootDrive⟩

/-- Record only the present run's physical tick and sixty stored ADC words. -/
def finiteADCPhysicalInstalledMicroPacket
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    FiniteADCWirePacketFor hardware.adcCode
      (finiteADCPhysicalRuntimeClockBits hardware bootInitial) :=
  recordedADCWirePacket hardware current.val.val
    (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode
      current.val.property)
    (lt_of_le_of_lt current.property installation.lastTick.isLt)

@[simp] theorem finiteADCPhysicalInstalledMicroPacket_tick
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    (finiteADCPhysicalInstalledMicroPacket installation current).1.val =
      current.val.val.sampleTick := rfl

/-- The current packet is accepted and decoded from its own stored run. -/
theorem finiteADCPhysicalInstalledMicroPacket_received
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    receiveADC128WirePacket hardware installation.lastTick.val
        (finiteADCPhysicalInstalledMicroPacket installation current) =
      some current.val.val.drive := by
  have received := receive_recordedADCWirePacket_current current.val
    (lt_of_le_of_lt current.property installation.lastTick.isLt)
    installation.lastTick.val current.property
  change receiveADC128WirePacket
      (finiteADCFixtureWithInitial hardware current.val.val.initial)
      installation.lastTick.val
      (@finiteADCPhysicalInstalledMicroPacket hardware bootInitial installation current) =
        some current.val.val.drive at received
  rw [receiveADC128WirePacket_initial_independent] at received
  exact received

/-- Run the stored program itself; no compiler occurs on this packet path. -/
def finiteADCPhysicalInstalledMicroExecution
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :=
  finiteADCRawMicroExecute installation.program installation.lastTick.val
    (finiteADCPhysicalInstalledMicroPacket installation current)

theorem finiteADCPhysicalInstalledMicroExecution_received
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    finiteADCRawMicroOutput
        (finiteADCPhysicalInstalledMicroExecution installation current) =
      some (some current.val.val.drive) := by
  unfold finiteADCPhysicalInstalledMicroExecution
  rw [finiteADCRawMicroExecute_completed,
    finiteADCRawMicroPacketResult_eq_receive,
    finiteADCPhysicalInstalledMicroPacket_received]

/-- Feedback is read from the terminal stored Boolean registers. -/
def finiteADCPhysicalInstalledMicroFeedback
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) : FiniteBinaryDrive :=
  match finiteADCRawMicroOutput
      (finiteADCPhysicalInstalledMicroExecution installation current) with
  | some (some received) => fun channel => !(received channel)
  | _ => uniformBinaryDrive false

theorem finiteADCPhysicalInstalledMicroFeedback_commutes
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    finiteADCPhysicalInstalledMicroFeedback installation current =
      finiteADCPhysicalFeedback current.val := by
  unfold finiteADCPhysicalInstalledMicroFeedback
  rw [finiteADCPhysicalInstalledMicroExecution_received,
    finiteADCPhysicalFeedback_exact]

/-- Actual delayed endpoint and installed terminal feedback generate the next run. -/
def finiteADCPhysicalInstalledMicroNext
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    FiniteADCPhysicalRuntimeCurrent hardware :=
  startFiniteADCPhysicalRuntime hardware
    (finiteADCPhysicalDelayedEndpoint current.val installation.processingTicks)
    (finiteADCPhysicalInstalledMicroFeedback installation current)

theorem finiteADCPhysicalInstalledMicroNext_commutes
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    finiteADCPhysicalInstalledMicroNext installation current =
      finiteADCPhysicalDelayedSuccessor installation.processingTicks current.val := by
  unfold finiteADCPhysicalInstalledMicroNext finiteADCPhysicalDelayedSuccessor
  rw [finiteADCPhysicalInstalledMicroFeedback_commutes]

theorem finiteADCPhysicalInstalledMicroNext_no_reset
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    finiteADCPhysicalStateAt (finiteADCPhysicalInstalledMicroNext installation current) 0 =
      finiteADCPhysicalStateAt current.val
        (finiteADCPhysicalSwitchTimeAt current.val installation.processingTicks) := by
  rw [finiteADCPhysicalInstalledMicroNext_commutes]
  exact finiteADCPhysicalDelayedSuccessor_no_reset installation.processingTicks current.val

theorem finiteADCPhysicalInstalledMicroNext_sampleTick_le
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    (finiteADCPhysicalInstalledMicroNext installation current).val.sampleTick ≤
      installation.lastTick.val := by
  calc
    _ = (finiteADCPhysicalDelayedSuccessor
        installation.processingTicks current.val).val.sampleTick :=
      congrArg (fun next => next.val.sampleTick)
        (finiteADCPhysicalInstalledMicroNext_commutes installation current)
    _ ≤ finiteADCPhysicalSuccessorTickBound hardware :=
      finiteADCPhysicalDelayedSuccessor_sampleTick_le current.val installation.processingTicks
    _ ≤ finiteADCPhysicalRuntimeMaxTick hardware bootInitial := le_max_right _ _
    _ = installation.lastTick.val := installation.lastTick_exact.symm

/-- The installed transition is closed on its current carrier by the generated core bound. -/
def finiteADCPhysicalInstalledMicroStep
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial) :
    FiniteADCPhysicalInstalledMicroCurrent installation →
      FiniteADCPhysicalInstalledMicroCurrent installation :=
  fun current => ⟨finiteADCPhysicalInstalledMicroNext installation current,
    finiteADCPhysicalInstalledMicroNext_sampleTick_le installation current⟩

@[simp] theorem finiteADCPhysicalInstalledMicroStep_erase
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    (finiteADCPhysicalInstalledMicroStep installation current).val =
      finiteADCPhysicalDelayedSuccessor installation.processingTicks current.val :=
  finiteADCPhysicalInstalledMicroNext_commutes installation current

theorem finiteADCPhysicalInstalledMicroStep_semiconj
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial) :
    Function.Semiconj (fun current : FiniteADCPhysicalInstalledMicroCurrent installation =>
        current.val)
      (finiteADCPhysicalInstalledMicroStep installation)
      (finiteADCPhysicalDelayedSuccessor installation.processingTicks) :=
  finiteADCPhysicalInstalledMicroStep_erase installation

/-- Frame indexing is now only a readout of repeated actual-current transitions. -/
def finiteADCPhysicalInstalledMicroCurrentAt
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    FiniteADCPhysicalInstalledMicroCurrent installation :=
  ((finiteADCPhysicalInstalledMicroStep installation)^[frames])
    (finiteADCPhysicalInstalledMicroBoot installation bootDrive)

theorem finiteADCPhysicalInstalledMicroCurrentAt_commutes
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    (finiteADCPhysicalInstalledMicroCurrentAt installation bootDrive frames).val =
      finiteADCPhysicalDelayedCurrentAfter installation.processingTicks
        (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames := by
  exact (finiteADCPhysicalInstalledMicroStep_semiconj installation).iterate_right frames
    (finiteADCPhysicalInstalledMicroBoot installation bootDrive)

theorem finiteADCPhysicalInstalledMicroCurrentAt_frontier
    {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {bootInitial : FiniteDimensionedSeriesRLCPortState}
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (bootDrive : FiniteBinaryDrive) (frames : Nat) :
    (finiteADCPhysicalDelayedExposure installation.processingTicks
      (startFiniteADCPhysicalRuntime hardware bootInitial bootDrive) frames).frontier =
        [(finiteADCPhysicalInstalledMicroCurrentAt installation bootDrive frames).val] := by
  rw [finiteADCPhysicalDelayedExposure_frontier,
    finiteADCPhysicalInstalledMicroCurrentAt_commutes]

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
