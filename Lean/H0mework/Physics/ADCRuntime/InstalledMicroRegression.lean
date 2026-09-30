import H0mework.Physics.ADCRuntime.MicroReceiver
import H0mework.Computation.ADCMicro.RawMicroFiniteCarrier

/-! # Direct controls for a fixed installation consuming actual physical currents -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Regression

open Netlist.Dissipative.Dimensioned.Driven.Interface
open Netlist.Dissipative.Dimensioned.Driven.Producer
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {bootInitial : FiniteDimensionedSeriesRLCPortState}

noncomputable section

theorem installed_counter_override_is_rejected
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (replacement : QuantizedWord (finiteADCPhysicalRuntimeClockBits hardware bootInitial))
    (different : replacement.val ≠ finiteADCPhysicalRuntimeMaxTick hardware bootInitial) :
    installation.lastTick ≠ replacement := by
  intro same
  exact different ((installation.lastTick_eq_iff replacement).mp same)

theorem installed_current_has_fresh_micro_boot
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    (finiteADCRawProgramPacketCall installation.program installation.lastTick.val
      (finiteADCPhysicalInstalledMicroPacket installation current)).state.values = #[] ∧
    finiteADCRawMicroOutput (finiteADCRawMicroBootWithProgram installation.program
      installation.lastTick.val (finiteADCPhysicalInstalledMicroPacket installation current)) = none :=
  ⟨by simp [finiteADCRawProgramPacketCall, aigOwnedProgressBoot,
      aigExecutionEmpty, AIGExecutionPrefix.values], rfl⟩

theorem installed_current_cannot_finish_early
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation)
    (ticks : Nat) (early : ticks < installation.processingTicks) :
    finiteADCRawMicroOutput
      (finiteADCRawMicroAfterWithProgram installation.program installation.lastTick.val
        (finiteADCPhysicalInstalledMicroPacket installation current) ticks) = none := by
  apply finiteADCRawMicro_not_completed_earlyWithProgram_of_accepted
    installation.program installation.lastTick.val _ current.val.val.drive _ ticks early
  rw [finiteADCRawMicroPacketResult_eq_receive,
    finiteADCPhysicalInstalledMicroPacket_received]

theorem installed_step_is_not_read_only
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    finiteADCPhysicalInstalledMicroStep installation current ≠ current := by
  intro unchanged
  have changed := congrArg
    (fun next : FiniteADCPhysicalRuntimeCurrent hardware => next.val.drive .sourceBound)
    (finiteADCPhysicalInstalledMicroNext_commutes installation current)
  rw [finiteADCPhysicalDelayedSuccessor_feedback_exact] at changed
  change (finiteADCPhysicalInstalledMicroStep installation current).val.val.drive .sourceBound =
    !(current.val.val.drive .sourceBound) at changed
  rw [unchanged] at changed
  cases actual : current.val.val.drive .sourceBound <;> simp [actual] at changed

theorem installed_next_reenters_the_same_receiver
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation) :
    let next := finiteADCPhysicalInstalledMicroStep installation current
    next.val.val.sampleTick ≤ installation.lastTick.val ∧
      finiteADCRawMicroOutput
        (finiteADCPhysicalInstalledMicroExecution installation next) =
          some (some next.val.val.drive) :=
  ⟨(finiteADCPhysicalInstalledMicroStep installation current).property,
    finiteADCPhysicalInstalledMicroExecution_received installation _⟩

theorem installed_program_does_not_reuse_another_currents_answer
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (left right : FiniteADCPhysicalInstalledMicroCurrent installation)
    (different : left.val.val.drive ≠ right.val.val.drive) :
    finiteADCRawMicroOutput (finiteADCPhysicalInstalledMicroExecution installation left) ≠
      finiteADCRawMicroOutput (finiteADCPhysicalInstalledMicroExecution installation right) := by
  rw [finiteADCPhysicalInstalledMicroExecution_received,
    finiteADCPhysicalInstalledMicroExecution_received]
  exact fun same => different (Option.some.inj (Option.some.inj same))

theorem installed_actual_next_cannot_replace_the_switch_endpoint
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (current : FiniteADCPhysicalInstalledMicroCurrent installation)
    (replacement : FiniteADCPhysicalRuntimeCurrent hardware)
    (different : finiteADCPhysicalStateAt replacement 0 ≠
      finiteADCPhysicalDelayedEndpoint current.val installation.processingTicks) :
    replacement ≠ (finiteADCPhysicalInstalledMicroStep installation current).val := by
  intro same
  apply different
  rw [same]
  exact finiteADCPhysicalInstalledMicroNext_no_reset installation current

theorem installed_controller_remains_finite
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial) :
    Finite (FiniteADCRawMicroStateWithProgram installation.program installation.lastTick.val) :=
  finiteADCRawMicroStateWithProgram_finite _ _

end

end Netlist.Dissipative.Dimensioned.Driven.Regression
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
