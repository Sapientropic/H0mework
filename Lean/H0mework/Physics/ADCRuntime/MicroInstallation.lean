import H0mework.Computation.ADCMicro.RawMicroMachine
import H0mework.Physics.ADCRuntime.DelayedCounter

/-!
# Source-only physical microreceiver installation

Immutable hardware and the named boot initial determine one counter capacity,
one exact maximum-tick word, and one stored receiver program. Installation takes
no drive, frame, packet, acceptance bit, or target output. Later actual currents
can consume this data without replaying boot or recompiling the program.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.LivingCortex.FinitePrecision

noncomputable section

/-- The already generated uniform bound fits its boot-fixed log/power capacity. -/
theorem finiteADCPhysicalMicroInstallation_capacity
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) :
    finiteADCPhysicalRuntimeMaxTick hardware bootInitial <
      2 ^ finiteADCPhysicalRuntimeClockBits hardware bootInitial :=
  Nat.lt_pow_succ_log_self (by decide : 1 < 2) _

/-- The counter word and program are both indexed by the same boot source. -/
structure FiniteADCPhysicalMicroInstallation
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) where
  lastTick : QuantizedWord (finiteADCPhysicalRuntimeClockBits hardware bootInitial)
  lastTick_exact : lastTick.val = finiteADCPhysicalRuntimeMaxTick hardware bootInitial
  program : FiniteADCRawInstalledProgram hardware.adcCode
    (finiteADCPhysicalRuntimeClockBits hardware bootInitial)

/-- Compile only immutable hardware and the named initial condition into installed data. -/
def compileFiniteADCPhysicalMicroInstallation
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (bootInitial : FiniteDimensionedSeriesRLCPortState) :
    FiniteADCPhysicalMicroInstallation hardware bootInitial where
  lastTick := ⟨finiteADCPhysicalRuntimeMaxTick hardware bootInitial,
    finiteADCPhysicalMicroInstallation_capacity hardware bootInitial⟩
  lastTick_exact := rfl
  program := compileFiniteADCRawInstalledProgram hardware.adcCode
    (finiteADCPhysicalRuntimeClockBits hardware bootInitial)

namespace FiniteADCPhysicalMicroInstallation

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {bootInitial : FiniteDimensionedSeriesRLCPortState}

/-- Extensionality stays abstract so proof comparison never unfolds large circuit compilers. -/
@[ext] theorem ext (left right : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (sameCounter : left.lastTick = right.lastTick) (sameProgram : left.program = right.program) :
    left = right := by
  rcases left with ⟨leftCounter, leftExact, leftProgram⟩
  rcases right with ⟨rightCounter, rightExact, rightProgram⟩
  cases sameCounter
  cases sameProgram
  rfl

/-- Every valid installation is exactly the one generated from its source. -/
theorem eq_compile (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial) :
    installation = compileFiniteADCPhysicalMicroInstallation hardware bootInitial := by
  apply ext
  · apply Fin.ext
    exact installation.lastTick_exact
  · exact installation.program.eq_compile

theorem unique (left right : FiniteADCPhysicalMicroInstallation hardware bootInitial) :
    left = right :=
  left.eq_compile.trans right.eq_compile.symm

/-- An alternative bounded word is the installed counter exactly when it has the source value. -/
theorem lastTick_eq_iff
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial)
    (counter : QuantizedWord (finiteADCPhysicalRuntimeClockBits hardware bootInitial)) :
    installation.lastTick = counter ↔
      counter.val = finiteADCPhysicalRuntimeMaxTick hardware bootInitial := by
  constructor
  · intro same
    rw [← same]
    exact installation.lastTick_exact
  · intro same
    apply Fin.ext
    exact installation.lastTick_exact.trans same.symm

theorem program_eq_compile
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial) :
    installation.program = compileFiniteADCRawInstalledProgram hardware.adcCode
      (finiteADCPhysicalRuntimeClockBits hardware bootInitial) :=
  installation.program.eq_compile

/-- The processing interval reads the stored graphs, without another compilation. -/
def processingTicks (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial) : Nat :=
  finiteADCRawMicroTicksWithProgram installation.program

theorem processingTicks_eq
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial) :
    installation.processingTicks = finiteADCRawMicroTicksFor hardware.adcCode
      (finiteADCPhysicalRuntimeClockBits hardware bootInitial) :=
  finiteADCRawMicroTicksWithProgram_eq installation.program

theorem processingTicks_pos
    (installation : FiniteADCPhysicalMicroInstallation hardware bootInitial) :
    0 < installation.processingTicks := by
  unfold processingTicks finiteADCRawMicroTicksWithProgram
  have positive := installation.program.packetGraph.aig.hzero
  omega

end FiniteADCPhysicalMicroInstallation

end

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
