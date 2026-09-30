import H0mework.Physics.ADCRuntime.LoadedEnvelopeBound
import H0mework.Physics.ADCRuntime.LoadedReceiverSample

/-! # A fresh loaded-loop sample has a source-only finite counter bound

The bound is computed before any receiver graph or counter width exists.
Its only data are the physical core, noise/clock codes and gate technology.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def loadedReceiverSampleDurationBound (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (technology : AIGCellTechnology) : SISecond :=
  let core := hardware.meteredSource.fixture.coreSource
  ⟨positiveExponentialSettlingTime (drivenCommonPhysicalDampingRate (finiteADCCorePhysicalSource core))
    (loadedReceiverEnvelopeBound core technology) (finiteADCClockedTransientTolerance hardware)⟩

theorem loadedReceiverSampleDurationBound_pos (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (technology : AIGCellTechnology) : 0 < (loadedReceiverSampleDurationBound hardware technology).value :=
  positiveExponentialSettlingTime_pos (drivenCommonPhysicalDampingRate_pos _)
    (Real.sqrt_nonneg _) (finiteADCClockedTransientTolerance_pos hardware)

def loadedReceiverSampleTickBound (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (technology : AIGCellTechnology) : Nat :=
  finiteSamplingClockTickCount hardware.meteredSource.fixture.coreSource hardware.clockCode
    (loadedReceiverSampleDurationBound hardware technology)

theorem loadedReceiverSampleTickBound_initial_independent
    (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) (technology : AIGCellTechnology)
    (initial : FiniteDimensionedSeriesRLCPortState) :
    loadedReceiverSampleTickBound (finiteADCFixtureWithInitial hardware initial) technology =
      loadedReceiverSampleTickBound hardware technology := rfl

namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (current : FiniteADCWholeJointCurrent hardware clockMax technology)

theorem commonRecoveryTarget_requiredDuration_le (drive : FiniteBinaryDrive) :
    (finiteADCClockedRequiredDuration (finiteADCFixtureWithInitial hardware
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2) drive).value ≤
        (loadedReceiverSampleDurationBound hardware technology).value := by
  have envelope := commonRecoveryTarget_envelope_le downstreamTechnology downstreamGraph current drive
  have tolerance := finiteADCClockedTransientTolerance_pos hardware
  have damping := drivenCommonPhysicalDampingRate_pos
    (finiteADCCorePhysicalSource hardware.meteredSource.fixture.coreSource)
  unfold finiteADCClockedRequiredDuration resonantSynchronousSettlingDurationFor
    loadedReceiverSampleDurationBound positiveExponentialSettlingTime
  dsimp only
  simp only [finiteADCFixtureWithInitial, finiteADCClockedTransientTolerance]
  apply div_le_div_of_nonneg_right _ damping.le
  have ratio := div_le_div_of_nonneg_right envelope tolerance.le
  unfold finiteADCClockedTransientTolerance at ratio
  linarith

theorem commonRecoveryTarget_sampleTick_le (drive : FiniteBinaryDrive) :
    finiteADCClockedSampleTick (finiteADCFixtureWithInitial hardware
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2) drive ≤
        loadedReceiverSampleTickBound hardware technology := by
  have duration := commonRecoveryTarget_requiredDuration_le downstreamTechnology downstreamGraph current drive
  have period := finiteSamplingClockTickPeriod_pos hardware.meteredSource.fixture.coreSource hardware.clockCode
  unfold finiteADCClockedSampleTick loadedReceiverSampleTickBound finiteSamplingClockTickCount
  simp only [finiteADCFixtureWithInitial]
  exact Nat.ceil_mono (div_le_div_of_nonneg_right duration period.le)

theorem loadedReceiverFreshSample_sampleTick_le :
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.sampleTick ≤
      loadedReceiverSampleTickBound hardware technology := by
  rw [loadedReceiverFreshSample_eq]
  exact commonRecoveryTarget_sampleTick_le downstreamTechnology downstreamGraph current _

theorem loadedReceiverFreshSample_sampleTick_lt_source_capacity :
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.sampleTick <
      2 ^ (Nat.log 2 (loadedReceiverSampleTickBound hardware technology) + 1) :=
  lt_of_le_of_lt (loadedReceiverFreshSample_sampleTick_le downstreamTechnology downstreamGraph current)
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _)

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
