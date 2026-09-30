import H0mework.Physics.ADCRuntime.LoadedClockBound

/-! # Boot and every loaded successor share a clock capacity chosen before the receiver graph -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

def loadedReceiverInstalledMaxTick (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (technology : AIGCellTechnology) (initial : FiniteDimensionedSeriesRLCPortState) : Nat :=
  max (maxADCSampleTick (finiteADCFixtureWithInitial hardware initial)) (loadedReceiverSampleTickBound hardware technology)

def loadedReceiverInstalledClockBits (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (technology : AIGCellTechnology) (initial : FiniteDimensionedSeriesRLCPortState) : Nat :=
  Nat.log 2 (loadedReceiverInstalledMaxTick hardware technology initial) + 1

theorem loadedReceiverInstalledClock_capacity (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (technology : AIGCellTechnology) (initial : FiniteDimensionedSeriesRLCPortState) :
    loadedReceiverInstalledMaxTick hardware technology initial <
      2 ^ loadedReceiverInstalledClockBits hardware technology initial :=
  Nat.lt_pow_succ_log_self (by decide : 1 < 2) _

theorem loadedReceiverBoot_sampleTick_le_installed (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (technology : AIGCellTechnology) (initial : FiniteDimensionedSeriesRLCPortState) (drive : FiniteBinaryDrive) :
    (startFiniteADCPhysicalRuntime hardware initial drive).val.sampleTick ≤
      loadedReceiverInstalledMaxTick hardware technology initial :=
  (adcSampleTick_le_max (finiteADCFixtureWithInitial hardware initial) drive).trans (le_max_left _ _)

namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (current : FiniteADCWholeJointCurrent hardware clockMax technology)
variable (actualBoot : FiniteDimensionedSeriesRLCPortState)

theorem loadedReceiverFreshSample_sampleTick_le_installed :
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.sampleTick ≤
      loadedReceiverInstalledMaxTick hardware technology actualBoot :=
  (loadedReceiverFreshSample_sampleTick_le downstreamTechnology downstreamGraph current).trans (le_max_right _ _)

theorem loadedReceiverFreshSample_fits_installed_clock :
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.sampleTick <
      2 ^ loadedReceiverInstalledClockBits hardware technology actualBoot :=
  (loadedReceiverFreshSample_sampleTick_le_installed downstreamTechnology downstreamGraph current actualBoot).trans_lt
    (loadedReceiverInstalledClock_capacity hardware technology actualBoot)

def loadedReceiverFreshPacket :
    FiniteADCWirePacketFor hardware.adcCode (loadedReceiverInstalledClockBits hardware technology actualBoot) :=
  recordedADCWirePacket hardware (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val
    (congrArg FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence.adcCode
      (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).property)
    (loadedReceiverFreshSample_fits_installed_clock downstreamTechnology downstreamGraph current actualBoot)

theorem loadedReceiverFreshPacket_received :
    receiveADC128WirePacket hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot)
      (loadedReceiverFreshPacket downstreamTechnology downstreamGraph current actualBoot) =
        some (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.drive := by
  have actual := receive_recordedADCWirePacket_current
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current)
    (loadedReceiverFreshSample_fits_installed_clock downstreamTechnology downstreamGraph current actualBoot)
    (loadedReceiverInstalledMaxTick hardware technology actualBoot)
    (loadedReceiverFreshSample_sampleTick_le_installed downstreamTechnology downstreamGraph current actualBoot)
  change receiveADC128WirePacket
    (finiteADCFixtureWithInitial hardware (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.initial)
    (loadedReceiverInstalledMaxTick hardware technology actualBoot)
    (loadedReceiverFreshPacket (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph current actualBoot) = _ at actual
  rw [receiveADC128WirePacket_initial_independent] at actual
  exact actual

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
