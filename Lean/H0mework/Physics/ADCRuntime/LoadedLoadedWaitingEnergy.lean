import H0mework.Physics.ADCRuntime.LoadedLoadedJointEnergy

/-!
# Fresh-sample waiting pays the next joint snapshot

The recovered memory continues under its old packet assignment while the independently
received command generates a fresh physical ADC run. Both branches end at that run's
literal executed duration; its initial recipient coordinates are the actual common target.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
  {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {technology : AIGCellTechnology} {actualBoot : FiniteDimensionedSeriesRLCPortState}
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (current : FiniteADCWholeJointCurrent hardware
    (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def waitingPhaseWork : SIJoule :=
  aigMemoryWorkAt technology (receiverWholeGraph hardware.adcCode
      (loadedReceiverInstalledClockBits hardware technology actualBoot))
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).1 current.assignment
    hardware.meteredSource.fixture.coreSource hardware.clockCode
    (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value +
  finiteADCRecipientWork (loadedReceiverFreshSample downstreamTechnology downstreamGraph current) 0
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.executedDuration

def waitingPhaseHeat : SIJoule :=
  aigMemoryHeatAt technology (receiverWholeGraph hardware.adcCode
      (loadedReceiverInstalledClockBits hardware technology actualBoot))
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).1 current.assignment
    downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode
    (loadedReceiverSnapshotDelay downstreamTechnology downstreamGraph current).value +
  finiteADCRecipientHeat (loadedReceiverFreshSample downstreamTechnology downstreamGraph current) 0
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.executedDuration

theorem waitingPhaseHeat_nonneg :
    0 ≤ (waitingPhaseHeat downstreamTechnology downstreamGraph current).value :=
  add_nonneg (aigMemoryHeatAt_nonneg _ _ _ _ _ _ _ _ _
      (loadedReceiverSnapshotDelay_pos downstreamTechnology downstreamGraph current).le)
    (finiteADCRecipientHeat_nonneg _ _ _
      (finiteADCPhysicalCurrent_duration_positive (loadedReceiverFreshSample downstreamTechnology downstreamGraph current)).le)

/-- No recipient zero-reset or target-memory substitution occurs at the fresh-run entrance. -/
theorem waitingPhase_recipient_initial_energy :
    finiteADCRecipientStoredEnergyAt (loadedReceiverFreshSample downstreamTechnology downstreamGraph current) 0 =
      drivenRLCBankStoredEnergy
        (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
        (commonRecoveryTarget downstreamTechnology downstreamGraph current).2 := by
  unfold finiteADCRecipientStoredEnergyAt
  rw [loadedReceiverFreshSample_no_reset]

/-- The actual waiting interval reaches exactly the next reusable joint current. -/
theorem waitingPhase_integrated_balance :
    (jointStoredEnergy (loadedStep downstreamTechnology downstreamGraph current)).value -
      ((commonRecoveryTarget downstreamTechnology downstreamGraph current).1.storedEnergy +
        drivenRLCBankStoredEnergy
          (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
          (commonRecoveryTarget downstreamTechnology downstreamGraph current).2).value =
        (waitingPhaseWork downstreamTechnology downstreamGraph current).value -
          (waitingPhaseHeat downstreamTechnology downstreamGraph current).value := by
  have receiver := loadedReceiverSnapshotMemory_paid downstreamTechnology downstreamGraph current
  have recipient := finiteADCRecipientStoredEnergyAt_integrated_balance
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current) 0
    (loadedReceiverFreshSample downstreamTechnology downstreamGraph current).val.executedDuration
  rw [waitingPhase_recipient_initial_energy] at recipient
  simp only [jointStoredEnergy, loadedStep_memory, loadedStep_plant, SIQuantity.add_value]
  dsimp only [waitingPhaseWork, waitingPhaseHeat, SIQuantity.add_value, loadedReceiverInstalledClockBits] at *
  linarith

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
