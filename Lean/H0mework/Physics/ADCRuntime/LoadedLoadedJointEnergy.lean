import H0mework.Physics.ReceiverActuation.LoadEnergy

/-!
# Joint snapshot energy and the actual read-phase bill

Receiver time starts at the recorded ADC snapshot. The recipient instead continues its
existing plant trajectory from that sample to the source-generated physical switch time.
The read delay is never substituted for a plant-start absolute time.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}

/-- Both stored subsystems are read at the same actual ADC snapshot. -/
def jointStoredEnergy (current : FiniteADCWholeJointCurrent hardware clockMax technology) : SIJoule :=
  current.memory.storedEnergy + finiteADCRecipientStoredEnergyAt current.plant current.plant.val.executedDuration

theorem jointStoredEnergy_nonneg (current : FiniteADCWholeJointCurrent hardware clockMax technology) :
    0 ≤ (jointStoredEnergy current).value := by
  have memoryNonnegative : 0 ≤ current.memory.storedEnergy.value := by
    unfold AIGCapacitorMemory.storedEnergy aigActualStoredEnergy
    dsimp only
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro atom _
      exact mul_nonneg (div_nonneg (compilePacketLineDriver technology
        (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig atom).capacitance_pos.le
        (by norm_num)) (sq_nonneg _)
    · apply Finset.sum_nonneg
      intro address _
      exact mul_nonneg (div_nonneg (compileDualRailCell technology
        (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig
        address.val.1 address.val.2).capacitance_pos.le (by norm_num)) (sq_nonneg _)
  exact add_nonneg memoryNonnegative (drivenRLCBankStoredEnergy_nonneg _ _)

variable {β : Type} [DecidableEq β] [Hashable β]
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (current : FiniteADCWholeJointCurrent hardware clockMax technology)

def readPhaseWork : SIJoule :=
  receiverSourceWorkAt current (readDelay (hardware := hardware) (clockMax := clockMax)
    (technology := technology) downstreamTechnology downstreamGraph).value +
  finiteADCRecipientWork current.plant current.plant.val.executedDuration
    (finiteADCPhysicalSwitchTimeAt current.plant
      (receiverWholeHardwareProcessingTicks hardware (Nat.log 2 clockMax + 1)
        technology downstreamTechnology downstreamGraph))

def readPhaseHeat : SIJoule :=
  receiverDissipatedHeatAt downstreamTechnology downstreamGraph current
    (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value +
  finiteADCRecipientHeat current.plant current.plant.val.executedDuration
    (finiteADCPhysicalSwitchTimeAt current.plant
      (receiverWholeHardwareProcessingTicks hardware (Nat.log 2 clockMax + 1)
        technology downstreamTechnology downstreamGraph))

theorem readPhaseHeat_nonneg :
    0 ≤ (readPhaseHeat downstreamTechnology downstreamGraph current).value :=
  add_nonneg (receiverDissipatedHeatAt_nonneg downstreamTechnology downstreamGraph current _
    (readDelay_nonneg downstreamTechnology downstreamGraph))
    (finiteADCRecipient_sample_to_switch_heat_nonneg current.plant _)

/-- The actual read endpoint is exactly the initial state of the existing complete load sheet. -/
theorem readPhase_integrated_balance :
    (outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current 0).value -
      (jointStoredEnergy current).value =
        (readPhaseWork downstreamTechnology downstreamGraph current).value -
          (readPhaseHeat downstreamTechnology downstreamGraph current).value := by
  have receiver := receiverStoredEnergyAt_paid_read downstreamTechnology downstreamGraph current
  have recipient := finiteADCRecipient_sample_to_switch_paid current.plant
    (receiverWholeHardwareProcessingTicks hardware (Nat.log 2 clockMax + 1)
      technology downstreamTechnology downstreamGraph)
  change (drivenRLCBankStoredEnergy
    (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
    (current.outputLoadInitialRecipient downstreamTechnology downstreamGraph)).value - _ = _ at recipient
  rw [outputLoadWholeStoredEnergyAt_initial]
  dsimp only [jointStoredEnergy, readPhaseWork, readPhaseHeat, SIQuantity.add_value] at *
  linarith

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
