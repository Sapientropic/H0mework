import H0mework.Physics.ReceiverActuation.LoadEnergy

/-! # Unactuated memory and the ten actual loads partition the complete energy -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (current : FiniteADCWholeJointCurrent hardware clockMax technology)

def outputLoadBackgroundStoredEnergyAt (time : ℝ) : SIJoule :=
  let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
  let absoluteTime := (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
    downstreamTechnology downstreamGraph).value + time
  ⟨(packetLinesStoredEnergyAt technology (aigOutputBank entry).aig current.assignment current.memory.inputInitial absoluteTime).value +
    ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
      if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then
        (aigMemoryCapacitorStoredEnergyAt technology entry current.memory current.assignment
          downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode address absoluteTime).value
      else 0⟩

theorem outputLoadBackgroundStoredEnergyAt_nonneg (time : ℝ) :
    0 ≤ (outputLoadBackgroundStoredEnergyAt downstreamTechnology downstreamGraph current time).value := by
  dsimp only [outputLoadBackgroundStoredEnergyAt]
  apply add_nonneg (packetLinesStoredEnergyAt_nonneg _ _ _ _ _)
  apply Finset.sum_nonneg
  intro address _
  split
  · exact mul_nonneg (div_nonneg
      (compileDualRailCell technology
        (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig
        address.val.1 address.val.2).capacitance_pos.le (by norm_num)) (sq_nonneg _)
  · exact le_rfl

/-- Subtraction is a derived census equality; the background definition is a positive row sum. -/
theorem outputLoadBackgroundStoredEnergyAt_eq_complement (time : ℝ) :
    (outputLoadBackgroundStoredEnergyAt downstreamTechnology downstreamGraph current time).value =
      (receiverStoredEnergyAt downstreamTechnology downstreamGraph current
        ((readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value + time)).value -
      ∑ channel, (outputLoadOldCapEnergyAt downstreamTechnology downstreamGraph current channel time).value := by
  let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
  let absoluteTime := (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
    downstreamTechnology downstreamGraph).value + time
  let energy : AIGCapacitorAddress (aigOutputBank entry).aig → ℝ := fun address =>
    (aigMemoryCapacitorStoredEnergyAt technology entry current.memory current.assignment
      downstreamTechnology downstreamGraph hardware.meteredSource.fixture.coreSource hardware.clockCode address absoluteTime).value
  have partition := outputLoad_unloaded_address_sum (hardware := hardware) (clockMax := clockMax) energy
  have selected (channel : FiniteEmbodimentChannel) :
      energy (outputLoadAddress hardware clockMax channel) =
        (outputLoadOldCapEnergyAt downstreamTechnology downstreamGraph current channel time).value := rfl
  simp_rw [selected] at partition
  change _ + (∑ address, if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then energy address else 0) =
    (_ + ∑ address, energy address) - _
  dsimp only [packetLinesStoredEnergyAt, packetLineStoredEnergyAt, aigMemoryInputWave]
  linarith

theorem outputLoadWholeStoredEnergyAt_eq_background_add_load (time : ℝ) :
    (outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current time).value =
      (outputLoadBackgroundStoredEnergyAt downstreamTechnology downstreamGraph current time).value +
        ∑ channel, (current.outputLoadEnergyAt downstreamTechnology downstreamGraph channel time).value := by
  rw [outputLoadWholeStoredEnergyAt_decomposition, outputLoadBackgroundStoredEnergyAt_eq_complement]

theorem outputLoadWholeStoredEnergyAt_nonneg (time : ℝ) :
    0 ≤ (outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current time).value := by
  rw [outputLoadWholeStoredEnergyAt_eq_background_add_load]
  exact add_nonneg (outputLoadBackgroundStoredEnergyAt_nonneg _ _ _ time)
    (Finset.sum_nonneg (s := Finset.univ) fun channel _ => capacitorRLCEnergyAt_nonneg _ _ _ _ _ _ _ time)

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
