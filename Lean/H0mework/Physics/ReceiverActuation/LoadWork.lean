import H0mework.Physics.ReceiverActuation.LoadBackground
import H0mework.Physics.ReceiverActuation.LoadHeat
import H0mework.Computation.AIGHold.HeldMemoryIntervalWork

/-! # Every load-phase row pays its actual source work and heat on the same interval -/

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

def outputLoadBackgroundWorkAt (time : ℝ) : SIJoule :=
  let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
  let start := (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
    downstreamTechnology downstreamGraph).value
  ⟨((packetLinesWorkAt technology (aigOutputBank entry).aig current.assignment current.memory.inputInitial (start + time)).value -
      (packetLinesWorkAt technology (aigOutputBank entry).aig current.assignment current.memory.inputInitial start).value) +
    ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
      if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then
        (aigMemoryCapacitorWorkAt technology entry current.memory current.assignment
          hardware.meteredSource.fixture.coreSource hardware.clockCode address (start + time)).value -
        (aigMemoryCapacitorWorkAt technology entry current.memory current.assignment
          hardware.meteredSource.fixture.coreSource hardware.clockCode address start).value
      else 0⟩

def outputLoadBackgroundHeatAt (time : ℝ) : SIJoule :=
  let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
  let start := (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
    downstreamTechnology downstreamGraph).value
  ⟨((packetLinesHeatAt technology (aigOutputBank entry).aig current.assignment current.memory.inputInitial (start + time)).value -
      (packetLinesHeatAt technology (aigOutputBank entry).aig current.assignment current.memory.inputInitial start).value) +
    ∑ address : AIGCapacitorAddress (aigOutputBank entry).aig,
      if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then
        (aigMemoryCapacitorHeatAt technology entry current.memory current.assignment downstreamTechnology downstreamGraph
          hardware.meteredSource.fixture.coreSource hardware.clockCode address (start + time)).value -
        (aigMemoryCapacitorHeatAt technology entry current.memory current.assignment downstreamTechnology downstreamGraph
          hardware.meteredSource.fixture.coreSource hardware.clockCode address start).value
      else 0⟩

theorem outputLoadBackgroundHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (outputLoadBackgroundHeatAt downstreamTechnology downstreamGraph current time).value := by
  dsimp only [outputLoadBackgroundHeatAt]
  apply add_nonneg (packetLinesHeatAt_interval_nonneg _ _ _ _ _ _ (le_add_of_nonneg_right nonnegative))
  apply Finset.sum_nonneg
  intro address _
  split
  · exact aigMemoryCapacitorHeatAt_interval_nonneg _ _ _ _ _ _ _ _ address _ _
      (le_add_of_nonneg_right nonnegative)
  · exact le_rfl

theorem outputLoadBackgroundStoredEnergyAt_integrated_balance (time : ℝ) :
    (outputLoadBackgroundStoredEnergyAt downstreamTechnology downstreamGraph current time).value -
        (outputLoadBackgroundStoredEnergyAt downstreamTechnology downstreamGraph current 0).value =
      (outputLoadBackgroundWorkAt downstreamTechnology downstreamGraph current time).value -
        (outputLoadBackgroundHeatAt downstreamTechnology downstreamGraph current time).value := by
  let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
  let start := (readDelay (hardware := hardware) (clockMax := clockMax) (technology := technology)
    downstreamTechnology downstreamGraph).value
  let energy := fun (address : AIGCapacitorAddress (aigOutputBank entry).aig) t =>
    (aigMemoryCapacitorStoredEnergyAt technology entry current.memory current.assignment downstreamTechnology downstreamGraph
      hardware.meteredSource.fixture.coreSource hardware.clockCode address t).value
  let work := fun (address : AIGCapacitorAddress (aigOutputBank entry).aig) t =>
    (aigMemoryCapacitorWorkAt technology entry current.memory current.assignment
      hardware.meteredSource.fixture.coreSource hardware.clockCode address t).value
  let heat := fun (address : AIGCapacitorAddress (aigOutputBank entry).aig) t =>
    (aigMemoryCapacitorHeatAt technology entry current.memory current.assignment downstreamTechnology downstreamGraph
      hardware.meteredSource.fixture.coreSource hardware.clockCode address t).value
  have inputs := packetLinesStoredEnergyAt_interval_balance technology (aigOutputBank entry).aig
    current.assignment current.memory.inputInitial start (start + time)
  have row (address : AIGCapacitorAddress (aigOutputBank entry).aig) :
      (if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then energy address (start + time) else 0) -
        (if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then energy address start else 0) =
      (if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then work address (start + time) - work address start else 0) -
        (if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then heat address (start + time) - heat address start else 0) := by
    by_cases selected : outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none
    · simp only [if_pos selected]
      exact aigMemoryCapacitorStoredEnergyAt_interval_balance _ _ _ _ _ _ _ _ address start (start + time)
    · simp only [if_neg selected, sub_self]
  have rows := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun address _ => row address)
  simp only [Finset.sum_sub_distrib] at rows
  dsimp only [outputLoadBackgroundStoredEnergyAt, outputLoadBackgroundWorkAt, outputLoadBackgroundHeatAt]
  simp only [add_zero]
  change _ + (∑ address, if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then energy address (start + time) else 0) -
    (_ + ∑ address, if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then energy address start else 0) =
    (_ + ∑ address, if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then work address (start + time) - work address start else 0) -
    (_ + ∑ address, if outputLoadChannel? hardware clockMax address.val.1 address.val.2 = none then heat address (start + time) - heat address start else 0)
  linarith

def outputLoadWholeHeatAt (time : ℝ) : SIJoule :=
  outputLoadBackgroundHeatAt downstreamTechnology downstreamGraph current time +
    wholeOutputLoadHeatAt downstreamTechnology downstreamGraph current time

theorem outputLoadWholeHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (outputLoadWholeHeatAt downstreamTechnology downstreamGraph current time).value :=
  add_nonneg (outputLoadBackgroundHeatAt_nonneg _ _ _ time nonnegative)
    (wholeOutputLoadHeatAt_nonneg _ _ _ time nonnegative)

/-- Exterior source work belongs to the unaffected circuit; signed load exchange cancels internally. -/
theorem outputLoadWholeStoredEnergyAt_integrated_balance (time : ℝ) :
    (outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current time).value -
        (outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current 0).value =
      (outputLoadBackgroundWorkAt downstreamTechnology downstreamGraph current time).value -
        (outputLoadWholeHeatAt downstreamTechnology downstreamGraph current time).value := by
  have background := outputLoadBackgroundStoredEnergyAt_integrated_balance downstreamTechnology downstreamGraph current time
  have loads := wholeOutputLoadEnergyAt_integrated_balance downstreamTechnology downstreamGraph current time
  rw [outputLoadWholeStoredEnergyAt_eq_background_add_load, outputLoadWholeStoredEnergyAt_eq_background_add_load]
  dsimp only [outputLoadWholeHeatAt, SIQuantity.add_value]
  linarith

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical

