import H0mework.Computation.AIGHold.HeldCapacitorRestriction

/-! # Actual source work, leakage heat and charge for every capacitor of a held memory run -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat Units.Interface Conductance
open Netlist.Dissipative.Dimensioned.Driven.Producer

variable {α β : Type} [DecidableEq α] [Hashable α] [DecidableEq β] [Hashable β] {width : Nat}

noncomputable section

variable (technology : AIGCellTechnology) (entry : AIG.RefVecEntry α width)
  (memory : AIGCapacitorMemory technology (aigOutputBank entry).aig) (assignment : α → Bool)
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (clock : ResonantDrivenCoreSource) (code : FiniteSamplingClockCode)
  (address : AIGCapacitorAddress (aigOutputBank entry).aig)

local notation "actualCell" => compileDualRailCell technology (AIG.RefVecEntry.aig (aigOutputBank entry)) (Prod.fst (Subtype.val address)) (Prod.snd (Subtype.val address))
local notation "rawInput" => aigMemoryInputWave technology entry memory assignment
local notation "rawWave" => aigCapacitorVoltageAt technology (AIG.RefVecEntry.aig (aigOutputBank entry)) rawInput (AIGCapacitorMemory.gateInitial memory) address
local notation "leftControl" => aigCapacitorControl technology (AIG.RefVecEntry.aig (aigOutputBank entry)) rawInput (AIGCapacitorMemory.gateInitial memory) address false
local notation "rightControl" => aigCapacitorControl technology (AIG.RefVecEntry.aig (aigOutputBank entry)) rawInput (AIGCapacitorMemory.gateInitial memory) address true
local notation "initialVoltage" => AIGCapacitorMemory.gateInitial memory (Prod.fst (Subtype.val address)) (Prod.snd (Subtype.val address))
local notation "captureTime" => SIQuantity.value (aigMemoryCaptureTime technology entry clock code)
local notation "localHold" => compileHoldLeaseForGraph actualCell downstreamTechnology downstreamGraph clock code

/-- Source branch-power integral, cut off at the actual capture only for isolated outputs. -/
def aigMemoryCapacitorWorkAt (time : ℝ) : SIJoule :=
  (actualCell).drivenWorkAt leftControl rightControl initialVoltage
    (if aigMemoryCapacitorIsHeld entry address then min time captureTime else time)

/-- Driven heat and post-capture leakage are both actual power integrals. -/
def aigMemoryCapacitorHeatAt (time : ℝ) : SIJoule :=
  ⟨((actualCell).drivenHeatAt leftControl rightControl initialVoltage
      (if aigMemoryCapacitorIsHeld entry address then min time captureTime else time)).value +
    if aigMemoryCapacitorIsHeld entry address then
      ((localHold).heatAt rawWave captureTime (max captureTime time)).value else 0⟩

def aigMemoryCapacitorStoredEnergyAt (time : ℝ) : SIJoule :=
  ⟨(actualCell).capacitance.value / 2 *
    (aigMemoryStateAt technology entry memory assignment downstreamTechnology downstreamGraph clock code
      address.val.1 address.val.2 time).value ^ 2⟩

theorem aigMemoryCapacitorStoredEnergyAt_initial :
    (aigMemoryCapacitorStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph
      clock code address 0).value = (actualCell).capacitance.value / 2 * (initialVoltage).value ^ 2 := by
  simp only [aigMemoryCapacitorStoredEnergyAt, aigMemoryStateAt_initial]

theorem aigMemoryCapacitorHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (aigMemoryCapacitorHeatAt technology entry memory assignment downstreamTechnology downstreamGraph
      clock code address time).value := by
  by_cases held : aigMemoryCapacitorIsHeld entry address
  · simp only [aigMemoryCapacitorHeatAt, if_pos held]
    exact add_nonneg ((actualCell).drivenHeatAt_nonneg _ _ _ _
      (le_min nonnegative (aigMemoryCaptureTime_nonneg technology entry clock code)))
      ((localHold).heatAt_nonneg _ _ _ (le_max_left _ _))
  · simp only [aigMemoryCapacitorHeatAt, if_neg held, add_zero]
    exact (actualCell).drivenHeatAt_nonneg _ _ _ _ nonnegative

private theorem aigMemoryRawCapacitor_paid (time : ℝ) :
    (actualCell).capacitance.value / 2 * (rawWave time).value ^ 2 =
      (actualCell).capacitance.value / 2 * (initialVoltage).value ^ 2 +
        ((actualCell).drivenWorkAt leftControl rightControl initialVoltage time).value -
        ((actualCell).drivenHeatAt leftControl rightControl initialVoltage time).value := by
  have inputContinuous : ∀ (node : Fin (aigOutputBank entry).aig.decls.size) atom,
      (aigOutputBank entry).aig.decls[node.val] = .atom atom → Continuous (fun t => (rawInput atom t).value) :=
    fun _ atom _ => packetLineInputWave_continuous technology (aigOutputBank entry).aig
      assignment memory.inputInitial atom
  simpa only [aigCapacitorVoltageAt_eq_driven, LoadedConductanceCellSource.drivenStoredEnergyAt] using
    (actualCell).drivenStoredEnergyAt_integrated_balance leftControl rightControl initialVoltage
      (aigCapacitorControl_continuous _ _ _ _ inputContinuous address false)
      (aigCapacitorControl_continuous _ _ _ _ inputContinuous address true) time

/-- All three time regions consume the same current, with no capture verdict or target state supplied. -/
theorem aigMemoryCapacitorStoredEnergyAt_integrated_balance (time : ℝ) :
    (aigMemoryCapacitorStoredEnergyAt technology entry memory assignment downstreamTechnology downstreamGraph
      clock code address time).value - (actualCell).capacitance.value / 2 * (initialVoltage).value ^ 2 =
      (aigMemoryCapacitorWorkAt technology entry memory assignment clock code address time).value -
        (aigMemoryCapacitorHeatAt technology entry memory assignment downstreamTechnology downstreamGraph
          clock code address time).value := by
  unfold aigMemoryCapacitorStoredEnergyAt aigMemoryCapacitorWorkAt aigMemoryCapacitorHeatAt
  rw [aigMemoryCapacitor_actual_restriction technology entry memory assignment
    downstreamTechnology downstreamGraph clock code address time]
  by_cases held : aigMemoryCapacitorIsHeld entry address
  · simp only [if_pos held]
    by_cases before : time ≤ captureTime
    · simp only [min_eq_left before, max_eq_left before, ClockedLeakyHoldSource.heatAt_stop,
        add_zero, ClockedLeakyHoldSource.wave,
        (localHold).voltageAt_before rawWave captureTime time before]
      have paid := aigMemoryRawCapacitor_paid technology entry memory assignment address time
      linarith
    · have afterStop := (lt_of_not_ge before).le
      simp only [min_eq_right afterStop, max_eq_right afterStop]
      have prefixPaid := aigMemoryRawCapacitor_paid technology entry memory assignment address captureTime
      have tailPaid := (localHold).storedEnergyAt_integrated_balance rawWave captureTime time afterStop
      rw [(localHold).storedEnergyAt_stop] at tailPaid
      change (actualCell).capacitance.value / 2 *
        ((localHold).wave rawWave captureTime time).value ^ 2 = _ at tailPaid
      linarith
  · simp only [if_neg held, add_zero]
    have paid := aigMemoryRawCapacitor_paid technology entry memory assignment address time
    linarith

end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
