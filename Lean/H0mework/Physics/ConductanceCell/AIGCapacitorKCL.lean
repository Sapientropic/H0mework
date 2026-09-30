import H0mework.Physics.ConductanceCell.AIGCapacitorControl
import H0mework.Physics.ConductanceCell.DrivenEnergy

/-!
# KCL and signed energy balance of the actual graph capacitors

Every voltage and control is a restriction of one compiled raw-input history.
The existing quartic conductance cell supplies KCL and the energy derivative;
neither target logic, an ODE certificate, nor an initial rail bound is assumed.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Std.Sat Units.Interface Storage

variable {α : Type} [DecidableEq α] [Hashable α]
variable (technology : AIGCellTechnology) (graph : AIG α) (input : α → ℝ → SIVolt)
variable (initial : Fin graph.decls.size → Bool → SIVolt)

noncomputable section

/-- Stored energy counts the physical capacitor at this address, including its literal load. -/
def aigCapacitorStoredEnergyAt (address : AIGCapacitorAddress graph) (time : ℝ) : SIJoule :=
  ⟨(compileDualRailCell technology graph address.val.1 address.val.2).capacitance.value / 2 *
    (aigCapacitorVoltageAt technology graph input initial address time).value ^ 2⟩

/-- Source power is signed; above-supply charge can return energy to the prescribed source. -/
def aigCapacitorSupplyPowerAt (address : AIGCapacitorAddress graph) (time : ℝ) : SIWatt :=
  (compileDualRailCell technology graph address.val.1 address.val.2).supplyPower
    (aigCapacitorControl technology graph input initial address false time)
    (aigCapacitorControl technology graph input initial address true time)
    (aigCapacitorVoltageAt technology graph input initial address time)

def aigCapacitorDissipatedPowerAt (address : AIGCapacitorAddress graph) (time : ℝ) : SIWatt :=
  (compileDualRailCell technology graph address.val.1 address.val.2).dissipatedPower
    (aigCapacitorControl technology graph input initial address false time)
    (aigCapacitorControl technology graph input initial address true time)
    (aigCapacitorVoltageAt technology graph input initial address time)

theorem aigCapacitorVoltageAt_initial (address : AIGCapacitorAddress graph) :
    (aigCapacitorVoltageAt technology graph input initial address 0).value =
      (initial address.val.1 address.val.2).value := by
  rw [aigCapacitorVoltageAt_eq_driven, LoadedConductanceCellSource.drivenVoltageAt_initial]

theorem aigCapacitorStoredEnergyAt_nonneg (address : AIGCapacitorAddress graph) (time : ℝ) :
    0 ≤ (aigCapacitorStoredEnergyAt technology graph input initial address time).value :=
  mul_nonneg (div_nonneg
    (compileDualRailCell technology graph address.val.1 address.val.2).capacitance_pos.le (by norm_num))
    (sq_nonneg _)

theorem aigCapacitorDissipatedPowerAt_nonneg (address : AIGCapacitorAddress graph) (time : ℝ) :
    0 ≤ (aigCapacitorDissipatedPowerAt technology graph input initial address time).value :=
  (compileDualRailCell technology graph address.val.1 address.val.2).dissipatedPower_nonneg _ _ _

theorem aigCapacitorStoredEnergyAt_initial (address : AIGCapacitorAddress graph) :
    (aigCapacitorStoredEnergyAt technology graph input initial address 0).value =
      (compileDualRailCell technology graph address.val.1 address.val.2).capacitance.value / 2 *
        (initial address.val.1 address.val.2).value ^ 2 := by
  simp only [aigCapacitorStoredEnergyAt, aigCapacitorVoltageAt_initial]

/-- Excess charge is physically retained and makes the source receive, rather than supply, power. -/
theorem aigCapacitorSupplyPowerAt_neg_of_above_supply
    (address : AIGCapacitorAddress graph) (time : ℝ)
    (aboveSupply : technology.supply.value <
      (aigCapacitorVoltageAt technology graph input initial address time).value) :
    (aigCapacitorSupplyPowerAt technology graph input initial address time).value < 0 := by
  exact mul_neg_of_pos_of_neg
    (mul_pos ((compileDualRailCell technology graph address.val.1 address.val.2).pullUp_pos _ _)
      technology.supply_pos) (sub_neg.mpr aboveSupply)

variable (inputContinuous : ∀ (node : Fin graph.decls.size) atom,
  graph.decls[node.val] = .atom atom → Continuous (fun t => (input atom t).value))

include inputContinuous

theorem aigCapacitorVoltageAt_continuous (address : AIGCapacitorAddress graph) :
    Continuous (fun t => (aigCapacitorVoltageAt technology graph input initial address t).value) :=
  compileAIGDualRailTrajectoryFromInputs_continuous technology graph input initial
    inputContinuous address.val.1 address.val.2

/-- The actual addressed node obeys the same cell KCL under its literal two control histories. -/
theorem aigCapacitorVoltageAt_kcl (address : AIGCapacitorAddress graph) (time : ℝ) :
    let cell := compileDualRailCell technology graph address.val.1 address.val.2
    let left := aigCapacitorControl technology graph input initial address false
    let right := aigCapacitorControl technology graph input initial address true
    let voltage := aigCapacitorVoltageAt technology graph input initial address
    HasDerivAt (fun t => (voltage t).value)
      ((cell.pullUp (left time) (right time) * (cell.supply.value - (voltage time).value) -
        cell.pullDown (left time) (right time) * (voltage time).value) / cell.capacitance.value) time := by
  dsimp only
  simpa only [aigCapacitorVoltageAt_eq_driven] using
    (compileDualRailCell technology graph address.val.1 address.val.2).drivenVoltageAt_kcl
      (aigCapacitorControl technology graph input initial address false)
      (aigCapacitorControl technology graph input initial address true)
      (initial address.val.1 address.val.2)
      (aigCapacitorControl_continuous technology graph input initial inputContinuous address false)
      (aigCapacitorControl_continuous technology graph input initial inputContinuous address true) time

/-- Exact local power balance consumes the existing generated cell-energy derivative. -/
theorem aigCapacitorStoredEnergyAt_power_balance (address : AIGCapacitorAddress graph) (time : ℝ) :
    HasDerivAt (fun t => (aigCapacitorStoredEnergyAt technology graph input initial address t).value)
      ((aigCapacitorSupplyPowerAt technology graph input initial address time).value -
        (aigCapacitorDissipatedPowerAt technology graph input initial address time).value) time := by
  have actual := (compileDualRailCell technology graph address.val.1 address.val.2).drivenStoredEnergyAt_power_balance
    (aigCapacitorControl technology graph input initial address false)
    (aigCapacitorControl technology graph input initial address true)
    (initial address.val.1 address.val.2)
    (aigCapacitorControl_continuous technology graph input initial inputContinuous address false)
    (aigCapacitorControl_continuous technology graph input initial inputContinuous address true) time
  simpa only [aigCapacitorStoredEnergyAt, aigCapacitorSupplyPowerAt, aigCapacitorDissipatedPowerAt,
    LoadedConductanceCellSource.drivenStoredEnergyAt, LoadedConductanceCellSource.drivenSupplyPowerAt,
    LoadedConductanceCellSource.drivenDissipatedPowerAt, LoadedConductanceCellSource.supplyPower,
    LoadedConductanceCellSource.dissipatedPower, aigCapacitorVoltageAt_eq_driven] using actual

end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
