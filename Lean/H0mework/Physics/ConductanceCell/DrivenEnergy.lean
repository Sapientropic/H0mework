import H0mework.Physics.ConductanceCell.Energy
import H0mework.Physics.ConductanceCell.Trajectory

/-! # The actual moving-input recovery pays capacitor change, source work, and heat together -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface

noncomputable section
namespace LoadedConductanceCellSource

def drivenStoredEnergyAt (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ) : SIJoule :=
  ⟨source.capacitance.value / 2 * source.drivenVoltageAt left right initial time ^ 2⟩

def drivenSupplyPowerAt (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ) : SIWatt :=
  source.supplyPower (left time) (right time) ⟨source.drivenVoltageAt left right initial time⟩

def drivenDissipatedPowerAt (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ) : SIWatt :=
  source.dissipatedPower (left time) (right time) ⟨source.drivenVoltageAt left right initial time⟩

theorem drivenStoredEnergyAt_nonneg (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ) :
    0 ≤ (source.drivenStoredEnergyAt left right initial time).value :=
  mul_nonneg (div_nonneg source.capacitance_pos.le (by norm_num)) (sq_nonneg _)

theorem drivenDissipatedPowerAt_nonneg (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ) :
    0 ≤ (source.drivenDissipatedPowerAt left right initial time).value :=
  source.dissipatedPower_nonneg (left time) (right time) ⟨source.drivenVoltageAt left right initial time⟩

theorem drivenStoredEnergyAt_initial (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) :
    (source.drivenStoredEnergyAt left right initial 0).value = source.capacitance.value / 2 * initial.value ^ 2 := by
  simp only [drivenStoredEnergyAt, drivenVoltageAt_initial]

/-- Arbitrary initial charge is retained; the generated KCL, not a payment premise, pays the balance. -/
theorem drivenStoredEnergyAt_power_balance (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) (time : ℝ) :
    HasDerivAt (fun t => (source.drivenStoredEnergyAt left right initial t).value)
      ((source.drivenSupplyPowerAt left right initial time).value -
        (source.drivenDissipatedPowerAt left right initial time).value) time := by
  have generated := ((source.drivenVoltageAt_kcl left right initial
    leftContinuous rightContinuous time).pow 2).const_mul (source.capacitance.value / 2)
  have capacitanceNonzero := ne_of_gt source.capacitance_pos
  convert generated using 1 <;> first | rfl | (
    dsimp only [drivenStoredEnergyAt, drivenSupplyPowerAt, drivenDissipatedPowerAt, supplyPower, dissipatedPower]
    field_simp
    ring)

/-- Above-supply charge sends energy back into the source; it is not silently called positive charging. -/
theorem drivenSupplyPowerAt_neg_of_above_supply (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ)
    (aboveSupply : source.supply.value < source.drivenVoltageAt left right initial time) :
    (source.drivenSupplyPowerAt left right initial time).value < 0 :=
  mul_neg_of_pos_of_neg (mul_pos (source.pullUp_pos (left time) (right time)) source.supply_pos)
    (sub_neg.mpr aboveSupply)

end LoadedConductanceCellSource
end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
