import H0mework.Computation.AIGHold.ClockedLeakyHold
import H0mework.Physics.ConductanceCell.CellWork

/-!
# Actual leakage and source work across a capacitor's capture event

The same capacitor retains its actual stop voltage. Its post-stop heat is the
integral of the existing leakage power, not an energy-difference definition.
Joining a driven prefix uses one-sided hold KCL; the switch is not claimed to
have matching derivatives on both sides.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Units.Interface Conductance Set MeasureTheory

noncomputable section
namespace ClockedLeakyHoldSource

variable {source : LoadedConductanceCellSource} (hold : ClockedLeakyHoldSource source)

/-- Actual leakage accumulated after the stop event. -/
def heatAt (input : ℝ → SIVolt) (stopTime time : ℝ) : SIJoule :=
  ⟨∫ t in stopTime..time, (hold.dissipatedPowerAt input stopTime t).value⟩

theorem heatAt_nonneg (input : ℝ → SIVolt) (stopTime time : ℝ) (afterStop : stopTime ≤ time) :
    0 ≤ (hold.heatAt input stopTime time).value :=
  intervalIntegral.integral_nonneg_of_forall afterStop
    (fun t => hold.dissipatedPowerAt_nonneg input stopTime t)

@[simp] theorem heatAt_stop (input : ℝ → SIVolt) (stopTime : ℝ) :
    hold.heatAt input stopTime stopTime = ⟨0⟩ := by
  simp only [heatAt, intervalIntegral.integral_same]

/-- Switching preserves the stored energy of the actual captured voltage. -/
theorem storedEnergyAt_stop (input : ℝ → SIVolt) (stopTime : ℝ) :
    (hold.storedEnergyAt input stopTime stopTime).value =
      source.capacitance.value / 2 * (input stopTime).value ^ 2 := by
  rw [storedEnergyAt, hold.voltageAt_before input stopTime stopTime le_rfl]

/-- Only the post-stop restriction is needed; the earlier input may be arbitrary. -/
theorem voltageAt_continuousOn_after (input : ℝ → SIVolt) (stopTime : ℝ) :
    ContinuousOn (hold.voltageAt input stopTime) (Ici stopTime) :=
  (hold.decayAt_continuous (input stopTime) stopTime).continuousOn.congr
    (fun t ht => hold.voltageAt_after input stopTime t ht)

/-- FTC consumes the existing switched KCL on the open interval and continuity at capture. -/
theorem storedEnergyAt_integrated_balance
    (input : ℝ → SIVolt) (stopTime time : ℝ) (afterStop : stopTime ≤ time) :
    (hold.storedEnergyAt input stopTime time).value =
      (hold.storedEnergyAt input stopTime stopTime).value - (hold.heatAt input stopTime time).value := by
  have voltageContinuous := (hold.voltageAt_continuousOn_after input stopTime).mono
    (show Icc stopTime time ⊆ Ici stopTime from fun _ ht => ht.1)
  have energyContinuous : ContinuousOn
      (fun t => (hold.storedEnergyAt input stopTime t).value) (Icc stopTime time) :=
    continuousOn_const.mul (voltageContinuous.pow 2)
  have heatContinuous : ContinuousOn
      (fun t => (hold.dissipatedPowerAt input stopTime t).value) (Icc stopTime time) :=
    (voltageContinuous.pow 2).div_const _
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le afterStop energyContinuous
    (fun t ht => (hold.storedEnergyAt_power_balance input stopTime t ht.1.le).hasDerivAt
      (Ici_mem_nhds ht.1)) (heatContinuous.neg.intervalIntegrable_of_Icc afterStop)
  rw [intervalIntegral.integral_neg] at paid
  change -(hold.heatAt input stopTime time).value = _ at paid
  linarith

/-- The entire drop, including negative initial voltage, is actual resistor heat. -/
theorem storedEnergyAt_drop_eq_heat
    (input : ℝ → SIVolt) (stopTime time : ℝ) (afterStop : stopTime ≤ time) :
    (hold.storedEnergyAt input stopTime stopTime).value -
        (hold.storedEnergyAt input stopTime time).value = (hold.heatAt input stopTime time).value := by
  rw [hold.storedEnergyAt_integrated_balance input stopTime time afterStop]
  ring

/-- The driven and held descriptions have the same literal capacitor energy at the switch. -/
theorem drivenStoredEnergyAt_switch
    (left right : ℝ → SIVolt) (initial : SIVolt) (stopTime : ℝ) :
    hold.storedEnergyAt (fun t => ⟨source.drivenVoltageAt left right initial t⟩) stopTime stopTime =
      source.drivenStoredEnergyAt left right initial stopTime := by
  apply SIQuantity.ext
  exact hold.storedEnergyAt_stop _ stopTime

theorem drivenStoredEnergyAt_initial
    (left right : ℝ → SIVolt) (initial : SIVolt) (stopTime : ℝ) (stopNonnegative : 0 ≤ stopTime) :
    (hold.storedEnergyAt (fun t => ⟨source.drivenVoltageAt left right initial t⟩) stopTime 0).value =
      source.capacitance.value / 2 * initial.value ^ 2 := by
  simp only [storedEnergyAt, hold.voltageAt_before _ stopTime 0 stopNonnegative,
    LoadedConductanceCellSource.drivenVoltageAt_initial]

/-- Source work ends at capture; actual heat includes both the driven and held segments. -/
theorem drivenStoredEnergyAt_integrated_balance
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (stopTime time : ℝ) (stopNonnegative : 0 ≤ stopTime) (afterStop : stopTime ≤ time) :
    let input := fun t => (⟨source.drivenVoltageAt left right initial t⟩ : SIVolt)
    (hold.storedEnergyAt input stopTime time).value =
      (hold.storedEnergyAt input stopTime 0).value + (source.drivenWorkAt left right initial stopTime).value -
        ((source.drivenHeatAt left right initial stopTime).value + (hold.heatAt input stopTime time).value) := by
  dsimp only
  rw [hold.storedEnergyAt_integrated_balance _ stopTime time afterStop,
    hold.drivenStoredEnergyAt_switch, hold.drivenStoredEnergyAt_initial _ _ _ stopTime stopNonnegative,
    source.drivenStoredEnergyAt_integrated_balance left right initial leftContinuous rightContinuous stopTime]
  ring

end ClockedLeakyHoldSource
end
end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
