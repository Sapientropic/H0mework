import H0mework.Physics.ConductanceCell.DrivenEnergy

/-! # Actual integrated source work and heat, not an endpoint-defined payment -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface MeasureTheory

noncomputable section
namespace LoadedConductanceCellSource

theorem powerFunctions_continuous (source : LoadedConductanceCellSource)
    (left right output : ℝ → SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value))
    (outputContinuous : Continuous (fun t => (output t).value)) :
    Continuous (fun t => (source.supplyPower (left t) (right t) (output t)).value) ∧
    Continuous (fun t => (source.dissipatedPower (left t) (right t) (output t)).value) := by
  have nl : Continuous (fun t => source.nConductance (left t)) := by
    unfold nConductance normalizedGate quarticNFactor
    fun_prop
  have nr : Continuous (fun t => source.nConductance (right t)) := by
    unfold nConductance normalizedGate quarticNFactor
    fun_prop
  have pl : Continuous (fun t => source.pConductance (left t)) := by
    unfold pConductance normalizedGate quarticPFactor
    fun_prop
  have pr : Continuous (fun t => source.pConductance (right t)) := by
    unfold pConductance normalizedGate quarticPFactor
    fun_prop
  have up : Continuous (fun t => source.pullUp (left t) (right t)) := pl.add pr
  have down : Continuous (fun t => source.pullDown (left t) (right t)) :=
    (nl.mul nr).div (nl.add nr) (fun t =>
      ne_of_gt (add_pos (source.nConductance_pos (left t)) (source.nConductance_pos (right t))))
  exact ⟨(up.mul continuous_const).mul (continuous_const.sub outputContinuous),
    (up.mul ((continuous_const.sub outputContinuous).pow 2)).add (down.mul (outputContinuous.pow 2))⟩

def drivenWorkAt (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ) : SIJoule :=
  ⟨∫ t in (0 : ℝ)..time, (source.drivenSupplyPowerAt left right initial t).value⟩

def drivenHeatAt (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ) : SIJoule :=
  ⟨∫ t in (0 : ℝ)..time, (source.drivenDissipatedPowerAt left right initial t).value⟩

theorem drivenHeatAt_nonneg (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt) (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (source.drivenHeatAt left right initial time).value :=
  intervalIntegral.integral_nonneg_of_forall nonnegative
    (fun t => source.drivenDissipatedPowerAt_nonneg left right initial t)

theorem drivenStoredEnergyAt_integrated_balance (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) (time : ℝ) :
    (source.drivenStoredEnergyAt left right initial time).value =
      source.capacitance.value / 2 * initial.value ^ 2 +
        (source.drivenWorkAt left right initial time).value -
        (source.drivenHeatAt left right initial time).value := by
  obtain ⟨supplyContinuous, heatContinuous⟩ := source.powerFunctions_continuous left right
    (fun t => ⟨source.drivenVoltageAt left right initial t⟩) leftContinuous rightContinuous
    (source.drivenVoltageAt_continuous left right initial leftContinuous rightContinuous)
  change Continuous (fun t => (source.drivenSupplyPowerAt left right initial t).value) at supplyContinuous
  change Continuous (fun t => (source.drivenDissipatedPowerAt left right initial t).value) at heatContinuous
  have paid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) time) =>
      source.drivenStoredEnergyAt_power_balance left right initial leftContinuous rightContinuous t)
    ((supplyContinuous.sub heatContinuous).intervalIntegrable 0 time)
  rw [intervalIntegral.integral_sub (supplyContinuous.intervalIntegrable 0 time)
    (heatContinuous.intervalIntegrable 0 time), source.drivenStoredEnergyAt_initial] at paid
  change (source.drivenWorkAt left right initial time).value -
    (source.drivenHeatAt left right initial time).value = _ at paid
  linarith

theorem drivenWorkAt_pays_energy_increase (source : LoadedConductanceCellSource)
    (left right : ℝ → SIVolt) (initial : SIVolt)
    (leftContinuous : Continuous (fun t => (left t).value))
    (rightContinuous : Continuous (fun t => (right t).value)) (time : ℝ) (nonnegative : 0 ≤ time) :
    (source.drivenStoredEnergyAt left right initial time).value -
        source.capacitance.value / 2 * initial.value ^ 2 ≤
      (source.drivenWorkAt left right initial time).value := by
  have paid := source.drivenStoredEnergyAt_integrated_balance left right initial leftContinuous rightContinuous time
  have heat := source.drivenHeatAt_nonneg left right initial time nonnegative
  linarith

end LoadedConductanceCellSource
end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
