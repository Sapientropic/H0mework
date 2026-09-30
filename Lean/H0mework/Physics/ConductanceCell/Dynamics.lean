import H0mework.Realization.RelaxationFlow.P245
import H0mework.Physics.ConductanceCell.CellSource
import H0mework.Physics.RLCResponse.Transient

/-! # The source topology generates the loaded-cell KCL trajectory -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface
open SaturationMonoid.AffineRelaxation
open Netlist.Dissipative.Dimensioned.Driven.Producer

noncomputable section
namespace LoadedConductanceCellSource

def voltageAt (source : LoadedConductanceCellSource) (left right initial : SIVolt) (time : ℝ) : ℝ :=
  realDecayRelaxFlow (source.equilibrium left right).value (source.rate left right) time initial.value

def flowAt (source : LoadedConductanceCellSource) (left right initial : SIVolt)
    (time : SISecond) : SIVolt :=
  ⟨source.voltageAt left right initial time.value⟩

theorem voltageAt_initial (source : LoadedConductanceCellSource) (left right initial : SIVolt) :
    source.voltageAt left right initial 0 = initial.value := by
  exact realDecayRelaxFlow_zero _ _ _

theorem voltageAt_kcl (source : LoadedConductanceCellSource) (left right initial : SIVolt)
    (time : ℝ) :
    HasDerivAt (source.voltageAt left right initial)
      ((source.pullUp left right * (source.supply.value - source.voltageAt left right initial time) -
        source.pullDown left right * source.voltageAt left right initial time) /
          source.capacitance.value) time := by
  have totalNonzero := ne_of_gt (add_pos (source.pullUp_pos left right) (source.pullDown_pos left right))
  have capacitanceNonzero := ne_of_gt source.capacitance_pos
  convert hasDerivAt_realDecayRelaxFlow (source.equilibrium left right).value
    (source.rate left right) time initial.value using 1
  all_goals first | rfl | (
    change (source.pullUp left right * (source.supply.value - source.voltageAt left right initial time) -
        source.pullDown left right * source.voltageAt left right initial time) /
          source.capacitance.value =
      ((source.pullUp left right + source.pullDown left right) / source.capacitance.value) *
        (source.pullUp left right * source.supply.value /
          (source.pullUp left right + source.pullDown left right) -
          source.voltageAt left right initial time)
    field_simp
    ring)

theorem flowAt_initial (source : LoadedConductanceCellSource) (left right initial : SIVolt) :
    source.flowAt left right initial ⟨0⟩ = initial := by
  apply SIQuantity.ext
  exact source.voltageAt_initial left right initial

theorem voltageAt_closed (source : LoadedConductanceCellSource) (left right initial : SIVolt)
    (time : ℝ) :
    source.voltageAt left right initial time =
      (source.equilibrium left right).value +
        Real.exp (-source.rate left right * time) *
          (initial.value - (source.equilibrium left right).value) := by
  unfold voltageAt
  rw [realDecayRelaxFlow_eq_closed]
  unfold realDecayResidual
  change _ - _ * (_ - _) = _
  ring

theorem voltageAt_mem_rail (source : LoadedConductanceCellSource) (left right initial : SIVolt)
    (initialRail : InRail source initial) (time : ℝ) (nonnegative : 0 ≤ time) :
    InRail source ⟨source.voltageAt left right initial time⟩ := by
  have eqRail := source.equilibrium_mem_rail left right
  have expPositive := (Real.exp_pos (-source.rate left right * time)).le
  have expBound : Real.exp (-source.rate left right * time) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (source.rate_pos left right).le) nonnegative
  change 0 ≤ source.voltageAt left right initial time ∧
    source.voltageAt left right initial time ≤ source.supply.value
  rw [source.voltageAt_closed]
  constructor
  · nlinarith [mul_nonneg expPositive initialRail.1,
      mul_nonneg (sub_nonneg.mpr expBound) eqRail.1]
  · nlinarith [mul_nonneg expPositive (sub_nonneg.mpr initialRail.2),
      mul_nonneg (sub_nonneg.mpr expBound) (sub_nonneg.mpr eqRail.2)]

theorem voltageAt_error (source : LoadedConductanceCellSource) (left right initial : SIVolt)
    (time : ℝ) :
    |source.voltageAt left right initial time - (source.equilibrium left right).value| =
      Real.exp (-source.rate left right * time) *
        |initial.value - (source.equilibrium left right).value| := by
  rw [source.voltageAt_closed]
  have cancel : (source.equilibrium left right).value +
      Real.exp (-source.rate left right * time) *
        (initial.value - (source.equilibrium left right).value) -
      (source.equilibrium left right).value =
        Real.exp (-source.rate left right * time) *
          (initial.value - (source.equilibrium left right).value) := by ring
  rw [cancel, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- A leakage floor is derived from the local law, not supplied as a delay certificate. -/
def minimumRate (source : LoadedConductanceCellSource) : ℝ :=
  1 / (128 * source.resistance.value * source.capacitance.value)

theorem minimumRate_pos (source : LoadedConductanceCellSource) : 0 < source.minimumRate := by
  unfold minimumRate
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) source.resistance_pos) source.capacitance_pos)

theorem minimumRate_le_rate (source : LoadedConductanceCellSource) (left right : SIVolt) :
    source.minimumRate ≤ source.rate left right := by
  have pLeft : 1 / 256 ≤ quarticPFactor (source.normalizedGate left) := by
    unfold quarticPFactor
    have fourth : 0 ≤ (1 - source.normalizedGate left) ^ 4 := by positivity
    linarith
  have pRight : 1 / 256 ≤ quarticPFactor (source.normalizedGate right) := by
    unfold quarticPFactor
    have fourth : 0 ≤ (1 - source.normalizedGate right) ^ 4 := by positivity
    linarith
  have upLower : 1 / (128 * source.resistance.value) ≤ source.pullUp left right := by
    rw [source.pullUp_normalized]
    have scaled := mul_le_mul_of_nonneg_left (add_le_add pLeft pRight)
      (inv_nonneg.mpr source.resistance_pos.le)
    calc
      _ = source.resistance.value⁻¹ * (1 / 256 + 1 / 256) := by ring
      _ ≤ _ := scaled
  unfold minimumRate rate
  have lower := div_le_div_of_nonneg_right
    (le_trans upLower (le_add_of_nonneg_right (source.pullDown_pos left right).le))
    source.capacitance_pos.le
  calc
    _ = (1 / (128 * source.resistance.value)) / source.capacitance.value := by ring
    _ ≤ _ := lower

/-- One source-only bound works for every held pair of input voltages. -/
def settlingTime (source : LoadedConductanceCellSource) : SISecond :=
  ⟨positiveExponentialSettlingTime source.minimumRate source.supply.value (source.supply.value / 8)⟩

theorem settlingTime_pos (source : LoadedConductanceCellSource) : 0 < source.settlingTime.value :=
  positiveExponentialSettlingTime_pos source.minimumRate_pos source.supply_pos.le
    (div_pos source.supply_pos (by norm_num))

theorem voltageAt_settles (source : LoadedConductanceCellSource) (left right initial : SIVolt)
    (initialRail : InRail source initial) (time : ℝ)
    (late : source.settlingTime.value ≤ time) :
    |source.voltageAt left right initial time - (source.equilibrium left right).value| <
      source.supply.value / 8 := by
  have nonnegative : 0 ≤ time := le_trans source.settlingTime_pos.le late
  have eqRail := source.equilibrium_mem_rail left right
  have initialError : |initial.value - (source.equilibrium left right).value| ≤ source.supply.value := by
    exact abs_le.mpr ⟨by linarith [initialRail.1, eqRail.2], by linarith [initialRail.2, eqRail.1]⟩
  have exponential : Real.exp (-source.rate left right * time) ≤
      Real.exp (-source.minimumRate * time) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (source.minimumRate_le_rate left right)) nonnegative
  rw [source.voltageAt_error]
  calc
    _ ≤ Real.exp (-source.minimumRate * time) * source.supply.value :=
      mul_le_mul exponential initialError (abs_nonneg _) (Real.exp_pos _).le
    _ = source.supply.value * Real.exp (-source.minimumRate * time) := mul_comm _ _
    _ < _ := positiveExponentialEnvelope_settles source.minimumRate_pos
      (div_pos source.supply_pos (by norm_num)) late

end LoadedConductanceCellSource
end
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
