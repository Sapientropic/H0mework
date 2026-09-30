import H0mework.Physics.ConductanceCell.Bands

/-! # The local leakage law leaves a source-sized interior margin on the full input rail -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface

theorem quarticNFactor_bounds_on_rail {gate : ℝ} (rail : 0 ≤ gate ∧ gate ≤ 1) :
    1 / 256 ≤ quarticNFactor gate ∧ quarticNFactor gate ≤ 257 / 256 := by
  have lower : 0 ≤ gate ^ 4 := by positivity
  have upper := pow_le_pow_left₀ rail.1 rail.2 4
  norm_num at upper
  unfold quarticNFactor
  constructor <;> linarith

theorem quarticPFactor_bounds_on_rail {gate : ℝ} (rail : 0 ≤ gate ∧ gate ≤ 1) :
    1 / 256 ≤ quarticPFactor gate ∧ quarticPFactor gate ≤ 257 / 256 :=
  quarticNFactor_bounds_on_rail ⟨by linarith [rail.2], by linarith [rail.1]⟩

theorem normalized_equilibrium_interior {left right : ℝ}
    (leftRail : 0 ≤ left ∧ left ≤ 1) (rightRail : 0 ≤ right ∧ right ≤ 1) :
    1 / 4096 ≤ parallelPFactor left right / (parallelPFactor left right + seriesNFactor left right) ∧
      parallelPFactor left right / (parallelPFactor left right + seriesNFactor left right) ≤ 4095 / 4096 := by
  have pl := quarticPFactor_bounds_on_rail leftRail
  have pr := quarticPFactor_bounds_on_rail rightRail
  have nl := quarticNFactor_bounds_on_rail leftRail
  have nr := quarticNFactor_bounds_on_rail rightRail
  have up : 1 / 128 ≤ parallelPFactor left right ∧ parallelPFactor left right ≤ 257 / 128 := by
    unfold parallelPFactor
    constructor <;> linarith [pl.1, pl.2, pr.1, pr.2]
  have downLow := seriesNFactor_ge_half_of_lower left right (1 / 256) nl.1 nr.1
  have downHigh := (seriesNFactor_le_left left right).trans nl.2
  have positive := add_pos (parallelPFactor_pos left right) (seriesNFactor_pos left right)
  constructor
  · apply (le_div_iff₀ positive).mpr
    linarith [up.1, up.2]
  · apply (div_le_iff₀ positive).mpr
    linarith [up.1, up.2]

namespace LoadedConductanceCellSource

theorem inRail_normalized (source : LoadedConductanceCellSource) (gate : SIVolt)
    (rail : InRail source gate) : 0 ≤ source.normalizedGate gate ∧ source.normalizedGate gate ≤ 1 :=
  ⟨div_nonneg rail.1 source.supply_pos.le, (div_le_one₀ source.supply_pos).mpr rail.2⟩

theorem equilibrium_interior_of_inputs_in_rail (source : LoadedConductanceCellSource) (left right : SIVolt)
    (leftRail : InRail source left) (rightRail : InRail source right) :
    source.supply.value / 4096 ≤ (source.equilibrium left right).value ∧
      (source.equilibrium left right).value ≤ source.supply.value - source.supply.value / 4096 := by
  have interior := normalized_equilibrium_interior (source.inRail_normalized left leftRail)
    (source.inRail_normalized right rightRail)
  have lower := mul_le_mul_of_nonneg_left interior.1 source.supply_pos.le
  have upper := mul_le_mul_of_nonneg_left interior.2 source.supply_pos.le
  rw [source.equilibrium_normalized]
  constructor <;> linarith

end LoadedConductanceCellSource
end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
