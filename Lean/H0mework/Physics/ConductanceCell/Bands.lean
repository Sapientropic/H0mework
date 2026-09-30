import H0mework.Physics.ConductanceCell.CellSource
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Continuous input bands generate a separated cell equilibrium

The low/high consumers are voltage intervals, not truth-table premises.
Bounds on the fixed local quartics pass through the literal parallel/series
network and yield stronger equilibrium margins than the requested eighth rails.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Conductance

open Units.Interface

noncomputable section

theorem quarticNFactor_le_of_low {gate : ℝ} (low : 0 ≤ gate ∧ gate ≤ 1 / 4) :
    quarticNFactor gate ≤ 1 / 128 := by
  have power := pow_le_pow_left₀ low.1 low.2 4
  norm_num at power
  unfold quarticNFactor
  linarith

theorem quarticPFactor_ge_of_low {gate : ℝ} (low : 0 ≤ gate ∧ gate ≤ 1 / 4) :
    41 / 128 ≤ quarticPFactor gate := by
  have complement : (3 : ℝ) / 4 ≤ 1 - gate := by linarith [low.2]
  have power := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) complement 4
  norm_num at power
  unfold quarticPFactor
  linarith

theorem quarticNFactor_ge_of_high {gate : ℝ} (high : 3 / 4 ≤ gate ∧ gate ≤ 1) :
    41 / 128 ≤ quarticNFactor gate := by
  have power := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) high.1 4
  norm_num at power
  unfold quarticNFactor
  linarith

theorem quarticPFactor_le_of_high {gate : ℝ} (high : 3 / 4 ≤ gate ∧ gate ≤ 1) :
    quarticPFactor gate ≤ 1 / 128 := by
  have complement : 0 ≤ 1 - gate ∧ 1 - gate ≤ (1 : ℝ) / 4 := by
    constructor <;> linarith [high.1, high.2]
  exact quarticNFactor_le_of_low complement

theorem seriesNFactor_le_left (left right : ℝ) :
    seriesNFactor left right ≤ quarticNFactor left := by
  apply (div_le_iff₀ (add_pos (quarticNFactor_pos left) (quarticNFactor_pos right))).mpr
  nlinarith [sq_nonneg (quarticNFactor left)]

theorem seriesNFactor_ge_half_of_lower (left right lower : ℝ)
    (leftBound : lower ≤ quarticNFactor left) (rightBound : lower ≤ quarticNFactor right) :
    lower / 2 ≤ seriesNFactor left right := by
  apply (le_div_iff₀ (add_pos (quarticNFactor_pos left) (quarticNFactor_pos right))).mpr
  have one := mul_nonneg (sub_nonneg.mpr leftBound) (quarticNFactor_pos right).le
  have two := mul_nonneg (sub_nonneg.mpr rightBound) (quarticNFactor_pos left).le
  nlinarith

theorem parallelPFactor_le_of_high_high {left right : ℝ}
    (leftHigh : 3 / 4 ≤ left ∧ left ≤ 1) (rightHigh : 3 / 4 ≤ right ∧ right ≤ 1) :
    parallelPFactor left right ≤ 1 / 64 := by
  have one := quarticPFactor_le_of_high leftHigh
  have two := quarticPFactor_le_of_high rightHigh
  unfold parallelPFactor
  linarith

theorem seriesNFactor_ge_of_high_high {left right : ℝ}
    (leftHigh : 3 / 4 ≤ left ∧ left ≤ 1) (rightHigh : 3 / 4 ≤ right ∧ right ≤ 1) :
    41 / 256 ≤ seriesNFactor left right := by
  have bound := seriesNFactor_ge_half_of_lower left right (41 / 128)
    (quarticNFactor_ge_of_high leftHigh) (quarticNFactor_ge_of_high rightHigh)
  norm_num at bound ⊢
  exact bound

theorem normalized_equilibrium_le_four_forty_fifths {left right : ℝ}
    (leftHigh : 3 / 4 ≤ left ∧ left ≤ 1) (rightHigh : 3 / 4 ≤ right ∧ right ≤ 1) :
    parallelPFactor left right / (parallelPFactor left right + seriesNFactor left right) ≤
      4 / 45 := by
  apply (div_le_iff₀ (add_pos (parallelPFactor_pos left right) (seriesNFactor_pos left right))).mpr
  have up := parallelPFactor_le_of_high_high leftHigh rightHigh
  have down := seriesNFactor_ge_of_high_high leftHigh rightHigh
  linarith

theorem normalized_equilibrium_ge_forty_one_forty_seconds {left right : ℝ}
    (leftLow : 0 ≤ left ∧ left ≤ 1 / 4) :
    41 / 42 ≤
      parallelPFactor left right / (parallelPFactor left right + seriesNFactor left right) := by
  apply (le_div_iff₀ (add_pos (parallelPFactor_pos left right) (seriesNFactor_pos left right))).mpr
  have upLower := quarticPFactor_ge_of_low leftLow
  have otherUp := quarticPFactor_pos right
  have downUpper := (seriesNFactor_le_left left right).trans (quarticNFactor_le_of_low leftLow)
  unfold parallelPFactor
  linarith

namespace LoadedConductanceCellSource

theorem lowBand_normalized (source : LoadedConductanceCellSource) (gate : SIVolt)
    (low : LowBand source gate) :
    0 ≤ source.normalizedGate gate ∧ source.normalizedGate gate ≤ 1 / 4 := by
  constructor
  · exact div_nonneg low.1 source.supply_pos.le
  · apply (div_le_iff₀ source.supply_pos).mpr
    dsimp only [LowBand] at low
    linarith [low.2]

theorem highBand_normalized (source : LoadedConductanceCellSource) (gate : SIVolt)
    (high : HighBand source gate) :
    3 / 4 ≤ source.normalizedGate gate ∧ source.normalizedGate gate ≤ 1 := by
  constructor
  · apply (le_div_iff₀ source.supply_pos).mpr
    dsimp only [HighBand] at high
    linarith [high.1]
  · apply (div_le_iff₀ source.supply_pos).mpr
    simpa only [one_mul] using high.2

theorem equilibrium_le_four_forty_fifths_of_high_high
    (source : LoadedConductanceCellSource) (left right : SIVolt)
    (leftHigh : HighBand source left) (rightHigh : HighBand source right) :
    (source.equilibrium left right).value ≤ (4 / 45 : ℝ) * source.supply.value := by
  rw [source.equilibrium_normalized]
  have bound := normalized_equilibrium_le_four_forty_fifths
    (source.highBand_normalized left leftHigh) (source.highBand_normalized right rightHigh)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left bound source.supply_pos.le

theorem equilibrium_le_eighth_of_high_high
    (source : LoadedConductanceCellSource) (left right : SIVolt)
    (leftHigh : HighBand source left) (rightHigh : HighBand source right) :
    (source.equilibrium left right).value ≤ source.supply.value / 8 := by
  have bound := source.equilibrium_le_four_forty_fifths_of_high_high left right leftHigh rightHigh
  nlinarith [source.supply_pos]

theorem forty_one_forty_seconds_le_equilibrium_of_low_left
    (source : LoadedConductanceCellSource) (left right : SIVolt)
    (leftLow : LowBand source left) :
    (41 / 42 : ℝ) * source.supply.value ≤ (source.equilibrium left right).value := by
  rw [source.equilibrium_normalized]
  have bound := normalized_equilibrium_ge_forty_one_forty_seconds
    (right := source.normalizedGate right) (source.lowBand_normalized left leftLow)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left bound source.supply_pos.le

theorem seven_eighths_le_equilibrium_of_low_left
    (source : LoadedConductanceCellSource) (left right : SIVolt)
    (leftLow : LowBand source left) :
    7 * source.supply.value / 8 ≤ (source.equilibrium left right).value := by
  have bound := source.forty_one_forty_seconds_le_equilibrium_of_low_left left right leftLow
  nlinarith [source.supply_pos]

theorem equilibrium_swap (source : LoadedConductanceCellSource) (left right : SIVolt) :
    source.equilibrium left right = source.equilibrium right left := by
  apply SIQuantity.ext
  simp only [equilibrium, pullUp, pullDown, add_comm, mul_comm]

theorem seven_eighths_le_equilibrium_of_low_right
    (source : LoadedConductanceCellSource) (left right : SIVolt)
    (rightLow : LowBand source right) :
    7 * source.supply.value / 8 ≤ (source.equilibrium left right).value := by
  rw [source.equilibrium_swap]
  exact source.seven_eighths_le_equilibrium_of_low_left right left rightLow

end LoadedConductanceCellSource

end

end Cells.Conductance
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
