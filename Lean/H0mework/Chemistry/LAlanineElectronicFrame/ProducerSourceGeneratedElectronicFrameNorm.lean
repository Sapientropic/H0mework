import H0mework.Chemistry.LAlanineElectronicFrame.SourceSourceBoundLAlanineElectronicFrame
import H0mework.Chemistry.LAlaninePropagation.GeneratedNativeDuration

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Source

open Propagation.Interface
open scoped Matrix.Norms.L2Operator
noncomputable section

def deltaNumerator (left right : Basis) : Int :=
  crossNumerator left right - if left = right then 1000000000000000 else 0

def deltaEntryMagnitude : Nat := ∑ left : Basis, ∑ right : Basis, (deltaNumerator left right).natAbs

def symmetricDeltaNumerator (left right : Basis) : Int := deltaNumerator left right + deltaNumerator right left

def symmetricEntryMagnitude : Nat :=
  ∑ left : Basis, ∑ right : Basis, (symmetricDeltaNumerator left right).natAbs

theorem cross_sub_one_entry (left right : Basis) :
    (crossMatrix - 1) left right = (deltaNumerator left right : ℂ) / 1000000000000000 := by
  by_cases same : left = right <;>
    simp [crossMatrix, deltaNumerator, Matrix.sub_apply, same]
  ring

theorem crossEntrySum_exact :
    (∑ left : Basis, ∑ right : Basis, ‖(crossMatrix - 1) left right‖) =
      (deltaEntryMagnitude : ℝ) / 1000000000000000 := by
  simp only [deltaEntryMagnitude, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  rw [cross_sub_one_entry]
  norm_num [norm_div, Complex.norm_intCast, Nat.cast_natAbs]

theorem symmetricDelta_entry (left right : Basis) :
    (star (crossMatrix - 1) + (crossMatrix - 1)) left right =
      (symmetricDeltaNumerator left right : ℂ) / 1000000000000000 := by
  change star ((crossMatrix - 1) right left) + (crossMatrix - 1) left right = _
  rw [cross_sub_one_entry, cross_sub_one_entry]
  simp [symmetricDeltaNumerator, Int.cast_add, add_div, add_comm]

theorem symmetricCrossEntrySum_exact :
    (∑ left : Basis, ∑ right : Basis, ‖(star (crossMatrix - 1) + (crossMatrix - 1)) left right‖) =
      (symmetricEntryMagnitude : ℝ) / 1000000000000000 := by
  simp only [symmetricEntryMagnitude, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  rw [symmetricDelta_entry]
  norm_num [norm_div, Complex.norm_intCast, Nat.cast_natAbs]

theorem gram_delta_decomposition :
    star crossMatrix * crossMatrix - 1 =
      (star (crossMatrix - 1) + (crossMatrix - 1)) + star (crossMatrix - 1) * (crossMatrix - 1) := by
  simp only [star_sub, star_one]
  noncomm_ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem deltaEntryMagnitude_exact : deltaEntryMagnitude = 351148 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem symmetricEntryMagnitude_exact : symmetricEntryMagnitude = 15264 := by decide

theorem crossMatrix_norm_bound : ‖crossMatrix - 1‖ ≤ (351148 : ℝ) / 1000000000000000 := by
  have bound := Propagation.Dynamics.NativeDuration.matrixOperator_norm_le_entrySum (crossMatrix - 1)
  change ‖crossMatrix - 1‖ ≤ _ at bound
  rw [crossEntrySum_exact, deltaEntryMagnitude_exact] at bound
  exact bound

theorem crossMatrix_close : ‖crossMatrix - 1‖ < 1 :=
  crossMatrix_norm_bound.trans_lt (by norm_num)

theorem symmetricDelta_norm_bound :
    ‖star (crossMatrix - 1) + (crossMatrix - 1)‖ ≤ (15264 : ℝ) / 1000000000000000 := by
  have bound := Propagation.Dynamics.NativeDuration.matrixOperator_norm_le_entrySum
    (star (crossMatrix - 1) + (crossMatrix - 1))
  change ‖star (crossMatrix - 1) + (crossMatrix - 1)‖ ≤ _ at bound
  rw [symmetricCrossEntrySum_exact, symmetricEntryMagnitude_exact] at bound
  exact bound

theorem gram_norm_bound :
    ‖star crossMatrix * crossMatrix - 1‖ ≤ (15264 : ℝ) / 1000000000000000 +
      ((351148 : ℝ) / 1000000000000000) ^ 2 := by
  rw [gram_delta_decomposition]
  calc
    ‖(star (crossMatrix - 1) + (crossMatrix - 1)) + star (crossMatrix - 1) * (crossMatrix - 1)‖ ≤
        ‖star (crossMatrix - 1) + (crossMatrix - 1)‖ + ‖star (crossMatrix - 1) * (crossMatrix - 1)‖ := norm_add_le _ _
    _ ≤ (15264 : ℝ) / 1000000000000000 + ‖crossMatrix - 1‖ * ‖crossMatrix - 1‖ :=
      add_le_add symmetricDelta_norm_bound (by simpa only [norm_star] using norm_mul_le (star (crossMatrix - 1)) (crossMatrix - 1))
    _ ≤ _ := by nlinarith [crossMatrix_norm_bound, norm_nonneg (crossMatrix - 1)]

theorem gram_norm_small : ‖star crossMatrix * crossMatrix - 1‖ < (2 : ℝ) / 10 ^ 11 :=
  gram_norm_bound.trans_lt (by norm_num)

end
end LAlanine40K2025.ElectronicFrame.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
