import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Norm
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open Propagation.Interface
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section


private def epsilon : ℝ := (gramEntryBound : ℝ) / (factorScale : ℝ)^2

private theorem epsilon_nonnegative : 0 ≤ epsilon := by
  norm_num [epsilon,gramEntryBound,factorScale]

private theorem epsilon_small : 24 * epsilon < 1 := by
  norm_num [epsilon,gramEntryBound,factorScale]

private theorem diagonal_lower (a : OccupiedSlot) :
    1 - epsilon ≤ ‖gram a a‖ := by
  have triangle : (1 : ℝ) ≤ ‖gram a a‖ + epsilon := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖gram a a - (gram - 1) a a‖ := by
        simp [Matrix.sub_apply]
      _ ≤ ‖gram a a‖ + ‖(gram - 1) a a‖ := norm_sub_le _ _
      _ ≤ ‖gram a a‖ + epsilon := by
        have paid : ‖(gram - 1) a a‖ ≤ epsilon := gram_entry_norm a a
        linarith
  linarith

private theorem off_diagonal_sum (a : OccupiedSlot) :
    (∑ b ∈ Finset.univ.erase a, ‖gram a b‖) ≤ 23 * epsilon := by
  calc
    _ ≤ ∑ b ∈ Finset.univ.erase a, epsilon := by
      apply Finset.sum_le_sum
      intro b hb
      have different : b ≠ a := (Finset.mem_erase.mp hb).1
      have same : (gram - 1) a b = gram a b := by
        simp [Matrix.sub_apply,different.symm]
      rw [← same]
      exact gram_entry_norm a b
    _ = 23 * epsilon := by
      simp

theorem gram_positive : gram.PosDef := by
  apply gram_positive_semidef.posDef_iff_det_ne_zero.mpr
  apply det_ne_zero_of_sum_row_lt_diag
  intro a
  have left := off_diagonal_sum a
  have right := diagonal_lower a
  linarith [epsilon_small]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
