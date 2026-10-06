import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Integrals
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Metric
open scoped BigOperators Matrix

variable {n : Type*} [Fintype n]

theorem congruence_entry (S X : Matrix n n ℝ) (i j : n) :
    (X.transpose*S*X) i j = ∑ k, ∑ l, X k i * X l j * S k l := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Source entry errors are transported with the actual two columns, retaining the AO metric. -/
theorem congruence_error (S T X : Matrix n n ℝ) (error : ℝ)
    (bounded : ∀ k l, |S k l-T k l| ≤ error) (i j : n) :
    |(X.transpose*S*X) i j-(X.transpose*T*X) i j| ≤
      error*(∑ k, |X k i|)*(∑ l, |X l j|) := by
  rw [congruence_entry,congruence_entry,← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,← mul_sub]
  calc
    _ ≤ ∑ k, ∑ l, |X k i * X l j * (S k l-T k l)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ k, ∑ l, |X k i| * |X l j| * error := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul,abs_mul]
      exact mul_le_mul_of_nonneg_left (bounded k l) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring

end LAlanine40K2025.UnifiedOrbitals.Metric
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
