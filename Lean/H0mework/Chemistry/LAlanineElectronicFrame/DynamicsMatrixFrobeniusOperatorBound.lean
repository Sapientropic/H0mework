import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.RowCol

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.MatrixNorm

open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Frobenius in
def frobeniusNorm (A : Matrix ι ι ℂ) : ℝ := ‖A‖

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_nonneg (A : Matrix ι ι ℂ) : 0 ≤ frobeniusNorm A := norm_nonneg A

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_eq (A : Matrix ι ι ℂ) :
    frobeniusNorm A = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  simpa only [frobeniusNorm, Real.rpow_two, Real.sqrt_eq_rpow] using Matrix.frobenius_norm_def A

theorem l2_norm_le_frobenius (A : Matrix ι ι ℂ) : ‖A‖ ≤ frobeniusNorm A := by
  rw [Matrix.cstar_norm_def]
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) A).opNorm_le_bound (frobeniusNorm_nonneg A)
  intro x
  have bound := Matrix.frobenius_norm_mul A (Matrix.replicateCol Unit (WithLp.ofLp x))
  rw [← Matrix.replicateCol_mulVec, Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at bound
  exact bound

theorem l2_norm_le_of_sq_sum_le (A : Matrix ι ι ℂ) {bound : ℝ}
    (nonnegative : 0 ≤ bound) (entries : (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ bound ^ 2) :
    ‖A‖ ≤ bound := by
  apply (l2_norm_le_frobenius A).trans
  rw [frobeniusNorm_eq]
  exact Real.sqrt_le_iff.mpr ⟨nonnegative, entries⟩

end
end LAlanine40K2025.ElectronicFrame.MatrixNorm
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
