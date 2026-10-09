import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Matrix

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

open scoped Matrix.Norms.Frobenius in
def frobenius (A : Matrix α β ℂ) : ℝ := ‖A‖

open scoped Matrix.Norms.Frobenius in
theorem frobenius_nonneg (A : Matrix α β ℂ) : 0 ≤ frobenius A := norm_nonneg A

open scoped Matrix.Norms.Frobenius in
theorem frobenius_value (A : Matrix α β ℂ) :
    frobenius A=Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) := by
  simpa only [frobenius,Real.rpow_two,Real.sqrt_eq_rpow] using Matrix.frobenius_norm_def A

variable [DecidableEq β]

theorem operator_le_frobenius (A : Matrix α β ℂ) : ‖A‖ ≤ frobenius A := by
  rw [Matrix.l2_opNorm_def]
  apply ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := α) (n := β)).trans LinearMap.toContinuousLinearMap A).opNorm_le_bound (frobenius_nonneg A)
  intro x
  have bound := Matrix.frobenius_norm_mul A (Matrix.replicateCol Unit (WithLp.ofLp x))
  rw [← Matrix.replicateCol_mulVec,Matrix.frobenius_norm_replicateCol,Matrix.frobenius_norm_replicateCol] at bound
  exact bound

theorem norm_from_entries (A : Matrix α β ℂ) (eps : ℝ) (nonnegative : 0 ≤ eps)
    (rows : Fintype.card α ≤ 64) (cols : Fintype.card β ≤ 64) (entries : ∀ i j, ‖A i j‖ ≤ eps) :
    ‖A‖ ≤ 64*eps := by
  apply (operator_le_frobenius A).trans
  rw [frobenius_value]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  have rc : (Fintype.card α : ℝ) ≤ 64 := by exact_mod_cast rows
  have cc : (Fintype.card β : ℝ) ≤ 64 := by exact_mod_cast cols
  calc
    _ ≤ ∑ _i : α, ∑ _j : β, eps^2 := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
      (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (entries i j) 2))
    _ = (Fintype.card α : ℝ)*(Fintype.card β : ℝ)*eps^2 := by simp; ring
    _ ≤ (64*eps)^2 := by nlinarith [mul_le_mul rc cc (Nat.cast_nonneg (Fintype.card β)) (by norm_num : (0 : ℝ) ≤ 64),sq_nonneg eps]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
