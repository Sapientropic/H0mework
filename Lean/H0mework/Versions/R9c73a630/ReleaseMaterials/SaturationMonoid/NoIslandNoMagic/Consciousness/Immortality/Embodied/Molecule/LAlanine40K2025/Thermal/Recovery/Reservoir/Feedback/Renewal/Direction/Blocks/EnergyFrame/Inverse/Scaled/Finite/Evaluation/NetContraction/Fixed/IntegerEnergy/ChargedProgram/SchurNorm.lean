import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.SpectralNorm
/-! Schur row/column bounds for the original fixed-scale integer matrices, without Hermitian assumptions on rounded entries. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
theorem schur_vector_square (A : Matrix α β ℂ) (R : ℝ) (hR : 0 ≤ R)
    (rows : ∀ i, ∑ j, ‖A i j‖ ≤ R) (cols : ∀ j, ∑ i, ‖A i j‖ ≤ R)
    (x : β → ℂ) :
    (∑ i, ‖(A *ᵥ x) i‖^2) ≤ R^2 * ∑ j, ‖x j‖^2 := by
  have point (i : α) : ‖(A *ᵥ x) i‖^2 ≤ R * ∑ j, ‖A i j‖*‖x j‖^2 := by
    have triangle : ‖(A *ᵥ x) i‖ ≤ ∑ j, ‖A i j‖*‖x j‖ := by
      simpa only [Matrix.mulVec, dotProduct, norm_mul] using
        (norm_sum_le (Finset.univ : Finset β) (fun j => A i j*x j))
    have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset β)
      (r := fun j => ‖A i j‖*‖x j‖)
      (f := fun j => ‖A i j‖)
      (g := fun j => ‖A i j‖*‖x j‖^2)
      (fun j _ => norm_nonneg (A i j))
      (fun j _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun j _ => by ring_nf; rfl)
    exact ((pow_le_pow_left₀ (norm_nonneg _) triangle 2).trans cauchy).trans
      (mul_le_mul_of_nonneg_right (rows i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))))
  calc
    _ ≤ ∑ i, R * ∑ j, ‖A i j‖*‖x j‖^2 := Finset.sum_le_sum (fun i _ => point i)
    _ = R * ∑ j, (∑ i, ‖A i j‖)*‖x j‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ R * ∑ j, R*‖x j‖^2 := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (cols j) (sq_nonneg _))
    _ = R^2 * ∑ j, ‖x j‖^2 := by rw [← Finset.mul_sum]; ring

theorem operator_le_row_column (A : Matrix α β ℂ) (R : ℝ) (hR : 0 ≤ R)
    (rows : ∀ i, ∑ j, ‖A i j‖ ≤ R) (cols : ∀ j, ∑ i, ‖A i j‖ ≤ R) :
    ‖A‖ ≤ R := by
  rw [Matrix.l2_opNorm_def]
  apply ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := α) (n := β)).trans
    LinearMap.toContinuousLinearMap A).opNorm_le_bound hR
  intro x
  change ‖(WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) : EuclideanSpace ℂ α)‖ ≤ R*‖x‖
  have square : ‖(WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) : EuclideanSpace ℂ α)‖^2 ≤
      (R*‖x‖)^2 := by
    rw [EuclideanSpace.norm_sq_eq,mul_pow,EuclideanSpace.norm_sq_eq]
    exact schur_vector_square A R hR rows cols (WithLp.ofLp x)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _))).mp square

omit [Fintype α] [Fintype β] [DecidableEq β] in
theorem integer_entry_norm_majorant (A : MatrixInt α β) (i : α) (j : β) :
    ‖value A i j‖ ≤ ((|A.re i j|+|A.im i j| : Int) : ℝ)/(scale : ℝ) := by
  have rawBound : ‖raw A i j‖ ≤ |(A.re i j : ℝ)|+|(A.im i j : ℝ)| := by
    simpa [raw] using Complex.norm_le_abs_re_add_abs_im (raw A i j)
  have scaled := mul_le_mul_of_nonneg_left rawBound
    (by norm_num : (0 : ℝ) ≤ (10^30 : ℝ)⁻¹)
  simpa [value,Matrix.smul_apply,smul_eq_mul,norm_mul,scale,div_eq_mul_inv,mul_comm] using scaled

theorem integer_operator_row_column_bound (A : MatrixInt α β) (radius : Int)
    (nonnegative : 0 ≤ radius)
    (rows : ∀ i, ∑ j, (|A.re i j|+|A.im i j|) ≤ radius)
    (cols : ∀ j, ∑ i, (|A.re i j|+|A.im i j|) ≤ radius) :
    ‖value A‖ ≤ (radius : ℝ)/(scale : ℝ) := by
  have scaleNonnegative : (0 : ℝ) ≤ (scale : ℝ) := by norm_num [scale]
  apply operator_le_row_column (value A) ((radius : ℝ)/(scale : ℝ))
    (div_nonneg (by exact_mod_cast nonnegative) scaleNonnegative)
  · intro i
    calc
      _ ≤ ∑ j, (((|A.re i j|+|A.im i j| : Int) : ℝ)/(scale : ℝ)) :=
        Finset.sum_le_sum (fun j _ => integer_entry_norm_majorant A i j)
      _ = ((∑ j, (|A.re i j|+|A.im i j|) : Int) : ℝ)/(scale : ℝ) := by
        rw [← Finset.sum_div]
        norm_cast
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast rows i) scaleNonnegative
  · intro j
    calc
      _ ≤ ∑ i, (((|A.re i j|+|A.im i j| : Int) : ℝ)/(scale : ℝ)) :=
        Finset.sum_le_sum (fun i _ => integer_entry_norm_majorant A i j)
      _ = ((∑ i, (|A.re i j|+|A.im i j|) : Int) : ℝ)/(scale : ℝ) := by
        rw [← Finset.sum_div]
        norm_cast
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast cols j) scaleNonnegative

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
