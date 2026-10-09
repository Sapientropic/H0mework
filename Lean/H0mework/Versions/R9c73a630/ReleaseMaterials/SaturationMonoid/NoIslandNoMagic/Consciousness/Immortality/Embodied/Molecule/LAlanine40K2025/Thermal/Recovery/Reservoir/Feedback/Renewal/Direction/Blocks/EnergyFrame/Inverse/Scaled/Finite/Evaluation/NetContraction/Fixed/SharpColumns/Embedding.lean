import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerColumns.Error
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

def columnEmbedding (g : ν → κ) : Matrix κ ν ℂ :=
  fun i j => if i=g j then 1 else 0

omit [Fintype ν] in
theorem column_embedding_adjoint_mul (g : ν → κ) (injective : Function.Injective g) :
    (columnEmbedding g)ᴴ*columnEmbedding g=1 := by
  ext i j
  by_cases same : i=j
  · subst j
    simp [columnEmbedding,Matrix.mul_apply,Matrix.conjTranspose_apply]
  · have different : g i ≠ g j := fun h => same (injective h)
    simp [columnEmbedding,Matrix.mul_apply,Matrix.conjTranspose_apply,
      same,Ne.symm different]

theorem column_embedding_norm [Nonempty ν] (g : ν → κ) (injective : Function.Injective g) :
    ‖columnEmbedding g‖ ≤ (1 : ℝ) := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (columnEmbedding g)
  rw [column_embedding_adjoint_mul g injective] at h
  simp only [CStarRing.norm_one] at h
  nlinarith [norm_nonneg (columnEmbedding g)]

omit [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν] in
theorem mul_column_embedding (A : Matrix ι κ ℂ) (g : ν → κ) :
    A*columnEmbedding g=A.submatrix id g := by
  ext i j
  simp [Matrix.mul_apply,columnEmbedding]

omit [DecidableEq ι] in
theorem submatrix_columns_norm_le [Nonempty ν] (A : Matrix ι κ ℂ) (g : ν → κ)
    (injective : Function.Injective g) :
    ‖A.submatrix id g‖ ≤ ‖A‖ := by
  rw [← mul_column_embedding]
  exact (Matrix.l2_opNorm_mul A (columnEmbedding g)).trans
    (by simpa using (mul_le_mul_of_nonneg_left (column_embedding_norm g injective)
      (norm_nonneg A)))

theorem submatrix_rows_norm_le [Nonempty ν] (A : Matrix κ ι ℂ) (f : ν → κ)
    (injective : Function.Injective f) :
    ‖A.submatrix f id‖ ≤ ‖A‖ := by
  calc
    _ = ‖(A.submatrix f id)ᴴ‖ := (Matrix.l2_opNorm_conjTranspose _).symm
    _ = ‖(Aᴴ).submatrix id f‖ := by rfl
    _ ≤ ‖Aᴴ‖ := submatrix_columns_norm_le _ f injective
    _ = ‖A‖ := Matrix.l2_opNorm_conjTranspose A

theorem submatrix_norm_le [Nonempty ι] [Nonempty ν]
    (A : Matrix κ κ ℂ) (f : ι → κ) (g : ν → κ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖A.submatrix f g‖ ≤ ‖A‖ := by
  change ‖(A.submatrix f id).submatrix id g‖ ≤ ‖A‖
  exact (submatrix_columns_norm_le _ g hg).trans
    (submatrix_rows_norm_le A f hf)


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
