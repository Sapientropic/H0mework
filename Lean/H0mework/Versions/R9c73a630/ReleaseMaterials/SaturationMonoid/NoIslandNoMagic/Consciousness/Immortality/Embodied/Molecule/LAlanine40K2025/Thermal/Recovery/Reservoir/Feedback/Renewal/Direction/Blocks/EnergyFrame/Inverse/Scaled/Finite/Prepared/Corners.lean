import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.TensorTrace

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem principal_order (f : κ → ι) (A B : Matrix ι ι ℂ) (ordered : A ≤ B) :
    A.submatrix f f ≤ B.submatrix f f := by
  have p := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr ordered)).submatrix f
  exact sub_nonneg.mp p.nonneg

omit [Fintype ι] [Fintype κ] in
theorem principal_one (f : κ → ι) (injective : Function.Injective f) :
    (1 : Matrix ι ι ℂ).submatrix f f=(1 : Matrix κ κ ℂ) := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.one_apply,injective.eq_iff]

theorem principal_norm (f : κ → ι) (injective : Function.Injective f) (A : Matrix ι ι ℂ)
    (hermitian : A.IsHermitian) : ‖A.submatrix f f‖ ≤ ‖A‖ := by
  have up := hermitian.isSelfAdjoint.le_algebraMap_norm_self
  have down := hermitian.neg.isSelfAdjoint.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one] at up down
  rw [norm_neg] at down
  have upper := principal_order f _ _ up
  have lower := principal_order f _ _ down
  have scalar (r : ℝ) : (r • (1 : Matrix ι ι ℂ)).submatrix f f=r • (1 : Matrix κ κ ℂ) := by
    rw [Matrix.submatrix_smul]
    change r • ((1 : Matrix ι ι ℂ).submatrix f f)=_
    rw [principal_one f injective]
  rw [scalar] at upper lower
  have negative : (-A).submatrix f f=-(A.submatrix f f) := rfl
  rw [negative] at lower
  apply self_adjoint_norm_of_sides _ (hermitian.submatrix f) ‖A‖ (norm_nonneg A) upper
  simpa only [neg_smul,neg_neg] using neg_le_neg lower

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
