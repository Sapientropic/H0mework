import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Indices

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gram_residual_nonnegative (A L : Matrix ι ι ℂ) (hermitian : A.IsHermitian) (delta : ℝ)
    (paid : ‖A-L*Lᴴ‖ ≤ delta) : 0 ≤ A+delta • (1 : Matrix ι ι ℂ) := by
  have gram := Matrix.posSemidef_self_mul_conjTranspose L
  have residual := hermitian.sub gram.isHermitian
  have bottom := residual.isSelfAdjoint.neg_algebraMap_norm_le_self
  rw [Algebra.algebraMap_eq_smul_one] at bottom
  have lower : -(delta • (1 : Matrix ι ι ℂ)) ≤ A-L*Lᴴ := by
    have compare := smul_le_smul_of_nonneg_right paid (zero_le_one : (0 : Matrix ι ι ℂ) ≤ 1)
    exact (neg_le_neg compare).trans bottom
  have positive := (neg_le_iff_add_nonneg').mp lower
  have whole := add_nonneg positive gram.nonneg
  convert whole using 1
  abel

theorem norm_bound_from_gram_factors (A L R : Matrix ι ι ℂ) (hermitian : A.IsHermitian) (mu delta : ℝ)
    (nonnegative : 0 ≤ mu)
    (minus : ‖(mu-delta) • (1 : Matrix ι ι ℂ)-A-L*Lᴴ‖ ≤ delta)
    (plus : ‖(mu-delta) • (1 : Matrix ι ι ℂ)+A-R*Rᴴ‖ ≤ delta) : ‖A‖ ≤ mu := by
  have hs : ((mu-delta) • (1 : Matrix ι ι ℂ)).IsHermitian := Matrix.isHermitian_one.smul (show IsSelfAdjoint (mu-delta) from IsSelfAdjoint.all _)
  have upper := gram_residual_nonnegative ((mu-delta) • (1 : Matrix ι ι ℂ)-A) L (hs.sub hermitian) delta minus
  have lower := gram_residual_nonnegative ((mu-delta) • (1 : Matrix ι ι ℂ)+A) R (hs.add hermitian) delta plus
  have up : 0 ≤ mu • (1 : Matrix ι ι ℂ)-A := by
    convert upper using 1
    module
  have down : 0 ≤ mu • (1 : Matrix ι ι ℂ)+A := by
    convert lower using 1
    module
  apply self_adjoint_norm_of_sides A hermitian mu nonnegative (sub_nonneg.mp up)
  rw [neg_smul]
  exact (neg_le_iff_add_nonneg').mpr down

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
