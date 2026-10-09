import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.NonDonor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def ordinaryCore (x y : ℝ) : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  smallLoaded x y-(sineHat : ℂ)^2 • Matrix.kronecker (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) numericEnvironmentRead

theorem environment_block (a b : Basis) (distinct : a ≠ b) :
    (Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead).submatrix
      (orbitPCE a b) (orbitPCE a b)=
    Matrix.kronecker (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) numericEnvironmentRead := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,orbitPCE,Matrix.one_apply]
  rw [if_congr (orbitPC_injective a b distinct).eq_iff rfl rfl]

private theorem restrict_expression {ι κ : Type*} (H D L R : Matrix ι ι ℂ)
    (s l r : ℂ) (f : κ → ι) :
    (H-s • D+l • L+r • R).submatrix f f=
      H.submatrix f f-s • D.submatrix f f+l • L.submatrix f f+r • R.submatrix f f := rfl

theorem original_rational_block (a b : Basis) (distinct : a ≠ b) :
    rationalCore.submatrix (orbitPCE a b) (orbitPCE a b)=ordinaryCore (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) := by
  rw [rationalCore,restrict_expression,nondonor_left_block a b distinct,nondonor_right_block a b distinct,
    smul_zero,smul_zero,add_zero,add_zero,original_numeric_load_block a b distinct,environment_block a b distinct]
  rfl

theorem ordinary_monotone (x y a b : ℝ) (first : a ≤ x) (second : b ≤ y) :
    ordinaryCore a b ≤ ordinaryCore x y := by
  have hpc := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (scalar_monotone x y a b first second))
  have delta : ordinaryCore x y-ordinaryCore a b=Matrix.kronecker (scalarHpc x y-scalarHpc a b)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    simp only [ordinaryCore,smallLoaded,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
      Matrix.sub_apply,Matrix.add_apply,Matrix.kronecker,Matrix.kroneckerMap_apply]
    ring
  apply sub_nonneg.mp
  rw [delta]
  exact (hpc.kronecker Matrix.PosSemidef.one).nonneg

theorem original_rational_offDiagonal_envelope (a b : Basis) (ordered : a < b) :
    rationalCore.submatrix (orbitPCE 0 1) (orbitPCE 0 1) ≤ rationalCore.submatrix (orbitPCE a b) (orbitPCE a b) ∧
    rationalCore.submatrix (orbitPCE a b) (orbitPCE a b) ≤ rationalCore.submatrix (orbitPCE 96 97) (orbitPCE 96 97) := by
  rw [original_rational_block 0 1 (by decide),original_rational_block a b ordered.ne,original_rational_block 96 97 (by decide)]
  have bounds := ordered_source_limits a b ordered
  exact ⟨ordinary_monotone _ _ _ _ bounds.1 bounds.2.1,ordinary_monotone _ _ _ _ bounds.2.2.1 bounds.2.2.2⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
