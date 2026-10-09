import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.TensorTrace

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem reindex_energy (e : κ ≃ ι) (O rho : Matrix ι ι ℂ) :
    energy (O.submatrix e e) (rho.submatrix e e)=energy O rho := by
  unfold energy
  rw [Matrix.submatrix_mul_equiv]
  exact congrArg Complex.re (Equiv.sum_comp e (fun i => (O*rho) i i))

theorem tensor_energy_norm_right (O : Matrix (κ × ι) (κ × ι) ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hermitian : A.IsHermitian) (positive : B.PosSemidef) :
    |energy O (Matrix.kronecker B A)| ≤ (Fintype.card ι : ℝ)*‖A‖*‖O‖*B.trace.re := by
  let e : ι × κ ≃ κ × ι := Equiv.prodComm ι κ
  have swapped : (Matrix.kronecker B A).submatrix e e=Matrix.kronecker A B := by
    ext i j
    simp only [Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,e,Equiv.prodComm_apply]
    exact mul_comm _ _
  rw [← reindex_energy e O (Matrix.kronecker B A),swapped]
  have paid := tensor_energy_norm (O.submatrix e e) A B hermitian positive
  simpa only [Finite.reindex_norm] using paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
