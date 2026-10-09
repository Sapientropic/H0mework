import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Corners
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.TensorBudget

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def diagonalReadout (w : κ → ℝ) (O : Matrix (ι × κ) (ι × κ) ℂ) : Matrix ι ι ℂ :=
  ∑ a : κ,w a • O.submatrix (fun i => (i,a)) (fun i => (i,a))

theorem diagonal_readout_norm (w : κ → ℝ) (nonnegative : ∀ a,0 ≤ w a) (normalized : ∑ a,w a=1)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (hermitian : O.IsHermitian) : ‖diagonalReadout w O‖ ≤ ‖O‖ := by
  apply (norm_sum_le _ _).trans
  calc
    _ = ∑ a : κ,w a*‖O.submatrix (fun i => (i,a)) (fun i => (i,a))‖ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [norm_smul,Real.norm_of_nonneg (nonnegative a)]
    _ ≤ ∑ a : κ,w a*‖O‖ := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (principal_norm (fun i : ι => (i,a)) (fun _ _ h => congrArg Prod.fst h) O hermitian) (nonnegative a)
    _ = _ := by rw [← Finset.sum_mul,normalized,one_mul]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem diagonal_readout_hermitian (w : κ → ℝ) (O : Matrix (ι × κ) (ι × κ) ℂ)
    (hermitian : O.IsHermitian) : (diagonalReadout w O).IsHermitian := by
  unfold diagonalReadout
  change (∑ a,w a • O.submatrix (fun i => (i,a)) (fun i => (i,a)))ᴴ=_
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact ((hermitian.submatrix (fun i : ι => (i,a))).smul (k := w a) (by rfl)).eq

omit [DecidableEq ι] in
theorem diagonal_readout_energy (w : κ → ℝ) (O : Matrix (ι × κ) (ι × κ) ℂ) (rho : Matrix ι ι ℂ) :
    energy O (Matrix.kronecker rho (Matrix.diagonal (fun a => (w a : ℂ))))=energy (diagonalReadout w O) rho := by
  unfold energy
  congr 1
  simp only [diagonalReadout,Matrix.sum_mul,Matrix.trace_sum,Matrix.smul_mul,Matrix.trace_smul]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type,Matrix.diagonal_apply,Matrix.submatrix_apply]
  simp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
