import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.DiagonalProjection

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def diagonalOrdinary (x : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  diagonalLoaded x-(sineHat : ℂ)^2 • Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) numericEnvironmentRead

private theorem restrict_expression {ι κ : Type*} (H D L R : Matrix ι ι ℂ)
    (s l r : ℂ) (f : κ → ι) :
    (H-s • D+l • L+r • R).submatrix f f=
      H.submatrix f f-s • D.submatrix f f+l • L.submatrix f f+r • R.submatrix f f := rfl

theorem original_rational_diagonal_block (a : Fin 97) :
    rationalCore.submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc)=diagonalOrdinary (Donor.calculatedEnergy a.castSucc) := by
  rw [rationalCore,restrict_expression,diagonal_left_block a,diagonal_right_block a,
    smul_zero,smul_zero,add_zero,add_zero,numeric_diagonal_load,diagonal_environment]
  rfl

theorem diagonal_affine (x y : ℝ) : diagonalOrdinary x-diagonalOrdinary y=
    (2*(x-y)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext ⟨c,e⟩ ⟨d,f⟩
  fin_cases c <;> fin_cases e <;> fin_cases d <;> fin_cases f <;>
    simp [diagonalOrdinary,diagonalLoaded,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
      diagonalHpc,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Complex.real_smul]
  all_goals ring

theorem diagonal_monotone (x y : ℝ) (ordered : x ≤ y) : diagonalOrdinary x ≤ diagonalOrdinary y := by
  apply sub_nonneg.mp
  rw [diagonal_affine]
  exact smul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ordered)) zero_le_one

theorem original_diagonal_envelope (a : Fin 97) :
    rationalCore.submatrix (diagonalPCE 0) (diagonalPCE 0) ≤ rationalCore.submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc) ∧
    rationalCore.submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc) ≤ rationalCore.submatrix (diagonalPCE 96) (diagonalPCE 96) := by
  have low := original_rational_diagonal_block (0 : Fin 97)
  have high := original_rational_diagonal_block (96 : Fin 97)
  change rationalCore.submatrix (diagonalPCE 0) (diagonalPCE 0)=diagonalOrdinary (Donor.calculatedEnergy 0) at low
  change rationalCore.submatrix (diagonalPCE 96) (diagonalPCE 96)=diagonalOrdinary (Donor.calculatedEnergy 96) at high
  rw [low,high,original_rational_diagonal_block a]
  have upper : a.castSucc ≤ (96 : Basis) := by
    change a.val ≤ 96
    have bound := a.isLt
    omega
  exact ⟨diagonal_monotone _ _ (source_energy_increasing.monotone (Fin.zero_le _)),
    diagonal_monotone _ _ (source_energy_increasing.monotone upper)⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
