import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal.Algebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.StarBounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem middle_error (f g : Fin 3 → ℂ)
    (zero : ‖f 0-g 0‖ ≤ (1/10^24 : ℝ)) (one : ‖f 1-g 1‖ ≤ (1/10^30 : ℝ))
    (two : ‖f 2-g 2‖ ≤ (1/10^30 : ℝ)) : ‖middle f-middle g‖ ≤ (2/10^24 : ℝ) := by
  have diag : ‖(f 0-g 0)+(f 2-g 2)‖ ≤ (1/10^24+1/10^30 : ℝ) :=
    (norm_add_le _ _).trans (add_le_add zero two)
  have same : middle f-middle g=!![(f 0-g 0)+(f 2-g 2),f 1-g 1; f 1-g 1,(f 0-g 0)+(f 2-g 2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [middle]
    all_goals ring
  rw [same]
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by norm_num)
  norm_num [Fin.sum_univ_succ]
  have first := pow_le_pow_left₀ (norm_nonneg _) diag 2
  have second := pow_le_pow_left₀ (norm_nonneg _) one 2
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
