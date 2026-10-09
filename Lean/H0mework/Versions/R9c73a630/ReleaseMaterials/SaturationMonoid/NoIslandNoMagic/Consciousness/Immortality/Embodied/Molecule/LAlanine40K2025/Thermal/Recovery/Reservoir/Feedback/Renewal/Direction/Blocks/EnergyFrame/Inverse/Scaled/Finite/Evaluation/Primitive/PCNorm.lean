import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCAlgebra
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsMatrixFrobeniusOperatorBound

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem pc_projection_norm (a : Fin 4) : ‖pcProjection a‖ ≤ 1 := by
  apply ElectronicFrame.MatrixNorm.l2_norm_le_of_sq_sum_le _ (by norm_num)
  fin_cases a <;>
    norm_num [pcProjection,rationalMatrix,pcProjectionQ,pcWeight,pcVector,Fin.sum_univ_succ]

theorem pc_assembly_error (f g : Fin 4 → ℂ) (d : ℝ) (nonnegative : 0 ≤ d)
    (bounded : ∀ a, ‖f a-g a‖ ≤ d) : ‖pcAssembly f-pcAssembly g‖ ≤ 4*d := by
  rw [pcAssembly,pcAssembly,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : Fin 4, ‖f a • pcProjection a-g a • pcProjection a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin 4, d := by
      apply Finset.sum_le_sum
      intro a _
      rw [← sub_smul,norm_smul]
      exact (mul_le_mul (bounded a) (pc_projection_norm a) (norm_nonneg _) nonnegative).trans (by rw [mul_one])
    _ = _ := by norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
