import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.MatrixSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem plus_matrix_error (a b : Basis) (M : Material a b) :
    ‖starAssembly (sourceDelta a b : ℂ) (fun k => Scalar.value (sourceCoefficient a b 1 k))-
      starAssembly (sourceDelta a b : ℂ) (fun k => Scalar.value (M.plus k))‖ ≤ (2/10^24 : ℝ) :=
  star_error _ (source_delta_norm a b) _ _
    ((scalar_error _ _ _ (M.plus_error 0)).trans (by norm_num [coefficientBudget]))
    ((scalar_error _ _ _ (M.plus_error 1)).trans (by norm_num [coefficientBudget]))
    ((scalar_error _ _ _ (M.plus_error 2)).trans (by norm_num [coefficientBudget,show (2 : Fin 3) ≠ 0 by decide]))

theorem minus_matrix_error (a b : Basis) (M : Material a b) :
    ‖starAssembly (sourceDelta a b : ℂ) (fun k => Scalar.value (sourceCoefficient a b 3 k))-
      starAssembly (sourceDelta a b : ℂ) (fun k => Scalar.value (M.minus k))‖ ≤ (2/10^24 : ℝ) :=
  star_error _ (source_delta_norm a b) _ _
    ((scalar_error _ _ _ (M.minus_error 0)).trans (by norm_num [coefficientBudget]))
    ((scalar_error _ _ _ (M.minus_error 1)).trans (by norm_num [coefficientBudget]))
    ((scalar_error _ _ _ (M.minus_error 2)).trans (by norm_num [coefficientBudget,show (2 : Fin 3) ≠ 0 by decide]))

theorem material_matrix_error (a b : Basis) (M : Material a b) :
    ‖sourceBlock a b-numericBlock a b M‖ ≤ (2/10^24 : ℝ) := by
  rw [sourceBlock,numericBlock,splice_sub]
  exact (splice_norm _ _ _ _).trans (max_le (plus_matrix_error a b M)
    (max_le ((scalar_error _ _ _ M.upper_error).trans (by norm_num))
      (max_le ((scalar_error _ _ _ M.lower_error).trans (by norm_num)) (minus_matrix_error a b M))))

theorem basis_difference_norm (A B : Matrix (Fin 8) (Fin 8) ℂ) :
    ‖(basis*A*inverse).submatrix flatten flatten-(basis*B*inverse).submatrix flatten flatten‖ ≤ ‖A-B‖ := by
  have same : (basis*A*inverse).submatrix flatten flatten-(basis*B*inverse).submatrix flatten flatten=
      (basis*A*inverse-basis*B*inverse).submatrix flatten flatten := rfl
  rw [same,← Matrix.sub_mul,← Matrix.mul_sub,Finite.reindex_norm]
  exact basis_action_norm _

theorem original_material_load_error (a b : Basis) (distinct : a ≠ b) (M : Material a b) :
    ‖Actions.loadPolynomial.submatrix (Scaled.Order.orbitPCE a b) (Scaled.Order.orbitPCE a b)-numericLoad a b M‖ ≤
      (2/10^24 : ℝ) := by
  rw [original_load_values a b distinct]
  unfold valueMatrix numericLoad
  rw [← source_block_original]
  exact (basis_difference_norm _ _).trans (material_matrix_error a b M)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
