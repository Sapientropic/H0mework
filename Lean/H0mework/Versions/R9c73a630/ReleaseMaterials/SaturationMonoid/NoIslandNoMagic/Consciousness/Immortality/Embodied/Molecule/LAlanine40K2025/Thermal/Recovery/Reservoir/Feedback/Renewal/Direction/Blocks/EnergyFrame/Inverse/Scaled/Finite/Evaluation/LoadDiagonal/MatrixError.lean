import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal.MatrixSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem material_middle_error (a : Basis) (M : Material a) :
    ‖middle (fun k => Scalar.value (LoadPrimitive.sourceCoefficient a a 3 k))-numericMiddle a M‖ ≤ (2/10^24 : ℝ) :=
  middle_error _ _
    ((LoadPrimitive.scalar_error _ _ _ M.centre_error).trans (by norm_num))
    ((LoadPrimitive.scalar_error _ _ _ M.beta_error).trans (by norm_num))
    ((LoadPrimitive.scalar_error _ _ _ M.gamma_error).trans (by norm_num))

theorem material_raw_error (a : Basis) (M : Material a) :
    ‖sourceRaw a-numericRaw a M‖ ≤ (2/10^24 : ℝ) := by
  rw [sourceRaw,numericRaw,raw_sub]
  exact (raw_norm _ _ _).trans (max_le
    ((LoadPrimitive.scalar_error _ _ _ M.lower_error).trans (by norm_num))
    (max_le (material_middle_error a M) ((LoadPrimitive.scalar_error _ _ _ M.upper_error).trans (by norm_num))))

theorem original_material_load_error (a : Basis) (M : Material a) :
    ‖Actions.loadPolynomial.submatrix (Scaled.Order.diagonalPCE a) (Scaled.Order.diagonalPCE a)-numericLoad a M‖ ≤
      (2/10^24 : ℝ) := by
  rw [original_load_values]
  unfold valueMatrix numericLoad
  rw [← source_raw_original]
  have same : (sourceRaw a).submatrix toNative.symm toNative.symm-(numericRaw a M).submatrix toNative.symm toNative.symm=
      (sourceRaw a-numericRaw a M).submatrix toNative.symm toNative.symm := rfl
  rw [same,Finite.reindex_norm]
  exact material_raw_error a M

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
