import H0mework.Chemistry.LAlanineSourceMatrix.MatrixComplete
import H0mework.Chemistry.LAlanineContinuousSource.RK4ReplayData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix

open SourceRectangle SourceSignedEvaluator SourceLowMatrixField
noncomputable section

def sourceGradientBox : Fin 3 → Pair := gradient calculatedBilinear
def sourceHessianBox : Fin 3 → Fin 3 → Pair := hessian calculatedBilinear
def sourceLaplacianBox : Pair := laplacian calculatedBilinear

theorem gradient_eq_source_report (axis : Fin 3) :
    sourceGradientBox axis = reportedDensity 1 (SourceMatrixField.firstIndex axis) := by
  fin_cases axis <;> decide +kernel

theorem hessian_eq_source_report (axis direction : Fin 3) :
    sourceHessianBox axis direction = reportedDensity 1 (SourceMatrixField.secondIndex axis direction) := by
  fin_cases axis <;> fin_cases direction <;> decide +kernel

theorem rectangle_ordered : ∀ axis : Fin 3, (actualBox 1 axis).1 ≤ (actualBox 1 axis).2 := by decide +kernel
theorem source_gradient_positive : 0 < (sourceGradientBox 2).1 := by decide +kernel
theorem source_laplacian_negative : sourceLaplacianBox.2 < 0 := by decide +kernel
theorem wrong_field_readout_rejected : sourceGradientBox 0 ≠ reportedDensity 0 1 := by decide +kernel

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix
