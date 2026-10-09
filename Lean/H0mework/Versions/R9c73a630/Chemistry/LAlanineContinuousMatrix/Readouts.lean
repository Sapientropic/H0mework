import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.Data
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.FieldAssembly

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedMatrix

open SourceRectangle SourceSignedEvaluator SourceMatrixField

noncomputable section

def sourceGradientBox : Fin 3 → Pair := gradient calculatedBilinear
def sourceHessianBox : Fin 3 → Fin 3 → Pair := hessian calculatedBilinear
def sourceLaplacianBox : Pair := laplacian calculatedBilinear

theorem gradient_eq_source_report (axis : Fin 3) :
    sourceGradientBox axis = reportedDensity 0 (firstIndex axis) := by
  fin_cases axis <;> decide +kernel

theorem hessian_eq_source_report (axis direction : Fin 3) :
    sourceHessianBox axis direction = reportedDensity 0 (secondIndex axis direction) := by
  fin_cases axis <;> fin_cases direction <;> decide +kernel

theorem first_gradient_strictly_positive :
    (47 / 10000 : ℚ) < (sourceGradientBox 0).1 := by decide +kernel

theorem second_gradient_strictly_negative :
    (sourceGradientBox 1).2 < (-56 / 1000 : ℚ) := by decide +kernel

theorem third_gradient_strictly_positive :
    (75 / 1000 : ℚ) < (sourceGradientBox 2).1 := by decide +kernel

theorem source_laplacian_strictly_negative :
    (sourceLaplacianBox).2 < (-16 / 100 : ℚ) := by decide +kernel

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedMatrix
