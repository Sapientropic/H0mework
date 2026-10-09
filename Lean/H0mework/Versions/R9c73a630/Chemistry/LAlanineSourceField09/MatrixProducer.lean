import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceField09.MatrixComplete
import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.RK4ReplayData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices.F9

open SourceRectangle SourceSignedEvaluator SourceLowMatrixField SourceGaussianModel SourceFiniteData ContinuousGradient
open IntervalParameterMap
noncomputable section

def sourceGradientBox : Fin 3 → Pair := gradient calculatedBilinear
def sourceHessianBox : Fin 3 → Fin 3 → Pair := hessian calculatedBilinear
def sourceLaplacianBox : Pair := SourceLowMatrixField.laplacian calculatedBilinear

theorem gradient_eq_source_report (axis : Fin 3) :
    sourceGradientBox axis = reportedDensity fieldIndex (SourceMatrixField.firstIndex axis) := by
  fin_cases axis <;> decide +kernel

theorem hessian_eq_source_report (axis direction : Fin 3) :
    sourceHessianBox axis direction = reportedDensity fieldIndex (SourceMatrixField.secondIndex axis direction) := by
  fin_cases axis <;> fin_cases direction <;> decide +kernel

theorem actual_field (x : Point) (inside : InRectangle (actualBox fieldIndex) x) :
    FieldHolds (SourceRK4Replay.recordedField fieldIndex) x := by
  constructor
  · intro axis
    change Holds (reportedDensity fieldIndex (SourceMatrixField.firstIndex axis)) (sourceGradient x axis)
    rw [← gradient_eq_source_report]
    exact gradient_contains _ _ actual_bilinear_bounds x inside axis
  · intro axis direction
    change Holds (reportedDensity fieldIndex (SourceMatrixField.secondIndex axis direction)) (sourceHessian x axis direction)
    rw [← hessian_eq_source_report]
    exact hessian_contains _ _ actual_bilinear_bounds x inside axis direction

theorem actual_laplacian (x : Point) (inside : InRectangle (actualBox fieldIndex) x) :
    Holds sourceLaplacianBox (SourceGaussianModel.laplacian sourceTerms densityMatrix x) :=
  laplacian_contains _ _ actual_bilinear_bounds x inside

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices.F9
