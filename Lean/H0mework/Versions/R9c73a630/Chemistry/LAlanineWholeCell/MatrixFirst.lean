import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.MatrixFieldReadout
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.SourceField

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellMatrix

open SourceGaussianModel SourceSignedEvaluator SourceFields SourceRectangle IntervalParameterMap

theorem first_actual_field (x : Point) (inside : InRectangle (WholeCellSource.box 0) x) :
    FieldHolds (WholeCellReplay.recordedField 0) x := by
  have original := SourceSignedMatrix.actual_first_field x (WholeCellSource.first_box_unchanged ▸ inside)
  constructor
  · intro axis
    change Holds (WholeCellSource.reportedDensity 0 (WholeCellReplay.gradientIndex axis)) _
    rw [WholeCellSource.first_density_unchanged]
    exact original.1 axis
  · intro axis direction
    change Holds (WholeCellSource.reportedDensity 0 (WholeCellReplay.hessianIndex axis direction)) _
    rw [WholeCellSource.first_density_unchanged]
    have same : fullJet (WholeCellReplay.hessianIndex axis direction) = SourceMatrixField.secondIndex axis direction := by
      fin_cases axis <;> fin_cases direction <;> rfl
    rw [same]
    exact original.2 axis direction

end LAlanine40K2025.BasinRefinement.WholeCellMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
