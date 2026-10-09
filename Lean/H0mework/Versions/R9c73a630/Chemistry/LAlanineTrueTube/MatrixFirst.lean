import H0mework.Versions.AB.Chemistry.LAlanineTrueTube.SourceData
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.MatrixFirst

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeMatrix

open SourceGaussianModel SourceSignedEvaluator SourceRectangle IntervalParameterMap

theorem first_box_reused : TrueTubeSource.box 0 = WholeCellSource.box 0 := by
  funext axis
  fin_cases axis <;> rfl

theorem first_field_reused : TrueTubeSource.recordedField 0 = WholeCellReplay.recordedField 0 := by
  rfl

theorem actual_initial_field (x : Point) (inside : InRectangle (TrueTubeSource.box 0) x) :
    FieldHolds (TrueTubeSource.recordedField 0) x := by
  rw [first_field_reused]
  exact WholeCellMatrix.first_actual_field x (first_box_reused ▸ inside)

end LAlanine40K2025.BasinRefinement.TrueTubeMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
