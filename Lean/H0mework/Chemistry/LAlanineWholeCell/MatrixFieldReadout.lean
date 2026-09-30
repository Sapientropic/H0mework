import H0mework.Chemistry.LAlanineSourceMatrix.MatrixLowAssembly
import H0mework.Chemistry.LAlanineWholeCell.SourceData
import H0mework.Chemistry.LAlanineWholeCell.ReplayModel

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellMatrix

open SourceGaussianModel SourceSignedEvaluator SourceFiniteData SourceRectangle SourceFields
open ContinuousGradient SourceLowMatrixField IntervalParameterMap

noncomputable section

theorem gradient_index_eq (axis : Fin 3) : WholeCellReplay.gradientIndex axis = firstLow axis := rfl
theorem hessian_index_eq (axis direction : Fin 3) :
    WholeCellReplay.hessianIndex axis direction = secondLow axis direction := by
  fin_cases axis <;> fin_cases direction <;> rfl

def fieldFromBilinear (b : LowJet → LowJet → Pair) : FieldBox :=
  ⟨SourceLowMatrixField.gradient b, SourceLowMatrixField.hessian b⟩

theorem fieldFromBilinear_contains (b : LowJet → LowJet → Pair) (x : Point)
    (bounds : ∀ j k, Holds (b j k)
      (bilinear sourceTerms densityMatrix (multiindex (fullJet j)) (multiindex (fullJet k)) x)) :
    FieldHolds (fieldFromBilinear b) x := by
  constructor
  · intro axis
    have ha := bounds (firstLow axis) 0
    have hb := bounds 0 (firstLow axis)
    simpa only [fieldFromBilinear, SourceLowMatrixField.gradient, first_index, zero_index,
      sourceGradient, firstBilinear] using add_holds _ _ _ _ ha hb
  · intro axis direction
    have ha := bounds (secondLow axis direction) 0
    have hb := bounds (firstLow axis) (firstLow direction)
    have hc := bounds (firstLow direction) (firstLow axis)
    have hd := bounds 0 (secondLow axis direction)
    simpa only [fieldFromBilinear, SourceLowMatrixField.hessian, first_index, second_index, zero_index,
      sourceHessian, firstBilinear] using
      add_holds _ _ _ _ (add_holds _ _ _ _ ha hb) (add_holds _ _ _ _ hc hd)

theorem laplacianFromBilinear_contains (b : LowJet → LowJet → Pair) (x : Point)
    (bounds : ∀ j k, Holds (b j k)
      (bilinear sourceTerms densityMatrix (multiindex (fullJet j)) (multiindex (fullJet k)) x)) :
    Holds (SourceLowMatrixField.laplacian b) (SourceGaussianModel.laplacian sourceTerms densityMatrix x) := by
  have hessian := (fieldFromBilinear_contains b x bounds).2
  have sum := add_holds _ _ _ _ (add_holds _ _ _ _ (hessian 0 0) (hessian 1 1)) (hessian 2 2)
  simp only [SourceSignedField.sourceHessian_diagonal] at sum
  change Holds _ (∑ axis : Fin 3, secondBilinear sourceTerms densityMatrix zeroJet zeroJet axis x)
  simpa only [SourceLowMatrixField.laplacian, fieldFromBilinear, Fin.sum_univ_three, add_assoc] using sum

end
end LAlanine40K2025.BasinRefinement.WholeCellMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
