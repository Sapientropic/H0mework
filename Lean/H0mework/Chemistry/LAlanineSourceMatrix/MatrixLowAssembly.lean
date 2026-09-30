import H0mework.Chemistry.LAlanineSourceMatrix.Assembly
import H0mework.Chemistry.LAlanineContinuousMatrix.FieldAssembly

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLowMatrixField

open SourceFields SourceRectangle SourceGaussianModel SourceSignedEvaluator SourceFiniteData ContinuousGradient

def firstLow (axis : Fin 3) : LowJet := ⟨axis.val + 1, by omega⟩
def secondLow (axis direction : Fin 3) : LowJet :=
  ⟨(SourceMatrixField.secondIndex axis direction).val, by fin_cases axis <;> fin_cases direction <;> decide⟩

theorem zero_index : multiindex (fullJet 0) = zeroJet := SourceMatrixField.zero_index
theorem first_index (axis : Fin 3) : multiindex (fullJet (firstLow axis)) = raise zeroJet axis :=
  SourceMatrixField.first_index axis
theorem second_index (axis direction : Fin 3) :
    multiindex (fullJet (secondLow axis direction)) = raise (raise zeroJet axis) direction :=
  SourceMatrixField.second_index axis direction

def gradient (b : LowJet → LowJet → Pair) (axis : Fin 3) : Pair :=
  add (b (firstLow axis) 0) (b 0 (firstLow axis))
def hessian (b : LowJet → LowJet → Pair) (axis direction : Fin 3) : Pair :=
  add (add (b (secondLow axis direction) 0) (b (firstLow axis) (firstLow direction)))
    (add (b (firstLow direction) (firstLow axis)) (b 0 (secondLow axis direction)))
def laplacian (b : LowJet → LowJet → Pair) : Pair :=
  add (add (hessian b 0 0) (hessian b 1 1)) (hessian b 2 2)

noncomputable section

def BilinearBounds (f : Field) (b : LowJet → LowJet → Pair) : Prop :=
  ∀ j k x, InRectangle (actualBox f) x →
    Holds (b j k) (bilinear sourceTerms densityMatrix (multiindex (fullJet j)) (multiindex (fullJet k)) x)

theorem gradient_contains (f : Field) (b : LowJet → LowJet → Pair) (valid : BilinearBounds f b)
    (x : Point) (inside : InRectangle (actualBox f) x) (axis : Fin 3) :
    Holds (gradient b axis) (sourceGradient x axis) := by
  have ha := valid (firstLow axis) 0 x inside
  have hb := valid 0 (firstLow axis) x inside
  simpa only [gradient, first_index, zero_index, sourceGradient, firstBilinear] using
    add_holds _ _ _ _ ha hb

theorem hessian_contains (f : Field) (b : LowJet → LowJet → Pair) (valid : BilinearBounds f b)
    (x : Point) (inside : InRectangle (actualBox f) x) (axis direction : Fin 3) :
    Holds (hessian b axis direction) (sourceHessian x axis direction) := by
  have ha := valid (secondLow axis direction) 0 x inside
  have hb := valid (firstLow axis) (firstLow direction) x inside
  have hc := valid (firstLow direction) (firstLow axis) x inside
  have hd := valid 0 (secondLow axis direction) x inside
  simpa only [hessian, first_index, second_index, zero_index,
    sourceHessian, firstBilinear] using
    add_holds _ _ _ _ (add_holds _ _ _ _ ha hb) (add_holds _ _ _ _ hc hd)

theorem laplacian_contains (f : Field) (b : LowJet → LowJet → Pair) (valid : BilinearBounds f b)
    (x : Point) (inside : InRectangle (actualBox f) x) :
    Holds (laplacian b) (SourceGaussianModel.laplacian sourceTerms densityMatrix x) := by
  have h := add_holds _ _ _ _ (add_holds _ _ _ _
    (hessian_contains f b valid x inside 0 0) (hessian_contains f b valid x inside 1 1))
    (hessian_contains f b valid x inside 2 2)
  simp only [SourceSignedField.sourceHessian_diagonal] at h
  change Holds _ (∑ axis : Fin 3, secondBilinear sourceTerms densityMatrix zeroJet zeroJet axis x)
  simpa only [laplacian, Fin.sum_univ_three, add_assoc] using h

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceLowMatrixField
