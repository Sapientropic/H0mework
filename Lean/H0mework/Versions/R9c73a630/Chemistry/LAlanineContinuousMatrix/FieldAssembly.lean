import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.SourceIncidence
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSignedEvaluator.Field
import H0mework.Versions.AB.Chemistry.LAlanineParametric.IntervalStage

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceMatrixField

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData ContinuousGradient
open IntervalParameterMap

def firstIndex (axis : Fin 3) : SourceRectangle.Jet := ⟨axis.val + 1, by omega⟩
def secondIndex (axis direction : Fin 3) : SourceRectangle.Jet :=
  ![![4, 5, 6], ![5, 7, 8], ![6, 8, 9]] axis direction

theorem zero_index : multiindex 0 = zeroJet := by funext axis; fin_cases axis <;> rfl
theorem first_index (axis : Fin 3) : multiindex (firstIndex axis) = raise zeroJet axis := by
  funext direction
  fin_cases axis <;> fin_cases direction <;> rfl
theorem second_index (axis direction : Fin 3) :
    multiindex (secondIndex axis direction) = raise (raise zeroJet axis) direction := by
  funext component
  fin_cases axis <;> fin_cases direction <;> fin_cases component <;> rfl

def gradient (b : SourceRectangle.Jet → SourceRectangle.Jet → Pair) (axis : Fin 3) : Pair :=
  add (b (firstIndex axis) 0) (b 0 (firstIndex axis))
def hessian (b : SourceRectangle.Jet → SourceRectangle.Jet → Pair) (axis direction : Fin 3) : Pair :=
  add (add (b (secondIndex axis direction) 0) (b (firstIndex axis) (firstIndex direction)))
    (add (b (firstIndex direction) (firstIndex axis)) (b 0 (secondIndex axis direction)))
def laplacian (b : SourceRectangle.Jet → SourceRectangle.Jet → Pair) : Pair :=
  add (add (hessian b 0 0) (hessian b 1 1)) (hessian b 2 2)
def field (b : SourceRectangle.Jet → SourceRectangle.Jet → Pair) : FieldBox :=
  ⟨gradient b, hessian b⟩

noncomputable section

def BilinearBounds (box : Rectangle) (b : SourceRectangle.Jet → SourceRectangle.Jet → Pair) : Prop :=
  ∀ left right x, InRectangle box x →
    Holds (b left right) (bilinear sourceTerms densityMatrix (multiindex left) (multiindex right) x)

theorem gradient_contains (box : Rectangle) (b : SourceRectangle.Jet → SourceRectangle.Jet → Pair)
    (valid : BilinearBounds box b) (x : Point) (inside : InRectangle box x) (axis : Fin 3) :
    Holds (gradient b axis) (sourceGradient x axis) := by
  have ha := valid (firstIndex axis) 0 x inside
  have hb := valid 0 (firstIndex axis) x inside
  simpa only [gradient, first_index, zero_index, sourceGradient, firstBilinear] using
    add_holds _ _ _ _ ha hb

theorem hessian_contains (box : Rectangle) (b : SourceRectangle.Jet → SourceRectangle.Jet → Pair)
    (valid : BilinearBounds box b) (x : Point) (inside : InRectangle box x) (axis direction : Fin 3) :
    Holds (hessian b axis direction) (sourceHessian x axis direction) := by
  have ha := valid (secondIndex axis direction) 0 x inside
  have hb := valid (firstIndex axis) (firstIndex direction) x inside
  have hc := valid (firstIndex direction) (firstIndex axis) x inside
  have hd := valid 0 (secondIndex axis direction) x inside
  simpa only [hessian, first_index, second_index, zero_index, sourceHessian, firstBilinear] using
    add_holds _ _ _ _ (add_holds _ _ _ _ ha hb) (add_holds _ _ _ _ hc hd)

theorem laplacian_contains (box : Rectangle) (b : SourceRectangle.Jet → SourceRectangle.Jet → Pair)
    (valid : BilinearBounds box b) (x : Point) (inside : InRectangle box x) :
    Holds (laplacian b) (SourceGaussianModel.laplacian sourceTerms densityMatrix x) := by
  have h := add_holds _ _ _ _ (add_holds _ _ _ _
    (hessian_contains box b valid x inside 0 0) (hessian_contains box b valid x inside 1 1))
    (hessian_contains box b valid x inside 2 2)
  simp only [SourceSignedField.sourceHessian_diagonal] at h
  change Holds _ (∑ axis : Fin 3, secondBilinear sourceTerms densityMatrix zeroJet zeroJet axis x)
  simpa only [laplacian, Fin.sum_univ_three, add_assoc] using h

theorem field_contains (box : Rectangle) (b : SourceRectangle.Jet → SourceRectangle.Jet → Pair)
    (valid : BilinearBounds box b) (x : Point) (inside : InRectangle box x) :
    FieldHolds (field b) x :=
  ⟨fun axis => gradient_contains box b valid x inside axis,
    fun axis direction => hessian_contains box b valid x inside axis direction⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceMatrixField
