import H0mework.Chemistry.LAlanineTrueTubeWhole.MatrixAllFields
import H0mework.Chemistry.LAlanineSignedEvaluator.Field

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitative

open SourceGaussianModel SourceFiniteData SourceSignedEvaluator ContinuousGradient
open TrueTubeSource TrueTubeWholeSource
noncomputable section

/-- The three diagonal reports of each original certified Hessian, with no new field evaluation. -/
def callTracePair (c : Call) : Pair :=
  add (add ((recordedCallField c).hessian 0 0) ((recordedCallField c).hessian 1 1))
    ((recordedCallField c).hessian 2 2)

theorem all_call_trace_bounds : ∀ c : Call,
    (-(3 / 4) : ℚ) < (callTracePair c).1 ∧ (callTracePair c).2 < -(1 / 4) := by
  decide +kernel

theorem actual_call_laplacian_contains (c : Call) (x : Point)
    (inside : InRectangle (callBox c) x) :
    Holds (callTracePair c) (laplacian sourceTerms densityMatrix x) := by
  have fields := (TrueTubeWholeMatrix.all_actual_call_fields c x inside).2
  have bound := add_holds _ _ _ _
    (add_holds _ _ _ _ (fields 0 0) (fields 1 1)) (fields 2 2)
  change Holds _ (∑ axis : Fin 3, secondBilinear sourceTerms densityMatrix zeroJet zeroJet axis x)
  simpa only [callTracePair, SourceSignedField.sourceHessian_diagonal,
    Fin.sum_univ_three, add_assoc] using bound

theorem actual_call_laplacian_bounds (c : Call) (x : Point)
    (inside : InRectangle (callBox c) x) :
    (-(3 / 4) : ℝ) < laplacian sourceTerms densityMatrix x ∧
      laplacian sourceTerms densityMatrix x < -(1 / 4) := by
  have bound := actual_call_laplacian_contains c x inside
  have lower : (-(3 / 4) : ℝ) < ((callTracePair c).1 : ℝ) := by
    simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr (all_call_trace_bounds c).1
  have upper : ((callTracePair c).2 : ℝ) < -(1 / 4 : ℝ) := by
    simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr (all_call_trace_bounds c).2
  exact ⟨lower.trans_le bound.1, bound.2.trans_lt upper⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitative
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
