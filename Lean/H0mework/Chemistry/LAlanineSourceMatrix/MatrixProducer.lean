import H0mework.Chemistry.LAlanineSourceMatrix.MatrixReadouts

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix

open SourceRectangle SourceSignedEvaluator SourceLowMatrixField SourceGaussianModel SourceFiniteData ContinuousGradient
open IntervalParameterMap
noncomputable section

theorem actual_field (x : Point) (inside : InRectangle (actualBox 1) x) :
    FieldHolds (SourceRK4Replay.recordedField 1) x := by
  constructor
  · intro axis
    change Holds (reportedDensity 1 (SourceMatrixField.firstIndex axis)) (sourceGradient x axis)
    rw [← gradient_eq_source_report]
    exact gradient_contains _ _ actual_bilinear_bounds x inside axis
  · intro axis direction
    change Holds (reportedDensity 1 (SourceMatrixField.secondIndex axis direction)) (sourceHessian x axis direction)
    rw [← hessian_eq_source_report]
    exact hessian_contains _ _ actual_bilinear_bounds x inside axis direction

theorem actual_laplacian (x : Point) (inside : InRectangle (actualBox 1) x) :
    Holds sourceLaplacianBox (SourceGaussianModel.laplacian sourceTerms densityMatrix x) :=
  laplacian_contains _ _ actual_bilinear_bounds x inside

def sourceWitness : Point := fun axis => ((actualBox 1 axis).1 : ℝ)
theorem sourceWitness_in_rectangle : InRectangle (actualBox 1) sourceWitness := by
  intro axis
  exact ⟨le_rfl, Rat.cast_le.mpr (rectangle_ordered axis)⟩

theorem actual_positive_direction (x : Point) (inside : InRectangle (actualBox 1) x) :
    0 < sourceGradient x 2 := by
  have positive : (0 : ℝ) < ((sourceGradientBox 2).1 : ℝ) := by exact_mod_cast source_gradient_positive
  exact positive.trans_le (gradient_contains _ _ actual_bilinear_bounds x inside 2).1

theorem actual_negative_laplacian (x : Point) (inside : InRectangle (actualBox 1) x) :
    SourceGaussianModel.laplacian sourceTerms densityMatrix x < 0 :=
  (actual_laplacian x inside).2.trans_lt (by exact_mod_cast source_laplacian_negative)

theorem zeroed_response_rejected : ¬ (∀ x, InRectangle (actualBox 1) x → sourceGradient x = 0) := by
  intro erased
  have positive := actual_positive_direction sourceWitness sourceWitness_in_rectangle
  rw [erased sourceWitness sourceWitness_in_rectangle, Pi.zero_apply] at positive
  exact lt_irrefl _ positive

def field1Closure : Prop :=
  SourceLowMatrixField.BilinearBounds 1 calculatedBilinear ∧
    (∀ x, InRectangle (actualBox 1) x → FieldHolds (SourceRK4Replay.recordedField 1) x) ∧
    (∀ x, InRectangle (actualBox 1) x → 0 < sourceGradient x 2) ∧
    (∀ x, InRectangle (actualBox 1) x → SourceGaussianModel.laplacian sourceTerms densityMatrix x < 0) ∧
    InRectangle (actualBox 1) sourceWitness

theorem sourceGeneratedActualField1 : field1Closure :=
  ⟨actual_bilinear_bounds, actual_field, actual_positive_direction, actual_negative_laplacian, sourceWitness_in_rectangle⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceField1Matrix
