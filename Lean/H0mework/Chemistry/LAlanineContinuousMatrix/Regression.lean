import H0mework.Chemistry.LAlanineContinuousMatrix.SourceField

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedMatrix

open SourceRectangle SourceSignedEvaluator ContinuousGradient SourceGaussianModel SourceFiniteData

theorem actual_positive_consumer :
    ∃ x, InRectangle (actualBox 0) x ∧ (75 / 1000 : ℝ) < sourceGradient x 2 :=
  ⟨sourceWitness, sourceWitness_in_rectangle,
    (actual_gradient_directions sourceWitness sourceWitness_in_rectangle).2.2⟩

theorem zeroed_response_rejected :
    ¬ (∀ x, InRectangle (actualBox 0) x → sourceGradient x = 0) := by
  intro erased
  exact actual_no_critical_point sourceWitness sourceWitness_in_rectangle
    (erased sourceWitness sourceWitness_in_rectangle)

theorem harmonic_replacement_rejected :
    ¬ (0 ≤ laplacian sourceTerms densityMatrix sourceWitness) := by
  have actual := actual_negative_laplacian sourceWitness sourceWitness_in_rectangle
  intro wrong
  linarith

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedMatrix
