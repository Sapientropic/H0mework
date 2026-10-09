import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceClosure
import Mathlib.LinearAlgebra.CrossProduct

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap ContinuousGradient ContinuousSeed
open TrueTubeWholeActual TrueFlowDifferential Matrix
open scoped Matrix
noncomputable section

def seedNormalQ : Fin 3 → ℚ :=
  ![Geometry.Source.basis 1 0 * Geometry.Source.basis 2 1 -
      Geometry.Source.basis 2 0 * Geometry.Source.basis 1 1,
    Geometry.Source.basis 2 0 * Geometry.Source.basis 0 1 -
      Geometry.Source.basis 0 0 * Geometry.Source.basis 2 1,
    Geometry.Source.basis 0 0 * Geometry.Source.basis 1 1 -
      Geometry.Source.basis 1 0 * Geometry.Source.basis 0 1]

def seedNormal : Point := fun i => (seedNormalQ i : ℝ)

def transverseLower : ℚ := ∑ i : Fin 3,
  min (seedNormalQ i * ((TrueTubeSource.recordedField 0).gradient i).1)
      (seedNormalQ i * ((TrueTubeSource.recordedField 0).gradient i).2)

theorem transverse_lower_positive : 0 < transverseLower := by decide +kernel

theorem original_gradient_transverse (x : Point) (inside : InRectangle (TrueTubeSource.box 0) x) :
    0 < seedNormal ⬝ᵥ sourceGradient x := by
  have bound : (transverseLower : ℝ) ≤ seedNormal ⬝ᵥ sourceGradient x := by
    simp only [transverseLower, Rat.cast_sum, Rat.cast_min, Rat.cast_mul, dotProduct]
    apply Finset.sum_le_sum
    intro i _
    have bounds := (TrueTubeMatrix.all_first_fields 0 x inside).1 i
    by_cases sign : (0 : ℝ) ≤ (seedNormalQ i : ℝ)
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left bounds.1 sign)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left bounds.2 (le_of_lt (lt_of_not_ge sign)))
  exact lt_of_lt_of_le (Rat.cast_pos.mpr transverse_lower_positive) bound

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
