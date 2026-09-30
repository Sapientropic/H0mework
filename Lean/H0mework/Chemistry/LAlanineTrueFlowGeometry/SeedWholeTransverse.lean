import H0mework.Chemistry.LAlanineTrueFlowGeometry.SeedTransverse
import H0mework.Chemistry.LAlanineTrueTubeWhole.MatrixAllFields

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open SourceGaussianModel SourceSignedEvaluator ContinuousGradient Matrix TrueTubeSource
open scoped Matrix
noncomputable section

def callTransverseLower (c : Call) : ℚ := ∑ i : Fin 3,
  min (seedNormalQ i * ((TrueTubeWholeSource.recordedCallField c).gradient i).1)
      (seedNormalQ i * ((TrueTubeWholeSource.recordedCallField c).gradient i).2)

theorem all_calls_transverse : ∀ c : Call, 0 < callTransverseLower c := by decide +kernel

theorem actual_call_transverse (c : Call) (x : Point) (inside : InRectangle (callBox c) x) :
    0 < seedNormal ⬝ᵥ sourceGradient x := by
  have bound : (callTransverseLower c : ℝ) ≤ seedNormal ⬝ᵥ sourceGradient x := by
    simp only [callTransverseLower, Rat.cast_sum, Rat.cast_min, Rat.cast_mul, dotProduct]
    apply Finset.sum_le_sum
    intro i _
    have bounds := (TrueTubeWholeMatrix.all_actual_call_fields c x inside).1 i
    by_cases sign : (0 : ℝ) ≤ (seedNormalQ i : ℝ)
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left bounds.1 sign)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left bounds.2 (le_of_lt (lt_of_not_ge sign)))
  exact lt_of_lt_of_le (Rat.cast_pos.mpr (all_calls_transverse c)) bound

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
