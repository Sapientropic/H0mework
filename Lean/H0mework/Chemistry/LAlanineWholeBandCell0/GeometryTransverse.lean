import H0mework.Chemistry.LAlanineBandSource.Data
import H0mework.Chemistry.LAlanineTrueFlowGeometry.SeedTransverse

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandTransverse

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap ContinuousGradient
open WholeBandSource TrueFlowGeometry Matrix
open scoped Matrix
noncomputable section

def normalLower (c : FullBandCall) : ℚ := ∑ i : Fin 3,
  min (seedNormalQ i * ((recordedCallField c).gradient i).1)
      (seedNormalQ i * ((recordedCallField c).gradient i).2)

theorem all_cell0_normal_lower : ∀ (d : Direction) (i : Step),
    1/20 < normalLower (callAt 0 d i .initial) ∧
    1/20 < normalLower (callAt 0 d i .tube) := by
  decide +kernel

theorem normal_dot_lower (c : FullBandCall) (x : Point)
    (actual : FieldHolds (recordedCallField c) x) :
    (normalLower c : ℝ) ≤ seedNormal ⬝ᵥ sourceGradient x := by
  simp only [normalLower, Rat.cast_sum, Rat.cast_min, Rat.cast_mul, dotProduct]
  apply Finset.sum_le_sum
  intro i _
  have bounds := actual.1 i
  by_cases sign : (0 : ℝ) ≤ (seedNormalQ i : ℝ)
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left bounds.1 sign)
  · exact (min_le_right _ _).trans
      (mul_le_mul_of_nonpos_left bounds.2 (le_of_lt (lt_of_not_ge sign)))

theorem actual_cell0_field_transverse (d : Direction) (i : Step) (role : CallRole) (x : Point)
    (actual : FieldHolds (recordedCallField (callAt 0 d i role)) x) :
    (1/20 : ℝ) < seedNormal ⬝ᵥ sourceGradient x := by
  have sourceQ : 1/20 < normalLower (callAt 0 d i role) := by
    cases role
    · exact (all_cell0_normal_lower d i).1
    · exact (all_cell0_normal_lower d i).2
  have source : (1/20 : ℝ) < (normalLower (callAt 0 d i role) : ℝ) := by
    have lifted : (((1/20 : ℚ) : ℝ)) < (normalLower (callAt 0 d i role) : ℝ) := Rat.cast_lt.mpr sourceQ
    norm_num at lifted ⊢
    exact lifted
  exact source.trans_le (normal_dot_lower _ x actual)

end
end LAlanine40K2025.BasinRefinement.WholeBandTransverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
