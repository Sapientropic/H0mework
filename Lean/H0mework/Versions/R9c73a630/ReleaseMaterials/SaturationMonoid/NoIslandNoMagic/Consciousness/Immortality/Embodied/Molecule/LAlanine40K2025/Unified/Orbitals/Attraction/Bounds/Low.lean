import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceSignedEvaluator SourceExponential
noncomputable section

def boysLowInterval (n K : ℕ) (T : ℚ) : Pair :=
  let expPair := negativeExp T 7
  (expPair.1 * boysPrefixQ n K T,
    expPair.2 * boysPrefixQ n K T + boysRemainderQ n K T)

private theorem low_exp_valid (T : ℚ) (hT : 0 ≤ T) (h60 : T ≤ 60) :
    ExpReductionValid T 7 := by
  intro _ _
  change |(-T) / 2^7| ≤ (1/2 : ℚ)
  rw [abs_div, abs_neg, abs_of_nonneg hT]
  norm_num at *
  linarith

theorem boys_low_interval_contains (n K : ℕ) (T : ℚ)
    (hT : 0 ≤ T) (h60 : T ≤ 60) :
    Holds (boysLowInterval n K T) (boys n (T : ℝ)) := by
  have expBounds := negative_exp_contains T 7 (low_exp_valid T hT h60)
  have prefixNonnegQ := boys_prefix_nonnegative n K T hT
  have coeffNonnegQ := boys_coefficient_nonnegative n K T hT
  have prefixNonneg : (0 : ℝ) ≤ (boysPrefixQ n K T : ℝ) := by
    exact_mod_cast prefixNonnegQ
  have coeffNonneg : (0 : ℝ) ≤ (boysCoefficientQ n K T : ℝ) := by
    exact_mod_cast coeffNonnegQ
  have Tnonneg : (0 : ℝ) ≤ T := by exact_mod_cast hT
  have series : boys n (T:ℝ) =
      Real.exp (-(T:ℝ)) * (boysPrefixQ n K T : ℝ) +
        (boysCoefficientQ n K T : ℝ) * boys (n+K) (T:ℝ) := by
    rw [boys_series]
    rw [boys_prefix_cast, boys_coefficient_cast]
  have remainderNonneg : 0 ≤
      (boysCoefficientQ n K T : ℝ) * boys (n+K) (T:ℝ) :=
    mul_nonneg coeffNonneg (boys_nonneg _ _)
  have remainderBound :
      (boysCoefficientQ n K T : ℝ) * boys (n+K) (T:ℝ) ≤
        (boysRemainderQ n K T : ℝ) := by
    have bound := mul_le_mul_of_nonneg_left
      (boys_le (n+K) (T:ℝ) Tnonneg) coeffNonneg
    calc
      _ ≤ (boysCoefficientQ n K T : ℝ) *
          (1 / (2*(n+K)+1 : ℝ)) := by
            simpa only [Nat.cast_add] using bound
      _ = (boysRemainderQ n K T : ℝ) := by
        simp only [boysRemainderQ, Rat.cast_div]
        push_cast
        ring
  dsimp only [Holds, boysLowInterval]
  constructor
  · push_cast
    calc
      (negativeExp T 7).1 * (boysPrefixQ n K T : ℝ) ≤
          Real.exp (-(T:ℝ)) * (boysPrefixQ n K T : ℝ) :=
        mul_le_mul_of_nonneg_right expBounds.1 prefixNonneg
      _ ≤ boys n (T:ℝ) := by rw [series]; linarith
  · push_cast
    rw [series]
    have upper := mul_le_mul_of_nonneg_right expBounds.2 prefixNonneg
    linarith

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
