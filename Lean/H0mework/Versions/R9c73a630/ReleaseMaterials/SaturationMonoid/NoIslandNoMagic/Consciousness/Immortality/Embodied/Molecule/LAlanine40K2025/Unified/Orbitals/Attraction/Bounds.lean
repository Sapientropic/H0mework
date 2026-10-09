import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Boys
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Sqrt

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceSignedEvaluator SourceExponential
open scoped BigOperators
noncomputable section

def boysPrefixQ (n K : ℕ) (T : ℚ) : ℚ :=
  ∑ k ∈ Finset.range K,
    (2*T)^k / ∏ j ∈ Finset.range (k+1), (2*n+2*j+1 : ℚ)

def boysCoefficientQ (n K : ℕ) (T : ℚ) : ℚ :=
  (2*T)^K / ∏ j ∈ Finset.range K, (2*n+2*j+1 : ℚ)

def boysRemainderQ (n K : ℕ) (T : ℚ) : ℚ :=
  boysCoefficientQ n K T / (2*(n+K)+1 : ℚ)

def halfCoefficientQ (n : ℕ) (T : ℚ) : ℚ :=
  (∏ j ∈ Finset.range n, (2*j+1 : ℚ)) / (2^(n+1)*T^n)

def tailCoefficientQ (n : ℕ) (T : ℚ) : ℚ :=
  (n.factorial : ℚ) / (2*T^(n+1)) *
    ∑ k ∈ Finset.range (n+1), T^k/(k.factorial : ℚ)

private theorem denominator_positive (n K : ℕ) :
    0 < ∏ j ∈ Finset.range K, (2*n+2*j+1 : ℚ) := by
  apply Finset.prod_pos
  intro j _
  positivity

theorem boys_prefix_nonnegative (n K : ℕ) (T : ℚ) (hT : 0 ≤ T) :
    0 ≤ boysPrefixQ n K T := by
  unfold boysPrefixQ
  apply Finset.sum_nonneg
  intro k _
  exact div_nonneg (pow_nonneg (by positivity) _) (denominator_positive n (k+1)).le

theorem boys_coefficient_nonnegative (n K : ℕ) (T : ℚ) (hT : 0 ≤ T) :
    0 ≤ boysCoefficientQ n K T := by
  unfold boysCoefficientQ
  exact div_nonneg (pow_nonneg (by positivity) _) (denominator_positive n K).le

theorem boys_remainder_nonnegative (n K : ℕ) (T : ℚ) (hT : 0 ≤ T) :
    0 ≤ boysRemainderQ n K T := by
  unfold boysRemainderQ
  exact div_nonneg (boys_coefficient_nonnegative n K T hT) (by positivity)

theorem half_coefficient_nonnegative (n : ℕ) (T : ℚ) (hT : 0 < T) :
    0 ≤ halfCoefficientQ n T := by
  unfold halfCoefficientQ
  positivity

theorem tail_coefficient_nonnegative (n : ℕ) (T : ℚ) (hT : 0 < T) :
    0 ≤ tailCoefficientQ n T := by
  unfold tailCoefficientQ
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro k _
    positivity

theorem boys_prefix_cast (n K : ℕ) (T : ℚ) :
    (boysPrefixQ n K T : ℝ) =
      ∑ k ∈ Finset.range K, (2*(T:ℝ))^k /
        ∏ j ∈ Finset.range (k+1), (2*n+2*j+1 : ℝ) := by
  simp only [boysPrefixQ, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_prod]
  congr 1
  funext k
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  ring

theorem boys_coefficient_cast (n K : ℕ) (T : ℚ) :
    (boysCoefficientQ n K T : ℝ) =
      (2*(T:ℝ))^K / ∏ j ∈ Finset.range K, (2*n+2*j+1 : ℝ) := by
  simp only [boysCoefficientQ, Rat.cast_div, Rat.cast_pow,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
