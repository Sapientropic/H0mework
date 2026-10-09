import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.Low

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceSignedEvaluator SourceExponential
open scoped BigOperators
noncomputable section

theorem half_moment_coefficient (n : ℕ) (T : ℚ) (hT : 0 < T) :
    halfMoment n (T:ℝ) = (halfCoefficientQ n T : ℝ) *
      Real.sqrt (Real.pi / (T:ℝ)) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hTzero : (T:ℝ) ≠ 0 := hTr.ne'
  have hSzero : Real.sqrt (T:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hTr
  unfold halfMoment halfCoefficientQ
  rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ Real.pi)]
  push_cast
  field_simp [hTzero, hSzero]

theorem tail_coefficient_cast (n : ℕ) (T : ℚ) :
    (tailCoefficientQ n T : ℝ) =
      (n.factorial : ℝ) / (2*(T:ℝ)^(n+1)) *
        ∑ k ∈ Finset.range (n+1), (T:ℝ)^k/(k.factorial : ℝ) := by
  simp only [tailCoefficientQ, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_sum, Rat.cast_ofNat, Rat.cast_natCast]

def boysHighInterval (n : ℕ) (T : ℚ) : Pair :=
  let root := (certifiedSqrtProposal T).interval
  let expPair := negativeExp T 8
  (halfCoefficientQ n T * root.1 - expPair.2 * tailCoefficientQ n T,
    halfCoefficientQ n T * root.2)

private theorem high_exp_valid (T : ℚ) (hT : 0 < T) :
    ExpReductionValid T 8 := by
  intro _ h112
  change |(-T) / 2^8| ≤ (1/2 : ℚ)
  rw [abs_div, abs_neg, abs_of_pos hT]
  norm_num at *
  linarith

theorem boys_high_interval_contains (n : ℕ) (T : ℚ) (hT : 0 < T) :
    Holds (boysHighInterval n T) (boys n (T:ℝ)) := by
  have hTr : (0:ℝ) < T := by exact_mod_cast hT
  have root := certified_sqrt_contains T hT
  have expBounds := negative_exp_contains T 8 (high_exp_valid T hT)
  have coeffQ := half_coefficient_nonnegative n T hT
  have tailQ := tail_coefficient_nonnegative n T hT
  have coeffNonneg : (0:ℝ) ≤ halfCoefficientQ n T := by exact_mod_cast coeffQ
  have tailNonneg : (0:ℝ) ≤ tailCoefficientQ n T := by exact_mod_cast tailQ
  have halfLower : (halfCoefficientQ n T : ℝ) *
      ((certifiedSqrtProposal T).interval.1 : ℝ) ≤ halfMoment n (T:ℝ) := by
    rw [half_moment_coefficient n T hT]
    exact mul_le_mul_of_nonneg_left root.1 coeffNonneg
  have halfUpper : halfMoment n (T:ℝ) ≤ (halfCoefficientQ n T : ℝ) *
      ((certifiedSqrtProposal T).interval.2 : ℝ) := by
    rw [half_moment_coefficient n T hT]
    exact mul_le_mul_of_nonneg_left root.2 coeffNonneg
  have tailUpper : boysTail n (T:ℝ) ≤
      ((negativeExp T 8).2 : ℝ) * (tailCoefficientQ n T : ℝ) := by
    have bound : boysTail n (T:ℝ) ≤
        Real.exp (-(T:ℝ)) * (tailCoefficientQ n T : ℝ) := by
      calc
        _ ≤ Real.exp (-(T:ℝ)) * (n.factorial : ℝ) /
            (2*(T:ℝ)^(n+1)) *
              ∑ k ∈ Finset.range (n+1), (T:ℝ)^k/(k.factorial : ℝ) :=
          boysTail_le n (T:ℝ) hTr
        _ = Real.exp (-(T:ℝ)) * (tailCoefficientQ n T : ℝ) := by
          rw [tail_coefficient_cast]
          ring
    exact bound.trans (mul_le_mul_of_nonneg_right expBounds.2 tailNonneg)
  have tailLower : 0 ≤ boysTail n (T:ℝ) := boysTail_nonneg n (T:ℝ) hTr
  have asymptotic := boys_asymptotic n (T:ℝ) hTr
  dsimp only [Holds, boysHighInterval]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
