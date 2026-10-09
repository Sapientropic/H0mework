import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.PairSum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Primitive

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceGaussianModel SourceFiniteData GlobalSource
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceSignedEvaluator SourceExponential
open scoped BigOperators
noncomputable section

def primitiveBoysInterval (s t : Term) (a : Fin 13) : Pair :=
  ∑ j ∈ Finset.range (attractionOrder s t + 1),
    mul (attractionCoefficientQ s t (Nuclear.nuclearPositionQ a) j,
      attractionCoefficientQ s t (Nuclear.nuclearPositionQ a) j)
      (sourceBoysInterval j s t a)

def primitivePrefactorInterval (s t : Term) : Pair :=
  let c : ℚ := s.weight * t.weight * (2 / pairExponent s t)
  mul (c,c) (mul (piLower,piUpper) (negativeExp (pairPenalty s t) 8))

def primitiveAttractionInterval (s t : Term) (a : Fin 13) : Pair :=
  mul (primitivePrefactorInterval s t) (primitiveBoysInterval s t a)

private theorem source_pair_penalty_nonnegative (i j : Basis)
    (s : Term) (hs : s ∈ sourceTerms i)
    (t : Term) (ht : t ∈ sourceTerms j) :
    0 ≤ pairPenalty s t := by
  unfold pairPenalty
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (source_exponents_positive i s hs).le
        (source_exponents_positive j t ht).le
    · exact (add_pos (source_exponents_positive i s hs)
        (source_exponents_positive j t ht)).le
  · exact sq_nonneg _

private theorem penalty_exp_valid (p : ℚ) (hp : 0 ≤ p) :
    ExpReductionValid p 8 := by
  intro _ h112
  change |(-p) / 2^8| ≤ (1/2 : ℚ)
  rw [abs_div, abs_neg, abs_of_nonneg hp]
  norm_num at *
  linarith

theorem primitive_boys_interval_contains (i j : Basis)
    (s : Term) (hs : s ∈ sourceTerms i)
    (t : Term) (ht : t ∈ sourceTerms j) (a : Fin 13) :
    Holds (primitiveBoysInterval s t a)
      (∑ m ∈ Finset.range (attractionOrder s t + 1),
        (attractionCoefficientQ s t (Nuclear.nuclearPositionQ a) m : ℝ) *
          boys m (boysArgument s t (Nuclear.nuclearPositionQ a))) := by
  unfold primitiveBoysInterval
  apply finset_sum_holds
  intro m hm
  apply mul_holds
  · exact ⟨le_rfl,le_rfl⟩
  · exact source_boys_interval_contains i j s hs t ht a m

theorem primitive_prefactor_interval_contains (i j : Basis)
    (s : Term) (hs : s ∈ sourceTerms i)
    (t : Term) (ht : t ∈ sourceTerms j) :
    Holds (primitivePrefactorInterval s t)
      ((s.weight : ℝ) * t.weight *
        (2*Real.pi/(pairExponent s t : ℝ)) *
          Real.exp (-(pairPenalty s t : ℝ))) := by
  have positive := add_pos (source_exponents_positive i s hs)
    (source_exponents_positive j t ht)
  have gammaNe : (pairExponent s t : ℝ) ≠ 0 := by
    exact_mod_cast (show pairExponent s t ≠ 0 from (by simpa only [pairExponent] using positive.ne'))
  have expBound := negative_exp_contains (pairPenalty s t) 8
    (penalty_exp_valid _ (source_pair_penalty_nonnegative i j s hs t ht))
  have piBound : Holds (piLower,piUpper) Real.pi := pi_bounds
  let c : ℚ := s.weight * t.weight * (2 / pairExponent s t)
  have bounds := mul_holds (c,c) (mul (piLower,piUpper)
      (negativeExp (pairPenalty s t) 8)) (c:ℝ)
      (Real.pi * Real.exp (-(pairPenalty s t:ℝ)))
      ⟨le_rfl,le_rfl⟩
      (mul_holds _ _ _ _ piBound expBound)
  have shape : (c:ℝ) * (Real.pi * Real.exp (-(pairPenalty s t:ℝ))) =
      (s.weight:ℝ)*t.weight *
        (2*Real.pi/(pairExponent s t:ℝ)) *
          Real.exp (-(pairPenalty s t:ℝ)) := by
    dsimp [c]
    push_cast
    field_simp [gammaNe]
  simpa only [primitivePrefactorInterval, ← shape] using bounds

theorem primitive_attraction_interval_contains (i j : Basis)
    (s : Term) (hs : s ∈ sourceTerms i)
    (t : Term) (ht : t ∈ sourceTerms j) (a : Fin 13) :
    Holds (primitiveAttractionInterval s t a)
      (primitiveAttraction s t (Nuclear.nuclearPositionQ a)) := by
  have pref := primitive_prefactor_interval_contains i j s hs t ht
  have body := primitive_boys_interval_contains i j s hs t ht a
  simpa only [primitiveAttractionInterval,primitiveAttraction] using
    mul_holds (primitivePrefactorInterval s t) (primitiveBoysInterval s t a)
      _ _ pref body

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
