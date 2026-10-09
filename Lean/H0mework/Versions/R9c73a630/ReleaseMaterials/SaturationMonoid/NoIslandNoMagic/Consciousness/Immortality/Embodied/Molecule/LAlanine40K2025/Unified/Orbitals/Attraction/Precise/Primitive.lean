import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.Primitive

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceGaussianModel SourceFiniteData GlobalSource
open LAlanine40K2025.UnifiedOrbitals.Attraction
open SourceSignedEvaluator
open scoped BigOperators
noncomputable section

def primitiveBoysAt (s t : Term) (C : Fin 3 → ℚ) : Pair :=
  ∑ m ∈ Finset.range (attractionOrder s t + 1),
    mul (attractionCoefficientQ s t C m, attractionCoefficientQ s t C m)
      (boysRationalInterval m (boysArgument s t C))

def primitiveIntervalAt (s t : Term) (C : Fin 3 → ℚ) : Pair :=
  mul (primitivePrefactorInterval s t) (primitiveBoysAt s t C)

theorem argument_nonnegative (i j : Basis)
    (s : Term) (hs : s ∈ sourceTerms i)
    (t : Term) (ht : t ∈ sourceTerms j) (C : Fin 3 → ℚ) :
    0 ≤ boysArgument s t C := by
  unfold boysArgument
  apply mul_nonneg
  · exact (add_pos (source_exponents_positive i s hs)
      (source_exponents_positive j t ht)).le
  · apply Finset.sum_nonneg
    intro k _
    exact sq_nonneg _

theorem primitive_boys_at_contains (i j : Basis)
    (s : Term) (hs : s ∈ sourceTerms i)
    (t : Term) (ht : t ∈ sourceTerms j) (C : Fin 3 → ℚ) :
    Holds (primitiveBoysAt s t C)
      (∑ m ∈ Finset.range (attractionOrder s t + 1),
        (attractionCoefficientQ s t C m : ℝ) *
          boys m (boysArgument s t C)) := by
  unfold primitiveBoysAt
  apply finset_sum_holds
  intro m _
  apply mul_holds
  · exact ⟨le_rfl,le_rfl⟩
  · exact boys_rational_interval_contains m _
      (argument_nonnegative i j s hs t ht C)

theorem primitive_interval_at_contains (i j : Basis)
    (s : Term) (hs : s ∈ sourceTerms i)
    (t : Term) (ht : t ∈ sourceTerms j) (C : Fin 3 → ℚ) :
    Holds (primitiveIntervalAt s t C) (primitiveAttraction s t C) := by
  have pref := primitive_prefactor_interval_contains i j s hs t ht
  have body := primitive_boys_at_contains i j s hs t ht C
  simpa only [primitiveIntervalAt,primitiveAttraction] using
    mul_holds (primitivePrefactorInterval s t) (primitiveBoysAt s t C)
      _ _ pref body

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
