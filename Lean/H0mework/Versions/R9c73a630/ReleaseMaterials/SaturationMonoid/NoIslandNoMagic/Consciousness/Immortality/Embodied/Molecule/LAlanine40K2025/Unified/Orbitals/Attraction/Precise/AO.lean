import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Integral
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Primitive
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.AO

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceGaussianModel SourceFiniteData GlobalSource
open LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceSignedEvaluator SourceCoulomb MeasureTheory
open scoped BigOperators
noncomputable section

def aoIntervalAt (i j : Basis) (C : Fin 3 → ℚ) : Pair :=
  ((sourceTerms i).map fun s =>
    ((sourceTerms j).map fun t => primitiveIntervalAt s t C).sum).sum

theorem ao_interval_at_contains (i j : Basis) (C : Fin 3 → ℚ) :
    Holds (aoIntervalAt i j C) (aoAttractionFinite i j C) := by
  have inner (s : Term) (hs : s ∈ sourceTerms i) :
      Holds ((sourceTerms j).map fun t => primitiveIntervalAt s t C).sum
        ((sourceTerms j).map fun t => primitiveAttraction s t C).sum :=
    list_sum_holds (sourceTerms j) _ _
      (fun t ht => primitive_interval_at_contains i j s hs t ht C)
  have whole := list_sum_holds (sourceTerms i)
    (fun s => ((sourceTerms j).map fun t => primitiveIntervalAt s t C).sum)
    (fun s => ((sourceTerms j).map fun t => primitiveAttraction s t C).sum) inner
  simpa only [aoIntervalAt,aoAttractionFinite] using whole

def aoInterval (i j : Basis) : Pair :=
  ∑ a : Fin 13,
    mul (nucleusChargePair a) (aoIntervalAt i j (nucleus a))

theorem ao_interval_contains (i j : Basis) :
    Holds (aoInterval i j) (aoIntegral i j) := by
  unfold aoInterval aoIntegral
  apply finset_sum_holds
  intro a _
  have charge : Holds (nucleusChargePair a) (-Nuclear.nuclearCharge a) := by
    simp [Holds,nucleusChargePair,Nuclear.nuclearCharge]
  have integral := ao_attraction_finite i j (nucleus a)
  have bound := ao_interval_at_contains i j (nucleus a)
  rw [← integral] at bound
  exact mul_holds _ _ _ _ charge bound

end
end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
