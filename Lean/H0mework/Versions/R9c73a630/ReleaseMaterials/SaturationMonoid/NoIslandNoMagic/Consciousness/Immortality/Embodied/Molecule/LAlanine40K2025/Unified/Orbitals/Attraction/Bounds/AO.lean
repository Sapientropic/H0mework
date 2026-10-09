import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.Primitive
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceGaussianModel SourceFiniteData GlobalSource
open LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All
open SourceSignedEvaluator
open scoped BigOperators
noncomputable section

def aoAttractionNucleusInterval (i j : Basis) (a : Fin 13) : Pair :=
  ((sourceTerms i).map fun s =>
    ((sourceTerms j).map fun t => primitiveAttractionInterval s t a).sum).sum

theorem ao_nucleus_interval_contains (i j : Basis) (a : Fin 13) :
    Holds (aoAttractionNucleusInterval i j a)
      (aoAttractionFinite i j (Nuclear.nuclearPositionQ a)) := by
  have inner (s : Term) (hs : s ∈ sourceTerms i) :
      Holds ((sourceTerms j).map fun t => primitiveAttractionInterval s t a).sum
        ((sourceTerms j).map fun t =>
          primitiveAttraction s t (Nuclear.nuclearPositionQ a)).sum :=
    list_sum_holds (sourceTerms j) _ _
      (fun t ht => primitive_attraction_interval_contains i j s hs t ht a)
  have whole := list_sum_holds (sourceTerms i)
    (fun s => ((sourceTerms j).map fun t => primitiveAttractionInterval s t a).sum)
    (fun s => ((sourceTerms j).map fun t =>
      primitiveAttraction s t (Nuclear.nuclearPositionQ a)).sum) inner
  simpa only [aoAttractionNucleusInterval,aoAttractionFinite] using whole

def nucleusChargePair (a : Fin 13) : Pair :=
  (-(Nuclear.nuclearChargeNat a : ℚ),-(Nuclear.nuclearChargeNat a : ℚ))

def aoAttractionInterval (i j : Basis) : Pair :=
  ∑ a : Fin 13, mul (nucleusChargePair a) (aoAttractionNucleusInterval i j a)

theorem ao_attraction_interval_contains (i j : Basis) :
    Holds (aoAttractionInterval i j) (Nuclear.aoAttraction i j) := by
  rw [source_ao_attraction_finite]
  unfold aoAttractionInterval sourceNuclearAttractionFinite
  apply finset_sum_holds
  intro a _
  have charge : Holds (nucleusChargePair a) (-Nuclear.nuclearCharge a) := by
    simp [Holds,nucleusChargePair,Nuclear.nuclearCharge]
  exact mul_holds _ _ _ _ charge (ao_nucleus_interval_contains i j a)

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
