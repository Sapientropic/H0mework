import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.AO
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.Runtime.Consumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.UnifiedOrbitals BasinRefinement SourceGaussianModel SourceFiniteData
open scoped BigOperators
noncomputable section

def sourceNuclearAttractionFinite (i j : Basis) : ℝ :=
  ∑ a : Fin 13,
    -BasinRefinement.WholeBandBasin.Family.All.Nuclear.nuclearCharge a *
      aoAttractionFinite i j
        (BasinRefinement.WholeBandBasin.Family.All.Nuclear.nuclearPositionQ a)

theorem source_ao_attraction_finite (i j : Basis) :
    BasinRefinement.WholeBandBasin.Family.All.Nuclear.aoAttraction i j =
      sourceNuclearAttractionFinite i j := by
  unfold BasinRefinement.WholeBandBasin.Family.All.Nuclear.aoAttraction
    sourceNuclearAttractionFinite
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (∫ x : Point, ao i x * ao j x *
    SourceCoulomb.kernel (x - fun k =>
      (BasinRefinement.WholeBandBasin.Family.All.Nuclear.nuclearPositionQ a k : ℝ))) = _
  exact ao_attraction_finite i j
    (BasinRefinement.WholeBandBasin.Family.All.Nuclear.nuclearPositionQ a)

theorem source_zone_attraction_finite :
    (∑ z : Option (Fin 13), ∑ a : Fin 13,
      (BasinRefinement.WholeBandBasin.Family.All.Nuclear.Runtime.readMaterial
        BasinRefinement.WholeBandBasin.Family.All.Nuclear.Runtime.afterFirst).zoneAttraction z a) =
      ∑ i : Basis, ∑ j : Basis,
        (BasinRefinement.SourceFiniteData.densityMatrix i j : ℝ) *
          sourceNuclearAttractionFinite i j := by
  rw [BasinRefinement.WholeBandBasin.Family.All.Nuclear.Runtime.actual_attraction_original_ao]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [source_ao_attraction_finite]

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
