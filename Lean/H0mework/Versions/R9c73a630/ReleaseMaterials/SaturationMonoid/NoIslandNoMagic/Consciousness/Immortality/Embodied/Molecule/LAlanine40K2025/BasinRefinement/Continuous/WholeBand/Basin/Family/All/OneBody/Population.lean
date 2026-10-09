import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.OneBody.Kinetic
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Source.Charge.Consumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody
open SourceGaussianModel ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory
open LAlanine40K2025.UnifiedOrbitals
open scoped BigOperators
noncomputable section

def zonePopulation (z : Option (Fin 13)) : ℝ := ∫ x in region z, sourceDensity x

theorem zone_population_sum :
    ∑ z : Option (Fin 13), zonePopulation z = ∫ x, sourceDensity x := by
  have h := integral_iUnion_fintype (s := region) all_regions_measurable regions_disjoint
    (fun _ => sourceDensity_integrable.integrableOn)
  rw [regions_cover] at h
  simpa only [setIntegral_univ,zonePopulation] using h.symm

theorem zone_population_total :
    |∑ z : Option (Fin 13), zonePopulation z - 48| ≤ (1/10^9 : ℝ) := by
  rw [zone_population_sum]
  exact UnifiedOrbitals.OriginalMetric.Charge.actual_whole_space_charge

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
