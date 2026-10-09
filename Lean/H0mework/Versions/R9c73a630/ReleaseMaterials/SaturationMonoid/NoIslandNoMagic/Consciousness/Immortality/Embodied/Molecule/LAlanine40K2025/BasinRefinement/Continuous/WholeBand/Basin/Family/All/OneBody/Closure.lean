import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.OneBody.Population

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory
open scoped BigOperators
noncomputable section

structure Material where
  parent : All.Material
  zoneLaplacian : Option (Fin 13) → ℝ
  zoneKinetic : Option (Fin 13) → ℝ
  zonePopulation : Option (Fin 13) → ℝ

def material : Material where
  parent := All.material
  zoneLaplacian := fun z => ∫ x in region z, laplacian sourceTerms densityMatrix x
  zoneKinetic := zoneKinetic
  zonePopulation := zonePopulation

theorem parent_same_source : material.parent=All.material := rfl
theorem zoneLaplacian_same_source (z : Option (Fin 13)) :
    material.zoneLaplacian z=(∫ x in region z, laplacian sourceTerms densityMatrix x) := rfl
theorem zoneKinetic_same_source (z : Option (Fin 13)) :
    material.zoneKinetic z=zoneKinetic z := rfl
theorem zonePopulation_same_source (z : Option (Fin 13)) :
    material.zonePopulation z=zonePopulation z := rfl

structure Closure : Prop where
  parent : All.Closure
  parentIdentity : type_of% parent_same_source
  zoneLaplacianIdentity : type_of% zoneLaplacian_same_source
  zoneKineticIdentity : type_of% zoneKinetic_same_source
  zonePopulationIdentity : type_of% zonePopulation_same_source
  basinsInvariant : type_of% basin_invariant
  regionsInvariant : type_of% region_invariant
  allBasinsZeroFlux : type_of% every_basin_zero_flux
  residualZeroFlux : type_of% residual_zero_flux
  allZonesZeroFlux : type_of% every_zone_zero_flux
  atom7Basin : type_of% atom7_same_basin
  atom7ZeroFlux : type_of% atom7_same_zero_flux
  wholeSpaceZeroFlux : type_of% Weak.Invariant.whole_space_zero_flux
  kineticDifference : type_of% kinetic_density_difference
  gradientKineticL1 : type_of% gradientKinetic_integrable
  laplacianKineticL1 : type_of% laplacianKinetic_integrable
  allZonesKineticUnique : type_of% every_zone_kinetic_unique
  regionsDisjoint : type_of% regions_disjoint
  regionsCover : type_of% regions_cover
  zoneKineticSum : type_of% zone_kinetic_sum
  kineticOriginalAO : type_of% total_kinetic_original_ao
  attractorLaplacianNegative : type_of% attractor_laplacian_negative
  attractorDensitiesDiffer : type_of% attractor_kinetic_densities_differ
  zonePopulationSum : type_of% zone_population_sum
  zonePopulationTotal : type_of% zone_population_total

theorem sourceGeneratedClosure : Closure :=
  ⟨All.sourceGeneratedClosure,
    parent_same_source,zoneLaplacian_same_source,zoneKinetic_same_source,
    zonePopulation_same_source,
    basin_invariant,region_invariant,every_basin_zero_flux,residual_zero_flux,
    every_zone_zero_flux,atom7_same_basin,atom7_same_zero_flux,
    Weak.Invariant.whole_space_zero_flux,
    kinetic_density_difference,gradientKinetic_integrable,laplacianKinetic_integrable,
    every_zone_kinetic_unique,regions_disjoint,regions_cover,zone_kinetic_sum,
    total_kinetic_original_ao,attractor_laplacian_negative,
    attractor_kinetic_densities_differ,zone_population_sum,zone_population_total⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
