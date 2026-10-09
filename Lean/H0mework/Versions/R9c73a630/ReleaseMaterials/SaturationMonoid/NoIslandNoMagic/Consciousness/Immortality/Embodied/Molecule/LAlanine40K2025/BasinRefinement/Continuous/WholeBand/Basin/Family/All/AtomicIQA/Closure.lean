import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AtomicIQA.Assignment
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AtomicIQA.Delocalization
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AtomicIQA.Energy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.AtomicIQA.FullUShift
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.KineticLedger.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
open LAlanine40K2025.UnifiedOrbitals
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource WholeBandBasin Set MeasureTheory
open scoped BigOperators
noncomputable section

structure Material where
  parent : KineticLedger.Material
  directCell : Option (Fin 13) × Option (Fin 13) → ℝ
  exchangeCell : Option (Fin 13) × Option (Fin 13) → ℝ
  sharedPairs : Option (Fin 13) × Option (Fin 13) → ℝ
  projectedPopulation : Option (Fin 13) → ℝ
  selfEnergy : Fin 13 → ℝ
  interaction : Fin 13 → Fin 13 → ℝ
  residualEnergy : ℝ

def material : Material where
  parent := KineticLedger.material
  directCell := directCell
  exchangeCell := exchangeCell
  sharedPairs := sharedPairs
  projectedPopulation := projectedPopulation
  selfEnergy := selfEnergy
  interaction := interaction
  residualEnergy := residualEnergy

theorem parent_same_source : material.parent=KineticLedger.material := rfl
theorem directCell_same_source (ij : Option (Fin 13) × Option (Fin 13)) :
    material.directCell ij=directCell ij := rfl
theorem exchangeCell_same_source (ij : Option (Fin 13) × Option (Fin 13)) :
    material.exchangeCell ij=exchangeCell ij := rfl
theorem sharedPairs_same_source (ij : Option (Fin 13) × Option (Fin 13)) :
    material.sharedPairs ij=sharedPairs ij := rfl
theorem projectedPopulation_same_source (i : Option (Fin 13)) :
    material.projectedPopulation i=projectedPopulation i := rfl
theorem selfEnergy_same_source (a : Fin 13) :
    material.selfEnergy a=selfEnergy a := rfl
theorem interaction_same_source (a b : Fin 13) :
    material.interaction a b=interaction a b := rfl
theorem residualEnergy_same_source :
    material.residualEnergy=residualEnergy := rfl

structure Closure : Prop where
  parent : KineticLedger.Closure
  parentIdentity : type_of% parent_same_source
  directCellIdentity : type_of% directCell_same_source
  exchangeCellIdentity : type_of% exchangeCell_same_source
  sharedPairsIdentity : type_of% sharedPairs_same_source
  projectedPopulationIdentity : type_of% projectedPopulation_same_source
  selfEnergyIdentity : type_of% selfEnergy_same_source
  interactionIdentity : type_of% interaction_same_source
  residualEnergyIdentity : type_of% residualEnergy_same_source
  attractorNearOwnNucleus : type_of% attractor_near_own_nucleus
  heavyAttractorOnNucleus : type_of% heavy_attractor_on_nucleus
  attractorFarFromOtherNuclei : type_of% attractor_far_from_other_nuclei
  attractorNearestNucleus : type_of% attractor_nearest_nucleus
  pairIntegrandSplit : type_of% pair_integrand_direct_exchange
  cellEnergySplit : type_of% cell_energy_direct_exchange
  directCellNonnegative : type_of% direct_cell_nonnegative
  exchangeCellNonnegative : type_of% exchange_cell_nonnegative
  exchangeCellBounded : type_of% exchange_cell_bounded
  directCellSymmetric : type_of% direct_cell_symmetric
  exchangeCellSymmetric : type_of% exchange_cell_symmetric
  directCellsTotal : type_of% direct_cells_total
  exchangeCellsTotal : type_of% exchange_cells_total
  holeDensityNonnegative : type_of% hole_density_nonnegative
  holeDensitySwap : type_of% hole_density_swap
  holeDensityIntegrable : type_of% hole_density_integrable
  occupiedOrthonormal : type_of% occupied_orthonormal
  holeReproducing : type_of% hole_reproducing
  sharedPairsNonnegative : type_of% shared_pairs_nonnegative
  sharedPairsSymmetric : type_of% shared_pairs_symmetric
  sharedPairsRow : type_of% shared_pairs_row
  projectedPopulationTotal : type_of% projected_population_total
  sharedPairsTotal : type_of% shared_pairs_total
  populationLocalizationDelocalization : type_of% population_localization_delocalization
  localizationDelocalizationSumRule : type_of% localization_delocalization_sum_rule
  zonePopulationProjected : type_of% zone_population_projected
  zoneResidualTotal : type_of% zone_residual_total
  interactionSplit : type_of% interaction_split
  interactionSymmetric : type_of% interaction_symmetric
  exchangeInteractionNonpositive : type_of% exchange_interaction_nonpositive
  exchangeInteractionBounded : type_of% exchange_interaction_bounded
  atomicIqaTotal : type_of% atomic_iqa_total
  atomicIqaOriginalAo : type_of% atomic_iqa_original_ao
  firstDerivativeAntisymmetric : type_of% first_derivative_antisymmetric
  connectionSquareNorm : type_of% connection_square_norm
  fullUKineticShift : type_of% full_U_kinetic_shift

theorem sourceGeneratedClosure : Closure :=
  ⟨KineticLedger.sourceGeneratedClosure,
    parent_same_source,directCell_same_source,exchangeCell_same_source,
    sharedPairs_same_source,projectedPopulation_same_source,
    selfEnergy_same_source,interaction_same_source,residualEnergy_same_source,
    attractor_near_own_nucleus,heavy_attractor_on_nucleus,
    attractor_far_from_other_nuclei,attractor_nearest_nucleus,
    pair_integrand_direct_exchange,cell_energy_direct_exchange,
    direct_cell_nonnegative,exchange_cell_nonnegative,exchange_cell_bounded,
    direct_cell_symmetric,exchange_cell_symmetric,
    direct_cells_total,exchange_cells_total,
    hole_density_nonnegative,hole_density_swap,hole_density_integrable,
    occupied_orthonormal,hole_reproducing,
    shared_pairs_nonnegative,shared_pairs_symmetric,shared_pairs_row,
    projected_population_total,shared_pairs_total,
    population_localization_delocalization,localization_delocalization_sum_rule,
    zone_population_projected,zone_residual_total,
    interaction_split,interaction_symmetric,
    exchange_interaction_nonpositive,exchange_interaction_bounded,
    atomic_iqa_total,atomic_iqa_original_ao,
    first_derivative_antisymmetric,connection_square_norm,full_U_kinetic_shift⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
