import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAttractionMixedPaid.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.LargePaid

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionLargePaid
open LAlanine40K2025.UnifiedOrbitals
noncomputable section

structure Material where
  parent : PreciseAttractionMixedPaid.Material
  paidAddresses : Finset (Fin 4851)
  actualWeighted : ℝ
  recordedWeighted : ℝ
  errorBudget : ℝ

def material : Material where
  parent := PreciseAttractionMixedPaid.material
  paidAddresses := UnifiedOrbitals.Attraction.Precise.Rows.largePaidAddresses
  actualWeighted := UnifiedOrbitals.Attraction.Precise.largeActualAttraction
  recordedWeighted := UnifiedOrbitals.Attraction.Precise.largeRecordedAttraction
  errorBudget := UnifiedOrbitals.Attraction.Precise.largeErrorBudget

theorem parent_same_source : material.parent = PreciseAttractionMixedPaid.material := rfl
theorem addresses_same_source :
    material.paidAddresses = UnifiedOrbitals.Attraction.Precise.Rows.largePaidAddresses := rfl
theorem actual_same_source :
    material.actualWeighted = UnifiedOrbitals.Attraction.Precise.largeActualAttraction := rfl
theorem recorded_same_source :
    material.recordedWeighted = UnifiedOrbitals.Attraction.Precise.largeRecordedAttraction := rfl
theorem budget_same_source :
    material.errorBudget = UnifiedOrbitals.Attraction.Precise.largeErrorBudget := rfl

structure Closure : Prop where
  parent : PreciseAttractionMixedPaid.Closure
  parentIdentity : type_of% parent_same_source
  addressesIdentity : type_of% addresses_same_source
  actualIdentity : type_of% actual_same_source
  recordedIdentity : type_of% recorded_same_source
  budgetIdentity : type_of% budget_same_source
  rowCensus : type_of% UnifiedOrbitals.Attraction.Precise.Rows.large_paid_addresses_card
  retainedCoverage : type_of% UnifiedOrbitals.Attraction.Precise.Rows.old_mixed_subset_large
  sourceRow : type_of% UnifiedOrbitals.Attraction.Precise.Rows.large_paid_address_error
  weightedActual : type_of% UnifiedOrbitals.Attraction.Precise.large_attraction_within_budget

theorem sourceGeneratedClosure : Closure :=
  ⟨PreciseAttractionMixedPaid.sourceGeneratedClosure,parent_same_source,
    addresses_same_source,actual_same_source,recorded_same_source,budget_same_source,
    UnifiedOrbitals.Attraction.Precise.Rows.large_paid_addresses_card,
    UnifiedOrbitals.Attraction.Precise.Rows.old_mixed_subset_large,
    UnifiedOrbitals.Attraction.Precise.Rows.large_paid_address_error,
    UnifiedOrbitals.Attraction.Precise.large_attraction_within_budget⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionLargePaid
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
