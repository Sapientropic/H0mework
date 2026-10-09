import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAttractionPaidExpanded.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.MixedPaid

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionMixedPaid
open LAlanine40K2025.UnifiedOrbitals
noncomputable section

structure Material where
  parent : PreciseAttractionPaidExpanded.Material
  paidAddresses : Finset (Fin 4851)
  actualWeighted : ℝ
  recordedWeighted : ℝ
  errorBudget : ℝ

def material : Material where
  parent := PreciseAttractionPaidExpanded.material
  paidAddresses := UnifiedOrbitals.Attraction.Precise.Rows.mixedPaidAddresses
  actualWeighted := UnifiedOrbitals.Attraction.Precise.mixedActualAttraction
  recordedWeighted := UnifiedOrbitals.Attraction.Precise.mixedRecordedAttraction
  errorBudget := UnifiedOrbitals.Attraction.Precise.mixedErrorBudget

theorem parent_same_source : material.parent = PreciseAttractionPaidExpanded.material := rfl
theorem addresses_same_source :
    material.paidAddresses = UnifiedOrbitals.Attraction.Precise.Rows.mixedPaidAddresses := rfl
theorem actual_same_source :
    material.actualWeighted = UnifiedOrbitals.Attraction.Precise.mixedActualAttraction := rfl
theorem recorded_same_source :
    material.recordedWeighted = UnifiedOrbitals.Attraction.Precise.mixedRecordedAttraction := rfl
theorem budget_same_source :
    material.errorBudget = UnifiedOrbitals.Attraction.Precise.mixedErrorBudget := rfl

structure Closure : Prop where
  parent : PreciseAttractionPaidExpanded.Closure
  parentIdentity : type_of% parent_same_source
  addressesIdentity : type_of% addresses_same_source
  actualIdentity : type_of% actual_same_source
  recordedIdentity : type_of% recorded_same_source
  budgetIdentity : type_of% budget_same_source
  rowCensus : type_of% UnifiedOrbitals.Attraction.Precise.Rows.mixed_paid_addresses_card
  retainedCoverage : type_of% UnifiedOrbitals.Attraction.Precise.Rows.expanded_subset_mixed
  sourceRow : type_of% UnifiedOrbitals.Attraction.Precise.Rows.mixed_paid_address_error
  weightedActual : type_of% UnifiedOrbitals.Attraction.Precise.mixed_attraction_within_budget

theorem sourceGeneratedClosure : Closure :=
  ⟨PreciseAttractionPaidExpanded.sourceGeneratedClosure,parent_same_source,
    addresses_same_source,actual_same_source,recorded_same_source,budget_same_source,
    UnifiedOrbitals.Attraction.Precise.Rows.mixed_paid_addresses_card,
    UnifiedOrbitals.Attraction.Precise.Rows.expanded_subset_mixed,
    UnifiedOrbitals.Attraction.Precise.Rows.mixed_paid_address_error,
    UnifiedOrbitals.Attraction.Precise.mixed_attraction_within_budget⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionMixedPaid
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
