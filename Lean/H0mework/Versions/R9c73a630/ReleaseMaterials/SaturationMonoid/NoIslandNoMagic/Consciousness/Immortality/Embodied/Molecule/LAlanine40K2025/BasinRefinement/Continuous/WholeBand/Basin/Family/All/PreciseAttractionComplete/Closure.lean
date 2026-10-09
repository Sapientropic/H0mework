import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAttractionAlmostPaid.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Complete

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionComplete
open LAlanine40K2025.UnifiedOrbitals
noncomputable section

structure Material where
  parent : PreciseAttractionAlmostPaid.Material
  paidAddresses : Finset (Fin 4851)
  actualWeighted : ℝ
  recordedWeighted : ℝ
  errorBudget : ℝ
  independentWeighted : ℝ

def material : Material where
  parent := PreciseAttractionAlmostPaid.material
  paidAddresses := UnifiedOrbitals.Attraction.Precise.Rows.fullPaidAddresses
  actualWeighted := UnifiedOrbitals.Attraction.Precise.totalIntegral
  recordedWeighted := UnifiedOrbitals.Attraction.Precise.recordedAttractionSum
  errorBudget := UnifiedOrbitals.Attraction.Precise.completeErrorBudget
  independentWeighted := UnifiedOrbitals.Attraction.Precise.independentElectronNuclear

theorem parent_same_source : material.parent = PreciseAttractionAlmostPaid.material := rfl
theorem addresses_same_source :
    material.paidAddresses = UnifiedOrbitals.Attraction.Precise.Rows.fullPaidAddresses := rfl
theorem actual_same_source :
    material.actualWeighted = UnifiedOrbitals.Attraction.Precise.totalIntegral := rfl
theorem recorded_same_source :
    material.recordedWeighted = UnifiedOrbitals.Attraction.Precise.recordedAttractionSum := rfl
theorem budget_same_source :
    material.errorBudget = UnifiedOrbitals.Attraction.Precise.completeErrorBudget := rfl
theorem independent_same_source :
    material.independentWeighted =
      UnifiedOrbitals.Attraction.Precise.independentElectronNuclear := rfl

structure Closure : Prop where
  parent : PreciseAttractionAlmostPaid.Closure
  parentIdentity : type_of% parent_same_source
  addressesIdentity : type_of% addresses_same_source
  actualIdentity : type_of% actual_same_source
  recordedIdentity : type_of% recorded_same_source
  budgetIdentity : type_of% budget_same_source
  independentIdentity : type_of% independent_same_source
  rowCensus : type_of% UnifiedOrbitals.Attraction.Precise.Rows.full_paid_addresses_card
  retainedCoverage : type_of% UnifiedOrbitals.Attraction.Precise.Rows.almost_subset_full
  sourceRow : type_of% UnifiedOrbitals.Attraction.Precise.Rows.full_address_error
  weightedActual : type_of% UnifiedOrbitals.Attraction.Precise.complete_attraction_within_budget
  independentActual : type_of% UnifiedOrbitals.Attraction.Precise.complete_attraction_within_independent

theorem sourceGeneratedClosure : Closure :=
  ⟨PreciseAttractionAlmostPaid.sourceGeneratedClosure,parent_same_source,
    addresses_same_source,actual_same_source,recorded_same_source,budget_same_source,
    independent_same_source,UnifiedOrbitals.Attraction.Precise.Rows.full_paid_addresses_card,
    UnifiedOrbitals.Attraction.Precise.Rows.almost_subset_full,
    UnifiedOrbitals.Attraction.Precise.Rows.full_address_error,
    UnifiedOrbitals.Attraction.Precise.complete_attraction_within_budget,
    UnifiedOrbitals.Attraction.Precise.complete_attraction_within_independent⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionComplete
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
