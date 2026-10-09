import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAttractionPaid.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.ExpandedPaid

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionPaidExpanded
open LAlanine40K2025.UnifiedOrbitals
noncomputable section

structure Material where
  parent : PreciseAttractionPaid.Material
  paidAddresses : Finset (Fin 4851)
  actualWeighted : ℝ
  recordedWeighted : ℝ

def material : Material where
  parent := PreciseAttractionPaid.material
  paidAddresses := UnifiedOrbitals.Attraction.Precise.Rows.expandedPaidAddresses
  actualWeighted := UnifiedOrbitals.Attraction.Precise.expandedPaidActualAttraction
  recordedWeighted := UnifiedOrbitals.Attraction.Precise.expandedPaidRecordedAttraction

theorem parent_same_source : material.parent = PreciseAttractionPaid.material := rfl
theorem addresses_same_source :
    material.paidAddresses = UnifiedOrbitals.Attraction.Precise.Rows.expandedPaidAddresses := rfl
theorem actual_same_source :
    material.actualWeighted = UnifiedOrbitals.Attraction.Precise.expandedPaidActualAttraction := rfl
theorem recorded_same_source :
    material.recordedWeighted = UnifiedOrbitals.Attraction.Precise.expandedPaidRecordedAttraction := rfl

structure Closure : Prop where
  parent : PreciseAttractionPaid.Closure
  parentIdentity : type_of% parent_same_source
  addressesIdentity : type_of% addresses_same_source
  actualIdentity : type_of% actual_same_source
  recordedIdentity : type_of% recorded_same_source
  rowCensus : type_of% UnifiedOrbitals.Attraction.Precise.Rows.expanded_paid_addresses_card
  retainedCoverage : type_of% UnifiedOrbitals.Attraction.Precise.Rows.old_paid_subset
  sourceRow : type_of% UnifiedOrbitals.Attraction.Precise.Rows.expanded_paid_address_error
  weightedActual : type_of% UnifiedOrbitals.Attraction.Precise.expanded_paid_attraction_within_report

theorem sourceGeneratedClosure : Closure :=
  ⟨PreciseAttractionPaid.sourceGeneratedClosure,parent_same_source,
    addresses_same_source,actual_same_source,recorded_same_source,
    UnifiedOrbitals.Attraction.Precise.Rows.expanded_paid_addresses_card,
    UnifiedOrbitals.Attraction.Precise.Rows.old_paid_subset,
    UnifiedOrbitals.Attraction.Precise.Rows.expanded_paid_address_error,
    UnifiedOrbitals.Attraction.Precise.expanded_paid_attraction_within_report⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionPaidExpanded
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
