import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.PreciseAttractionLedger.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Contraction.Paid

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionPaid
open LAlanine40K2025.UnifiedOrbitals
noncomputable section

structure Material where
  parent : PreciseAttractionLedger.Material
  paidAddresses : Finset (Fin 4851)
  actualWeighted : ℝ
  recordedWeighted : ℝ

def material : Material where
  parent := PreciseAttractionLedger.material
  paidAddresses := UnifiedOrbitals.Attraction.Precise.Rows.paidAddresses
  actualWeighted := UnifiedOrbitals.Attraction.Precise.paidActualAttraction
  recordedWeighted := UnifiedOrbitals.Attraction.Precise.paidRecordedAttraction

theorem parent_same_source : material.parent = PreciseAttractionLedger.material := rfl
theorem addresses_same_source :
    material.paidAddresses = UnifiedOrbitals.Attraction.Precise.Rows.paidAddresses := rfl
theorem actual_same_source :
    material.actualWeighted = UnifiedOrbitals.Attraction.Precise.paidActualAttraction := rfl
theorem recorded_same_source :
    material.recordedWeighted = UnifiedOrbitals.Attraction.Precise.paidRecordedAttraction := rfl

structure Closure : Prop where
  parent : PreciseAttractionLedger.Closure
  parentIdentity : type_of% parent_same_source
  addressesIdentity : type_of% addresses_same_source
  actualIdentity : type_of% actual_same_source
  recordedIdentity : type_of% recorded_same_source
  rowCensus : type_of% UnifiedOrbitals.Attraction.Precise.Rows.paid_addresses_card
  sourceRow : type_of% UnifiedOrbitals.Attraction.Precise.Rows.paid_address_error
  weightedActual : type_of% UnifiedOrbitals.Attraction.Precise.paid_attraction_within_report

theorem sourceGeneratedClosure : Closure :=
  ⟨PreciseAttractionLedger.sourceGeneratedClosure,parent_same_source,
    addresses_same_source,actual_same_source,recorded_same_source,
    UnifiedOrbitals.Attraction.Precise.Rows.paid_addresses_card,
    UnifiedOrbitals.Attraction.Precise.Rows.paid_address_error,
    UnifiedOrbitals.Attraction.Precise.paid_attraction_within_report⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.PreciseAttractionPaid
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
