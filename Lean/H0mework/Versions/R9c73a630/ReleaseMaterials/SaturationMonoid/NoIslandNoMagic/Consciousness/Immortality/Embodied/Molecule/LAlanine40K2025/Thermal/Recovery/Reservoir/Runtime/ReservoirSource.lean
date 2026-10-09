import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedFiniteReservoir
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Runtime.ChargingIngress

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime
noncomputable section

/-- Registration remains at the inherited source row; the source current carries the evolving material. -/
def reservoirSupport : RecoverySupport := Charging.Runtime.chargingSourceSupport

inductive ReservoirCurrent
  | ingress
  | running (state : Current.State)

def reservoirCurrentState : ReservoirCurrent → Current.State
  | .ingress => Current.initial
  | .running state => state

def reservoirNext (current : ReservoirCurrent) : ReservoirCurrent :=
  .running (match current with
    | .ingress => Current.supplyNext Current.initial
    | .running state => Current.loadNext state)

def reservoirVocabulary : ConstructiveRoot.Vocabulary where
  Current := ReservoirCurrent
  Anchor := RecoveryN.Anchor
  Incidence := RecoverySupport
  Lineage := RecoveryN.Lineage
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := fun _ => reservoirSupport
  lineageAt := fun _ => LAlanine40K2025.Source.key
  NativeWriteAt := fun _ => PUnit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => reservoirNext current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev ReservoirV := reservoirVocabulary

def reservoirEventLaw : SourceNativeEventAlgebra RecoveryN ReservoirV where
  EventAt := fun _ support => PLift (support = reservoirSupport)
  compile := fun _ => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.down
    exact recoveryInventory _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.down.symm
  lineage_commutes := fun _ => rfl

def reservoirSource : SourceNativeSource RecoveryN ReservoirV where
  initial := .ingress
  law := reservoirEventLaw

def reservoirEmitted (current : ReservoirCurrent) : reservoirSource.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport, ⟨rfl⟩⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
