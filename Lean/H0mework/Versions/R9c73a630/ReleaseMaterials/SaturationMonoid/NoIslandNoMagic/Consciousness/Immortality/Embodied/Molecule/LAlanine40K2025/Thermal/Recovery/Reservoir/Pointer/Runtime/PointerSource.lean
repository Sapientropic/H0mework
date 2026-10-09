import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Producer.SourceGeneratedPointerInstrument
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer
noncomputable section

inductive PointerCurrent
  | ingress
  | running (state : Live.State)

def pointerCurrentState : PointerCurrent → Live.State
  | .ingress => Live.initial
  | .running state => state

def pointerNext (current : PointerCurrent) : PointerCurrent :=
  .running (match current with
    | .ingress => Live.first
    | .running state => Live.loadNext state)

def pointerAction : PointerCurrent → Matrix.unitaryGroup PointerIndex ℂ
  | .ingress => sourceUnitary
  | .running _ => Pointer.loadPulse (nativeClockStep : ℝ)

theorem pointerNext_joint (current : PointerCurrent) :
    (pointerCurrentState (pointerNext current)).joint =
      Quantum.conjugation (pointerAction current) (pointerCurrentState current).joint := by
  cases current with
  | ingress => exact Live.measureNext_joint Live.initial
  | running state => exact Live.loadNext_joint state

theorem pointerNext_clock (current : PointerCurrent) :
    (pointerCurrentState (pointerNext current)).localClock =
      (pointerCurrentState current).localClock + nativeClockStep := by
  cases current <;> rfl

def pointerVocabulary : ConstructiveRoot.Vocabulary where
  Current := PointerCurrent
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
  nativeTarget := fun {current} _ => pointerNext current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev PointerV := pointerVocabulary

def pointerEventLaw : SourceNativeEventAlgebra RecoveryN PointerV where
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

def pointerSource : SourceNativeSource RecoveryN PointerV where
  initial := .ingress
  law := pointerEventLaw

def pointerEmitted (current : PointerCurrent) : pointerSource.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport, ⟨rfl⟩⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
