import H0mework.Chemistry.LAlanineInertia.SourceSourceBoundLAlanine40KInertialStep
import H0mework.Chemistry.LAlanineInertia.RuntimeInertiaParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

inductive InertiaCurrent
  | ingress
  | ready (material : Interface.InertialStepReadout)

def inertiaReadout : InertiaCurrent → Interface.InertialStepReadout
  | .ingress => Source.stepReadout
  | .ready material => material

def inertiaFrame : InertiaCurrent → Interface.NuclearFrame
  | .ingress => Source.stepReadout.current
  | .ready material => material.target

def inertiaCurrentLedger : InertiaCurrent → Energy.Interface.MolecularEnergyLedger
  | .ingress => Source.stepReadout.currentLedger
  | .ready material => material.targetLedger

def inertiaPhysicalTime : InertiaCurrent → ℚ
  | .ingress => 0
  | .ready material => material.duration

def inertiaNext (current : InertiaCurrent) : InertiaCurrent := .ready (inertiaReadout current)
def inertiaSupport : LAlanineStage := .forceDrivenMaterialNextCertified

def inertiaVocabulary : ConstructiveRoot.Vocabulary where
  Current := InertiaCurrent
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := fun _ => inertiaSupport
  lineageAt := fun _ => LAlanine40K2025.Source.key
  NativeWriteAt := fun current => match current with | .ingress => PUnit | .ready _ => PEmpty
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun current => match current with | .ingress => PEmpty | .ready _ => PUnit
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := by
    intro current write
    cases current with
    | ingress => exact inertiaNext .ingress
    | ready _ => exact nomatch write
  relationTarget := PEmpty.elim
  continuedTarget := by
    intro current write
    cases current with
    | ingress => exact nomatch write
    | ready material => exact .ready material
  redirectTarget := PEmpty.elim

abbrev InertiaV := inertiaVocabulary

def inertiaEventLaw : SourceNativeEventAlgebra N InertiaV where
  EventAt := fun _ support => PLift (support = inertiaSupport)
  compile := by
    intro current support event
    cases current with
    | ingress => exact .nativeWrite PUnit.unit
    | ready _ => exact .continuedTransport PUnit.unit
  AffectedInventoryAt := fun _ => Unit
  affectedInventoryPresentation := by
    intro current support event
    cases event.down
    exact Root.eventLaw.affectedInventoryPresentation (.exact inertiaSupport)
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.down.symm
  lineage_commutes := fun _ => rfl

def inertiaSource : SourceNativeSource N InertiaV where
  initial := .ingress
  law := inertiaEventLaw

def inertiaEmitted (current : InertiaCurrent) : inertiaSource.toRootSource.actual.OccurrenceAt current :=
  ⟨inertiaSupport, ⟨rfl⟩⟩

theorem inertiaCompiled_next (current : InertiaCurrent) :
    (inertiaSource.toRootSource.actual.compile (inertiaEmitted current)).nextCurrent? =
      some (inertiaNext current) := by cases current <;> rfl

theorem inertiaReadiness_no_native_write (material : Interface.InertialStepReadout) :
    IsEmpty (InertiaV.NativeWriteAt (.ready material)) := ⟨fun write => nomatch write⟩

theorem inertiaReadiness_retains (material : Interface.InertialStepReadout) :
    inertiaReadout (inertiaNext (.ready material)) = material ∧
      inertiaFrame (inertiaNext (.ready material)) = material.target ∧
      inertiaCurrentLedger (inertiaNext (.ready material)) = material.targetLedger ∧
      inertiaPhysicalTime (inertiaNext (.ready material)) = material.duration := ⟨rfl, rfl, rfl, rfl⟩

end
end LAlanine40K2025.Inertia.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
