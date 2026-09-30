import H0mework.Chemistry.LAlanineReentry.RuntimeRuntimeMaterial

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
noncomputable section

inductive ReentryCurrent
  | ingress
  | ready (result : ReentryResult)

def reentryResponse : ReentryCurrent → ReentryResult
  | .ingress => reentrySourceResult
  | .ready result => result

def reentryHeld : ReentryCurrent → Matrix Basis Basis ℂ
  | .ingress => reentryParentHeld
  | .ready result => result.held

def reentryFrame : ReentryCurrent → Inertia.Interface.NuclearFrame
  | .ingress => reentryParentFrame
  | .ready result => result.nuclear.target

def reentryCurrentLedger : ReentryCurrent → Energy.Interface.MolecularEnergyLedger
  | .ingress => reentryParentLedger
  | .ready result => result.nuclear.targetLedger

def reentryCurrentPacket : ReentryCurrent → Inertia.Interface.InertialStepReadout
  | .ingress => reentryParentPacket
  | .ready result => result.nuclear

def reentryPhysicalTime : ReentryCurrent → ℚ
  | .ingress => reentryParentTime
  | .ready result => result.clock

def reentryNext (current : ReentryCurrent) : ReentryCurrent := .ready (reentryResponse current)
def reentrySupport : LAlanineStage := .forceDrivenMaterialNextCertified

def reentryVocabulary : ConstructiveRoot.Vocabulary where
  Current := ReentryCurrent
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := fun _ => reentrySupport
  lineageAt := fun _ => LAlanine40K2025.Source.key
  NativeWriteAt := fun current => match current with | .ingress => PUnit | .ready _ => PEmpty
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun current => match current with | .ingress => PEmpty | .ready _ => PUnit
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := by
    intro current write
    cases current with
    | ingress => exact reentryNext .ingress
    | ready _ => exact nomatch write
  relationTarget := PEmpty.elim
  continuedTarget := by
    intro current write
    cases current with
    | ingress => exact nomatch write
    | ready result => exact .ready result
  redirectTarget := PEmpty.elim

abbrev ReentryV := reentryVocabulary

def reentryEventLaw : SourceNativeEventAlgebra N ReentryV where
  EventAt := fun _ support => PLift (support = reentrySupport)
  compile := by
    intro current support event
    cases current with
    | ingress => exact .nativeWrite PUnit.unit
    | ready _ => exact .continuedTransport PUnit.unit
  AffectedInventoryAt := fun _ => Unit
  affectedInventoryPresentation := by
    intro current support event
    cases event.down
    exact Root.eventLaw.affectedInventoryPresentation (.exact reentrySupport)
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.down.symm
  lineage_commutes := fun _ => rfl

def reentrySource : SourceNativeSource N ReentryV where
  initial := .ingress
  law := reentryEventLaw

def reentryEmitted (current : ReentryCurrent) : reentrySource.toRootSource.actual.OccurrenceAt current := ⟨reentrySupport, ⟨rfl⟩⟩

theorem reentryCompiled_next (current : ReentryCurrent) :
    (reentrySource.toRootSource.actual.compile (reentryEmitted current)).nextCurrent? = some (reentryNext current) := by
  cases current <;> rfl

theorem reentryReadiness_no_native_write (result : ReentryResult) :
    IsEmpty (ReentryV.NativeWriteAt (.ready result)) := ⟨fun write => nomatch write⟩

theorem reentryNext_idempotent (current : ReentryCurrent) : reentryNext (reentryNext current) = reentryNext current := rfl

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
