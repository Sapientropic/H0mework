import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime.Parent

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
noncomputable section

abbrev ActuationResult := ReceiverBody.Runtime.ActuationResult

def sourceInput : ActuationResult := FiniteActuation.input.joint.body
def sourceOutput : ActuationResult := generatedBody

inductive BodyCurrent
  | ingress
  | ready (result : ActuationResult)

def currentResult : BodyCurrent → ActuationResult
  | .ingress => sourceInput
  | .ready result => result

def nextCurrent : BodyCurrent → BodyCurrent
  | .ingress => .ready sourceOutput
  | .ready result => .ready result

-- A completed joint action is retained. Transport does not mint another physical step.
def vocabulary : ConstructiveRoot.Vocabulary where
  Current := BodyCurrent
  Anchor := RecoveryN.Anchor
  Incidence := RecoverySupport
  Lineage := RecoveryN.Lineage
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := fun _ => reservoirSupport
  lineageAt := fun _ => LAlanine40K2025.Source.key
  NativeWriteAt := fun current => match current with | .ingress => PUnit | .ready _ => PEmpty
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun current => match current with | .ingress => PEmpty | .ready _ => PUnit
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := by
    intro current write
    cases current with
    | ingress => exact nextCurrent .ingress
    | ready _ => exact nomatch write
  relationTarget := PEmpty.elim
  continuedTarget := by
    intro current write
    cases current with
    | ingress => exact nomatch write
    | ready result => exact .ready result
  redirectTarget := PEmpty.elim

abbrev BodyV := vocabulary

def eventLaw : SourceNativeEventAlgebra RecoveryN BodyV where
  EventAt := fun _ support => PLift (support=reservoirSupport)
  compile := by
    intro current support event
    cases current with
    | ingress => exact .nativeWrite PUnit.unit
    | ready _ => exact .continuedTransport PUnit.unit
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

def source : SourceNativeSource RecoveryN BodyV where
  initial := .ingress
  law := eventLaw

def emitted (current : BodyCurrent) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport,⟨rfl⟩⟩

theorem ready_no_native (result : ActuationResult) : IsEmpty (BodyV.NativeWriteAt (.ready result)) :=
  ⟨fun write => nomatch write⟩

theorem ready_retains (result : ActuationResult) : currentResult (nextCurrent (.ready result))=result := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
