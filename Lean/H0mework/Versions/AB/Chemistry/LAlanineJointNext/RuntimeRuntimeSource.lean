import H0mework.Versions.AB.Chemistry.LAlanineJointNext.RuntimeRuntimeMaterial

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
noncomputable section

inductive JointCurrent
  | ingress
  | ready (result : JointResult)

def jointResponse : JointCurrent → JointResult
  | .ingress => jointSourceResult
  | .ready result => result

def jointHeld : JointCurrent → Matrix Basis Basis ℂ
  | .ingress => jointParentHeld
  | .ready result => result.held

def jointFrame : JointCurrent → Inertia.Interface.NuclearFrame
  | .ingress => jointParentFrame
  | .ready result => result.nuclear.target

def jointCurrentLedger : JointCurrent → Energy.Interface.MolecularEnergyLedger
  | .ingress => jointParentEnergyLedger
  | .ready result => result.nuclear.targetLedger

def jointCurrentPacket : JointCurrent → Inertia.Interface.InertialStepReadout
  | .ingress => jointParentHistory
  | .ready result => result.nuclear

def jointPhysicalTime : JointCurrent → ℚ
  | .ingress => jointParentTime
  | .ready result => result.clock

def jointNext (current : JointCurrent) : JointCurrent := .ready (jointResponse current)
def jointSupport : LAlanineStage := .forceDrivenMaterialNextCertified

def jointVocabulary : ConstructiveRoot.Vocabulary where
  Current := JointCurrent
  Anchor := N.Anchor
  Incidence := N.Incidence
  Lineage := N.Lineage
  anchorAt := fun _ => LAlanine40K2025.Source.key
  incidenceAt := fun _ => jointSupport
  lineageAt := fun _ => LAlanine40K2025.Source.key
  NativeWriteAt := fun current => match current with | .ingress => PUnit | .ready _ => PEmpty
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun current => match current with | .ingress => PEmpty | .ready _ => PUnit
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := by
    intro current write
    cases current with
    | ingress => exact jointNext .ingress
    | ready _ => exact nomatch write
  relationTarget := PEmpty.elim
  continuedTarget := by
    intro current write
    cases current with
    | ingress => exact nomatch write
    | ready result => exact .ready result
  redirectTarget := PEmpty.elim

abbrev JointV := jointVocabulary

def jointEventLaw : SourceNativeEventAlgebra N JointV where
  EventAt := fun _ support => PLift (support = jointSupport)
  compile := by
    intro current support event
    cases current with
    | ingress => exact .nativeWrite PUnit.unit
    | ready _ => exact .continuedTransport PUnit.unit
  AffectedInventoryAt := fun _ => Unit
  affectedInventoryPresentation := by
    intro current support event
    cases event.down
    exact Root.eventLaw.affectedInventoryPresentation (.exact jointSupport)
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.down.symm
  lineage_commutes := fun _ => rfl

def jointSource : SourceNativeSource N JointV where
  initial := .ingress
  law := jointEventLaw

def jointEmitted (current : JointCurrent) : jointSource.toRootSource.actual.OccurrenceAt current := ⟨jointSupport, ⟨rfl⟩⟩

theorem jointCompiled_next (current : JointCurrent) :
    (jointSource.toRootSource.actual.compile (jointEmitted current)).nextCurrent? = some (jointNext current) := by
  cases current <;> rfl

theorem jointReadiness_no_native_write (result : JointResult) :
    IsEmpty (JointV.NativeWriteAt (.ready result)) := ⟨fun write => nomatch write⟩

theorem jointNext_idempotent (current : JointCurrent) : jointNext (jointNext current) = jointNext current := rfl

end
end LAlanine40K2025.JointNext.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
