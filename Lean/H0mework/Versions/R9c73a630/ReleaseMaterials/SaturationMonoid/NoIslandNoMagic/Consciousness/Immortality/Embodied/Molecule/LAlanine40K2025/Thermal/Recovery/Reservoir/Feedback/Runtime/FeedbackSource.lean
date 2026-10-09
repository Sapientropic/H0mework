import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedFeedbackCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Runtime.FeedbackParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer
noncomputable section

inductive FeedbackCurrent
  | ingress
  | running (state : Live.State)

def feedbackCurrentState : FeedbackCurrent → Live.State
  | .ingress => receivedState
  | .running state => state

def feedbackNext (current : FeedbackCurrent) : FeedbackCurrent :=
  .running (match current with
    | .ingress => firstState
    | .running state => Live.loadNext state)

def feedbackAction : FeedbackCurrent → Matrix.unitaryGroup PointerIndex ℂ
  | .ingress => feedbackPulse (nativeClockStep : ℝ)
  | .running _ => Pointer.loadPulse (nativeClockStep : ℝ)

theorem feedbackNext_joint (current : FeedbackCurrent) :
    (feedbackCurrentState (feedbackNext current)).joint =
      Quantum.conjugation (feedbackAction current) (feedbackCurrentState current).joint := by
  cases current with
  | ingress => exact respondNext_joint receivedState
  | running state => exact Live.loadNext_joint state

theorem feedbackNext_clock (current : FeedbackCurrent) :
    (feedbackCurrentState (feedbackNext current)).localClock =
      (feedbackCurrentState current).localClock + nativeClockStep := by
  cases current <;> rfl

def feedbackVocabulary : ConstructiveRoot.Vocabulary where
  Current := FeedbackCurrent
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
  nativeTarget := fun {current} _ => feedbackNext current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev FeedbackV := feedbackVocabulary

def feedbackEventLaw : SourceNativeEventAlgebra RecoveryN FeedbackV where
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

def feedbackSource : SourceNativeSource RecoveryN FeedbackV where
  initial := .ingress
  law := feedbackEventLaw

def feedbackEmitted (current : FeedbackCurrent) : feedbackSource.toRootSource.actual.OccurrenceAt current :=
  ⟨reservoirSupport, ⟨rfl⟩⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
