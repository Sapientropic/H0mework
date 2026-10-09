import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Runtime.Authority

/-! # The exact nine-q occurrence generates the original weak pulse and its resource receipt -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Recovery.Runtime Reservoir.Runtime Charging.Runtime Feedback.Runtime
noncomputable section

def occurrencePresentation : ConstructivePresentation
    (Parent.toAuthoritativeRoot.toRoot.actual.OccurrenceAt parentVisit.current)
    (livingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      livingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => emitted .ingress
  backward := fun _ => parentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change PLift (support = reservoirSupport) at event
    cases event.down
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change PLift (support = reservoirSupport) at event
    cases event.down
    rfl

/-- The parent causal entry and its full resources certify this exact generated answer. -/
structure WeakActionReceiptAt
    (event : ExactTemporalCausalRootEventAt
      Parent.toAuthoritativeRoot.toLedgerRoot parentVisit)
    (answer : Live.State) : Type 3 where
  sourceExact : event = parentEvent
  parentRow : parentGenerated.GeneratedEntryRowAt parentEntry
  actualAnswer : answer = currentState firstSuccessor.targetCurrent
  originCurrent : origin = Renewal.Runtime.currentState parentVisit.current
  parentFaces : ∀ face, type_of% (parent_face_factorizes face)
  sourceClosure : WeakSupplyAndLoadCandidate
  donorDebit : Resource.donorRemainingOf (Resource.suppliedBlock answer) +
      transfer = Resource.donorRemainingOf (Resource.suppliedBlock origin)
  netAccount :
    (Live.freeEnergy answer - Live.freeEnergy origin) +
      (Live.entropyProduction answer - Live.entropyProduction origin) = pulseWork origin

def actionTargetAt
    (event : ExactTemporalCausalRootEventAt
      Parent.toAuthoritativeRoot.toLedgerRoot parentVisit) :
    SourceNativeSequentialActualActionTargetAt Parent parentVisit event
      parentEntry parentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := RecoveryN
      translation := chargingTranslation
      TargetV := WeakV
      targetRoot := livingRoot
      targetTheory := TheoryState.rootSemantic RecoveryN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := occurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := chargingTranslation.oldOpenLedger reservoirSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := chargingIngress_no_fresh_rows reservoirSupport
      translatedSourceEntryRow := by
        rw [parent_translation_entry]
        exact initialEntryRow
      firstSuccessor := firstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := Live.State
      answer := currentState firstSuccessor.targetCurrent
      Receipt := WeakActionReceiptAt parentEvent
      receipt :=
        { sourceExact := rfl
          parentRow := parentEntryRow
          actualAnswer := rfl
          originCurrent := origin_is_parent
          parentFaces := parent_face_factorizes
          sourceClosure := sourceGeneratedWeakSupplyAndLoad
          donorDebit := remaining_debit
          netAccount := Weak.next_net_account origin } }

def actionProgram : SourceNativeSequentialActualActionProgramAt Parent parentVisit
    parentEntry parentAuthority where
  targetAt := actionTargetAt

def generatedAction : SourceGeneratedSequentialActualActionAt actionProgram parentEvent :=
  actionProgram.generate parentEvent

theorem generated_action_answer : generatedAction.answer = target := rfl

def generatedReceipt : WeakActionReceiptAt parentEvent target := generatedAction.receipt

theorem generated_action_next : generatedAction.target.targetAnswerAndNext.nextCurrent =
    ⟨WeakV, authoritativeRoot, generatedAction.target.targetVisit⟩ :=
  generatedAction.target.targetAnswerAndNext_next_eq

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
