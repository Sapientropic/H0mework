import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Runtime.Authority

/-! # The exact feedback occurrence generates its resource-paid renewal action -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Recovery.Runtime Reservoir.Runtime Charging.Runtime Feedback.Runtime
noncomputable section

def occurrencePresentation : ConstructivePresentation
    (feedbackLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt parentVisit.current)
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
structure RenewalActionReceiptAt
    (event : ExactTemporalCausalRootEventAt
      feedbackLivingRoot.toAuthoritativeRoot.toLedgerRoot parentVisit)
    (answer : Live.State) : Type 3 where
  sourceExact : event = parentEvent
  parentRow : parentGenerated.GeneratedEntryRowAt parentEntry
  actualAnswer : answer = currentState firstSuccessor.targetCurrent
  receivedCurrent : received = feedbackCurrentState parentVisit.current
  parentResources : type_of% parent_resources
  sourceClosure : RemainingRenewalClosure
  donorDebit : Resource.donorRemainingOf (Resource.suppliedBlock answer) +
      supplyTransfer received = Resource.donorRemainingOf (Resource.suppliedBlock received)
  netAccount :
    (Live.freeEnergy answer - Live.freeEnergy received) +
      (Live.entropyProduction answer - Live.entropyProduction received) = responseWork received

def actionTargetAt
    (event : ExactTemporalCausalRootEventAt
      feedbackLivingRoot.toAuthoritativeRoot.toLedgerRoot parentVisit) :
    SourceNativeSequentialActualActionTargetAt feedbackLivingRoot parentVisit event
      parentEntry parentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := RecoveryN
      translation := chargingTranslation
      TargetV := RenewalV
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
      Receipt := RenewalActionReceiptAt parentEvent
      receipt :=
        { sourceExact := rfl
          parentRow := parentEntryRow
          actualAnswer := rfl
          receivedCurrent := received_is_parent
          parentResources := parent_resources
          sourceClosure := sourceGeneratedRemainingRenewal
          donorDebit := response_remaining_debit received
          netAccount := respondNext_netAccount received } }

def actionProgram : SourceNativeSequentialActualActionProgramAt feedbackLivingRoot parentVisit
    parentEntry parentAuthority where
  targetAt := actionTargetAt

def generatedAction : SourceGeneratedSequentialActualActionAt actionProgram parentEvent :=
  actionProgram.generate parentEvent

theorem generated_action_answer : generatedAction.answer = supplied := rfl

def generatedReceipt : RenewalActionReceiptAt parentEvent supplied := generatedAction.receipt

theorem generated_action_next : generatedAction.target.targetAnswerAndNext.nextCurrent =
    ⟨RenewalV, authoritativeRoot, generatedAction.target.targetVisit⟩ :=
  generatedAction.target.targetAnswerAndNext_next_eq

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
