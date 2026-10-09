import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime.Authority

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open Thermal.Recovery.Charging.Runtime
noncomputable section

theorem translated_entry_exact :
    (chargingTranslation.oldOpenLedger reservoirSupport).forward parentEntry=initialEntry := by
  rw [parent_entry_exact]
  rfl

def occurrencePresentation : ConstructivePresentation
    (Parent.toAuthoritativeRoot.toRoot.actual.OccurrenceAt parentVisit.current)
    (livingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt livingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => emitted .ingress
  backward := fun _ => parentEvent.occurrence
  backward_forward := by
    rintro ⟨support,event⟩
    change PLift (support=reservoirSupport) at event
    cases event.down
    rfl
  forward_backward := by
    rintro ⟨support,event⟩
    change PLift (support=reservoirSupport) at event
    cases event.down
    rfl

structure JointActionReceiptAt
    (event : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit)
    (answer : ActuationResult) : Type 3 where
  sourceExact : event=parentEvent
  parentRow : parentGenerated.GeneratedEntryRowAt parentEntry
  actualAnswer : answer=currentResult firstSuccessor.targetCurrent
  resourceSource : type_of% actuation_input_is_parent
  bodySourceReceipt : type_of% bodyReceipt
  parentFaces : ∀ face, type_of% (parent_face_factorizes face)
  bodyFaces : ∀ face, type_of% (body_face_factorizes face)
  action : OriginalJointActuation
  generatedBody : ∀ i, (answer.frame.position i.1 i.2 : ℝ)=positionPath duration i ∧
    (answer.frame.momentum i.1 i.2 : ℝ)=momentumPath duration i ∧
    answer.resource.quantum.joint=resourcePath duration
  resourceClock : answer.resource.quantum.localClock=19*Propagation.Producer.nativeClockStep
  bodyClock : answer.bodyClock=4*Propagation.Producer.nativeClockStep
  realization : answer.realized=answer.held+answer.inheritedResidual+answer.newNumericalResidual

def actionTargetAt
    (event : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit) :
    SourceNativeSequentialActualActionTargetAt Parent parentVisit event parentEntry parentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := RecoveryN
      translation := chargingTranslation
      TargetV := BodyV
      targetRoot := livingRoot
      targetTheory := TheoryState.rootSemantic RecoveryN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id,commuting := fun _ => rfl }
      occurrencePresentation := occurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := chargingTranslation.oldOpenLedger reservoirSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := chargingIngress_no_fresh_rows reservoirSupport
      translatedSourceEntryRow := by rw [translated_entry_exact]; exact initialEntryRow
      firstSuccessor := firstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := ActuationResult
      answer := currentResult firstSuccessor.targetCurrent
      Receipt := JointActionReceiptAt parentEvent
      receipt :=
        { sourceExact := rfl
          parentRow := parentEntryRow
          actualAnswer := rfl
          resourceSource := actuation_input_is_parent
          bodySourceReceipt := bodyReceipt
          parentFaces := parent_face_factorizes
          bodyFaces := body_face_factorizes
          action := originalJointActuation
          generatedBody := source_output_generated
          resourceClock := source_output_resource_clock
          bodyClock := source_output_body_clock
          realization := source_output_realization } }

def actionProgram : SourceNativeSequentialActualActionProgramAt Parent parentVisit parentEntry parentAuthority where
  targetAt := actionTargetAt

def generatedAction : SourceGeneratedSequentialActualActionAt actionProgram parentEvent :=
  actionProgram.generate parentEvent

theorem generated_action_answer : generatedAction.answer=sourceOutput := rfl

def generatedReceipt : JointActionReceiptAt parentEvent sourceOutput := generatedAction.receipt

theorem generated_action_next : generatedAction.target.targetAnswerAndNext.nextCurrent=
    ⟨BodyV,authoritativeRoot,generatedAction.target.targetVisit⟩ :=
  generatedAction.target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
