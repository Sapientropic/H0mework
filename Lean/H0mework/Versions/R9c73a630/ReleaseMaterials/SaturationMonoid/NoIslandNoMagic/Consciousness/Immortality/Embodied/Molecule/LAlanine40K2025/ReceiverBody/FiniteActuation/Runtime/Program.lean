import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime.Authority

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
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

structure FiniteActionReceiptAt
    (event : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit)
    (answer : ActuationResult) : Type 3 where
  sourceExact : event=parentEvent
  parentRow : parentGenerated.GeneratedEntryRowAt parentEntry
  actualAnswer : answer=currentResult firstSuccessor.targetCurrent
  inputSource : type_of% input_is_parent
  parentFaces : ∀ face, type_of% (parent_face_factorizes face)
  action : OriginalFiniteActuation
  generatedBody : ∀ i,
    nuclearPosition .leave duration i=(answer.frame.position i.1 i.2 : ℝ) ∧
    nuclearMomentum .leave duration i=(answer.frame.momentum i.1 i.2 : ℝ) ∧
    receiver .leave duration=answer.resource.momentum ∧
    gammaPath .leave duration=answer.realized ∧
    quantumPath .leave duration=answer.resource.quantum.joint
  resourceClock : answer.resource.quantum.localClock=22*Propagation.Producer.nativeClockStep
  bodyClock : answer.bodyClock=7*Propagation.Producer.nativeClockStep
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
      Receipt := FiniteActionReceiptAt parentEvent
      receipt :=
        { sourceExact := rfl
          parentRow := parentEntryRow
          actualAnswer := rfl
          inputSource := input_is_parent
          parentFaces := parent_face_factorizes
          action := originalFiniteActuation
          generatedBody := target_endpoints
          resourceClock := generated_clocks.1
          bodyClock := generated_clocks.2
          realization := target_retains_residual } }

def actionProgram : SourceNativeSequentialActualActionProgramAt Parent parentVisit parentEntry parentAuthority where
  targetAt := actionTargetAt

def generatedAction : SourceGeneratedSequentialActualActionAt actionProgram parentEvent :=
  actionProgram.generate parentEvent

theorem generated_action_answer : generatedAction.answer=sourceOutput := rfl

def generatedReceipt : FiniteActionReceiptAt parentEvent sourceOutput := generatedAction.receipt

theorem generated_action_next : generatedAction.target.targetAnswerAndNext.nextCurrent=
    ⟨BodyV,authoritativeRoot,generatedAction.target.targetVisit⟩ :=
  generatedAction.target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
