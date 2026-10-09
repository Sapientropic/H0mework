import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime.Authority

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
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
  forward := fun _ => emitted initialState
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

structure BootstrapReceiptAt
    (event : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit)
    (answer : Material) : Type 3 where
  sourceExact : event=parentEvent
  parentRow : parentGenerated.GeneratedEntryRowAt parentEntry
  actualAnswer : answer=firstSuccessor.targetCurrent.1
  inputSource : type_of% input_is_parent
  parentFaces : ∀ face, type_of% (parent_face_factorizes face)
  action : ActualStep initialState
  target : answer=nextMaterial initialMaterial
  newReserve : answer.reserve=initialMaterial.reserve/2
  newClocks : answer.body.resource.quantum.localClock=initialMaterial.body.resource.quantum.localClock+3*Propagation.Producer.nativeClockStep ∧
    answer.body.bodyClock=initialMaterial.body.bodyClock+3*Propagation.Producer.nativeClockStep

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
      Answer := Material
      answer := firstSuccessor.targetCurrent.1
      Receipt := BootstrapReceiptAt parentEvent
      receipt :=
        { sourceExact := rfl
          parentRow := parentEntryRow
          actualAnswer := rfl
          inputSource := input_is_parent
          parentFaces := parent_face_factorizes
          action := actualStep initialState
          target := rfl
          newReserve := rfl
          newClocks := next_clocks initialMaterial } }

def actionProgram : SourceNativeSequentialActualActionProgramAt Parent parentVisit parentEntry parentAuthority where
  targetAt := actionTargetAt

def generatedAction : SourceGeneratedSequentialActualActionAt actionProgram parentEvent :=
  actionProgram.generate parentEvent

theorem generated_action_answer : generatedAction.answer=nextMaterial initialMaterial := rfl

def generatedReceipt : BootstrapReceiptAt parentEvent (nextMaterial initialMaterial) := generatedAction.receipt

theorem generated_action_next : generatedAction.target.targetAnswerAndNext.nextCurrent=
    ⟨BodyV,authoritativeRoot,generatedAction.target.targetVisit⟩ :=
  generatedAction.target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
