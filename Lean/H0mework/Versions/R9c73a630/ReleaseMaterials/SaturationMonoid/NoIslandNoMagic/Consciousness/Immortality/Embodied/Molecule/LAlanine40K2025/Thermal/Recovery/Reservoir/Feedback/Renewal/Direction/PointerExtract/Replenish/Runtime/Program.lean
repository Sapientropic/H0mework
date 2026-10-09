import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime.Authority

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

open Charging.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion

theorem parent_translation_entry :
    (chargingTranslation.oldOpenLedger reservoirSupport).forward parentEntry=recoveryEntry reservoirSupport := by
  rw [parent_entry_exact]
  rfl

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

structure ReplenishmentActionReceiptAt
    (event : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit)
    (answer : Material) : Type 3 where
  sourceExact : event=parentEvent
  parentRow : parentGenerated.GeneratedEntryRowAt parentEntry
  actualAnswer : answer=currentMaterial firstSuccessor.targetCurrent
  originCurrent : Replenish.material=Restore.Runtime.currentMaterial parentVisit.current
  parentFaces : ∀ face, type_of% (parent_face_factorizes face)
  sourceClosure : OriginalReplenishment
  actualJoint : answer.quantum.joint=Quantum.conjugation (feedbackPulse (nativeClockStep : ℝ)) Replenish.origin.joint
  actualReceiver : answer.momentum=Replenish.material.momentum
  actualGain : (69/100 : ℝ) < pcEnergyOf (bodyRead answer.quantum.joint)-pcEnergyOf (bodyRead Replenish.origin.joint)
  actualDebit : donorRemainingOf (suppliedBlock answer.quantum)+Registered.transfer=
    donorRemainingOf (suppliedBlock Replenish.origin)
  actualEnergy : (Live.freeEnergy answer.quantum-Live.freeEnergy Replenish.origin)+
    (Live.entropyProduction answer.quantum-Live.entropyProduction Replenish.origin)=responseWork Replenish.origin

def actionTargetAt
    (event : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit) :
    SourceNativeSequentialActualActionTargetAt Parent parentVisit event parentEntry parentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := RecoveryN
      translation := chargingTranslation
      TargetV := ReplenishV
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
      translatedSourceEntryRow := by rw [parent_translation_entry]; exact initialEntryRow
      firstSuccessor := firstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := Material
      answer := currentMaterial firstSuccessor.targetCurrent
      Receipt := ReplenishmentActionReceiptAt parentEvent
      receipt :=
        { sourceExact := rfl
          parentRow := parentEntryRow
          actualAnswer := rfl
          originCurrent := origin_is_parent
          parentFaces := parent_face_factorizes
          sourceClosure := originalReplenishment
          actualJoint := respondNext_joint Replenish.origin
          actualReceiver := next_receiver .ingress
          actualGain := first_pc_gain
          actualDebit := response_remaining_debit Replenish.origin
          actualEnergy := respondNext_netAccount Replenish.origin } }


def actionProgram : SourceNativeSequentialActualActionProgramAt Parent parentVisit parentEntry parentAuthority where
  targetAt := actionTargetAt

def generatedAction : SourceGeneratedSequentialActualActionAt actionProgram parentEvent :=
  actionProgram.generate parentEvent

theorem generated_action_answer : generatedAction.answer=suppliedMaterial := rfl

def generatedReceipt : ReplenishmentActionReceiptAt parentEvent suppliedMaterial := generatedAction.receipt

theorem generated_action_next : generatedAction.target.targetAnswerAndNext.nextCurrent=
    ⟨ReplenishV,authoritativeRoot,generatedAction.target.targetVisit⟩ :=
  generatedAction.target.targetAnswerAndNext_next_eq

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Replenish.Runtime
