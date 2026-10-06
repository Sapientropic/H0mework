import H0mework.Versions.AB.Chemistry.LAlanineJointNext.RuntimeRuntimeAuthority

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open LAlanine40K2025.Root HeldForce.Runtime Inertia.Runtime Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def jointOccurrencePresentation : ConstructivePresentation
    (heldForceLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt jointParentVisit.current)
    (jointLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt jointLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => jointEmitted .ingress
  backward := fun _ => jointParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change PLift (support = heldForceSupport) at event
    cases event.down
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change PLift (support = jointSupport) at event
    cases event.down
    rfl

theorem jointTranslatedEntry_exact :
    (inertiaTranslation.oldOpenLedger jointSupport).forward jointParentEntry = jointInitialEntry := by
  rw [jointParentEntry_exact]
  rfl

structure JointActionReceiptAt
    (event : ExactTemporalCausalRootEventAt heldForceLivingRoot.toAuthoritativeRoot.toLedgerRoot jointParentVisit)
    (answer : JointResult) : Type 3 where
  sourceExact : event = jointParentEvent
  actualAnswer : answer = jointSourceResult
  sourceJointStep : Producer.jointClosure
  parentFirstForce : HeldForceActionReceiptAt heldForceParentEvent jointParentResult
  receivedInstalledFaces : type_of% jointParent_installedFaces
  receivedFirstForceTrace : type_of% jointParent_firstForce_trace
  generatedNuclear : answer.nuclear = Source.stepReadout.nuclear
  sameCurrent : answer.nuclear.current = jointParentFrame
  exactHeld : answer.held = Producer.exactTarget
  numericalRealization : answer.realized = Source.targetRealized
  realizationReconstruction : answer.realized = answer.held + answer.inheritedResidual + answer.newNumericalResidual
  realizationError : ‖answer.totalRealizationResidual‖ < (1 : ℝ) / 10 ^ 8
  targetPhysicalClock : answer.clock = 2 * Propagation.Producer.nativeClockStep
  oneElapsedClock : answer.clock - jointParentTime = Interface.duration

def jointActionTargetAt
    (event : ExactTemporalCausalRootEventAt heldForceLivingRoot.toAuthoritativeRoot.toLedgerRoot jointParentVisit) :
    SourceNativeSequentialActualActionTargetAt heldForceLivingRoot jointParentVisit event jointParentEntry jointParentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := N
      translation := inertiaTranslation
      TargetV := JointV
      targetRoot := jointLivingRoot
      targetTheory := TheoryState.rootSemantic N
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := jointOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := inertiaTranslation.oldOpenLedger jointSupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := inertiaIngress_no_fresh _
      translatedSourceEntryRow := by rw [jointTranslatedEntry_exact]; exact jointInitialEntryRow
      firstSuccessor := jointFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := JointResult
      answer := jointResponse jointFirstSuccessor.targetCurrent
      Receipt := JointActionReceiptAt jointParentEvent
      receipt :=
        { sourceExact := rfl
          actualAnswer := rfl
          sourceJointStep := Producer.sourceGeneratedJointStep
          parentFirstForce := jointParentFirstForceReceipt
          receivedInstalledFaces := jointParent_installedFaces
          receivedFirstForceTrace := jointParent_firstForce_trace
          generatedNuclear := rfl
          sameCurrent := rfl
          exactHeld := rfl
          numericalRealization := rfl
          realizationReconstruction := Producer.total_error_reconstruction.2
          realizationError := Producer.total_realization_error_bound
          targetPhysicalClock := Interface.targetClock_exact
          oneElapsedClock := Interface.one_elapsed_clock.1 } }

def jointActionProgram : SourceNativeSequentialActualActionProgramAt heldForceLivingRoot jointParentVisit
    jointParentEntry jointParentAuthority where
  targetAt := jointActionTargetAt

def generatedJointAction : SourceGeneratedSequentialActualActionAt jointActionProgram jointParentEvent :=
  jointActionProgram.generate jointParentEvent

theorem generatedJointAction_answer : generatedJointAction.answer = jointSourceResult := rfl
def generatedJointAction_receipt : JointActionReceiptAt jointParentEvent jointSourceResult := generatedJointAction.receipt

theorem generatedJointAction_next : generatedJointAction.target.targetAnswerAndNext.nextCurrent =
    ⟨JointV, jointAuthoritativeRoot, generatedJointAction.target.targetVisit⟩ :=
  generatedJointAction.target.targetAnswerAndNext_next_eq

end
end LAlanine40K2025.JointNext.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
