import H0mework.Chemistry.LAlanineReentry.RuntimeRuntimeAuthority

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open LAlanine40K2025.Root JointNext.Runtime Inertia.Runtime Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def reentryOccurrencePresentation : ConstructivePresentation
    (jointLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt reentryParentVisit.current)
    (reentryLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt reentryLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => reentryEmitted .ingress
  backward := fun _ => reentryParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change PLift (support = jointSupport) at event
    cases event.down
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change PLift (support = reentrySupport) at event
    cases event.down
    rfl

theorem reentryTranslatedEntry_exact :
    (inertiaTranslation.oldOpenLedger reentrySupport).forward reentryParentEntry = reentryInitialEntry := by
  rw [reentryParentEntry_exact]
  rfl

structure ReentryActionReceiptAt
    (event : ExactTemporalCausalRootEventAt jointLivingRoot.toAuthoritativeRoot.toLedgerRoot reentryParentVisit)
    (answer : ReentryResult) : Type 3 where
  sourceExact : event = reentryParentEvent
  actualAnswer : answer = reentrySourceResult
  sourceReentry : Producer.reentryClosure
  parentFirstJoint : JointActionReceiptAt jointParentEvent reentryParentResult
  receivedInstalledFaces : type_of% reentryParent_installed
  receivedHistoricalFaces : type_of% reentryParent_historicalFaces
  receivedFirstJointTrace : type_of% reentryParent_firstJoint_trace
  retainedHistory : type_of% reentrySourceHistory_actual
  generatedNuclear : answer.nuclear = Source.stepReadout.nuclear
  sameCurrent : answer.nuclear.current = reentryParentFrame
  exactHeld : answer.held = Producer.exactTarget
  numericalRealization : answer.realized = Source.targetRealized
  inheritedTotalNorm : ‖answer.inheritedResidual‖ = ‖reentryParentResidual‖
  realizationReconstruction : answer.realized = answer.held + answer.inheritedResidual + answer.newNumericalResidual
  realizationError : ‖answer.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9
  targetPhysicalClock : answer.clock = 3 * Propagation.Producer.nativeClockStep
  oneElapsedClock : answer.clock - reentryParentTime = Continuation.duration

def reentryActionTargetAt
    (event : ExactTemporalCausalRootEventAt jointLivingRoot.toAuthoritativeRoot.toLedgerRoot reentryParentVisit) :
    SourceNativeSequentialActualActionTargetAt jointLivingRoot reentryParentVisit event reentryParentEntry reentryParentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := N
      translation := inertiaTranslation
      TargetV := ReentryV
      targetRoot := reentryLivingRoot
      targetTheory := TheoryState.rootSemantic N
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := reentryOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := inertiaTranslation.oldOpenLedger reentrySupport
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := inertiaIngress_no_fresh _
      translatedSourceEntryRow := by rw [reentryTranslatedEntry_exact]; exact reentryInitialEntryRow
      firstSuccessor := reentryFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := ReentryResult
      answer := reentryResponse reentryFirstSuccessor.targetCurrent
      Receipt := ReentryActionReceiptAt reentryParentEvent
      receipt :=
        { sourceExact := rfl
          actualAnswer := rfl
          sourceReentry := Producer.sourceGeneratedReentry
          parentFirstJoint := reentryParentFirstJointReceipt
          receivedInstalledFaces := reentryParent_installed
          receivedHistoricalFaces := reentryParent_historicalFaces
          receivedFirstJointTrace := reentryParent_firstJoint_trace
          retainedHistory := reentrySourceHistory_actual
          generatedNuclear := rfl
          sameCurrent := rfl
          exactHeld := rfl
          numericalRealization := rfl
          inheritedTotalNorm := Producer.inherited_error_exact
          realizationReconstruction := Producer.total_error_reconstruction.2
          realizationError := Producer.total_realization_error_bound
          targetPhysicalClock := Continuation.targetClock_exact
          oneElapsedClock := by change reentryParentTime + Continuation.duration - reentryParentTime = _; ring } }

def reentryActionProgram : SourceNativeSequentialActualActionProgramAt jointLivingRoot reentryParentVisit
    reentryParentEntry reentryParentAuthority where
  targetAt := reentryActionTargetAt

def generatedReentryAction : SourceGeneratedSequentialActualActionAt reentryActionProgram reentryParentEvent :=
  reentryActionProgram.generate reentryParentEvent

theorem generatedReentryAction_answer : generatedReentryAction.answer = reentrySourceResult := rfl
def generatedReentryAction_receipt : ReentryActionReceiptAt reentryParentEvent reentrySourceResult := generatedReentryAction.receipt

theorem generatedReentryAction_next : generatedReentryAction.target.targetAnswerAndNext.nextCurrent =
    ⟨ReentryV, reentryAuthoritativeRoot, generatedReentryAction.target.targetVisit⟩ :=
  generatedReentryAction.target.targetAnswerAndNext_next_eq

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
