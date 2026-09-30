import H0mework.Chemistry.LAlanineWork.FieldActionIngress

/-! # One exact old occurrence generates the field-controlled descendant law -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Drive
open scoped ComplexOrder

noncomputable section

structure FieldActionReceiptAt
    (event : ExactTemporalCausalRootEventAt Installation.root.toAuthoritativeRoot.toLedgerRoot fieldParentVisit)
    (answer : FieldState) : Type 3 where
  sourceExact : event = fieldParentEvent
  actualAnswer : answer = fieldCurrentState fieldFirstSuccessor.targetCurrent
  receivedPreviousTarget : type_of% fieldStateNext_received
  workCapacity : fieldCapacity answer.pair answer.positive.isHermitian -
    fieldCapacity fieldInitialState.pair fieldInitialState.positive.isHermitian = answer.netWork

def fieldActionTargetAt
    (event : ExactTemporalCausalRootEventAt Installation.root.toAuthoritativeRoot.toLedgerRoot fieldParentVisit) :
    SourceNativeSequentialActualActionTargetAt Installation.root fieldParentVisit event
      fieldParentEntry fieldParentAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := FieldN
      translation := fieldTranslation
      TargetV := FieldV
      targetRoot := fieldLivingRoot
      targetTheory := TheoryState.rootSemantic FieldN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := { compile := id, commuting := fun _ => rfl }
      occurrencePresentation := fieldOccurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := fieldTranslation.oldOpenLedger (.nativeElectronicCurrent fieldSourceTime)
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := fieldIngress_no_fresh_rows _
      translatedSourceEntryRow := by
        rw [fieldTranslatedEntry_exact]
        exact fieldInitialEntryRow
      firstSuccessor := fieldFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := FieldState
      answer := fieldCurrentState fieldFirstSuccessor.targetCurrent
      Receipt := FieldActionReceiptAt fieldParentEvent
      receipt :=
        { sourceExact := rfl
          actualAnswer := rfl
          receivedPreviousTarget := fieldStateNext_received
          workCapacity := by
            change fieldCapacity (fieldStateNext fieldInitialState).pair _ -
              fieldCapacity fieldInitialState.pair _ = (fieldStateNext fieldInitialState).netWork
            have balance := fieldStateNext_capacity fieldInitialState
            simpa only [show fieldInitialState.netWork = 0 from rfl, sub_zero] using balance } }

def fieldActionProgram : SourceNativeSequentialActualActionProgramAt Installation.root fieldParentVisit
    fieldParentEntry fieldParentAuthority where
  targetAt := fieldActionTargetAt

def generatedFieldAction : SourceGeneratedSequentialActualActionAt fieldActionProgram fieldParentEvent :=
  fieldActionProgram.generate fieldParentEvent

theorem generatedFieldAction_answer : generatedFieldAction.answer = fieldStateNext fieldInitialState := rfl

def generatedFieldAction_receipt : FieldActionReceiptAt fieldParentEvent (fieldStateNext fieldInitialState) :=
  generatedFieldAction.receipt

theorem generatedFieldAction_next : generatedFieldAction.target.targetAnswerAndNext.nextCurrent =
    ⟨FieldV, fieldAuthoritativeRoot, generatedFieldAction.target.targetVisit⟩ :=
  generatedFieldAction.target.targetAnswerAndNext_next_eq

end

end LAlanine40K2025.Thermal.Work.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
