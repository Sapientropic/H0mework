import H0mework.Physics.SpinRuntime.Source

/-! A sequential actual action at the existing material visit 3. The initial
ledger is literally unchanged; the new physical source generates its first
write, configuration receipt and canonical next. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineGravityBianchi StageNineCClassicalWorldAcceptance

noncomputable section

def sourceEvent : ExactTemporalCausalRootEventAt
    materialLivingRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit :=
  materialLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit sourceVisit

private def identityRetract (A : Type) : ConstructiveRetract A A := ⟨id, id, fun _ => rfl⟩

private def translation : TypedSemanticWorldNetworkTranslationAt MaterialN MaterialN where
  support := identityRetract _
  anchor := identityRetract _
  incidence := identityRetract _
  lineage := identityRetract _
  responsibility := identityRetract _
  claim := identityRetract _
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ => identityRetract _
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ evidence => evidence
  oldDispositionSurvives := fun _ _ receipt => receipt

private def occurrencePresentation : ConstructivePresentation
    (materialLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt sourceVisit.current)
    (livingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      livingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => emitted .ingress
  backward := fun _ => sourceEvent.occurrence
  backward_forward := by
    rintro ⟨oldSupport, event⟩
    change MaterialEventAt sourceVisit.current oldSupport at event
    cases event.support_eq
    rfl
  forward_backward := by
    rintro ⟨targetSupport, event⟩
    change EventAt .ingress targetSupport at event
    cases event.support_eq
    rfl

structure FirstWriteReceiptAt
    (event : ExactTemporalCausalRootEventAt
      materialLivingRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit)
    (answer : StageNineHolonomicConfiguration) : Type 3 where
  sourceExact : event = sourceEvent
  configurationProjection : authoritativeRoot.projectionOutcomeAt (.inherited .configuration)
    firstSuccessor.targetCurrent = .inl ⟨PUnit.unit, answer⟩
  residualProjection : authoritativeRoot.projectionOutcomeAt (.inherited .residual)
    firstSuccessor.targetCurrent =
      .inl ⟨PUnit.unit, materialResidual (support firstSuccessor.targetCurrent)⟩
  actual_eq : answer = Material.SpinPair.actual
  smooth : answer.Smooth
  nondegenerate : answer.Nondegenerate
  lorentzAdmissible : GravityConnectionLorentzAdmissible answer
  scalarSourceContact : DynamicScalarSourceContactAtOrigin positiveSmoothUnifiedSource answer

private def targetAt (event : ExactTemporalCausalRootEventAt
    materialLivingRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit) :
    SourceNativeSequentialActualActionTargetAt materialLivingRoot sourceVisit event
      sourceEntry sourceAuthority := by
  rw [event.eq_generated]
  exact
    { TargetN := MaterialN
      translation := translation
      TargetV := V
      targetRoot := livingRoot
      targetTheory := TheoryState.rootSemantic MaterialN
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
      occurrencePresentation := occurrencePresentation
      occurrence_commutes := rfl
      initialSupport_heq := HEq.rfl
      initialOpenLedger := identityRetract _
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := fun entry => ⟨⟨entry, PLift.up rfl⟩⟩
      translatedSourceEntryRow := initialEntryRow
      firstSuccessor := firstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := StageNineHolonomicConfiguration
      answer := materialConfiguration (support firstSuccessor.targetCurrent)
      Receipt := FirstWriteReceiptAt sourceEvent
      receipt :=
        { sourceExact := rfl
          configurationProjection := rfl
          residualProjection := rfl
          actual_eq := rfl
          smooth := Material.SpinPair.actual_smooth
          nondegenerate := Material.SpinPair.actual_nondegenerate
          lorentzAdmissible := Material.SpinPair.actual_lorentzAdmissible
          scalarSourceContact := Material.SpinPair.actual_dynamicScalarSourceContact } }

def actionProgram : SourceNativeSequentialActualActionProgramAt materialLivingRoot
    sourceVisit sourceEntry sourceAuthority where
  targetAt := targetAt

def generatedAction : SourceGeneratedSequentialActualActionAt actionProgram sourceEvent :=
  actionProgram.generate sourceEvent

theorem generatedAction_answer : generatedAction.answer = Material.SpinPair.actual := rfl

def generatedAction_receipt : FirstWriteReceiptAt sourceEvent Material.SpinPair.actual :=
  generatedAction.receipt

theorem generatedAction_next : generatedAction.target.targetAnswerAndNext.nextCurrent =
    ⟨V, authoritativeRoot, generatedAction.target.targetVisit⟩ :=
  generatedAction.target.targetAnswerAndNext_next_eq

/-- The primitive slot is consumed only by this exact-visit action compiler. -/
def inquiryProgram : SourceNativeInquiryCompilationProgramAt materialLivingRoot sourceVisit
    materialU7 materialInquiryCalculus (TheoryState.rootSemantic MaterialN) PUnit.unit
    (ULift.up.{1, 0} (materialLivingRoot.emitted sourceVisit.current))
    sourceEntry sourceAuthority where
  compile := fun event => .actualAction (actionProgram.generate event)

def inquiryState : RootInquiryStateAt MaterialN MaterialV where
  root := materialLivingRoot
  visit := sourceVisit
  U7 := materialU7
  calculus := materialInquiryCalculus
  Query := PUnit
  entryAt := fun _ => sourceEntry
  authorityAt := fun _ => sourceAuthority
  compilationProgramAt := fun query => by cases query; exact inquiryProgram
  compilationFaceAt := fun query => by
    cases query
    exact ⟨.spinPairAction, PUnit.unit, rfl, HEq.rfl⟩
  u7RootDisposition_commutes := by
    intro query obstruction audit equality
    cases query
    cases equality

def inquiryPresentation : RootInquiryStatePresentation where
  N := MaterialN
  V := MaterialV
  state := .create inquiryState

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair
