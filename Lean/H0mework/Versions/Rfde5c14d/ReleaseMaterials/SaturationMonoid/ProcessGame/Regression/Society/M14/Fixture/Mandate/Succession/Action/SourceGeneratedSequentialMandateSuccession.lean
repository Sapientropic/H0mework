import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Succession.Action.SourceGeneratedMandateSuccessionActionSource

/-!
# Source-generated sequential mandate succession

One fixed actual-action program consumes the post-exit target occurrence and
recomputes the one-slot successor representation.  The successor event,
controller lineage, office relation, phase, role, responsibility admission,
Payment, target ledger and next are dependent readouts; none enters the
public producer mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialMandateSuccession

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Renewal Election Relations Power
open M8ActualElectionMandateRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9SourceSuppliedMandateSuffix
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceMandateRenewal
open M14SourceMandateSuccession
open M14SourceGeneratedMandateExitTargetRoot
open M14SourceGeneratedSequentialMandateExit
open M14SourceGeneratedMandateExitTargetHistory
open M14SourceGeneratedPostExitTerminalContinuation
open M14SourceGeneratedMandateSuccessorTargetRoot
open M14SourceGeneratedMandateSuccessionActionSource

def mandateSuccessionOccurrencePresentationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ConstructivePresentation
      (mandateExitTargetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (mandateSuccessionActionSourceVisitAt initial depth).current)
      (mandateSuccessorTargetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        mandateSuccessorTargetInitialVisit.current) :=
  ConstructivePresentation.refl _

@[simp] theorem mandateSuccessionOccurrencePresentation_commutes
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateSuccessionActionSourceVisitAt initial depth)) :
    (mandateSuccessionOccurrencePresentationAt initial depth).forward
        exactSource.occurrence =
      mandateSuccessorTargetRoot.emitted
        mandateSuccessorTargetInitialVisit.current := by
  rw [exactSource.eq_generated]
  rfl

/-- Receipt of the fixed transition.  It witnesses both the retained terminal
archive in the source occurrence and the genuinely new admission in the
target occurrence. -/
structure ExactMandateSuccessionActionReceiptAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateSuccessionActionSourceVisitAt initial depth))
    (_answer : PUnit) : Type 3 where
  sourceExact : exactSource =
    mandateSuccessionActionExactSourceEventAt initial depth
  sourceIsExitMacroNext :
    (generatedMandateExitActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨M14SourceGeneratedMandateExitTargetRoot.V,
        mandateExitTargetRoot.toAuthoritativeRoot,
        mandateSuccessionActionSourceVisitAt initial depth⟩
  sourcePostExitOccurrence : HEq exactSource
    (sourceGeneratedPostExitTerminalContinuationAt initial depth
      ).rootOccurrence
  sourceTerminalExit : ∃ archive,
    (sourceGeneratedPostExitTerminalContinuationAt initial depth
      ).mandateFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateExitHistory.current).val]? =
      some (.terminal archive)
  sourceHasPayment : Nonempty PostExitSourceBackedPaymentAt
  sourceWholeLedgerExact :
    (sourceGeneratedPostExitTerminalContinuationAt initial depth
      ).wholeLedgerWriteBack =
      (mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (mandateExitTargetTemporalVisitAt 1)).wholeLedgerWriteBack
  targetFaceExact : installedMandateSuccessorLocalFace =
    sourceMandateSuccessorFace
  targetRetainsExitTrace : sourceMandateExitHistory.current ∈
    sourceMandateSuccessorHistory.occurrence.trace
  targetControllerFromFold :
    installedMandateSuccessorLocalFace.actor.1 =
      sourceMandateExitControllerMaximum + 1
  targetControllerFresh :
    installedMandateSuccessorLocalFace.actor.1 ≠
        sourceMandateHistory.current.controllerSeed ∧
      installedMandateSuccessorLocalFace.actor.1 ≠
        sourceMandateExitHistory.current.controllerSeed
  targetOfficePersists :
    (mandateOffice sourceMandateSuccessorHistory lineageCompiler).1 =
      (mandateOffice sourceMandateExitHistory lineageCompiler).1
  targetPhaseRenew :
    (officeControllerRelationCompiler sourceMandateSuccessorHistory
      lineageCompiler).phaseStep
        (generatedOfficeControllerRelation sourceMandateSuccessorHistory
          lineageCompiler) = MandatePhase.renew
  targetRoleHeld :
    (officeControllerRelationCompiler sourceMandateSuccessorHistory
      lineageCompiler).roleAt
        (generatedOfficeControllerRelation sourceMandateSuccessorHistory
          lineageCompiler) .target = MandateRole.held
  targetPowerRestored :
    (installedMandateSuccessorLocalFace.responsibilityConsumer.1.1
      ).freedomChange.kind = FreedomChangeKind.restored
  targetNewAdmission :
    sourceMandateSuccessorAdmissionEdge.lifecycleEvent.kind =
      LifecycleKind.admitted
  targetCannotReopenOldTerminal : ∀ archive :
      TerminalArchive (mandateVocabulary lineageCompiler),
    IsEmpty ((mandateProcess lineageCompiler).ReopenEvent archive)
  targetObligationLive :
    installedMandateSuccessorLocalFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateSuccessorHistory.current).val]? =
      some (.live (mandateObligation lineageCompiler
        sourceMandateSuccessorHistory.current))
  targetPayment : MandateSuccessorTargetSourceBackedPaymentAt
  targetOneMandateCoordinate :
    mandateProjectionFor sourceMandateSuccessorHistory ≠
      recognitionWitnessProjectionFor sourceMandateSuccessorHistory
  targetFirstWholeLedgerWriteExact :
    mandateSuccessorTargetInitialGenerated.wholeLedgerWriteBack =
      (mandateSuccessorTargetRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          mandateSuccessorTargetInitialVisit).wholeLedgerWriteBack

def exactMandateSuccessionActionReceiptAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateSuccessionActionSourceVisitAt initial depth))
    (answer : PUnit) :
    ExactMandateSuccessionActionReceiptAt initial depth exactSource answer := by
  rw [exactSource.eq_generated]
  exact
    { sourceExact := rfl
      sourceIsExitMacroNext :=
        mandateSuccessionActionSource_is_exitMacroNext initial depth
      sourcePostExitOccurrence :=
        mandateSuccessionActionSource_consumes_postExitOccurrence
          initial depth
      sourceTerminalExit :=
        mandateSuccessionActionSource_retains_terminalExit initial depth
      sourceHasPayment :=
        (mandateSuccessionActionSource_hasPaymentAndWholeWrite
          initial depth).1
      sourceWholeLedgerExact :=
        (mandateSuccessionActionSource_hasPaymentAndWholeWrite
          initial depth).2
      targetFaceExact := installedMandateSuccessor_face_exact
      targetRetainsExitTrace := installedMandateSuccessor_retains_exit_trace
      targetControllerFromFold := rfl
      targetControllerFresh := installedMandateSuccessor_controller_fresh
      targetOfficePersists :=
        sourceMandateSuccessor_office_and_relation_exact.2.1
      targetPhaseRenew := installedMandateSuccessor_phase_renew
      targetRoleHeld := installedMandateSuccessor_role_held
      targetPowerRestored := installedMandateSuccessor_power_restored
      targetNewAdmission := sourceMandateSuccessorAdmissionEdge_kind
      targetCannotReopenOldTerminal :=
        sourceMandateSuccessor_has_no_terminal_reopen
      targetObligationLive := installedMandateSuccessor_obligation_live
      targetPayment := mandateSuccessorTargetSourceBackedPaymentAt
      targetOneMandateCoordinate :=
        successor_inventory_has_one_named_mandate_coordinate.1
      targetFirstWholeLedgerWriteExact := rfl }

def mandateSuccessionActionTargetAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateSuccessionActionSourceVisitAt initial depth)) :
    SourceNativeSequentialActualActionTargetAt mandateExitTargetRoot
      (mandateSuccessionActionSourceVisitAt initial depth) exactSource
      (mandateSuccessionActionSourceEntryAt initial depth)
      (mandateSuccessionActionSourceAuthorityAt initial depth) := by
  rw [exactSource.eq_generated]
  exact
    { TargetN := M14SourceGeneratedMandateSuccessorTargetRoot.N
      translation := mandateExitIdentityTranslation
      TargetV := M14SourceGeneratedMandateSuccessorTargetRoot.V
      targetRoot := mandateSuccessorTargetRoot
      targetTheory := RootInquiryU8CompletionRegression.oldTheory
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic :=
        { compile := fun expression => nomatch expression
          commuting := fun expression => nomatch expression }
      occurrencePresentation :=
        mandateSuccessionOccurrencePresentationAt initial depth
      occurrence_commutes :=
        mandateSuccessionOccurrencePresentation_commutes initial depth
          (mandateSuccessionActionExactSourceEventAt initial depth)
      initialSupport_heq := HEq.rfl
      initialOpenLedger := mandateExitIdentityTranslation.oldOpenLedger true
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := fun targetEntry =>
        ⟨⟨targetEntry, PLift.up rfl⟩⟩
      translatedSourceEntryRow := mandateSuccessorTargetEntryRow
      firstSuccessor := mandateSuccessorTargetFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := PUnit
      answer := PUnit.unit
      Receipt := fun answer =>
        ExactMandateSuccessionActionReceiptAt initial depth
          (mandateSuccessionActionExactSourceEventAt initial depth) answer
      receipt := exactMandateSuccessionActionReceiptAt initial depth
        (mandateSuccessionActionExactSourceEventAt initial depth) PUnit.unit }

def mandateSuccessionActionProgramAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceNativeSequentialActualActionProgramAt mandateExitTargetRoot
      (mandateSuccessionActionSourceVisitAt initial depth)
      (mandateSuccessionActionSourceEntryAt initial depth)
      (mandateSuccessionActionSourceAuthorityAt initial depth) where
  targetAt := mandateSuccessionActionTargetAt initial depth

/-- Sole succession producer.  Its mouth is only the already registered
canonical source cycle and finite depth. -/
def generatedMandateSuccessionActionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceGeneratedSequentialActualActionAt
      (mandateSuccessionActionProgramAt initial depth)
      (mandateSuccessionActionExactSourceEventAt initial depth) :=
  (mandateSuccessionActionProgramAt initial depth).generate
    (mandateSuccessionActionExactSourceEventAt initial depth)

def mandateSuccessionInquiryEventAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  ULift.up.{1, 0}
    (mandateExitTargetRoot.emitted
      (mandateSuccessionActionSourceVisitAt initial depth).current)

def mandateSuccessionActualActionCompilationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateSuccessionActionSourceVisitAt initial depth)) :
    SourceNativeInquiryCompilationAt mandateExitTargetRoot
      (mandateSuccessionActionSourceVisitAt initial depth)
      M9ProofCarryingRenewalU8Failure.U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory ()
      (mandateSuccessionInquiryEventAt initial depth)
      (mandateSuccessionActionSourceEntryAt initial depth)
      (mandateSuccessionActionSourceAuthorityAt initial depth) :=
  .actualAction ((mandateSuccessionActionProgramAt initial depth).generate
    exactSource)

@[simp] theorem generatedMandateSuccessionAction_targetRoot_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedMandateSuccessionActionAt initial depth).target.targetRoot =
      mandateSuccessorTargetRoot :=
  rfl

theorem generatedMandateSuccessionAction_macroNext_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedMandateSuccessionActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedMandateSuccessionActionAt initial depth).target.TargetV,
        (generatedMandateSuccessionActionAt initial depth
          ).target.targetRoot.toAuthoritativeRoot,
        (generatedMandateSuccessionActionAt initial depth).target.targetVisit⟩ :=
  (generatedMandateSuccessionActionAt initial depth).target
    |>.targetAnswerAndNext_next_eq

/-- Heterogeneous authority occurrence.  The post-exit target visit has a
shared normal form, while the actual action identity retains the canonical
source depth in its dependent program/receipt index. -/
abbrev AnyMandateSuccessionActionOccurrenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :=
  Sigma fun depth : Nat =>
    SourceGeneratedSequentialActualActionAt
      (mandateSuccessionActionProgramAt initial depth)
      (mandateSuccessionActionExactSourceEventAt initial depth)

def mandateSuccessionActionOccurrenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    AnyMandateSuccessionActionOccurrenceAt initial :=
  ⟨depth, generatedMandateSuccessionActionAt initial depth⟩

theorem mandateSuccessionActionOccurrenceAt_injective
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    Function.Injective (mandateSuccessionActionOccurrenceAt initial) := by
  intro left right equality
  exact congrArg Sigma.fst equality

theorem no_single_mandateSuccessionAction_occurrence_carries_all_depths
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    ¬ ∃ occurrence : AnyMandateSuccessionActionOccurrenceAt initial,
      ∀ depth : Nat,
        mandateSuccessionActionOccurrenceAt initial depth = occurrence := by
  rintro ⟨occurrence, allDepths⟩
  have equality := (allDepths 0).trans (allDepths 1).symm
  have depthEquality :=
    mandateSuccessionActionOccurrenceAt_injective initial equality
  omega

end
end M14SourceGeneratedSequentialMandateSuccession
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialMandateSuccession.generatedMandateSuccessionActionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialMandateSuccession.ExactMandateSuccessionActionReceiptAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialMandateSuccession.generatedMandateSuccessionAction_macroNext_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialMandateSuccession.no_single_mandateSuccessionAction_occurrence_carries_all_depths
