import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Exit.Action.SourceGeneratedMandateExitActionSource

/-!
# Source-generated sequential actual mandate exit

One fixed program consumes the exact generated-next occurrence of the
installed standing mandate and recomputes the one-slot exit target root.  The
execution seal contains no target, root, ledger, receipt or next; those are
dependent readouts of the fixed program.

This is the dedicated sequential-actual-action runtime.  It does not pretend
that M9's inherited U8 inquiry coordinate has an `.answered` audit, and it
does not route the action through search authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialMandateExit

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Renewal Election Relations Power
open M8ActualElectionMandateRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M14SourceMandateRenewal
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceInstalledMandateFiniteConstitutionIncidence
open M14SourceGeneratedMandateExitTargetRoot
open M14SourceGeneratedMandateExitActionSource

def mandateExitIdentityTranslation :
    TypedSemanticWorldNetworkTranslationAt
      M9ProofCarryingRenewalInquiryRoot.N
      M9ProofCarryingRenewalInquiryRoot.N where
  support :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  incidence :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  lineage :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  responsibility :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  claim :=
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ =>
    { forward := id
      backward := id
      backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ proof => proof
  oldDispositionSurvives := fun _ _ proof => proof

def mandateExitOccurrencePresentationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ConstructivePresentation
      (jointRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (mandateExitActionSourceVisitAt initial depth).current)
      (mandateExitTargetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        mandateExitTargetVisit.current) :=
  ConstructivePresentation.refl _

@[simp] theorem mandateExitOccurrencePresentation_commutes
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateExitActionSourceVisitAt initial depth)) :
    (mandateExitOccurrencePresentationAt initial depth).forward
        exactSource.occurrence =
      mandateExitTargetRoot.emitted mandateExitTargetVisit.current := by
  rw [exactSource.eq_generated]
  rfl

/-- Nonempty action receipt.  It records the source-generated transition and
the already installed target authorities, not a caller target verdict. -/
structure ExactMandateExitActionReceiptAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateExitActionSourceVisitAt initial depth))
    (_answer : PUnit) : Type 3 where
  sourceExact : exactSource = mandateExitActionExactSourceEventAt initial depth
  sourceGeneratedByStandingNext :
    (sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
      ).mandate.mandate.generatedNext =
      ⟨M9ProofCarryingRenewalInquiryRoot.V,
        jointRoot.toAuthoritativeRoot,
        mandateExitActionSourceVisitAt initial depth⟩
  sourceIsNextCycleOccurrence :
    HEq exactSource
      (jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (M14UBIPeriodicRootHistory.temporalVisitAt
          (mandateConstitutionDepthAt initial (depth + 1))))
  priorStandingTraceRetained :
    sourceMandateHistory.current ∈ sourceMandateExitHistory.occurrence.trace
  targetFaceExact : installedMandateExitLocalFace = sourceMandateExitFace
  targetPowerLost :
    installedMandateExitLocalFace.responsibilityConsumer.1.1.freedomChange.kind =
      FreedomChangeKind.lost
  targetPhaseExit :
    (officeControllerRelationCompiler sourceMandateExitHistory lineageCompiler
      ).phaseStep
        (generatedOfficeControllerRelation sourceMandateExitHistory
          lineageCompiler) = MandatePhase.exit
  targetRoleExited :
    (officeControllerRelationCompiler sourceMandateExitHistory lineageCompiler
      ).roleAt
        (generatedOfficeControllerRelation sourceMandateExitHistory
          lineageCompiler) .target = MandateRole.exited
  targetDispositionTerminal :
    ∃ archive,
      installedMandateExitLocalFace.exactDisposition.1.target.slots[
          (mandateSlot lineageCompiler
            sourceMandateExitHistory.current).val]? =
        some (.terminal archive)
  targetUBIRestrictionExact :
    installedMandateExitTargetUBI.payload.consumer =
      M14UBIProofCarryingRootRestriction.sourceGeneratedUBIRootRestriction
  targetInventoryOneMandate :
    M9SourceSuppliedMandateSuffix.mandateProjectionFor
        sourceMandateExitHistory ≠
      M9SourceSuppliedMandateSuffix.recognitionWitnessProjectionFor
        sourceMandateExitHistory
  targetFirstWholeLedgerWriteExact :
    mandateExitTargetInitialGenerated.wholeLedgerWriteBack =
      (mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          mandateExitTargetVisit).wholeLedgerWriteBack

def exactMandateExitActionReceiptAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateExitActionSourceVisitAt initial depth))
    (answer : PUnit) :
    ExactMandateExitActionReceiptAt initial depth exactSource answer := by
  rw [exactSource.eq_generated]
  exact
    { sourceExact := rfl
      sourceGeneratedByStandingNext :=
        standingMandate_generatedNext_eq_actionSource initial depth
      sourceIsNextCycleOccurrence :=
        actionSourceOccurrence_is_nextCycleMandateOccurrence initial depth
      priorStandingTraceRetained :=
        installedMandateExit_retains_prior_standing_trace
      targetFaceExact := installedMandateExit_face_exact
      targetPowerLost := installedMandateExit_power_lost
      targetPhaseExit := installedMandateExit_phase_exit
      targetRoleExited := installedMandateExit_role_exited
      targetDispositionTerminal := installedMandateExit_disposition_terminal
      targetUBIRestrictionExact := installedMandateExitTargetUBI_consumer_exact
      targetInventoryOneMandate :=
        target_inventory_has_one_named_mandate_coordinate.1
      targetFirstWholeLedgerWriteExact := rfl }

def mandateExitActionTargetAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateExitActionSourceVisitAt initial depth)) :
    SourceNativeSequentialActualActionTargetAt jointRoot
      (mandateExitActionSourceVisitAt initial depth) exactSource
      (mandateExitActionSourceEntryAt initial depth)
      (mandateExitActionSourceAuthorityAt initial depth) := by
  rw [exactSource.eq_generated]
  exact
    { TargetN := M9ProofCarryingRenewalInquiryRoot.N
      translation := mandateExitIdentityTranslation
      TargetV := M9ProofCarryingRenewalInquiryRoot.V
      targetRoot := mandateExitTargetRoot
      targetTheory := RootInquiryU8CompletionRegression.oldTheory
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic :=
        { compile := fun expression => nomatch expression
          commuting := fun expression => nomatch expression }
      occurrencePresentation :=
        mandateExitOccurrencePresentationAt initial depth
      occurrence_commutes :=
        mandateExitOccurrencePresentation_commutes initial depth
          (mandateExitActionExactSourceEventAt initial depth)
      initialSupport_heq := HEq.rfl
      initialOpenLedger := mandateExitIdentityTranslation.oldOpenLedger true
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh := fun targetEntry =>
        ⟨⟨targetEntry, PLift.up rfl⟩⟩
      translatedSourceEntryRow := mandateExitTargetEntryRow
      firstSuccessor := mandateExitTargetFirstSuccessor
      canonical_targetNextVisit_eq := rfl
      Answer := PUnit
      answer := PUnit.unit
      Receipt := fun answer =>
        ExactMandateExitActionReceiptAt initial depth
          (mandateExitActionExactSourceEventAt initial depth) answer
      receipt := exactMandateExitActionReceiptAt initial depth
        (mandateExitActionExactSourceEventAt initial depth) PUnit.unit }

def mandateExitActionProgramAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceNativeSequentialActualActionProgramAt jointRoot
      (mandateExitActionSourceVisitAt initial depth)
      (mandateExitActionSourceEntryAt initial depth)
      (mandateExitActionSourceAuthorityAt initial depth) where
  targetAt := mandateExitActionTargetAt initial depth

/-- Sole actual-action producer; the mouth is only the canonical cycle and
depth. -/
def generatedMandateExitActionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceGeneratedSequentialActualActionAt
      (mandateExitActionProgramAt initial depth)
      (mandateExitActionExactSourceEventAt initial depth) :=
  (mandateExitActionProgramAt initial depth).generate
    (mandateExitActionExactSourceEventAt initial depth)

def mandateExitInquiryEventAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  ULift.up.{1, 0}
    (jointRoot.emitted (mandateExitActionSourceVisitAt initial depth).current)

/-- Structural inquiry-compilation readout of the dedicated action.  This is
not installed in M9's incompatible U8 inquiry coordinate. -/
def mandateExitActualActionCompilationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (exactSource : ExactTemporalCausalRootEventAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot
        (mandateExitActionSourceVisitAt initial depth)) :
    SourceNativeInquiryCompilationAt jointRoot
      (mandateExitActionSourceVisitAt initial depth)
      M9ProofCarryingRenewalU8Failure.U7
      RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory ()
      (mandateExitInquiryEventAt initial depth)
      (mandateExitActionSourceEntryAt initial depth)
      (mandateExitActionSourceAuthorityAt initial depth) :=
  .actualAction ((mandateExitActionProgramAt initial depth).generate exactSource)

@[simp] theorem generatedMandateExitAction_targetRoot_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedMandateExitActionAt initial depth).target.targetRoot =
      mandateExitTargetRoot :=
  rfl

theorem generatedMandateExitAction_macroNext_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedMandateExitActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedMandateExitActionAt initial depth).target.TargetV,
        (generatedMandateExitActionAt initial depth
          ).target.targetRoot.toAuthoritativeRoot,
        (generatedMandateExitActionAt initial depth).target.targetVisit⟩ :=
  (generatedMandateExitActionAt initial depth).target
    |>.targetAnswerAndNext_next_eq

end
end M14SourceGeneratedSequentialMandateExit
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialMandateExit.generatedMandateExitActionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialMandateExit.ExactMandateExitActionReceiptAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialMandateExit.generatedMandateExitAction_macroNext_exact
