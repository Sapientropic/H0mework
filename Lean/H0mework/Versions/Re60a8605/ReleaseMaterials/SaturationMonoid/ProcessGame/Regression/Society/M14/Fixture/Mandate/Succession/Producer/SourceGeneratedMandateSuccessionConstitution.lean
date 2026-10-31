import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Succession.Action.SourceGeneratedSequentialMandateSuccession
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Ordinary.CrossCompiler.Mandate.Exit.Producer.SourceGeneratedMandateOrdinaryExitConstitution

/-!
# Root-controlled mandate succession Constitution

The full ordinary-exit Constitution is followed by its generated target macro
step and one second fixed actual action.  A presentation carries the next
canonical Constitution Payment's visible occurrence into the post-exit
source; the actual succession action then carries that exact source occurrence
into the successor target Payment.  Occurrence identities remain distinct and
visit-indexed throughout.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedMandateSuccessionConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost Election
open M8ActualElectionMandateRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M9SourceSuppliedMandateSuffix
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceInstalledMandateFiniteConstitutionIncidence
open M14SourceMandateRenewal
open M14SourceMandateSuccession
open M14SourceGeneratedMandateExitTargetRoot
open M14SourceGeneratedMandateExitTargetHistory
open M14SourceGeneratedPostExitTerminalContinuation
open M14SourceGeneratedMandateSuccessorTargetRoot
open M14SourceGeneratedMandateSuccessionActionSource
open M14SourceGeneratedSequentialMandateSuccession
open M14SourceGeneratedMandateOrdinaryExitConstitution

def MandateSuccessionOperationalMaterialAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  ∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
    ∃ code : birthBearerExitRelationCompiler.FutureCode,
      ∃ slot : Fin
          (anomiePhaseAt
            (cycleExitCapacityDepthAt initial (depth + 2))).served.length,
        semanticRenewal.exit.1 = code ∧
          ExitCapacitySemanticMaterialAt initial (depth + 2) code slot ∧
          ExitCapacityTemporalMaterialAt initial (depth + 2) code

theorem mandateSuccessionOperationalMaterialAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    MandateSuccessionOperationalMaterialAt initial depth :=
  (cycleCanonicalRootLawConstitutionFromActualFold initial (depth + 2)
    ).semanticRenewalIncidence

/-- A representation transporter between two already generated occurrences.
It does not identify their visit-indexed authority. -/
def mandateSuccessionConstitutionPresentationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ConstructivePresentation
      (jointRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (temporalVisitAt
          (mandateConstitutionDepthAt initial (depth + 2))).current)
      (mandateExitTargetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (mandateExitTargetTemporalVisitAt 1).current) :=
  ConstructivePresentation.refl _

theorem mandateSuccessionConstitution_to_postExitPayment_commutes
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (mandateSuccessionConstitutionPresentationAt initial depth).forward
        (canonicalConstitutionEmbeddedPaymentAt initial (depth + 2)
          ).rootOccurrence.occurrence =
      postExitSourceBackedPaymentAt.rootOccurrence.occurrence := by
  rw [canonicalConstitutionEmbeddedPayment_eq_periodic]
  rfl

theorem mandateSuccessionAction_targetPayment_commutes
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedMandateSuccessionActionAt initial depth
      ).target.occurrencePresentation.forward
        (mandateSuccessionActionExactSourceEventAt initial depth).occurrence =
      mandateSuccessorTargetSourceBackedPaymentAt.rootOccurrence.occurrence :=
  rfl

/-- Zero-choice full transition carrier. -/
structure MandateSuccessionConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Type 32 where
  private mk ::
  exit : MandateOrdinaryExitConstitutionAt initial depth
  exitExact : exit =
    sourceGeneratedMandateOrdinaryExitConstitutionAt initial depth
  postExit : SourceGeneratedPostExitTerminalContinuationAt initial depth
  postExitExact : postExit =
    sourceGeneratedPostExitTerminalContinuationAt initial depth
  successionAction : SourceGeneratedSequentialActualActionAt
    (mandateSuccessionActionProgramAt initial depth)
    (mandateSuccessionActionExactSourceEventAt initial depth)
  successionActionExact : successionAction =
    generatedMandateSuccessionActionAt initial depth
  targetPayment : MandateSuccessorTargetSourceBackedPaymentAt
  targetPaymentExact : targetPayment =
    mandateSuccessorTargetSourceBackedPaymentAt
  constitutionToPostExitPayment :
    (mandateSuccessionConstitutionPresentationAt initial depth).forward
        (canonicalConstitutionEmbeddedPaymentAt initial (depth + 2)
          ).rootOccurrence.occurrence =
      postExit.payment.rootOccurrence.occurrence
  postExitToTargetPayment :
    successionAction.target.occurrencePresentation.forward
        (mandateSuccessionActionExactSourceEventAt initial depth).occurrence =
      targetPayment.rootOccurrence.occurrence
  retainedTerminal : ∃ archive,
    postExit.mandateFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateExitHistory.current).val]? =
      some (.terminal archive)
  successorLive :
    installedMandateSuccessorLocalFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateSuccessorHistory.current).val]? =
      some (.live (mandateObligation lineageCompiler
        sourceMandateSuccessorHistory.current))
  sameSlotOrdinal :
    (mandateSlot lineageCompiler sourceMandateExitHistory.current).val =
      (mandateSlot lineageCompiler
        sourceMandateSuccessorHistory.current).val
  distinctObligation :
    mandateObligation lineageCompiler sourceMandateExitHistory.current ≠
      mandateObligation lineageCompiler
        sourceMandateSuccessorHistory.current
  freshController :
    installedMandateSuccessorLocalFace.actor.1 ≠
        sourceMandateHistory.current.controllerSeed ∧
      installedMandateSuccessorLocalFace.actor.1 ≠
        sourceMandateExitHistory.current.controllerSeed
  successorCoordinateSeparation : SuccessorMandateCoordinateSeparation
  operationalMaterial : MandateSuccessionOperationalMaterialAt initial depth

def sourceGeneratedMandateSuccessionConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    MandateSuccessionConstitutionAt initial depth :=
  let exit := sourceGeneratedMandateOrdinaryExitConstitutionAt initial depth
  let postExit := sourceGeneratedPostExitTerminalContinuationAt initial depth
  let action := generatedMandateSuccessionActionAt initial depth
  let payment := mandateSuccessorTargetSourceBackedPaymentAt
  { exit := exit
    exitExact := rfl
    postExit := postExit
    postExitExact := rfl
    successionAction := action
    successionActionExact := rfl
    targetPayment := payment
    targetPaymentExact := rfl
    constitutionToPostExitPayment :=
      mandateSuccessionConstitution_to_postExitPayment_commutes initial depth
    postExitToTargetPayment :=
      mandateSuccessionAction_targetPayment_commutes initial depth
    retainedTerminal := postExit.terminalDisposition
    successorLive := installedMandateSuccessor_obligation_live
    sameSlotOrdinal := sourceMandate_exit_successor_slotOrdinal_same
    distinctObligation := sourceMandate_exit_successor_obligations_distinct
    freshController := installedMandateSuccessor_controller_fresh
    successorCoordinateSeparation :=
      successor_inventory_has_one_named_mandate_coordinate
    operationalMaterial := mandateSuccessionOperationalMaterialAt
      initial depth }

namespace MandateSuccessionConstitutionAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
variable {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
variable (succession : MandateSuccessionConstitutionAt initial depth)

include succession
theorem exact_actual_succession :
    succession.successionAction.target.targetRoot =
        mandateSuccessorTargetRoot ∧
      installedMandateSuccessorLocalFace.actor.1 =
        sourceMandateExitControllerMaximum + 1 ∧
      (installedMandateSuccessorLocalFace.responsibilityConsumer.1.1
        ).freedomChange.kind = FreedomChangeKind.restored ∧
      (officeControllerRelationCompiler sourceMandateSuccessorHistory
        lineageCompiler).phaseStep
          (generatedOfficeControllerRelation sourceMandateSuccessorHistory
            lineageCompiler) = MandatePhase.renew ∧
      (officeControllerRelationCompiler sourceMandateSuccessorHistory
        lineageCompiler).roleAt
          (generatedOfficeControllerRelation sourceMandateSuccessorHistory
            lineageCompiler) .target = MandateRole.held := by
  rw [succession.successionActionExact]
  exact ⟨generatedMandateSuccessionAction_targetRoot_exact initial depth,
    rfl, installedMandateSuccessor_power_restored,
    installedMandateSuccessor_phase_renew,
    installedMandateSuccessor_role_held⟩

theorem wholeLedgerAndMacroNext :
    succession.successionAction.target.firstSuccessor =
        mandateSuccessorTargetFirstSuccessor ∧
      succession.successionAction.target.targetAnswerAndNext.nextCurrent =
        ⟨succession.successionAction.target.TargetV,
          succession.successionAction.target.targetRoot.toAuthoritativeRoot,
          succession.successionAction.target.targetVisit⟩ := by
  rw [succession.successionActionExact]
  exact ⟨rfl,
    generatedMandateSuccessionAction_macroNext_exact initial depth⟩

end MandateSuccessionConstitutionAt

end
end M14SourceGeneratedMandateSuccessionConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateSuccessionConstitution.mandateSuccessionConstitution_to_postExitPayment_commutes
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateSuccessionConstitution.sourceGeneratedMandateSuccessionConstitutionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateSuccessionConstitution.MandateSuccessionConstitutionAt.exact_actual_succession
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateSuccessionConstitution.MandateSuccessionConstitutionAt.wholeLedgerAndMacroNext
