import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Exit.Action.SourceGeneratedSequentialMandateExit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Exit.Bearer.SourceGeneratedMandateExitCriticalRelationBearer

/-!
# Root-controlled mandate ordinary-exit Constitution

The installed continuing mandate generates its exact next occurrence.  That
occurrence executes one fixed sequential actual action, whose target root has
the sole mandate coordinate compiled from the exiting history.  The source
event is the next cycle's canonical Constitution Payment occurrence, and its
presentation lands on the target root's installed UBI Payment restriction.

No exit face, target root, bearer equality, Payment, Constitution or verdict
is accepted by the producer mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedMandateOrdinaryExitConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost Election
open M8ActualElectionMandateRenewalRegression
open M3FiniteExchangeFixture
open M14SourceMandateRenewal
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedLossAllocationMaterial
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceInstalledMandateFiniteConstitutionIncidence
open M14SourceGeneratedMandateExitTargetRoot
open M14SourceGeneratedMandateExitActionSource
open M14SourceGeneratedSequentialMandateExit
open M14SourceGeneratedMandateExitCriticalRelationBearer

/-- Canonical next-cycle operational material.  The definition contains no
target Payment or mandate face; the commuting square below connects those
source and target restrictions. -/
def MandateExitOperationalMaterialAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  ∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
    ∃ code : birthBearerExitRelationCompiler.FutureCode,
      ∃ slot : Fin
          (anomiePhaseAt
            (cycleExitCapacityDepthAt initial (depth + 1))).served.length,
        semanticRenewal.exit.1 = code ∧
          ExitCapacitySemanticMaterialAt initial (depth + 1) code slot ∧
          ExitCapacityTemporalMaterialAt initial (depth + 1) code

theorem mandateExitOperationalMaterialAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    MandateExitOperationalMaterialAt initial depth :=
  (cycleCanonicalRootLawConstitutionFromActualFold initial (depth + 1)
    ).semanticRenewalIncidence

/-- The exact action source is the canonical next-cycle Constitution Payment
root occurrence. -/
theorem mandateExitActionSource_eq_nextConstitutionPaymentRoot
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq (mandateExitActionExactSourceEventAt initial depth)
      (canonicalConstitutionEmbeddedPaymentAt initial (depth + 1)
        ).rootOccurrence := by
  rw [canonicalConstitutionEmbeddedPayment_eq_periodic]
  exact actionSourceOccurrence_is_nextCycleMandateOccurrence initial depth

/-- Source canonical Payment and target installed Payment form the action's
occurrence-presentation square. -/
theorem mandateExitAction_targetPayment_commutes
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedMandateExitActionAt initial depth
      ).target.occurrencePresentation.forward
        (mandateExitActionExactSourceEventAt initial depth).occurrence =
      mandateExitTargetSourceBackedPaymentAt.rootOccurrence.occurrence :=
  rfl

/-- Zero-choice integration carrier. -/
structure MandateOrdinaryExitConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Type 32 where
  private mk ::
  standing : SourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
  standingExact : standing =
    sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
  action : SourceGeneratedSequentialActualActionAt
    (mandateExitActionProgramAt initial depth)
    (mandateExitActionExactSourceEventAt initial depth)
  actionExact : action = generatedMandateExitActionAt initial depth
  exitBearer : MandateExitCriticalRelationBearerAt
  exitBearerExact : exitBearer = mandateExitCriticalRelationBearerAt
  targetPayment : MandateExitTargetSourceBackedPaymentAt
  targetPaymentExact : targetPayment =
    mandateExitTargetSourceBackedPaymentAt
  sourceIsNextConstitutionPayment :
    HEq (mandateExitActionExactSourceEventAt initial depth)
      (canonicalConstitutionEmbeddedPaymentAt initial (depth + 1)
        ).rootOccurrence
  sourceToTargetPaymentCommutes :
    action.target.occurrencePresentation.forward
        (mandateExitActionExactSourceEventAt initial depth).occurrence =
      targetPayment.rootOccurrence.occurrence
  commonBearerIsExitWorker : exitBearer.commonBearer =
    exchangeLaw.bearerOfActor birthBearerWorker
  operationalMaterial : MandateExitOperationalMaterialAt initial depth

/-- Sole producer; every field is generated from `initial/depth`. -/
def sourceGeneratedMandateOrdinaryExitConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    MandateOrdinaryExitConstitutionAt initial depth :=
  let action := generatedMandateExitActionAt initial depth
  let exitBearer := mandateExitCriticalRelationBearerAt
  let targetPayment := mandateExitTargetSourceBackedPaymentAt
  { standing :=
      sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
    standingExact := rfl
    action := action
    actionExact := rfl
    exitBearer := exitBearer
    exitBearerExact := rfl
    targetPayment := targetPayment
    targetPaymentExact := rfl
    sourceIsNextConstitutionPayment :=
      mandateExitActionSource_eq_nextConstitutionPaymentRoot initial depth
    sourceToTargetPaymentCommutes :=
      mandateExitAction_targetPayment_commutes initial depth
    commonBearerIsExitWorker := by
      rw [mandateExitCriticalRelationBearer_commonBearer_eq_parent]
      exact birthBearerWorker_bearer_exact.symm
    operationalMaterial := mandateExitOperationalMaterialAt initial depth }

namespace MandateOrdinaryExitConstitutionAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
variable {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
variable (exit : MandateOrdinaryExitConstitutionAt initial depth)

include exit
theorem exact_actual_exit :
    exit.action.target.targetRoot = mandateExitTargetRoot ∧
      installedMandateExitLocalFace.responsibilityConsumer.1.1 =
        mandateActionPower sourceMandateExitHistory lineageCompiler ∧
      MandateExitRelationCompiler.phaseStep
          installedMandateExitLocalFace.standing.relation = .exit ∧
      MandateExitRelationCompiler.roleAt
          installedMandateExitLocalFace.standing.relation .target = .exited ∧
      ∃ archive,
        installedMandateExitLocalFace.exactDisposition.1.target.slots[
            (mandateSlot lineageCompiler
              sourceMandateExitHistory.current).val]? =
          some (.terminal archive) := by
  rw [exit.actionExact]
  exact
    ⟨generatedMandateExitAction_targetRoot_exact initial depth,
      mandateExitCriticalRelationBearer_exact_power_phase_role.1,
      mandateExitCriticalRelationBearer_exact_power_phase_role.2.1,
      mandateExitCriticalRelationBearer_exact_power_phase_role.2.2,
      installedMandateExit_disposition_terminal⟩

theorem wholeLedgerAndMacroNext :
    exit.action.target.firstSuccessor = mandateExitTargetFirstSuccessor ∧
      exit.action.target.targetAnswerAndNext.nextCurrent =
        ⟨exit.action.target.TargetV,
          exit.action.target.targetRoot.toAuthoritativeRoot,
          exit.action.target.targetVisit⟩ := by
  rw [exit.actionExact]
  exact ⟨rfl,
    generatedMandateExitAction_macroNext_exact initial depth⟩

end MandateOrdinaryExitConstitutionAt

end
end M14SourceGeneratedMandateOrdinaryExitConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateOrdinaryExitConstitution.mandateExitActionSource_eq_nextConstitutionPaymentRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateOrdinaryExitConstitution.sourceGeneratedMandateOrdinaryExitConstitutionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateOrdinaryExitConstitution.MandateOrdinaryExitConstitutionAt.exact_actual_exit
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateOrdinaryExitConstitution.MandateOrdinaryExitConstitutionAt.wholeLedgerAndMacroNext
