import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Ordinary.CrossCompiler.Mandate.Standing.Producer.SourceInstalledMandateFiniteConstitutionIncidence

/-!
# No-go boundaries for installed mandate standing

The source face at this checkpoint is continuing mandate standing.  Deleting
its exact critical carrier, bearer lineage, M9 root factorization or canonical
Constitution incidence is impossible.  Equally, reporting the installed face
as already lost/exited is impossible: the real source values remain
`restored / renew / held`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceInstalledMandateFiniteConstitutionNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost Election
open M8ActualElectionMandateRenewalRegression
open M14UBIExitCapacityFixture
open M14UBIPeriodicActualServiceCapacity
open M14SourceMandateRenewal
open M14PeriodicMandatePowerRenewal
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceInstalledMandateCriticalRelationBearer
open M14SourceInstalledMandateFiniteConstitutionIncidence

abbrev CanonicalMandateDepthAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  mandateConstitutionDepthAt initial depth

def CanonicalMandateBearerLineageDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  IsEmpty (SourceMandateBearerLineageAt
    (periodicMandatePowerRenewalAt
      (CanonicalMandateDepthAt initial depth)).localFace.standing.relation
    sourceGeneratedLossAllocationMaterial.parentBearer)

theorem canonicalMandateBearerLineageDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (CanonicalMandateBearerLineageDeletionAt initial depth) := by
  constructor
  intro deleted
  apply deleted.false
  rw [(periodicMandatePowerRenewalAt
    (CanonicalMandateDepthAt initial depth)).localFaceExact]
  exact SourceMandateBearerLineageAt.generated

def AlternateMandateCommonBearerAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  ∃ bearer : Lifecycle.ActorBearer,
    bearer ≠ sourceGeneratedLossAllocationMaterial.parentBearer ∧
      Nonempty (SourceMandateBearerLineageAt
        (periodicMandatePowerRenewalAt
          (CanonicalMandateDepthAt initial depth)
          ).localFace.standing.relation bearer)

theorem alternateMandateCommonBearer_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (AlternateMandateCommonBearerAt initial depth) :=
  ⟨fun alternate => by
    rcases alternate with ⟨bearer, bearerNe, ⟨lineage⟩⟩
    exact bearerNe
      (sourceMandateBearerLineage_commonBearer_unique lineage).2⟩

def InstalledMandateCriticalCarrierDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  IsEmpty (InstalledMandateCriticalRelationBearerAt
    (CanonicalMandateDepthAt initial depth))

theorem installedMandateCriticalCarrierDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (InstalledMandateCriticalCarrierDeletionAt initial depth) :=
  ⟨fun deleted => deleted.false
    (installedMandateCriticalRelationBearerAt
      (CanonicalMandateDepthAt initial depth))⟩

def InstalledMandateRootFactorizationDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  IsEmpty
    ((periodicMandatePowerRenewalAt
      (CanonicalMandateDepthAt initial depth)
      ).installed.RootAnswerAndNextFactorizes)

theorem installedMandateRootFactorizationDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (InstalledMandateRootFactorizationDeletionAt initial depth) :=
  ⟨fun deleted => deleted.false
    (periodicMandatePowerRenewalAt
      (CanonicalMandateDepthAt initial depth)).rootFactorization⟩

def EmbeddedPaymentRootSeparationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  (sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
    ).mandate.mandate.rootOccurrence ≠
      (canonicalConstitutionEmbeddedPaymentAt initial depth).rootOccurrence

theorem embeddedPaymentRootSeparation_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (EmbeddedPaymentRootSeparationAt initial depth) :=
  ⟨fun separated => separated
    (sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
      ).sameEmbeddedM9Root⟩

def CanonicalConstitutionIncidenceDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  IsEmpty
    (∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
      ∃ code : birthBearerExitRelationCompiler.FutureCode,
        ∃ slot : Fin
            (anomiePhaseAt
              (cycleExitCapacityDepthAt initial depth)).served.length,
          semanticRenewal.exit.1 = code ∧
            ExitCapacitySemanticMaterialAt initial depth code slot ∧
            ExitCapacityTemporalMaterialAt initial depth code)

theorem canonicalConstitutionIncidenceDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (CanonicalConstitutionIncidenceDeletionAt initial depth) :=
  ⟨fun deleted => deleted.false
    (sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth
      ).semanticRenewalIncidence⟩

def InstalledMandateReportedLostAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  (periodicMandatePowerRenewalAt
    (CanonicalMandateDepthAt initial depth)
    ).localFace.responsibilityConsumer.1.1.freedomChange.kind = .lost

theorem installedMandateReportedLost_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (InstalledMandateReportedLostAt initial depth) :=
  ⟨fun reported => by
    change
      (periodicMandatePowerRenewalAt
        (CanonicalMandateDepthAt initial depth)
        ).localFace.responsibilityConsumer.1.1.freedomChange.kind = .lost
      at reported
    have restored := (periodicMandatePowerRenewalAt
      (CanonicalMandateDepthAt initial depth)).local_power_is_restored
    rw [restored] at reported
    cases reported⟩

def InstalledMandateReportedExitPhaseAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  MandateRelationCompiler.phaseStep
      (periodicMandatePowerRenewalAt
        (CanonicalMandateDepthAt initial depth)
        ).localFace.standing.relation = .exit

theorem installedMandateReportedExitPhase_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (InstalledMandateReportedExitPhaseAt initial depth) :=
  ⟨fun reported => by
    change MandateRelationCompiler.phaseStep
      (periodicMandatePowerRenewalAt
        (CanonicalMandateDepthAt initial depth)
        ).localFace.standing.relation = .exit at reported
    rw [(periodicMandatePowerRenewalAt
      (CanonicalMandateDepthAt initial depth)).localFaceExact] at reported
    cases reported⟩

def InstalledMandateReportedExitedRoleAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  MandateRelationCompiler.roleAt
      (periodicMandatePowerRenewalAt
        (CanonicalMandateDepthAt initial depth)
        ).localFace.standing.relation .target = .exited

theorem installedMandateReportedExitedRole_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (InstalledMandateReportedExitedRoleAt initial depth) :=
  ⟨fun reported => by
    change MandateRelationCompiler.roleAt
      (periodicMandatePowerRenewalAt
        (CanonicalMandateDepthAt initial depth)
        ).localFace.standing.relation .target = .exited at reported
    rw [(periodicMandatePowerRenewalAt
      (CanonicalMandateDepthAt initial depth)).localFaceExact] at reported
    cases reported⟩

theorem continuingMandateRejectsExitAction :
    ¬ MandateControllerCompiler.actionAdmittedAt (exitingEvent 1) :=
  sourceMandate_wrong_current_event_rejected

structure InstalledMandateFiniteConstitutionNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  private mk ::
  positive : Nonempty
    (SourceInstalledMandateFiniteConstitutionIncidenceAt initial depth)
  bearerLineageDeletion :
    IsEmpty (CanonicalMandateBearerLineageDeletionAt initial depth)
  alternateBearer : IsEmpty (AlternateMandateCommonBearerAt initial depth)
  criticalCarrierDeletion :
    IsEmpty (InstalledMandateCriticalCarrierDeletionAt initial depth)
  rootFactorizationDeletion :
    IsEmpty (InstalledMandateRootFactorizationDeletionAt initial depth)
  embeddedPaymentRootSeparation :
    IsEmpty (EmbeddedPaymentRootSeparationAt initial depth)
  constitutionIncidenceDeletion :
    IsEmpty (CanonicalConstitutionIncidenceDeletionAt initial depth)
  falseLoss : IsEmpty (InstalledMandateReportedLostAt initial depth)
  falseExitPhase :
    IsEmpty (InstalledMandateReportedExitPhaseAt initial depth)
  falseExitedRole :
    IsEmpty (InstalledMandateReportedExitedRoleAt initial depth)
  wrongCurrentRejected :
    ¬ MandateControllerCompiler.actionAdmittedAt (exitingEvent 1)

theorem sourceInstalledMandateFiniteConstitutionNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    InstalledMandateFiniteConstitutionNoGoAt initial depth where
  positive :=
    ⟨sourceInstalledMandateFiniteConstitutionIncidenceAt initial depth⟩
  bearerLineageDeletion :=
    canonicalMandateBearerLineageDeletion_isEmpty initial depth
  alternateBearer := alternateMandateCommonBearer_isEmpty initial depth
  criticalCarrierDeletion :=
    installedMandateCriticalCarrierDeletion_isEmpty initial depth
  rootFactorizationDeletion :=
    installedMandateRootFactorizationDeletion_isEmpty initial depth
  embeddedPaymentRootSeparation :=
    embeddedPaymentRootSeparation_isEmpty initial depth
  constitutionIncidenceDeletion :=
    canonicalConstitutionIncidenceDeletion_isEmpty initial depth
  falseLoss := installedMandateReportedLost_isEmpty initial depth
  falseExitPhase := installedMandateReportedExitPhase_isEmpty initial depth
  falseExitedRole := installedMandateReportedExitedRole_isEmpty initial depth
  wrongCurrentRejected := continuingMandateRejectsExitAction

end
end M14SourceInstalledMandateFiniteConstitutionNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateFiniteConstitutionNoGo.canonicalMandateBearerLineageDeletion_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateFiniteConstitutionNoGo.alternateMandateCommonBearer_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateFiniteConstitutionNoGo.installedMandateReportedLost_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledMandateFiniteConstitutionNoGo.sourceInstalledMandateFiniteConstitutionNoGoAt
