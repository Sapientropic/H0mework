import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Constitution.Producer.SourceGeneratedHealthCessationConstitution
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Service.Producer.SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Maintenance.SourceEssentialServiceRestoration
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Death.PortfolioMaintenanceDeath
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.NoGo.SourceGeneratedCycleCanonicalRootLawStepNoGo

/-!
# No-go boundaries for source-generated health cessation

The source occurrence is the mandate-succession macro next.  The independent
outer health-channel read retains Payment and service evidence but has an
empty local ledger, so it cannot replace that sequential source.  The action
keeps the health relation's generated `.t2` bearer, terminal disposition,
single installed service coordinate, target Payment, first write and macro
next.

These fibres also reject restoration replay, caller target/law replacement,
U8 relabelling, search-side actual writes, portfolio-death transport retyping
and a one-occurrence completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedHealthCessationNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations Power Renewal UBI Election
open UniversalRootGrammar
open M8ActualElectionMandateRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9SourceHealthCessationSuffix
open M14UBIExitCapacityFixture
open M14EssentialAccessRelationFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceGeneratedCycleCanonicalRootLawStepNoGo
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessity
open M14SourceEssentialServiceRestoration
open M14PortfolioMaintenanceDeath
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceHealthCessationRenewal
open M14SourceGeneratedHealthCessationActionSource
open M14SourceGeneratedHealthCessationTargetRoot
open M14SourceGeneratedSequentialHealthCessation
open M14SourceGeneratedHealthCessationConstitution
open M14SourceGeneratedMandateSuccessorTargetRoot
open M14SourceGeneratedSequentialMandateSuccession
open M14SourceMandateRenewal
open M14SourceMandateSuccession

/-! ## The complete Constitution cannot be deleted -/

def HealthCessationConstitutionDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) : Prop :=
  IsEmpty (SourceGeneratedHealthCessationConstitutionAt initial observerFuel
    depth)

theorem healthCessationConstitutionDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    IsEmpty (HealthCessationConstitutionDeletionAt initial observerFuel
      depth) :=
  ⟨fun deleted => deleted.false
    (sourceGeneratedHealthCessationConstitutionAt initial observerFuel depth)⟩

/-! ## The source action spine cannot be erased -/

def HealthActionReceiptProvenanceDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  IsEmpty (HealthCessationActionReceiptProvenanceAt initial depth
    (healthCessationActionExactSourceEventAt initial depth))

theorem healthActionReceiptProvenanceDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (HealthActionReceiptProvenanceDeletionAt initial depth) :=
  ⟨fun deleted => deleted.false
    (healthCessationActionReceiptProvenanceAt initial depth
      (healthCessationActionExactSourceEventAt initial depth))⟩

def SourceSuccessionMacroNextSeparationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  (generatedMandateSuccessionActionAt initial depth
    ).target.targetAnswerAndNext.nextCurrent ≠
      ⟨M14SourceGeneratedMandateSuccessorTargetRoot.V,
        mandateSuccessorTargetRoot.toAuthoritativeRoot,
        healthCessationActionSourceVisitAt initial depth⟩

theorem sourceSuccessionMacroNextSeparation_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (SourceSuccessionMacroNextSeparationAt initial depth) :=
  ⟨fun separated => separated
    (healthCessationActionSource_is_successionMacroNext initial depth)⟩

/-! ## The outer channel cannot supply sequential source authority -/

abbrev OuterHealthChannelSourceEntryAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  OpenResponsibilityAt (JointSettlementNAt oldVisit)
    (sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
      oldVisit sourceIndex (healthCessationChannelIndexAt initial depth)
      ).outerRootEvent.occurrence.1

/-- Any sequential source would first need a local open-ledger entry.  The
outer channel occurrence has none. -/
def OuterHealthChannelSequentialSourceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  Nonempty (OuterHealthChannelSourceEntryAt initial depth)

theorem outerHealthChannelSequentialSource_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (OuterHealthChannelSequentialSourceAt initial depth) :=
  let countermodel :=
    sourceGeneratedServiceBeneficiaryBearerAlignmentIndependentNecessityAt
      oldVisit sourceIndex (healthCessationChannelIndexAt initial depth)
  ⟨fun source => countermodel.localLedgerEmpty.false source.some⟩

/-! ## Health relation and bearer cannot be collapsed -/

def HealthCriticalBearerCollapsedToT1 : Prop :=
  sourceGeneratedHealthCriticalAction.criticalBearer.commonBearer =
    Lifecycle.ActorBearer.target .t1

theorem healthCriticalBearerCollapsedToT1_isEmpty :
    IsEmpty HealthCriticalBearerCollapsedToT1 :=
  ⟨fun collapsed => healthCriticalBearer_ne_t1 collapsed⟩

abbrev HealthBeneficiaryBearerAlignmentAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  HealthServiceBeneficiaryBearerAlignmentAt oldVisit sourceIndex
    (healthCessationChannelIndexAt initial depth)

theorem healthBeneficiaryBearerAlignment_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (HealthBeneficiaryBearerAlignmentAt initial depth) :=
  healthServiceBeneficiaryBearerAlignment_isEmpty oldVisit sourceIndex
    (healthCessationChannelIndexAt initial depth)

def HealthCriticalBearerLineageDeletion : Prop :=
  IsEmpty (EssentialAccessCriticalBearerLineageAt
    (essentialAccessCriticalRelation .health)
    (M3FiniteExchangeFixture.exchangeLaw.bearerOfActor
      (essentialAccessCriticalActor .health)))

theorem healthCriticalBearerLineageDeletion_isEmpty :
    IsEmpty HealthCriticalBearerLineageDeletion :=
  ⟨fun deleted => deleted.false
    (essentialAccessCriticalBearerLineage .health)⟩

/-! ## Target and law are generated, not caller-selected -/

def CallerTargetOverrideAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  (generatedHealthCessationActionAt initial depth).target.targetRoot ≠
    healthCessationTargetRoot

theorem callerTargetOverride_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (CallerTargetOverrideAt initial depth) :=
  ⟨fun override => override
    (generatedHealthCessationAction_targetRoot_exact initial depth)⟩

def CallerTargetLawOverrideAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  ¬ HEq
    (generatedHealthCessationActionAt initial depth
      ).target.targetRoot.source.base.lawSurface
    (generatedHealthCessationActionAt initial depth).target.targetTheory

theorem callerTargetLawOverride_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (CallerTargetLawOverrideAt initial depth) :=
  ⟨fun override => override
    (generatedHealthCessationActionAt initial depth).target.lawSurface_heq⟩

/-! ## No restoration replay and no duplicate service coordinate -/

def HealthCessationReportedRestored : Prop :=
  installedHealthCessationConsumer.action.loss.power.freedomChange.kind =
    .restored

theorem healthCessationReportedRestored_isEmpty :
    IsEmpty HealthCessationReportedRestored :=
  ⟨fun replay => by
    change FreedomChangeKind.lost = FreedomChangeKind.restored at replay
    cases replay⟩

theorem legacyRestoration_hasNoCessationPayload : True := by
  fail_if_success exact sourceGeneratedHealthServiceRestoration.freedomChange
  fail_if_success exact sourceGeneratedHealthServiceRestoration.terminal
  fail_if_success exact sourceGeneratedHealthServiceRestoration.targetRoot
  fail_if_success exact sourceGeneratedHealthServiceRestoration.nextCurrent
  trivial

theorem secondHealthCessationCoordinate_isEmpty :
    IsEmpty SecondInstalledHealthCessationCoordinate :=
  secondInstalledHealthCessationCoordinate_isEmpty

/-! ## The installed health update cannot be erased or substituted -/

def InstalledHealthConsumerDeletion : Prop :=
  IsEmpty
    (installedHealthCessationConsumer = sourceHealthCessationConsumer)

theorem installedHealthConsumerDeletion_isEmpty :
    IsEmpty InstalledHealthConsumerDeletion :=
  ⟨fun deleted => deleted.false installedHealthCessation_consumer_exact⟩

def InstalledHealthDispositionDeletion : Prop :=
  IsEmpty
    (installedHealthCessationDisposition = sourceHealthCessationDisposition)

theorem installedHealthDispositionDeletion_isEmpty :
    IsEmpty InstalledHealthDispositionDeletion :=
  ⟨fun deleted => deleted.false installedHealthCessation_disposition_exact⟩

def InstalledHealthUpdateDeletion : Prop :=
  IsEmpty (installedHealthCessationDisposition.update =
    sourceGeneratedHealthCriticalActualUpdate)

theorem installedHealthUpdateDeletion_isEmpty :
    IsEmpty InstalledHealthUpdateDeletion :=
  ⟨fun deleted => deleted.false installedHealthCessation_update_exact⟩

def InstalledHealthFactorizationDeletion : Prop :=
  IsEmpty installedHealthCessation.RootAnswerAndNextFactorizes

theorem installedHealthFactorizationDeletion_isEmpty :
    IsEmpty InstalledHealthFactorizationDeletion :=
  ⟨fun deleted => deleted.false installedHealthCessation_factorizes⟩

/-! ## The successor mandate remains live on the health target -/

def SuccessorMandateFaceDeletion : Prop :=
  IsEmpty (installedSuccessorMandateLocalFace = sourceMandateSuccessorFace)

theorem successorMandateFaceDeletion_isEmpty :
    IsEmpty SuccessorMandateFaceDeletion :=
  ⟨fun deleted => deleted.false installedSuccessorMandate_face_exact⟩

def SuccessorMandateRestoredDeletion : Prop :=
  IsEmpty
    ((installedSuccessorMandateLocalFace.responsibilityConsumer.1.1
      ).freedomChange.kind = FreedomChangeKind.restored)

theorem successorMandateRestoredDeletion_isEmpty :
    IsEmpty SuccessorMandateRestoredDeletion :=
  ⟨fun deleted => deleted.false installedSuccessorMandate_power_restored⟩

def SuccessorMandateLiveDeletion : Prop :=
  IsEmpty
    (installedSuccessorMandateLocalFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateSuccessorHistory.current).val]? =
      some (.live (mandateObligation lineageCompiler
        sourceMandateSuccessorHistory.current)))

theorem successorMandateLiveDeletion_isEmpty :
    IsEmpty SuccessorMandateLiveDeletion :=
  ⟨fun deleted => deleted.false installedSuccessorMandate_obligation_live⟩

def SuccessorMandateFactorizationDeletion : Prop :=
  IsEmpty installedSuccessorMandate.RootAnswerAndNextFactorizes

theorem successorMandateFactorizationDeletion_isEmpty :
    IsEmpty SuccessorMandateFactorizationDeletion :=
  ⟨fun deleted => deleted.false installedSuccessorMandate_factorizes⟩

def SuccessorMandateReplayedAsTerminal : Prop :=
  ∃ archive : TerminalArchive (mandateVocabulary lineageCompiler),
    installedSuccessorMandateLocalFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateSuccessorHistory.current).val]? =
      some (.terminal archive)

theorem successorMandateReplayedAsTerminal_isEmpty :
    IsEmpty SuccessorMandateReplayedAsTerminal :=
  ⟨fun replay => by
    rcases replay with ⟨archive, replay⟩
    rw [installedSuccessorMandate_obligation_live] at replay
    cases replay⟩

/-! ## Terminal, Payment, first write and macro next cannot be deleted -/

def TargetHealthTerminalDeletion : Prop :=
  IsEmpty (∃ archive,
    (essentialAccessCriticalTerminalAt .health).terminal.target.slots[
      (criticalRelationSlot essentialAccessCriticalBearerOf .health).val]? =
        some (.terminal archive))

theorem targetHealthTerminalDeletion_isEmpty :
    IsEmpty TargetHealthTerminalDeletion :=
  ⟨fun deleted => deleted.false installedHealthCessation_terminal⟩

def SourcePaymentConstitutionIncidenceDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  IsEmpty (HealthPaymentConstitutionIncidenceAt initial depth)

theorem sourcePaymentConstitutionIncidenceDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (SourcePaymentConstitutionIncidenceDeletionAt initial depth) :=
  ⟨fun deleted => deleted.false
    (healthPaymentConstitutionIncidenceAt initial depth)⟩

def TargetPaymentDeletion : Prop :=
  IsEmpty HealthCessationTargetSourceBackedPaymentAt

theorem targetPaymentDeletion_isEmpty : IsEmpty TargetPaymentDeletion :=
  ⟨fun deleted => deleted.false
    healthCessationTargetSourceBackedPaymentAt⟩

def TargetPaymentCommutationDeletionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  (generatedHealthCessationActionAt initial depth
    ).target.occurrencePresentation.forward
      (healthCessationActionExactSourceEventAt initial depth).occurrence ≠
    healthCessationTargetSourceBackedPaymentAt.rootOccurrence.occurrence

theorem targetPaymentCommutationDeletion_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (TargetPaymentCommutationDeletionAt initial depth) :=
  ⟨fun deleted => deleted
    (generatedHealthCessationAction_targetPayment_commutes initial depth)⟩

def TargetFirstWriteDeletion : Prop :=
  IsEmpty (SourceNativeLedgerGeneratedSuccessorAt
    healthCessationTargetInitialGenerated.occurrence
    healthCessationTargetInitialGenerated.wholeLedgerWriteBack)

theorem targetFirstWriteDeletion_isEmpty :
    IsEmpty TargetFirstWriteDeletion :=
  ⟨fun deleted => deleted.false healthCessationTargetFirstSuccessor⟩

def TargetMacroNextDivergenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  (generatedHealthCessationActionAt initial depth
    ).target.targetAnswerAndNext.nextCurrent ≠
      ⟨(generatedHealthCessationActionAt initial depth).target.TargetV,
        (generatedHealthCessationActionAt initial depth
          ).target.targetRoot.toAuthoritativeRoot,
        (generatedHealthCessationActionAt initial depth).target.targetVisit⟩

theorem targetMacroNextDivergence_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (TargetMacroNextDivergenceAt initial depth) :=
  ⟨fun divergent => divergent
    (generatedHealthCessationAction_macroNext_exact initial depth)⟩

/-! ## No U8/search substitution, transporter retyping or completed future -/

def HealthCessationActionMasqueradesAsU8At
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  (healthCessationActualActionCompilationAt initial depth
    (healthCessationActionExactSourceEventAt initial depth)).audit =
      .obstructed RootInquiryU8CompletionRegression.obstruction
        (.requiresU8 RootInquiryU8CompletionRegression.u7Gate
          RootInquiryU8CompletionRegression.failure)

theorem healthCessationActionMasqueradesAsU8_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    IsEmpty (HealthCessationActionMasqueradesAsU8At initial depth) :=
  ⟨fun masquerade => by cases masquerade⟩

theorem portfolioDeathTransport_hasNoActualActionPayload
    (depth : Nat) : True := by
  let transport := maintenanceRestorationTransportAt (depth := depth)
    (portfolioMaintenanceDeathAt depth)
  fail_if_success exact transport.program
  fail_if_success exact transport.sourceEntry
  fail_if_success exact transport.targetRoot
  fail_if_success exact transport.receipt
  trivial

structure HealthCessationNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) : Prop where
  private mk ::
  positive : Nonempty
    (SourceGeneratedHealthCessationConstitutionAt initial observerFuel depth)
  constitutionDeletion : IsEmpty
    (HealthCessationConstitutionDeletionAt initial observerFuel depth)
  actionReceiptProvenanceDeletion :
    IsEmpty (HealthActionReceiptProvenanceDeletionAt initial depth)
  sourceMacroNextDeletion :
    IsEmpty (SourceSuccessionMacroNextSeparationAt initial depth)
  outerLedgerSource :
    IsEmpty (OuterHealthChannelSequentialSourceAt initial depth)
  t2NotT1 : IsEmpty HealthCriticalBearerCollapsedToT1
  noLegacyAlignment :
    IsEmpty (HealthBeneficiaryBearerAlignmentAt initial depth)
  bearerLineageDeletion : IsEmpty HealthCriticalBearerLineageDeletion
  callerTarget : IsEmpty (CallerTargetOverrideAt initial depth)
  callerLaw : IsEmpty (CallerTargetLawOverrideAt initial depth)
  restorationReplay : IsEmpty HealthCessationReportedRestored
  secondServiceCoordinate : IsEmpty SecondInstalledHealthCessationCoordinate
  installedConsumerDeletion : IsEmpty InstalledHealthConsumerDeletion
  installedDispositionDeletion : IsEmpty InstalledHealthDispositionDeletion
  installedUpdateDeletion : IsEmpty InstalledHealthUpdateDeletion
  installedFactorizationDeletion : IsEmpty InstalledHealthFactorizationDeletion
  successorMandateFaceDeletion : IsEmpty SuccessorMandateFaceDeletion
  successorMandateRestoredDeletion : IsEmpty SuccessorMandateRestoredDeletion
  successorMandateLiveDeletion : IsEmpty SuccessorMandateLiveDeletion
  successorMandateFactorizationDeletion :
    IsEmpty SuccessorMandateFactorizationDeletion
  successorMandateTerminalReplay :
    IsEmpty SuccessorMandateReplayedAsTerminal
  terminalDeletion : IsEmpty TargetHealthTerminalDeletion
  sourcePaymentConstitutionDeletion :
    IsEmpty (SourcePaymentConstitutionIncidenceDeletionAt initial depth)
  targetPaymentDeletion : IsEmpty TargetPaymentDeletion
  targetPaymentCommutation :
    IsEmpty (TargetPaymentCommutationDeletionAt initial depth)
  firstWriteDeletion : IsEmpty TargetFirstWriteDeletion
  macroNextDivergence : IsEmpty (TargetMacroNextDivergenceAt initial depth)
  u8Masquerade :
    IsEmpty (HealthCessationActionMasqueradesAsU8At initial depth)
  noCompletedFutureOccurrence :
    ¬ ∃ occurrence : AnyHealthCessationActionOccurrenceAt initial,
      ∀ futureDepth : Nat,
        healthCessationActionOccurrenceAt initial futureDepth = occurrence
  sourceSearchNoActualWrite : IsEmpty
    (SourceNativeScenarioActualWriteAuthorityAt
      (postSettlementSocietyVocabulary oldVisit sourceIndex)
      .fullCaptureSearch)

theorem sourceGeneratedHealthCessationNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    HealthCessationNoGoAt initial observerFuel depth where
  positive :=
    ⟨sourceGeneratedHealthCessationConstitutionAt initial observerFuel depth⟩
  constitutionDeletion :=
    healthCessationConstitutionDeletion_isEmpty initial observerFuel depth
  actionReceiptProvenanceDeletion :=
    healthActionReceiptProvenanceDeletion_isEmpty initial depth
  sourceMacroNextDeletion :=
    sourceSuccessionMacroNextSeparation_isEmpty initial depth
  outerLedgerSource :=
    outerHealthChannelSequentialSource_isEmpty initial depth
  t2NotT1 := healthCriticalBearerCollapsedToT1_isEmpty
  noLegacyAlignment :=
    healthBeneficiaryBearerAlignment_isEmpty initial depth
  bearerLineageDeletion := healthCriticalBearerLineageDeletion_isEmpty
  callerTarget := callerTargetOverride_isEmpty initial depth
  callerLaw := callerTargetLawOverride_isEmpty initial depth
  restorationReplay := healthCessationReportedRestored_isEmpty
  secondServiceCoordinate := secondHealthCessationCoordinate_isEmpty
  installedConsumerDeletion := installedHealthConsumerDeletion_isEmpty
  installedDispositionDeletion := installedHealthDispositionDeletion_isEmpty
  installedUpdateDeletion := installedHealthUpdateDeletion_isEmpty
  installedFactorizationDeletion :=
    installedHealthFactorizationDeletion_isEmpty
  successorMandateFaceDeletion := successorMandateFaceDeletion_isEmpty
  successorMandateRestoredDeletion :=
    successorMandateRestoredDeletion_isEmpty
  successorMandateLiveDeletion := successorMandateLiveDeletion_isEmpty
  successorMandateFactorizationDeletion :=
    successorMandateFactorizationDeletion_isEmpty
  successorMandateTerminalReplay :=
    successorMandateReplayedAsTerminal_isEmpty
  terminalDeletion := targetHealthTerminalDeletion_isEmpty
  sourcePaymentConstitutionDeletion :=
    sourcePaymentConstitutionIncidenceDeletion_isEmpty initial depth
  targetPaymentDeletion := targetPaymentDeletion_isEmpty
  targetPaymentCommutation :=
    targetPaymentCommutationDeletion_isEmpty initial depth
  firstWriteDeletion := targetFirstWriteDeletion_isEmpty
  macroNextDivergence := targetMacroNextDivergence_isEmpty initial depth
  u8Masquerade :=
    healthCessationActionMasqueradesAsU8_isEmpty initial depth
  noCompletedFutureOccurrence :=
    no_single_healthCessationAction_occurrence_carries_all_depths initial
  sourceSearchNoActualWrite :=
    sourceSearchActualWrite_isEmpty
      (sourceGeneratedCycleCanonicalRootLawStep initial (depth + 3))

end
end M14SourceGeneratedHealthCessationNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationNoGo.outerHealthChannelSequentialSource_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationNoGo.legacyRestoration_hasNoCessationPayload
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationNoGo.portfolioDeathTransport_hasNoActualActionPayload
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationNoGo.sourceGeneratedHealthCessationNoGoAt
