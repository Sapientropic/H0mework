import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Constitution.NoGo.SourceGeneratedHealthCessationNoGo
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Consumer.ProofCarryingCanonicalSocietyCofinalReadout

/-!
# Proof-carrying health-cessation Constitution

This consumer opens the action receipt all the way to `receipt.down.down` and
reads every source, local and target authority face.  The outer health channel
is retained only as a Payment/relation incidence and is simultaneously proved
incapable of supplying the sequential source ledger.

The public consumer accepts only the source-generated Constitution carrier.
It reconstructs no target, law, Payment or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingHealthCessationConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost Election
open M3FiniteExchangeFixture
open M8ActualElectionMandateRenewalRegression
open M9SourceHealthCessationSuffix
open M14EssentialAccessRelationFixture
open M14UBIExitCapacityFixture
open M14UBIPeriodicActualServiceCapacity
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14ProofCarryingFiniteCycleCanonicalRootLaw
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14ProofCarryingCanonicalSocietyCofinalReadout
open M14ProofCarryingContributionCapacityMacroFutureBirth
open M14SourceInstalledMandateFiniteConstitutionIncidence
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceHealthCessationRenewal
open M14SourceMandateRenewal
open M14SourceMandateSuccession
open M14SourceGeneratedMandateSuccessorTargetRoot
open M14SourceGeneratedSequentialMandateSuccession
open M14SourceGeneratedHealthCessationActionSource
open M14SourceGeneratedHealthCessationTargetRoot
open M14SourceGeneratedSequentialHealthCessation
open M14SourceGeneratedHealthCessationConstitution
open M14SourceGeneratedHealthCessationNoGo

/-! ## Literal receipt elimination -/

/-- Every field below is read from the literal lifted receipt provenance. -/
structure ProofCarryingHealthCessationReceiptAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  private mk ::
  sourceExact :
    healthCessationActionExactSourceEventAt initial depth =
      healthCessationActionExactSourceEventAt initial depth
  sourceSuccessionMacroNext :
    (generatedMandateSuccessionActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨M14SourceGeneratedMandateSuccessorTargetRoot.V,
        mandateSuccessorTargetRoot.toAuthoritativeRoot,
        healthCessationActionSourceVisitAt initial depth⟩
  sourceEntryFromSuccession : HEq
    (healthCessationActionSourceEntryAt initial depth)
    (generatedMandateSuccessionActionAt initial depth).target.targetEntry
  sourceAuthorityFromSuccession : HEq
    (healthCessationActionSourceAuthorityAt initial depth)
    (generatedMandateSuccessionActionAt initial depth).target.targetAuthority
  sourceUBIConsumerExact :
    (installedHealthCessationSourceUBIAt initial depth).payload.consumer =
      sourceGeneratedUBIRootRestriction
  sourceUBIFactorization :
    (installedHealthCessationSourceUBIAt initial depth
      ).RootAnswerAndNextFactorizes
  sourcePaymentReceipt : Nonempty
    (SourceBackedUBIPaymentReceiptAt
      exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave)
  localPowerLost :
    sourceGeneratedHealthCriticalAction.loss.power.freedomChange =
      .lost .health healthCriticalAction_sourceActionable
        healthCriticalAction_targetAbsent
  localBearerT2 :
    sourceGeneratedHealthCriticalAction.criticalBearer.commonBearer =
      Lifecycle.ActorBearer.target .t2
  localBearerNotT1 :
    sourceGeneratedHealthCriticalAction.criticalBearer.commonBearer ≠
      Lifecycle.ActorBearer.target .t1
  localPhaseHealth :
    essentialAccessRelationCompiler.phaseStep healthRelation = .health
  localRoleHealthProvider :
    essentialAccessRelationCompiler.roleAt healthRelation .target =
      .healthProvider
  localRelationProvenance :
    ∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = Lifecycle.Universal.FixedAdapter.targetFace.state
            Lifecycle.actualEventGame.source ∧
        essentialAccessRelationCompiler.relationSeedAt
            Lifecycle.actualEventGame.source state seed.1 ∧
        Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
            Lifecycle.actualEventGame.source state
            (essentialAccessRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor essentialAccessRelationCompiler = healthActor ∧
      essentialAccessRelationCompiler.relationOf seed = healthRelation
  localControllerProvenance :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = (essentialAccessCriticalActionController .health).actionState
          Lifecycle.actualEventGame.source ∧
      (essentialAccessCriticalActionController .health).actionAdmittedAt
        sourceGeneratedHealthCriticalAction.loss.power.action.1
  localUpdateExact : sourceGeneratedHealthCriticalActualUpdate =
    sourceGeneratedEssentialAccessCriticalActualUpdateAt .health
  localBearerCommutes :
    sourceGeneratedHealthCriticalAction.criticalBearer.commonBearer =
      (criticalRelationObligation essentialAccessCriticalBearerOf .health
        ).bearer
  localAdmissionKind :
    (essentialAccessCriticalTerminalAt .health).admission.lifecycleEvent.kind =
      LifecycleKind.admitted
  localTerminal : ∃ archive,
    (essentialAccessCriticalTerminalAt .health).terminal.target.slots[
        (criticalRelationSlot essentialAccessCriticalBearerOf .health).val]? =
      some (.terminal archive)
  localNoReopen : ∀ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
    IsEmpty ((criticalRelationTerminalProcess
      essentialAccessCriticalBearerOf).ReopenEvent archive)
  targetRootExact : healthCessationTargetRoot =
    M9SourceHealthCessationSuffix.jointRoot
  targetInstalledConsumerExact : installedHealthCessationConsumer =
    sourceHealthCessationConsumer
  targetInstalledDispositionExact : installedHealthCessationDisposition =
    sourceHealthCessationDisposition
  targetInstalledUpdateExact : installedHealthCessationDisposition.update =
    sourceGeneratedHealthCriticalActualUpdate
  targetInstalledHealthFactorization :
    installedHealthCessation.RootAnswerAndNextFactorizes
  targetSuccessorMandateFaceExact : installedSuccessorMandateLocalFace =
    sourceMandateSuccessorFace
  targetSuccessorMandateRestored :
    (installedSuccessorMandateLocalFace.responsibilityConsumer.1.1
      ).freedomChange.kind = FreedomChangeKind.restored
  targetSuccessorMandateLive :
    installedSuccessorMandateLocalFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateSuccessorHistory.current).val]? =
      some (.live (mandateObligation lineageCompiler
        sourceMandateSuccessorHistory.current))
  targetSuccessorMandateFactorization :
    installedSuccessorMandate.RootAnswerAndNextFactorizes
  targetPaymentPresentation :
    (healthCessationOccurrencePresentationAt initial depth).forward
        (healthCessationActionExactSourceEventAt initial depth).occurrence =
      healthCessationTargetSourceBackedPaymentAt.rootOccurrence.occurrence
  targetPaymentFactorization :
    (healthCessationTargetSourceBackedPaymentAt.installed
      ).RootAnswerAndNextFactorizes
  targetGenerated : Nonempty
    (SourceNativeTemporalVisitGeneratedEvolutionAt
      healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot
        healthCessationTargetInitialVisit)
  targetFirstWholeLedgerSuccessor : Nonempty
    (SourceNativeLedgerGeneratedSuccessorAt
      healthCessationTargetInitialGenerated.occurrence
      healthCessationTargetInitialGenerated.wholeLedgerWriteBack)

/-- This theorem is the literal receipt eliminator.  The named projection is
definitionally the same `receipt.down.down`; all authority fields are then
read one by one from that value. -/
theorem proofCarryingHealthCessationReceipt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (receipt : ExactHealthCessationActionReceiptAt initial depth
      (healthCessationActionExactSourceEventAt initial depth)
      (PUnit.unit : PUnit.{0})) :
    ProofCarryingHealthCessationReceiptAt initial depth := by
  let provenance : HealthCessationActionReceiptProvenanceAt initial depth
      (healthCessationActionExactSourceEventAt initial depth) :=
    receipt.down.down
  have namedProjectionExact : receipt.provenance = provenance := rfl
  exact
    { sourceExact := provenance.source.exactSourceCanonical
      sourceSuccessionMacroNext := provenance.source.successionMacroNext
      sourceEntryFromSuccession := provenance.source.sourceEntryFromSuccession
      sourceAuthorityFromSuccession :=
        provenance.source.sourceAuthorityFromSuccession
      sourceUBIConsumerExact := provenance.source.sourceUBIConsumerExact
      sourceUBIFactorization := provenance.source.sourceUBIFactorization
      sourcePaymentReceipt := provenance.source.sourcePaymentReceipt
      localPowerLost := provenance.localSeal.powerLost
      localBearerT2 := provenance.localSeal.bearerT2
      localBearerNotT1 := provenance.localSeal.bearerNotT1
      localPhaseHealth := provenance.localSeal.phaseHealth
      localRoleHealthProvider := provenance.localSeal.roleHealthProvider
      localRelationProvenance := provenance.localSeal.exactRelationProvenance
      localControllerProvenance :=
        provenance.localSeal.exactControllerProvenance
      localUpdateExact := provenance.localSeal.updateExact
      localBearerCommutes := provenance.localSeal.bearerCommutes
      localAdmissionKind := provenance.localSeal.admissionKind
      localTerminal := provenance.localSeal.terminal
      localNoReopen := provenance.localSeal.noReopen
      targetRootExact := provenance.target.targetRootExact
      targetInstalledConsumerExact := provenance.target.installedConsumerExact
      targetInstalledDispositionExact :=
        provenance.target.installedDispositionExact
      targetInstalledUpdateExact := provenance.target.installedUpdateExact
      targetInstalledHealthFactorization :=
        provenance.target.installedHealthFactorization
      targetSuccessorMandateFaceExact :=
        provenance.target.successorMandateFaceExact
      targetSuccessorMandateRestored :=
        provenance.target.successorMandateRestored
      targetSuccessorMandateLive :=
        provenance.target.successorMandateLive
      targetSuccessorMandateFactorization :=
        provenance.target.successorMandateFactorization
      targetPaymentPresentation := provenance.target.targetPaymentPresentation
      targetPaymentFactorization := provenance.target.targetPaymentFactorization
      targetGenerated := provenance.target.targetGenerated
      targetFirstWholeLedgerSuccessor :=
        provenance.target.firstWholeLedgerSuccessor }

/-! ## Operational and canonical depth-three audits -/

def HealthCessationOperationalAuthorityAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  ∃ code : birthBearerExitRelationCompiler.FutureCode,
    ∃ slot : Fin
        (anomiePhaseAt
          (cycleExitCapacityDepthAt initial (depth + 3))).served.length,
      code ∈ birthBearerExitRelationCompiler.futureCodeCarrier ∧
        Nonempty
          (birthBearerExitRelationCompiler.FutureContinuationAt
            birthBearerIndependentExitRelation.1 .target code) ∧
        ¬ birthBearerExitRelationCompiler.futureIdle code ∧
        ¬ birthBearerNoCapture.Captures code ∧
        Nonempty
          (SourceBackedUBIPaymentReceiptAt
            birthBearerExitCapacityProgram.purchasingPowerStanding code) ∧
        Nonempty
          (SourceGeneratedUBIRouteReceiptAt code
            (ExactServedCrossingDebitedRunAt.servicedCrossingAt
              (phase := anomiePhaseAt
                (cycleExitCapacityDepthAt initial (depth + 3)))
              (crossingCompiler := crossingCompilerAt
                (cycleExitCapacityDepthAt initial (depth + 3))) slot)) ∧
        PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex
          (cycleLifecycleIndex initial (depth + 3)) ∧
        PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex
          (cycleLifecycleIndex initial (depth + 3)) ∧
        Function.Injective
          (paidExitLifecycleActualServiceKAt oldVisit sourceIndex
            (cycleLifecycleIndex initial (depth + 3)))

theorem HealthCessationOperationalMaterialAt.directAuthority
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (material : HealthCessationOperationalMaterialAt initial depth) :
    HealthCessationOperationalAuthorityAt initial depth := by
  rcases material with
    ⟨_renewal, code, slot, _codeExact, semantic, temporal⟩
  exact
    ⟨code, slot, semantic.codeInCarrier,
      semantic.employmentIndependentContinuation, semantic.nonIdle,
      semantic.uncaptured, semantic.sourceBackedPayment, semantic.actualRoute,
      temporal.externalResidual, temporal.actualServicesAndFuture,
      temporal.actualServiceKInjective⟩

structure HealthCessationCanonicalDepthThreeAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat)
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel
      (depth + 3)) : Prop where
  private mk ::
  transition :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 3)
    ProofCarryingCycleCanonicalRootLawTransitionAt initial observerFuel
      (depth + 3) step
  grammarActualSearch :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 3)
    CycleCanonicalRootLawGrammarExhaustionAt initial (depth + 3)
        step.sourceLaw ∧
      CycleCanonicalRootLawActualSearchSameRootAt step.sourceLaw ∧
      CycleCanonicalRootLawLedgerAndNextAt initial (depth + 3) step.sourceLaw
  selfU8 : ExactCanonicalSelfU8TickAt initial (depth + 3)
  compatibleFutureBirth :
    ExactCanonicalCompatibleFutureBirthAt initial observerFuel (depth + 3)
  macroFutureBirthAudit :
    CanonicalContributionCapacityMacroFutureBirthAuditAt oldVisit sourceIndex
      (cycleLifecycleIndex initial (depth + 3 + 1))
  pointMaterial : CanonicalSocietyCofinalPointMaterialAt initial observerFuel
    (depth + 3) pulse

theorem healthCessationCanonicalDepthThreeAuditAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (pulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel
      (depth + 3)) :
    HealthCessationCanonicalDepthThreeAuditAt initial observerFuel depth
      pulse :=
  { transition := pulse.rootLawTransition
    grammarActualSearch :=
      ⟨pulse.rootLawTransition.sourceGrammarExhaustion,
        pulse.rootLawTransition.sourceActualSearchSameRoot,
        pulse.rootLawTransition.sourceRootLedgerAndNext⟩
    selfU8 := pulse.selfU8Tick
    compatibleFutureBirth := pulse.compatibleFutureBirth
    macroFutureBirthAudit := pulse.canonicalMacroFutureBirthAudit
    pointMaterial := canonicalSocietyCofinalPointMaterialAt pulse }

/-! ## Complete consumer -/

structure ProofCarryingHealthCessationConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat)
    (constitution : SourceGeneratedHealthCessationConstitutionAt initial
      observerFuel depth) : Prop where
  private mk ::
  actionToken : ∃ token : SourceGeneratedSequentialActualActionAt
      (healthCessationActionProgramAt initial depth)
      (healthCessationActionExactSourceEventAt initial depth),
    token = generatedHealthCessationActionAt initial depth
  sourceSpineExact : constitution.actionSourceSpine =
    healthCessationActionSourceSpineAt initial depth
  receipt : ProofCarryingHealthCessationReceiptAt initial depth
  outerChannelOnlyIncidence :
    constitution.paymentIncidence =
        healthPaymentConstitutionIncidenceAt initial depth ∧
      constitution.paymentIncidence.healthAction.criticalBearer.commonBearer =
        constitution.paymentIncidence.healthBearer ∧
      constitution.paymentIncidence.healthChannel =
        healthCessationHealthChannelAt initial depth ∧
      (constitution.paymentIncidence.healthChannel.witnessReturn.1.actor
          essentialAccessRelationCompiler = healthActor ∧
        essentialAccessRelationCompiler.relationOf
          constitution.paymentIncidence.healthChannel.witnessReturn.1 =
            healthRelation) ∧
      (constitution.paymentIncidence.healthChannel.actualExit.paymentOccurrence
        ).rootOccurrence =
        (canonicalConstitutionEmbeddedPaymentAt initial (depth + 3)
          ).rootOccurrence ∧
      IsEmpty (OuterHealthChannelSequentialSourceAt initial depth)
  targetFaces : HealthCessationActionTargetFacesAt initial depth
  paymentSquaresAndWholeNext :
    (healthCessationConstitutionSourcePresentationAt initial depth).forward
        (canonicalConstitutionEmbeddedPaymentAt initial (depth + 3)
          ).rootOccurrence.occurrence =
      (healthCessationActionExactSourceEventAt initial depth).occurrence ∧
    (generatedHealthCessationActionAt initial depth
      ).target.occurrencePresentation.forward
        (healthCessationActionExactSourceEventAt initial depth).occurrence =
      healthCessationTargetSourceBackedPaymentAt.rootOccurrence.occurrence ∧
    (generatedHealthCessationActionAt initial depth).target.firstSuccessor =
      healthCessationTargetFirstSuccessor ∧
    (generatedHealthCessationActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedHealthCessationActionAt initial depth).target.TargetV,
        (generatedHealthCessationActionAt initial depth
          ).target.targetRoot.toAuthoritativeRoot,
        (generatedHealthCessationActionAt initial depth).target.targetVisit⟩
  operationalAuthority :
    HealthCessationOperationalAuthorityAt initial depth
  canonicalDepthThree : HealthCessationCanonicalDepthThreeAuditAt initial
    observerFuel depth constitution.canonicalPulse
  noGo : HealthCessationNoGoAt initial observerFuel depth
  noCompletedFuture :
    ¬ ∃ occurrence : AnyHealthCessationActionOccurrenceAt initial,
      ∀ futureDepth : Nat,
        healthCessationActionOccurrenceAt initial futureDepth = occurrence

/-- Sole public consumer.  No target-side object is accepted at the mouth. -/
theorem proofCarryingHealthCessationConstitution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (constitution : SourceGeneratedHealthCessationConstitutionAt initial
      observerFuel depth) :
    ProofCarryingHealthCessationConstitutionAt initial observerFuel depth
      constitution := by
  let noGo := sourceGeneratedHealthCessationNoGoAt initial observerFuel depth
  rcases constitution.actionSourceSpine.actionReceipt with ⟨actionReceipt⟩
  let rawProvenance : HealthCessationActionReceiptProvenanceAt initial depth
      (healthCessationActionExactSourceEventAt initial depth) :=
    actionReceipt.down.down
  have namedProjectionExact : actionReceipt.provenance = rawProvenance := rfl
  let receipt := proofCarryingHealthCessationReceipt actionReceipt
  exact
    { actionToken := constitution.actionSourceSpine.actionToken
      sourceSpineExact := constitution.actionSourceSpineExact
      receipt := receipt
      outerChannelOnlyIncidence :=
        ⟨constitution.paymentIncidenceExact,
          constitution.paymentIncidence.criticalBearerIsHealthBearer,
          constitution.paymentIncidence.healthChannelExact,
          constitution.paymentIncidence.relationWitness,
          constitution.paymentIncidence.channelPaymentIsConstitutionPayment,
          noGo.outerLedgerSource⟩
      targetFaces := constitution.actionTargetFaces
      paymentSquaresAndWholeNext :=
        ⟨constitution.paymentIncidence.constitutionToSourcePayment,
          receipt.targetPaymentPresentation,
          constitution.actionTargetFaces.firstWholeLedgerSuccessor,
          constitution.actionTargetFaces.macroNext⟩
      operationalAuthority :=
        HealthCessationOperationalMaterialAt.directAuthority
          constitution.operationalMaterial
      canonicalDepthThree :=
        healthCessationCanonicalDepthThreeAuditAt constitution.canonicalPulse
      noGo := noGo
      noCompletedFuture := noGo.noCompletedFutureOccurrence }

end
end M14ProofCarryingHealthCessationConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingHealthCessationConstitution.proofCarryingHealthCessationReceipt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingHealthCessationConstitution.HealthCessationOperationalMaterialAt.directAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingHealthCessationConstitution.healthCessationCanonicalDepthThreeAuditAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingHealthCessationConstitution.proofCarryingHealthCessationConstitution
