import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Ordinary.CrossCompiler.Mandate.Exit.NoGo.SourceGeneratedMandateOrdinaryExitNoGo
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Producer.SourceGeneratedCanonicalSocietyCofinalReadout

/-!
# Proof-carrying mandate ordinary exit

The consumer eliminates the same next-cycle Constitution material used by the
producer, together with the exact sequential action receipt.  It exposes the
role-independent continuation, Payment, route, services/future, external
residual and K, while retaining the target mandate loss, terminal disposition,
first target write, macro next and canonical next-cycle root law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingMandateOrdinaryExitConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost Election
open M3FiniteExchangeFixture
open M8ActualElectionMandateRenewalRegression
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIPeriodicActualServiceCapacity
open M14UBIProofCarryingRootRestriction
open M14UBIExitCapacityFixture
open M14SourceMandateRenewal
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceInstalledMandateFiniteConstitutionIncidence
open M14ProofCarryingFiniteCycleCanonicalRootLaw
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14SourceGeneratedMandateExitTargetRoot
open M14SourceGeneratedMandateExitActionSource
open M14SourceGeneratedSequentialMandateExit
open M14SourceGeneratedMandateExitCriticalRelationBearer
open M14SourceGeneratedMandateOrdinaryExitConstitution

theorem MandateExitOperationalMaterialAt.directAuthority
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (material : MandateExitOperationalMaterialAt initial depth) :
    ∃ code : birthBearerExitRelationCompiler.FutureCode,
      ∃ slot : Fin
          (anomiePhaseAt
            (cycleExitCapacityDepthAt initial (depth + 1))).served.length,
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
                  (cycleExitCapacityDepthAt initial (depth + 1)))
                (crossingCompiler := crossingCompilerAt
                  (cycleExitCapacityDepthAt initial (depth + 1))) slot)) ∧
          PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex
            (cycleLifecycleIndex initial (depth + 1)) ∧
          PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex
            (cycleLifecycleIndex initial (depth + 1)) ∧
          Function.Injective
            (paidExitLifecycleActualServiceKAt oldVisit sourceIndex
              (cycleLifecycleIndex initial (depth + 1))) := by
  rcases material with
    ⟨_renewal, code, slot, _exact, semantic, temporal⟩
  exact
    ⟨code, slot, semantic.codeInCarrier,
      semantic.employmentIndependentContinuation, semantic.nonIdle,
      semantic.uncaptured, semantic.sourceBackedPayment, semantic.actualRoute,
      temporal.externalResidual, temporal.actualServicesAndFuture,
      temporal.actualServiceKInjective⟩

structure ProofCarryingMandateOrdinaryExitConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat)
    (exit : MandateOrdinaryExitConstitutionAt initial depth) : Prop where
  private mk ::
  actionExact : exit.action = generatedMandateExitActionAt initial depth
  actionReceipt : Nonempty (ExactMandateExitActionReceiptAt initial depth
    (mandateExitActionExactSourceEventAt initial depth)
      (PUnit.unit : PUnit.{0}))
  sourceStandingGeneratedNext :
    exit.standing.mandate.mandate.generatedNext =
      ⟨M9ProofCarryingRenewalInquiryRoot.V,
        M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot,
        mandateExitActionSourceVisitAt initial depth⟩
  sourceIsNextConstitutionPayment :
    HEq (mandateExitActionExactSourceEventAt initial depth)
      (canonicalConstitutionEmbeddedPaymentAt initial (depth + 1)
        ).rootOccurrence
  sourceToTargetPayment :
    exit.action.target.occurrencePresentation.forward
        (mandateExitActionExactSourceEventAt initial depth).occurrence =
      exit.targetPayment.rootOccurrence.occurrence
  targetPaymentRestriction : exit.targetPayment.installed.payload.consumer =
    sourceGeneratedUBIRootRestriction
  targetPaymentFactorization :
    exit.targetPayment.installed.RootAnswerAndNextFactorizes
  targetMandateFactorization : installedMandateExit.RootAnswerAndNextFactorizes
  targetPowerPhaseRoleTerminal :
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
          some (.terminal archive)
  controllerRelationObligationExact :
    installedMandateExitLocalFace.standing.controller.1 =
        installedMandateExitLocalFace.standing.relation.1.controller ∧
      installedMandateExitLocalFace.standing.relation.1.controller =
        installedMandateExitLocalFace.standing.obligation.bearer
  criticalRelationAndControllerProvenance :
    (∃ seed : MandateExitRelationCompiler.ExactRelationSeed,
      (∃ state ∈ SourceMandateExitGame.occurrence.trace,
        state = (officeFace lineageCompiler).state
          SourceMandateExitGame.source ∧
        MandateExitRelationCompiler.relationSeedAt
          SourceMandateExitGame.source state seed.1 ∧
        (officeFace lineageCompiler).SeedAt SourceMandateExitGame.source state
          (MandateExitRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor MandateExitRelationCompiler =
        installedMandateExitLocalFace.standing.office ∧
      MandateExitRelationCompiler.relationOf seed =
        installedMandateExitLocalFace.standing.relation) ∧
      (∃ state ∈ SourceMandateExitGame.occurrence.trace,
        state = MandateExitControllerCompiler.actionState
          SourceMandateExitGame.source ∧
        MandateExitControllerCompiler.actionAdmittedAt
          installedMandateExitLocalFace.responsibilityConsumer.1.1.action.1)
  commonBearerOnly : exit.exitBearer.commonBearer =
    exchangeLaw.bearerOfActor birthBearerWorker
  operationalMaterial : MandateExitOperationalMaterialAt initial depth
  firstTargetWriteAndMacroNext :
    exit.action.target.firstSuccessor = mandateExitTargetFirstSuccessor ∧
      exit.action.target.targetAnswerAndNext.nextCurrent =
        ⟨exit.action.target.TargetV,
          exit.action.target.targetRoot.toAuthoritativeRoot,
          exit.action.target.targetVisit⟩
  nextCycleRootLawTransition :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 1)
    ProofCarryingCycleCanonicalRootLawTransitionAt initial observerFuel
      (depth + 1) step
  nextCycleActualSearchSameRoot :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 1)
    CycleCanonicalRootLawActualSearchSameRootAt step.sourceLaw
  nextCycleRootLedgerAndNext :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 1)
    CycleCanonicalRootLawLedgerAndNextAt initial (depth + 1) step.sourceLaw
  nextCycleSelfU8Tick : ExactCanonicalSelfU8TickAt initial (depth + 1)
  nextCycleCompatibleFutureBirth :
    ExactCanonicalCompatibleFutureBirthAt initial observerFuel (depth + 1)

theorem proofCarryingMandateOrdinaryExitConstitution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (exit : MandateOrdinaryExitConstitutionAt initial depth) :
    ProofCarryingMandateOrdinaryExitConstitutionAt initial observerFuel
      depth exit := by
  let pulse := exactCanonicalSocietyRenewalPulseAt initial observerFuel
    (depth + 1)
  exact
    { actionExact := exit.actionExact
      actionReceipt :=
        ⟨exactMandateExitActionReceiptAt initial depth
          (mandateExitActionExactSourceEventAt initial depth) PUnit.unit⟩
      sourceStandingGeneratedNext := by
        rw [exit.standingExact]
        exact standingMandate_generatedNext_eq_actionSource initial depth
      sourceIsNextConstitutionPayment :=
        exit.sourceIsNextConstitutionPayment
      sourceToTargetPayment := exit.sourceToTargetPaymentCommutes
      targetPaymentRestriction := by
        rw [exit.targetPaymentExact]
        rfl
      targetPaymentFactorization := by
        rw [exit.targetPaymentExact]
        exact mandateExitTargetSourceBackedPaymentAt.rootFactorization
      targetMandateFactorization :=
        installedMandateExit.rootAnswerAndNext_factorizes
      targetPowerPhaseRoleTerminal := exit.exact_actual_exit.2
      controllerRelationObligationExact :=
        mandateExit_controller_relation_obligation_exact
      criticalRelationAndControllerProvenance :=
        mandateExitCriticalRelationBearer_exact_provenance
      commonBearerOnly := exit.commonBearerIsExitWorker
      operationalMaterial := exit.operationalMaterial
      firstTargetWriteAndMacroNext := exit.wholeLedgerAndMacroNext
      nextCycleRootLawTransition := pulse.rootLawTransition
      nextCycleActualSearchSameRoot :=
        pulse.rootLawTransition.sourceActualSearchSameRoot
      nextCycleRootLedgerAndNext :=
        pulse.rootLawTransition.sourceRootLedgerAndNext
      nextCycleSelfU8Tick := pulse.selfU8Tick
      nextCycleCompatibleFutureBirth := pulse.compatibleFutureBirth }

theorem sourceGeneratedProofCarryingMandateOrdinaryExitConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    let exit := sourceGeneratedMandateOrdinaryExitConstitutionAt initial depth
    ProofCarryingMandateOrdinaryExitConstitutionAt initial observerFuel
      depth exit :=
  proofCarryingMandateOrdinaryExitConstitution
    (sourceGeneratedMandateOrdinaryExitConstitutionAt initial depth)

end
end M14ProofCarryingMandateOrdinaryExitConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMandateOrdinaryExitConstitution.MandateExitOperationalMaterialAt.directAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMandateOrdinaryExitConstitution.proofCarryingMandateOrdinaryExitConstitution
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMandateOrdinaryExitConstitution.sourceGeneratedProofCarryingMandateOrdinaryExitConstitutionAt
