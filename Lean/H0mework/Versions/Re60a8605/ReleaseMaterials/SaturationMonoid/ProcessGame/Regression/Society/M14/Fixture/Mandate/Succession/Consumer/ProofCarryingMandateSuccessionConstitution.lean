import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Succession.NoGo.SourceGeneratedMandateSuccessionNoGo
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Ordinary.CrossCompiler.Mandate.Exit.Consumer.ProofCarryingMandateOrdinaryExitConstitution
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Producer.SourceGeneratedCanonicalSocietyCofinalReadout

/-!
# Proof-carrying mandate succession

The consumer eliminates the full ordinary-exit proof, the generated post-exit
occurrence, the second actual-action receipt and the next finite Constitution.
It exposes terminal retention and new admission simultaneously without
reopening one obligation, and carries Payment, route/services/future,
external residual, K, whole-ledger next, actual/search separation, self-U8 and
FutureBirth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingMandateSuccessionConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost Election
open M3FiniteExchangeFixture
open M8ActualElectionMandateRenewalRegression
open M14UBIPeriodicActualServiceCapacity
open M14UBIProofCarryingRootRestriction
open M14UBIExitCapacityFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14ProofCarryingFiniteCycleCanonicalRootLaw
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14SourceInstalledMandateFiniteConstitutionIncidence
open M14SourceMandateRenewal
open M14SourceMandateSuccession
open M14SourceGeneratedMandateExitTargetRoot
open M14SourceGeneratedMandateExitTargetHistory
open M14SourceGeneratedSequentialMandateExit
open M14SourceGeneratedPostExitTerminalContinuation
open M14SourceGeneratedMandateSuccessorTargetRoot
open M14SourceGeneratedMandateSuccessionActionSource
open M14SourceGeneratedSequentialMandateSuccession
open M14SourceGeneratedMandateOrdinaryExitConstitution
open M14ProofCarryingMandateOrdinaryExitConstitution
open M14SourceGeneratedMandateSuccessionConstitution
open M14SourceGeneratedMandateSuccessionNoGo

theorem MandateSuccessionOperationalMaterialAt.directAuthority
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (material : MandateSuccessionOperationalMaterialAt initial depth) :
    ∃ code : birthBearerExitRelationCompiler.FutureCode,
      ∃ slot : Fin
          (anomiePhaseAt
            (cycleExitCapacityDepthAt initial (depth + 2))).served.length,
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
                  (cycleExitCapacityDepthAt initial (depth + 2)))
                (crossingCompiler := crossingCompilerAt
                  (cycleExitCapacityDepthAt initial (depth + 2))) slot)) ∧
          PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex
            (cycleLifecycleIndex initial (depth + 2)) ∧
          PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex
            (cycleLifecycleIndex initial (depth + 2)) ∧
          Function.Injective
            (paidExitLifecycleActualServiceKAt oldVisit sourceIndex
              (cycleLifecycleIndex initial (depth + 2))) := by
  rcases material with
    ⟨_renewal, code, slot, _exact, semantic, temporal⟩
  exact
    ⟨code, slot, semantic.codeInCarrier,
      semantic.employmentIndependentContinuation, semantic.nonIdle,
      semantic.uncaptured, semantic.sourceBackedPayment, semantic.actualRoute,
      temporal.externalResidual, temporal.actualServicesAndFuture,
      temporal.actualServiceKInjective⟩

structure ProofCarryingMandateSuccessionConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat)
    (succession : MandateSuccessionConstitutionAt initial depth) : Prop where
  private mk ::
  exitConsumer : ProofCarryingMandateOrdinaryExitConstitutionAt initial
    observerFuel depth succession.exit
  successionNoGo : MandateSuccessionNoGoAt initial depth
  actionExact : succession.successionAction =
    generatedMandateSuccessionActionAt initial depth
  actionReceipt : Nonempty (ExactMandateSuccessionActionReceiptAt
    initial depth (mandateSuccessionActionExactSourceEventAt initial depth)
      (PUnit.unit : PUnit.{0}))
  sourceIsExitMacroNext :
    (generatedMandateExitActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨M14SourceGeneratedMandateExitTargetRoot.V,
        mandateExitTargetRoot.toAuthoritativeRoot,
        mandateSuccessionActionSourceVisitAt initial depth⟩
  sourcePostExitOccurrence : HEq
    (mandateSuccessionActionExactSourceEventAt initial depth)
    succession.postExit.rootOccurrence
  sourceTerminalAndPayment :
    (∃ archive,
      succession.postExit.mandateFace.exactDisposition.1.target.slots[
          (mandateSlot lineageCompiler
            sourceMandateExitHistory.current).val]? =
        some (.terminal archive)) ∧
      Nonempty PostExitSourceBackedPaymentAt ∧
      succession.postExit.installedMandate.RootAnswerAndNextFactorizes
  constitutionToPostExitPayment :
    (mandateSuccessionConstitutionPresentationAt initial depth).forward
        (canonicalConstitutionEmbeddedPaymentAt initial (depth + 2)
          ).rootOccurrence.occurrence =
      succession.postExit.payment.rootOccurrence.occurrence
  postExitToTargetPayment :
    succession.successionAction.target.occurrencePresentation.forward
        (mandateSuccessionActionExactSourceEventAt initial depth).occurrence =
      succession.targetPayment.rootOccurrence.occurrence
  controllerFoldUnique : ∀
      (candidate : RootedAccountedUnfolding ActualEvent → Nat),
    (∀ (origin : ActualEvent) (branches : AccountedBranches ActualEvent),
      candidate (.occur origin branches) =
        sourceMandateControllerMaximumAlgebra origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) →
      candidate sourceMandateExitHistory.occurrence =
        sourceMandateExitControllerMaximum
  targetTraceAndFreshController :
    sourceMandateExitHistory.current ∈
        sourceMandateSuccessorHistory.occurrence.trace ∧
      installedMandateSuccessorLocalFace.actor.1 =
        sourceMandateExitControllerMaximum + 1 ∧
      installedMandateSuccessorLocalFace.actor.1 ≠
        sourceMandateHistory.current.controllerSeed ∧
      installedMandateSuccessorLocalFace.actor.1 ≠
        sourceMandateExitHistory.current.controllerSeed
  targetRelationProvenance :
    OfficeRelationTraceAt sourceMandateSuccessorHistory
  targetPowerPhaseRole :
    (installedMandateSuccessorLocalFace.responsibilityConsumer.1.1
      ).freedomChange.kind = FreedomChangeKind.restored ∧
      (officeControllerRelationCompiler sourceMandateSuccessorHistory
        lineageCompiler).phaseStep
          (generatedOfficeControllerRelation sourceMandateSuccessorHistory
            lineageCompiler) = MandatePhase.renew ∧
      (officeControllerRelationCompiler sourceMandateSuccessorHistory
        lineageCompiler).roleAt
          (generatedOfficeControllerRelation sourceMandateSuccessorHistory
            lineageCompiler) .target = MandateRole.held
  targetAdmissionNotReopen :
    sourceMandateSuccessorAdmissionEdge.lifecycleEvent.kind =
        LifecycleKind.admitted ∧
      ∀ archive : TerminalArchive (mandateVocabulary lineageCompiler),
        IsEmpty ((mandateProcess lineageCompiler).ReopenEvent archive)
  oneSlotReplacement :
    (mandateSlot lineageCompiler sourceMandateExitHistory.current).val =
        (mandateSlot lineageCompiler
          sourceMandateSuccessorHistory.current).val ∧
      mandateObligation lineageCompiler sourceMandateExitHistory.current ≠
        mandateObligation lineageCompiler
          sourceMandateSuccessorHistory.current ∧
      installedMandateSuccessorLocalFace.exactDisposition.1.target.slots[
          (mandateSlot lineageCompiler
            sourceMandateSuccessorHistory.current).val]? =
        some (.live (mandateObligation lineageCompiler
          sourceMandateSuccessorHistory.current))
  successorCoordinateSeparation : SuccessorMandateCoordinateSeparation
  targetFactorizations :
    installedMandateSuccessor.RootAnswerAndNextFactorizes ∧
      succession.targetPayment.installed.RootAnswerAndNextFactorizes
  operationalAuthority :
    ∃ code : birthBearerExitRelationCompiler.FutureCode,
      ∃ slot : Fin
          (anomiePhaseAt
            (cycleExitCapacityDepthAt initial (depth + 2))).served.length,
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
                  (cycleExitCapacityDepthAt initial (depth + 2)))
                (crossingCompiler := crossingCompilerAt
                  (cycleExitCapacityDepthAt initial (depth + 2))) slot)) ∧
          PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex
            (cycleLifecycleIndex initial (depth + 2)) ∧
          PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex
            (cycleLifecycleIndex initial (depth + 2)) ∧
          Function.Injective
            (paidExitLifecycleActualServiceKAt oldVisit sourceIndex
              (cycleLifecycleIndex initial (depth + 2)))
  firstTargetWriteAndMacroNext :
    succession.successionAction.target.firstSuccessor =
        mandateSuccessorTargetFirstSuccessor ∧
      succession.successionAction.target.targetAnswerAndNext.nextCurrent =
        ⟨succession.successionAction.target.TargetV,
          succession.successionAction.target.targetRoot.toAuthoritativeRoot,
          succession.successionAction.target.targetVisit⟩
  nextCycleRootLawTransition :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 2)
    ProofCarryingCycleCanonicalRootLawTransitionAt initial observerFuel
      (depth + 2) step
  nextCycleActualSearchSameRoot :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 2)
    CycleCanonicalRootLawActualSearchSameRootAt step.sourceLaw
  nextCycleRootLedgerAndNext :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 2)
    CycleCanonicalRootLawLedgerAndNextAt initial (depth + 2) step.sourceLaw
  nextCycleSelfU8Tick : ExactCanonicalSelfU8TickAt initial (depth + 2)
  nextCycleCompatibleFutureBirth :
    ExactCanonicalCompatibleFutureBirthAt initial observerFuel (depth + 2)
  noCompletedFuture :
    ¬ ∃ occurrence : AnyMandateSuccessionActionOccurrenceAt initial,
      ∀ futureDepth : Nat,
        mandateSuccessionActionOccurrenceAt initial futureDepth = occurrence

theorem proofCarryingMandateSuccessionConstitution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {observerFuel depth : Nat}
    (succession : MandateSuccessionConstitutionAt initial depth) :
    ProofCarryingMandateSuccessionConstitutionAt initial observerFuel depth
      succession := by
  let pulse := exactCanonicalSocietyRenewalPulseAt initial observerFuel
    (depth + 2)
  exact
    { exitConsumer :=
        proofCarryingMandateOrdinaryExitConstitution succession.exit
      successionNoGo := sourceGeneratedMandateSuccessionNoGoAt initial depth
      actionExact := succession.successionActionExact
      actionReceipt :=
        ⟨exactMandateSuccessionActionReceiptAt initial depth
          (mandateSuccessionActionExactSourceEventAt initial depth)
            PUnit.unit⟩
      sourceIsExitMacroNext :=
        mandateSuccessionActionSource_is_exitMacroNext initial depth
      sourcePostExitOccurrence := by
        rw [succession.postExitExact]
        exact mandateSuccessionActionSource_consumes_postExitOccurrence
          initial depth
      sourceTerminalAndPayment :=
        ⟨succession.retainedTerminal, ⟨succession.postExit.payment⟩,
          succession.postExit.mandateRootFactorization⟩
      constitutionToPostExitPayment :=
        succession.constitutionToPostExitPayment
      postExitToTargetPayment := succession.postExitToTargetPayment
      controllerFoldUnique := fun candidate commutes =>
        sourceMandateExitControllerMaximum_fold_unique candidate commutes
      targetTraceAndFreshController :=
        ⟨installedMandateSuccessor_retains_exit_trace, rfl,
          succession.freshController.1, succession.freshController.2⟩
      targetRelationProvenance :=
        sourceMandateSuccessor_office_relation_has_exact_trace
      targetPowerPhaseRole :=
        ⟨installedMandateSuccessor_power_restored,
          installedMandateSuccessor_phase_renew,
          installedMandateSuccessor_role_held⟩
      targetAdmissionNotReopen :=
        ⟨sourceMandateSuccessorAdmissionEdge_kind,
          sourceMandateSuccessor_has_no_terminal_reopen⟩
      oneSlotReplacement :=
        ⟨succession.sameSlotOrdinal, succession.distinctObligation,
          succession.successorLive⟩
      successorCoordinateSeparation :=
        succession.successorCoordinateSeparation
      targetFactorizations :=
        ⟨installedMandateSuccessor.rootAnswerAndNext_factorizes, by
          rw [succession.targetPaymentExact]
          exact mandateSuccessorTargetSourceBackedPaymentAt.rootFactorization⟩
      operationalAuthority :=
        MandateSuccessionOperationalMaterialAt.directAuthority
          succession.operationalMaterial
      firstTargetWriteAndMacroNext := succession.wholeLedgerAndMacroNext
      nextCycleRootLawTransition := pulse.rootLawTransition
      nextCycleActualSearchSameRoot :=
        pulse.rootLawTransition.sourceActualSearchSameRoot
      nextCycleRootLedgerAndNext :=
        pulse.rootLawTransition.sourceRootLedgerAndNext
      nextCycleSelfU8Tick := pulse.selfU8Tick
      nextCycleCompatibleFutureBirth := pulse.compatibleFutureBirth
      noCompletedFuture :=
        no_single_mandateSuccessionAction_occurrence_carries_all_depths
          initial }

theorem sourceGeneratedProofCarryingMandateSuccessionConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    let succession :=
      sourceGeneratedMandateSuccessionConstitutionAt initial depth
    ProofCarryingMandateSuccessionConstitutionAt initial observerFuel depth
      succession :=
  proofCarryingMandateSuccessionConstitution
    (sourceGeneratedMandateSuccessionConstitutionAt initial depth)

end
end M14ProofCarryingMandateSuccessionConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMandateSuccessionConstitution.MandateSuccessionOperationalMaterialAt.directAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMandateSuccessionConstitution.proofCarryingMandateSuccessionConstitution
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingMandateSuccessionConstitution.sourceGeneratedProofCarryingMandateSuccessionConstitutionAt
