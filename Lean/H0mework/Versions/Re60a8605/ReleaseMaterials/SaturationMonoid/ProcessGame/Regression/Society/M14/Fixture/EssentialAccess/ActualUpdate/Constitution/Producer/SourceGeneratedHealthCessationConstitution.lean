import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Action.SourceGeneratedSequentialHealthCessation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Producer.SourceGeneratedCanonicalSocietyCofinalReadout

/-!
# Source-generated health-cessation Constitution

The existing sequential health action is joined to the high-universe
health/Payment incidence and to the canonical Constitution at `depth + 3`.
The action receipt remains the local receipt of the sequential action: target
terminality, Payment, whole-ledger next, actual/search law, self-U8 and
FutureBirth are Constitution-level dependent faces.

The sole carrier has a private constructor.  Its public producer accepts only
the original cycle, observer fuel and depth; no target root, Payment,
Constitution, terminal disposition or future is supplied by a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedHealthCessationConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost Election
open M3FiniteExchangeFixture
open M8ActualElectionMandateRenewalRegression
open M14EssentialAccessRelationFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14ProofCarryingFiniteCycleCanonicalRootLaw
open M14SourceGeneratedCanonicalSocietyCofinalReadout
open M14SourceInstalledMandateFiniteConstitutionIncidence
open M14SourceMandateRenewal
open M14SourceMandateSuccession
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalTerminal
open M14SourceGeneratedMandateSuccessorTargetRoot
open M14SourceGeneratedSequentialMandateSuccession
open M14SourceHealthCessationRenewal
open M14SourceGeneratedHealthCessationActionSource
open M14SourceGeneratedHealthCessationTargetRoot
open M14SourceGeneratedSequentialHealthCessation
open M9SourceHealthCessationSuffix

/-! ## Canonical operational material at the health depth -/

/-- Existing exit-capacity material selected by the canonical actual-fold
Constitution at `depth + 3`.  No health-specific exit program is introduced. -/
def HealthCessationOperationalMaterialAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  ∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
    ∃ code : birthBearerExitRelationCompiler.FutureCode,
      ∃ slot : Fin
          (anomiePhaseAt
            (cycleExitCapacityDepthAt initial (depth + 3))).served.length,
        semanticRenewal.exit.1 = code ∧
          ExitCapacitySemanticMaterialAt initial (depth + 3) code slot ∧
          ExitCapacityTemporalMaterialAt initial (depth + 3) code

theorem healthCessationOperationalMaterialAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HealthCessationOperationalMaterialAt initial depth :=
  (cycleCanonicalRootLawConstitutionFromActualFold initial (depth + 3)
    ).semanticRenewalIncidence

/-! ## Exact action/target faces -/

/-- Constitution-level faces of the already generated sequential action.
Every object in this proposition is fixed by `initial` and `depth`; no caller
can submit a target root, Payment, disposition or next current. -/
structure HealthCessationActionTargetFacesAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  private mk ::
  targetRootExact :
    (generatedHealthCessationActionAt initial depth).target.targetRoot =
      healthCessationTargetRoot
  sourceToTargetPayment :
    (generatedHealthCessationActionAt initial depth
      ).target.occurrencePresentation.forward
        (healthCessationActionExactSourceEventAt initial depth).occurrence =
      healthCessationTargetSourceBackedPaymentAt.rootOccurrence.occurrence
  targetPaymentFactorization :
    (healthCessationTargetSourceBackedPaymentAt.installed
      ).RootAnswerAndNextFactorizes
  installedHealthConsumerExact :
    installedHealthCessationConsumer = sourceHealthCessationConsumer
  installedHealthDispositionExact :
    installedHealthCessationDisposition = sourceHealthCessationDisposition
  installedHealthUpdateExact :
    installedHealthCessationDisposition.update =
      sourceGeneratedHealthCriticalActualUpdate
  installedHealthFactorization :
    installedHealthCessation.RootAnswerAndNextFactorizes
  successorMandateFaceExact : installedSuccessorMandateLocalFace =
    sourceMandateSuccessorFace
  successorMandateRestored :
    (installedSuccessorMandateLocalFace.responsibilityConsumer.1.1
      ).freedomChange.kind = FreedomChangeKind.restored
  successorMandateLive :
    installedSuccessorMandateLocalFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler
          sourceMandateSuccessorHistory.current).val]? =
      some (.live (mandateObligation lineageCompiler
        sourceMandateSuccessorHistory.current))
  successorMandateFactorization :
    installedSuccessorMandate.RootAnswerAndNextFactorizes
  targetTerminal : ∃ archive,
    (essentialAccessCriticalTerminalAt .health).terminal.target.slots[
        (criticalRelationSlot essentialAccessCriticalBearerOf .health).val]? =
      some (ObligationSlot.terminal archive)
  targetNoReopen : ∀ archive :
      TerminalArchive Lifecycle.LifecycleVocabulary,
    IsEmpty ((criticalRelationTerminalProcess
      essentialAccessCriticalBearerOf).ReopenEvent archive)
  targetOneCoordinate :
    IsEmpty SecondInstalledHealthCessationCoordinate ∧
      healthCessationProjection ≠ mandateProjection ∧
      healthCessationProjection ≠ ubiProjection
  firstWholeLedgerSuccessor :
    (generatedHealthCessationActionAt initial depth).target.firstSuccessor =
      healthCessationTargetFirstSuccessor
  macroNext :
    (generatedHealthCessationActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedHealthCessationActionAt initial depth).target.TargetV,
        (generatedHealthCessationActionAt initial depth
          ).target.targetRoot.toAuthoritativeRoot,
        (generatedHealthCessationActionAt initial depth).target.targetVisit⟩

theorem healthCessationActionTargetFacesAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HealthCessationActionTargetFacesAt initial depth where
  targetRootExact :=
    generatedHealthCessationAction_targetRoot_exact initial depth
  sourceToTargetPayment :=
    generatedHealthCessationAction_targetPayment_commutes initial depth
  targetPaymentFactorization :=
    healthCessationTargetSourceBackedPaymentAt.rootFactorization
  installedHealthConsumerExact := installedHealthCessation_consumer_exact
  installedHealthDispositionExact := installedHealthCessation_disposition_exact
  installedHealthUpdateExact := installedHealthCessation_update_exact
  installedHealthFactorization := installedHealthCessation_factorizes
  successorMandateFaceExact := installedSuccessorMandate_face_exact
  successorMandateRestored := installedSuccessorMandate_power_restored
  successorMandateLive := installedSuccessorMandate_obligation_live
  successorMandateFactorization := installedSuccessorMandate_factorizes
  targetTerminal := installedHealthCessation_terminal
  targetNoReopen := installedHealthCessation_no_reopen
  targetOneCoordinate := target_has_one_healthCessation_coordinate
  firstWholeLedgerSuccessor := rfl
  macroNext := generatedHealthCessationAction_macroNext_exact initial depth

/-! ## Exact source action spine -/

/-- The action token, its local receipt and the source-side UBI/Payment
factorization are kept together below the high-universe incidence carrier.
The receipt is the existing `ULift (PLift provenance)` generated by the
sequential action; this carrier neither changes nor supplements it. -/
structure HealthCessationActionSourceSpineAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  private mk ::
  actionToken : ∃ token : SourceGeneratedSequentialActualActionAt
      (healthCessationActionProgramAt initial depth)
      (healthCessationActionExactSourceEventAt initial depth),
    token = generatedHealthCessationActionAt initial depth
  actionReceipt : Nonempty
    (ExactHealthCessationActionReceiptAt initial depth
      (healthCessationActionExactSourceEventAt initial depth)
      (PUnit.unit : PUnit.{0}))
  sourceIsSuccessionMacroNext :
    (generatedMandateSuccessionActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨M14SourceGeneratedMandateSuccessorTargetRoot.V,
        mandateSuccessorTargetRoot.toAuthoritativeRoot,
        healthCessationActionSourceVisitAt initial depth⟩
  sourceUBI : ∃ installed : SourceInstalledRenewalAt
      mandateSuccessorTargetUBIRecognition
      (healthCessationActionSourceVisitAt initial depth),
    installed = installedHealthCessationSourceUBIAt initial depth ∧
      installed.payload.consumer = sourceGeneratedUBIRootRestriction ∧
      installed.RootAnswerAndNextFactorizes
  sourcePaymentReceipt : ∃ receipt : SourceBackedUBIPaymentReceiptAt
      exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave,
    receipt = healthCessationActionSourcePaymentReceiptAt initial depth

theorem healthCessationActionSourceSpineAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HealthCessationActionSourceSpineAt initial depth :=
  let action := generatedHealthCessationActionAt initial depth
  let sourceUBI := installedHealthCessationSourceUBIAt initial depth
  let sourcePayment := healthCessationActionSourcePaymentReceiptAt initial depth
  { actionToken := ⟨action, rfl⟩
    actionReceipt :=
      ⟨exactHealthCessationActionReceiptAt initial depth
        (healthCessationActionExactSourceEventAt initial depth) PUnit.unit⟩
    sourceIsSuccessionMacroNext :=
      healthCessationActionSource_is_successionMacroNext initial depth
    sourceUBI :=
      ⟨sourceUBI, rfl,
        installedHealthCessationSourceUBI_consumer_exact initial depth,
        installedHealthCessationSourceUBI_factorizes initial depth⟩
    sourcePaymentReceipt := ⟨sourcePayment, rfl⟩ }

/-! ## Zero-choice Constitution producer -/

/-- The source Payment incidence, sequential actual action, target Payment and
canonical depth-three pulse form one dependent Constitution.  The pulse is the
existing root-law/self-U8/FutureBirth pulse, not a stored future. -/
structure SourceGeneratedHealthCessationConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) : Type 32 where
  private mk ::
  paymentIncidence : HealthPaymentConstitutionIncidenceAt initial depth
  paymentIncidenceExact : paymentIncidence =
    healthPaymentConstitutionIncidenceAt initial depth
  actionSourceSpine : HealthCessationActionSourceSpineAt initial depth
  actionSourceSpineExact : actionSourceSpine =
    healthCessationActionSourceSpineAt initial depth
  actionTargetFaces : HealthCessationActionTargetFacesAt initial depth
  operationalMaterial : HealthCessationOperationalMaterialAt initial depth
  canonicalPulse : ExactCanonicalSocietyRenewalPulseAt initial observerFuel
    (depth + 3)

def sourceGeneratedHealthCessationConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (observerFuel depth : Nat) :
    SourceGeneratedHealthCessationConstitutionAt initial observerFuel depth :=
  let incidence := healthPaymentConstitutionIncidenceAt initial depth
  let sourceSpine := healthCessationActionSourceSpineAt initial depth
  { paymentIncidence := incidence
    paymentIncidenceExact := rfl
    actionSourceSpine := sourceSpine
    actionSourceSpineExact := rfl
    actionTargetFaces := healthCessationActionTargetFacesAt initial depth
    operationalMaterial := healthCessationOperationalMaterialAt initial depth
    canonicalPulse :=
      exactCanonicalSocietyRenewalPulseAt initial observerFuel (depth + 3) }

theorem everyHealthCessationDepth_generatesConstitution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) :
    ∀ observerFuel depth,
      Nonempty
        (SourceGeneratedHealthCessationConstitutionAt initial observerFuel
          depth) :=
  fun observerFuel depth =>
    ⟨sourceGeneratedHealthCessationConstitutionAt initial observerFuel depth⟩

namespace SourceGeneratedHealthCessationConstitutionAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
variable {initial : CycleAt oldVisit sourceIndex boundary}
variable {observerFuel depth : Nat}
variable (constitution : SourceGeneratedHealthCessationConstitutionAt initial
  observerFuel depth)

/-- The high-universe incidence carries the exact health action and `.t2`
bearer.  Its power and both relation/action provenance witnesses remain the
source-generated critical action, and `.t2` is not the tenure bearer. -/
theorem exact_health_authority :
    constitution.paymentIncidence.healthAction.loss.power.freedomChange =
        ActionableFreedomChange.lost .health
          healthCriticalAction_sourceActionable
          healthCriticalAction_targetAbsent ∧
      constitution.paymentIncidence.healthAction.criticalBearer.commonBearer =
        constitution.paymentIncidence.healthBearer ∧
      constitution.paymentIncidence.healthBearer =
        Lifecycle.ActorBearer.target .t2 ∧
      constitution.paymentIncidence.healthBearer ≠
        Lifecycle.ActorBearer.target .t1 ∧
      essentialAccessRelationCompiler.phaseStep healthRelation = .health ∧
      essentialAccessRelationCompiler.roleAt healthRelation .target =
        .healthProvider ∧
      (∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
        (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
          state = Lifecycle.Universal.FixedAdapter.targetFace.state
              Lifecycle.actualEventGame.source ∧
          essentialAccessRelationCompiler.relationSeedAt
              Lifecycle.actualEventGame.source state seed.1 ∧
          Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
              Lifecycle.actualEventGame.source state
              (essentialAccessRelationCompiler.beneficiaryActorSeed seed.1)) ∧
        seed.actor essentialAccessRelationCompiler = healthActor ∧
        essentialAccessRelationCompiler.relationOf seed = healthRelation) ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = (essentialAccessCriticalActionController .health).actionState
            Lifecycle.actualEventGame.source ∧
        (essentialAccessCriticalActionController .health).actionAdmittedAt
          constitution.paymentIncidence.healthAction.loss.power.action.1) := by
  have bearerIncidence :=
    constitution.paymentIncidence.criticalBearerIsHealthBearer
  rw [constitution.paymentIncidence.healthActionExact,
    constitution.paymentIncidence.healthBearerExact] at bearerIncidence ⊢
  exact
    ⟨healthCriticalAction_freedomLoss_exact, bearerIncidence, rfl,
      healthCriticalBearer_ne_t1, healthCriticalAction_phase_exact,
      healthCriticalAction_targetRole_exact,
      healthCriticalAction_exact_provenance.1,
      healthCriticalAction_exact_provenance.2⟩

include constitution

/-- The Constitution consumes the actual-action token and its local receipt,
then keeps the succession macro next, source-installed UBI restriction,
source Payment receipt and root factorization as one dependent source spine. -/
theorem actionSourceTokenReceiptAndFactorization :
    (∃ token : SourceGeneratedSequentialActualActionAt
        (healthCessationActionProgramAt initial depth)
        (healthCessationActionExactSourceEventAt initial depth),
      token = generatedHealthCessationActionAt initial depth) ∧
      Nonempty
        (ExactHealthCessationActionReceiptAt initial depth
          (healthCessationActionExactSourceEventAt initial depth)
          (PUnit.unit : PUnit.{0})) ∧
      (generatedMandateSuccessionActionAt initial depth
        ).target.targetAnswerAndNext.nextCurrent =
        ⟨M14SourceGeneratedMandateSuccessorTargetRoot.V,
          mandateSuccessorTargetRoot.toAuthoritativeRoot,
          healthCessationActionSourceVisitAt initial depth⟩ ∧
      (∃ installed : SourceInstalledRenewalAt
          mandateSuccessorTargetUBIRecognition
          (healthCessationActionSourceVisitAt initial depth),
        installed = installedHealthCessationSourceUBIAt initial depth ∧
          installed.payload.consumer = sourceGeneratedUBIRootRestriction ∧
          installed.RootAnswerAndNextFactorizes) ∧
      (∃ receipt : SourceBackedUBIPaymentReceiptAt
          exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave,
        receipt =
          healthCessationActionSourcePaymentReceiptAt initial depth) :=
  ⟨constitution.actionSourceSpine.actionToken,
    constitution.actionSourceSpine.actionReceipt,
    constitution.actionSourceSpine.sourceIsSuccessionMacroNext,
    constitution.actionSourceSpine.sourceUBI,
    constitution.actionSourceSpine.sourcePaymentReceipt⟩

/-- Target terminality is tied to the target root of this exact sequential
action.  The terminal archive cannot be reopened and the target inventory has
one health-cessation coordinate. -/
theorem target_terminal_noReopen_oneCoordinate :
    (generatedHealthCessationActionAt initial depth).target.targetRoot =
        healthCessationTargetRoot ∧
      installedHealthCessationConsumer = sourceHealthCessationConsumer ∧
      installedHealthCessationDisposition = sourceHealthCessationDisposition ∧
      installedHealthCessationDisposition.update =
        sourceGeneratedHealthCriticalActualUpdate ∧
      installedHealthCessation.RootAnswerAndNextFactorizes ∧
      installedSuccessorMandateLocalFace = sourceMandateSuccessorFace ∧
      (installedSuccessorMandateLocalFace.responsibilityConsumer.1.1
        ).freedomChange.kind = FreedomChangeKind.restored ∧
      installedSuccessorMandateLocalFace.exactDisposition.1.target.slots[
          (mandateSlot lineageCompiler
            sourceMandateSuccessorHistory.current).val]? =
        some (.live (mandateObligation lineageCompiler
          sourceMandateSuccessorHistory.current)) ∧
      installedSuccessorMandate.RootAnswerAndNextFactorizes ∧
      (∃ archive,
        (essentialAccessCriticalTerminalAt .health).terminal.target.slots[
            (criticalRelationSlot essentialAccessCriticalBearerOf
              .health).val]? = some (ObligationSlot.terminal archive)) ∧
      (∀ archive : TerminalArchive Lifecycle.LifecycleVocabulary,
        IsEmpty ((criticalRelationTerminalProcess
          essentialAccessCriticalBearerOf).ReopenEvent archive)) ∧
      IsEmpty SecondInstalledHealthCessationCoordinate ∧
      M9SourceHealthCessationSuffix.healthCessationProjection ≠
        M9SourceHealthCessationSuffix.mandateProjection ∧
      M9SourceHealthCessationSuffix.healthCessationProjection ≠
        M9SourceHealthCessationSuffix.ubiProjection := by
  exact
    ⟨(constitution.actionTargetFaces).targetRootExact,
      (constitution.actionTargetFaces).installedHealthConsumerExact,
      (constitution.actionTargetFaces).installedHealthDispositionExact,
      (constitution.actionTargetFaces).installedHealthUpdateExact,
      (constitution.actionTargetFaces).installedHealthFactorization,
      (constitution.actionTargetFaces).successorMandateFaceExact,
      (constitution.actionTargetFaces).successorMandateRestored,
      (constitution.actionTargetFaces).successorMandateLive,
      (constitution.actionTargetFaces).successorMandateFactorization,
      (constitution.actionTargetFaces).targetTerminal,
      (constitution.actionTargetFaces).targetNoReopen,
      (constitution.actionTargetFaces).targetOneCoordinate.1,
      (constitution.actionTargetFaces).targetOneCoordinate.2.1,
      (constitution.actionTargetFaces).targetOneCoordinate.2.2⟩

/-- The canonical depth-three Payment is carried through the source
presentation into the exact action source, then into the target Payment.  The
same target supplies its Payment factorization, first whole-ledger successor
and macro next. -/
theorem targetPayment_wholeLedgerAndMacroNext :
    (healthCessationConstitutionSourcePresentationAt initial depth).forward
        (canonicalConstitutionEmbeddedPaymentAt initial (depth + 3)
          ).rootOccurrence.occurrence =
      (healthCessationActionExactSourceEventAt initial depth).occurrence ∧
    (generatedHealthCessationActionAt initial depth
      ).target.occurrencePresentation.forward
        (healthCessationActionExactSourceEventAt initial depth).occurrence =
      healthCessationTargetSourceBackedPaymentAt.rootOccurrence.occurrence ∧
    (healthCessationTargetSourceBackedPaymentAt.installed
      ).RootAnswerAndNextFactorizes ∧
    (generatedHealthCessationActionAt initial depth).target.firstSuccessor =
        healthCessationTargetFirstSuccessor ∧
    (generatedHealthCessationActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedHealthCessationActionAt initial depth).target.TargetV,
        (generatedHealthCessationActionAt initial depth
          ).target.targetRoot.toAuthoritativeRoot,
        (generatedHealthCessationActionAt initial depth).target.targetVisit⟩ := by
  exact
    ⟨(constitution.paymentIncidence).constitutionToSourcePayment,
      (constitution.actionTargetFaces).sourceToTargetPayment,
      (constitution.actionTargetFaces).targetPaymentFactorization,
      (constitution.actionTargetFaces).firstWholeLedgerSuccessor,
      (constitution.actionTargetFaces).macroNext⟩

/-- The operational Constitution, actual/search exhaustion, self-U8 and
compatible FutureBirth are projections of one canonical pulse at exactly
`depth + 3`. -/
theorem canonicalDepthThree :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 3)
    HealthCessationOperationalMaterialAt initial depth ∧
      CycleCanonicalRootLawGrammarExhaustionAt initial (depth + 3)
        step.sourceLaw ∧
      CycleCanonicalRootLawActualSearchSameRootAt step.sourceLaw ∧
      ExactCanonicalSelfU8TickAt initial (depth + 3) ∧
      ExactCanonicalCompatibleFutureBirthAt initial observerFuel
        (depth + 3) := by
  let step := sourceGeneratedCycleCanonicalRootLawStep initial (depth + 3)
  exact
    ⟨constitution.operationalMaterial,
      ((constitution.canonicalPulse).rootLawTransition
        ).sourceGrammarExhaustion,
      ((constitution.canonicalPulse).rootLawTransition
        ).sourceActualSearchSameRoot,
      (constitution.canonicalPulse).selfU8Tick,
      (constitution.canonicalPulse).compatibleFutureBirth⟩

end SourceGeneratedHealthCessationConstitutionAt

end
end M14SourceGeneratedHealthCessationConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationConstitution.healthCessationOperationalMaterialAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationConstitution.sourceGeneratedHealthCessationConstitutionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationConstitution.SourceGeneratedHealthCessationConstitutionAt.exact_health_authority
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationConstitution.SourceGeneratedHealthCessationConstitutionAt.actionSourceTokenReceiptAndFactorization
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationConstitution.SourceGeneratedHealthCessationConstitutionAt.target_terminal_noReopen_oneCoordinate
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationConstitution.SourceGeneratedHealthCessationConstitutionAt.targetPayment_wholeLedgerAndMacroNext
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationConstitution.SourceGeneratedHealthCessationConstitutionAt.canonicalDepthThree
