import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Producer.SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch

/-!
# Source-generated finite exit-capacity constitution

The existing bearer program has one semantic `ExitCapacityRenewalAt`; no new
program is introduced here.  At every recursively generated cycle, the full
paid-exit maximum is equivalent to an explicit constitutional contract whose
right side independently retains source-backed standing and payment,
employment-independent continuation, noncapture, actual route/service,
external residual disposition, the same node's self-U8 authority and its
generated next cycle.

The reverse implication receives no maximum witness.  It reconstructs the
existing maximum contract from these material fields and consumes the
already proved maximum-contract equivalence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Observer UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityDebitedRunFixture
open M3ExchangeSettlementPriceRegression
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPaidExitLifecycleMaximumCharacterization
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism.SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphismAt
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch

/-- Actual-service depth already selected by one cycle's paid lifecycle. -/
def cycleExitCapacityDepthAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Nat :=
  paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth)

/-- The semantic verdict reuses the installed bearer program and its existing
uncaptured actionable exit. -/
def semanticExitCapacityRenewal :
    ExitCapacityRenewalAt birthBearerExitCapacityProgram :=
  ExitCapacityRenewalAt.generate birthBearerActionableExit

/-- Local strongest characterization of that semantic verdict. -/
theorem semanticExitCapacityRenewal_strongest_iff :
    Nonempty (ExitCapacityRenewalAt birthBearerExitCapacityProgram) ↔
      ∃ code,
        code ∈ birthBearerExitRelationCompiler.futureCodeCarrier ∧
        Nonempty (birthBearerExitRelationCompiler.FutureContinuationAt
          birthBearerIndependentExitRelation.1 .target code) ∧
        ¬ birthBearerExitRelationCompiler.futureIdle code ∧
        ¬ birthBearerNoCapture.Captures code :=
  ExitCapacityRenewalAt.nonempty_iff_sourceGeneratedUncapturedContinuation

/-- Semantic material at one actual service slot.  Every field is independent
of the typed lifecycle maximum. -/
structure ExitCapacitySemanticMaterialAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (code : birthBearerExitRelationCompiler.FutureCode)
    (slot : Fin
      (anomiePhaseAt (cycleExitCapacityDepthAt initial depth)).served.length) :
    Prop where
  codeInCarrier : code ∈ birthBearerExitRelationCompiler.futureCodeCarrier
  employmentRelationIndependent :
    birthBearerEmploymentRelation ≠ birthBearerIndependentExitRelation
  employmentIndependentContinuation : Nonempty
    (birthBearerExitRelationCompiler.FutureContinuationAt
      birthBearerIndependentExitRelation.1 .target code)
  nonIdle : ¬ birthBearerExitRelationCompiler.futureIdle code
  uncaptured : ¬ birthBearerNoCapture.Captures code
  sourceBackedPayment : Nonempty
    (SourceBackedUBIPaymentReceiptAt
      birthBearerExitCapacityProgram.purchasingPowerStanding code)
  actualRoute : Nonempty
    (SourceGeneratedUBIRouteReceiptAt code
      (ExactServedCrossingDebitedRunAt.servicedCrossingAt
        (phase := anomiePhaseAt (cycleExitCapacityDepthAt initial depth))
        (crossingCompiler := crossingCompilerAt
          (cycleExitCapacityDepthAt initial depth)) slot))

/-- Root-temporal material indexed by the semantic code. -/
structure ExitCapacityTemporalMaterialAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (code : birthBearerExitRelationCompiler.FutureCode) : Prop where
  occurrenceSpine : PaidExitLifecycleOccurrenceSpineAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth)
  responseExecution : PaidExitLifecycleResponseExecutionAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth)
  roleIndependentContinuation :
    PaidExitLifecycleRoleIndependentContinuationAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth) code
  externalResidual : PaidExitLifecycleExternalDispositionAt oldVisit
    sourceIndex (cycleLifecycleIndex initial depth)
  actualServicesAndFuture : PaidExitLifecycleServicesAndFutureAt oldVisit
    sourceIndex (cycleLifecycleIndex initial depth)
  outerAuthorityInjective : Function.Injective
    (paidExitLifecycleOuterAuthorityAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth))
  actualServiceKInjective : Function.Injective
    (paidExitLifecycleActualServiceKAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth))
  actionReadoutConstant : ∀ stage : PaidExitLifecycleStage,
    paidExitLifecycleActionReadoutAt oldVisit sourceIndex
        (cycleLifecycleIndex initial depth) stage =
      birthBearerExactExitExerciseAction

/-- Explicit constitutional RHS.  The existential binds one semantic renewal
to the same code/slot material used to reconstruct the maximum contract. -/
structure FiniteExitCapacityConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop where
  semanticRenewalIncidence :
    ∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
      ∃ code : birthBearerExitRelationCompiler.FutureCode,
        ∃ slot : Fin
            (anomiePhaseAt
              (cycleExitCapacityDepthAt initial depth)).served.length,
          semanticRenewal.exit.1 = code ∧
            ExitCapacitySemanticMaterialAt initial depth code slot ∧
            ExitCapacityTemporalMaterialAt initial depth code
  sourceBackedStanding :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      residualConsumerCompiler.activationSeedAt
        Lifecycle.actualEventGame.source state
        (PurchasingPowerStandingAt.renewalEvent
          birthBearerExitCapacityProgram.purchasingPowerStanding)
  purchasingPowerNextExact :
    birthBearerExitCapacityProgram.payment.nextGenerated =
      PurchasingPowerStandingAt.nextGeneratedState
        birthBearerExitCapacityProgram.purchasingPowerStanding
  paidRenewalIsLifecycleStageZero :
    paidRenewalAt (cycleMorphism (cycleAt initial depth)) =
      cycleLifecycle initial depth
  sourceEventExact :
    (cycleLifecycle initial depth).sourceConsequence.outerRootEvent =
      (sourceSubmission
        (legislationSpan
          (cycleMorphism (cycleAt initial depth)))).exactEvent
  actualPaymentExact :
    (cycleLifecycle initial depth
      ).sourceConsequence.actualExit.paymentOccurrence =
      targetPaymentOccurrence
        (legislationSpan (cycleMorphism (cycleAt initial depth)))
  selfU8 :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (cycleMorphism (cycleAt initial depth))
  selfU8CoreExact :
    targetCore (cycleMorphism (cycleAt initial depth)) =
      generatedU8CoreAt oldVisit sourceIndex (boundary + depth)
  selfU8RootFactorization :
    (activatedSubmissionAt oldVisit sourceIndex
      (boundary + depth)).RootAnswerAndNextFactorizes
  generatedNextCycle :
    cycleAt initial (depth + 1) = (stepAt initial depth).nextCycle

namespace FiniteExitCapacityConstitutionAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
variable {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}

/-- The semantic verdict and lifecycle material use one literal code. -/
theorem semanticCodeExact
    (constitution : FiniteExitCapacityConstitutionAt initial depth) :
    ∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
      ∃ code : birthBearerExitRelationCompiler.FutureCode,
        semanticRenewal.exit.1 = code := by
  rcases constitution.semanticRenewalIncidence with
    ⟨renewal, code, _slot, codeIncidence, _semantic, _temporal⟩
  exact ⟨renewal, code, codeIncidence⟩

/-- The semantic four-field mouth is a projection, not an assumed verdict. -/
theorem semanticContract
    (constitution : FiniteExitCapacityConstitutionAt initial depth) :
    ∃ code,
      code ∈ birthBearerExitRelationCompiler.futureCodeCarrier ∧
      Nonempty (birthBearerExitRelationCompiler.FutureContinuationAt
        birthBearerIndependentExitRelation.1 .target code) ∧
      ¬ birthBearerExitRelationCompiler.futureIdle code ∧
      ¬ birthBearerNoCapture.Captures code := by
  rcases constitution.semanticRenewalIncidence with
    ⟨_renewal, code, _slot, _codeIncidence, semantic, _temporal⟩
  exact ⟨code, semantic.codeInCarrier,
    semantic.employmentIndependentContinuation,
    semantic.nonIdle, semantic.uncaptured⟩

/-- Named code-incidence projection used by downstream role consumers. -/
theorem roleIndependentCodeExact
    (constitution : FiniteExitCapacityConstitutionAt initial depth) :
    ∃ semanticRenewal : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
      ∃ code : birthBearerExitRelationCompiler.FutureCode,
        semanticRenewal.exit.1 = code ∧
          code =
            (paidExitLifecycleContinuationAt oldVisit sourceIndex
              (cycleLifecycleIndex initial depth)
            ).successorContinuationAction.1 := by
  rcases constitution.semanticRenewalIncidence with
    ⟨renewal, code, _slot, codeIncidence, _semantic, temporal⟩
  exact ⟨renewal, code, codeIncidence,
    temporal.roleIndependentContinuation.codeExact⟩

/-- Hence the explicit constitution regenerates the semantic renewal without
using a lifecycle maximum. -/
theorem semanticRenewalNonempty
    (constitution : FiniteExitCapacityConstitutionAt initial depth) :
    Nonempty (ExitCapacityRenewalAt birthBearerExitCapacityProgram) := by
  rcases constitution.semanticRenewalIncidence with
    ⟨renewal, _code, _slot, _codeIncidence, _semantic, _temporal⟩
  exact ⟨renewal⟩

/-- Reassemble the already defined full maximum contract field by field. -/
theorem maximumContract
    (constitution : FiniteExitCapacityConstitutionAt initial depth) :
    PaidExitLifecycleMaximumContractAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth) := by
  rcases constitution.semanticRenewalIncidence with
    ⟨_renewal, code, slot, _codeIncidence, semantic, temporal⟩
  exact
    ⟨code, slot, semantic.codeInCarrier,
      semantic.employmentIndependentContinuation, semantic.nonIdle,
      semantic.uncaptured, semantic.sourceBackedPayment, semantic.actualRoute,
      { occurrenceSpine := temporal.occurrenceSpine
        responseExecution := temporal.responseExecution
        roleIndependentContinuation := temporal.roleIndependentContinuation
        externalDisposition := temporal.externalResidual
        servicesAndFuture := temporal.actualServicesAndFuture
        outerAuthorityInjective := temporal.outerAuthorityInjective
        actualServiceKInjective := temporal.actualServiceKInjective
        actionReadoutConstant := temporal.actionReadoutConstant }⟩

end FiniteExitCapacityConstitutionAt

/-- Forward extraction from any genuine maximum. -/
theorem constitutionOfMaximum
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (maximum : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) :
    FiniteExitCapacityConstitutionAt initial depth := by
  let renewal := maximum.actionableRenewal
  have generated :=
    (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
      birthBearerNoCapture birthBearerIndependentExitRelation renewal.code).mp
      renewal.feasible.codeSurvives
  let semanticRenewal :
      ExitCapacityRenewalAt birthBearerExitCapacityProgram :=
    ExitCapacityRenewalAt.generate
      ⟨renewal.code, renewal.feasible.codeSurvives⟩
  have semantic : ExitCapacitySemanticMaterialAt initial depth renewal.code
      renewal.slot :=
    { codeInCarrier := generated.1
      employmentRelationIndependent :=
        birthBearerEmployment_ne_independentExit
      employmentIndependentContinuation := generated.2.1
      nonIdle := generated.2.2.1
      uncaptured := generated.2.2.2
      sourceBackedPayment := ⟨renewal.feasible.paymentReceipt⟩
      actualRoute := ⟨renewal.feasible.routeReceipt⟩ }
  have temporal : ExitCapacityTemporalMaterialAt initial depth renewal.code :=
    { occurrenceSpine := maximum.rooted.occurrenceSpine
      responseExecution := maximum.rooted.responseExecution
      roleIndependentContinuation :=
        maximum.rooted.roleIndependentContinuation
      externalResidual := maximum.rooted.externalDisposition
      actualServicesAndFuture := maximum.rooted.servicesAndFuture
      outerAuthorityInjective := maximum.rooted.outerAuthorityInjective
      actualServiceKInjective := maximum.rooted.actualServiceKInjective
      actionReadoutConstant := maximum.rooted.actionReadoutConstant }
  let selfU8 := cycleMorphismCertificate (cycleAt initial depth)
  exact
    { semanticRenewalIncidence :=
        ⟨semanticRenewal, renewal.code, renewal.slot, rfl, semantic, temporal⟩
      sourceBackedStanding :=
        birthBearerExitCapacityProgram.payment_event_mem_source_trace
      purchasingPowerNextExact :=
        birthBearerExitCapacityProgram.payment_next_is_exact_generated
      paidRenewalIsLifecycleStageZero :=
        cycleMorphismPaidRenewal_eq_cycleLifecycle initial depth
      sourceEventExact :=
        cycleLifecycle_sourceEvent_isCycleSpanSourceEvent initial depth
      actualPaymentExact :=
        cycleLifecycle_sourcePayment_isCycleSpanPayment initial depth
      selfU8 := selfU8
      selfU8CoreExact := selfU8.targetCoreExact
      selfU8RootFactorization := selfU8.targetRootFactorization
      generatedNextCycle := cycleAt_succ initial depth }

/-- Strong proof-carrying equivalence.  Its reverse consumes only the explicit
constitutional RHS and the independent maximum-contract theorem. -/
theorem cycleLifecycleMaximum_nonempty_iff_constitution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    Nonempty
        (ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
          (cycleLifecycleIndex initial depth)) ↔
      FiniteExitCapacityConstitutionAt initial depth := by
  constructor
  · rintro ⟨maximum⟩
    exact constitutionOfMaximum initial depth maximum
  · intro constitution
    exact
      (ProofCarryingPaidExitLifecycleMaximumAt.nonempty_iff_maximumContract
        oldVisit sourceIndex (cycleLifecycleIndex initial depth)).mpr
        constitution.maximumContract

/-- Premise-free producer at every recursively generated cycle node. -/
theorem sourceGeneratedFiniteExitCapacityConstitutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    FiniteExitCapacityConstitutionAt initial depth :=
  constitutionOfMaximum initial depth (cycleLifecycleMaximum initial depth)

/-- The full lifecycle contract reaches the program-level semantic verdict
through the semantic strongest iff, with no maximum witness as input. -/
theorem lifecycleMaximumContract_impliesSemanticRenewal
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (contract : PaidExitLifecycleMaximumContractAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)) :
    Nonempty (ExitCapacityRenewalAt birthBearerExitCapacityProgram) := by
  rcases contract with
    ⟨code, _slot, inCarrier, continuation, nonIdle, uncaptured,
      _payment, _route, _rooted⟩
  exact semanticExitCapacityRenewal_strongest_iff.mpr
    ⟨code, inCarrier, continuation, nonIdle, uncaptured⟩

/-- Direct every-node bridge from the generated maximum to the semantic
renewal, retaining the stronger constitution for downstream consumers. -/
theorem cycleLifecycleMaximum_generatesSemanticRenewal
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    Nonempty (ExitCapacityRenewalAt birthBearerExitCapacityProgram) ∧
      FiniteExitCapacityConstitutionAt initial depth := by
  let constitution := sourceGeneratedFiniteExitCapacityConstitutionAt
    initial depth
  exact ⟨constitution.semanticRenewalNonempty, constitution⟩

end
end M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.semanticExitCapacityRenewal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.FiniteExitCapacityConstitutionAt.semanticCodeExact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.FiniteExitCapacityConstitutionAt.roleIndependentCodeExact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.constitutionOfMaximum
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.cycleLifecycleMaximum_nonempty_iff_constitution
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.sourceGeneratedFiniteExitCapacityConstitutionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.lifecycleMaximumContract_impliesSemanticRenewal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution.cycleLifecycleMaximum_generatesSemanticRenewal
