import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.NoGo.SourceGeneratedCycleCanonicalRootLawStepNoGo

/-!
# Proof-carrying finite canonical root law

Every requested edge consumes the stored source and target universal Society
grammars, their actual/search exhaustion, projection coverage, whole-ledger
factorization, exact Payment restrictions, root-law commuting seams and all
negative controls.  The edge at `fuel + 1` is generated on demand and exposes
the law at `fuel + 2`.

`PaidCanonicalPrefixAt` is only a retrospective proposition over `Fin`; this
file introduces no state function, list, history, schedule, registry or
completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingFiniteCycleCanonicalRootLaw

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14SourceGeneratedCycleCanonicalRootLawStepNoGo

/-! ## Exact stored-law consumers -/

/-- Actual/search classification, no-dormant coverage and projection
exhaustion consumed from one stored universal Society grammar. -/
structure CycleCanonicalRootLawGrammarExhaustionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (law : CycleCanonicalRootLawAt initial depth) : Prop where
  private mk ::
  actualCanonical :
    universalSocietyActualCompiledAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth) =
      SourceNativeUniversalRootGrammarDispositionAt.canonical
        (universalSocietyExpectedActualPassedAt oldVisit sourceIndex
          (cycleCanonicalRootLawIndex initial depth))
  searchFailed :
    universalSocietyFullCaptureSearchCompiledAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth) =
      SourceNativeUniversalRootGrammarDispositionAt.failed
        (universalSocietyFullCaptureSearchFailureAuditAt oldVisit sourceIndex
          (cycleCanonicalRootLawIndex initial depth))
  actualNoDormant : ∀ face : PostSettlementSocietyBearingFace,
    ∃! point :
        (universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
          (universalSocietyVisitAt oldVisit sourceIndex
            (cycleCanonicalRootLawIndex initial depth)),
      point ∈ ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex
            (cycleCanonicalRootLawIndex initial depth))).trace ∧
        point.scenario = .actual ∧ point.face = face
  searchNoDormant : ∀ face : PostSettlementSocietyBearingFace,
    ∃! point :
        (universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
          (universalSocietyVisitAt oldVisit sourceIndex
            (cycleCanonicalRootLawIndex initial depth)),
      point ∈ ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex
            (cycleCanonicalRootLawIndex initial depth))).trace ∧
        point.scenario = .fullCaptureSearch ∧ point.face = face
  everyRootProjectionCovered : ∀ projection :
      ContributionCapacityPostSettlementRenewalProjection,
    projection = .installedSocietyGrammar ∨
      ∃ face : PostSettlementSocietyBearingFace,
        projection = universalSocietyRootProjectionOfBearingFace face
  searchHasNoActualWrite : IsEmpty
    (SourceNativeScenarioActualWriteAuthorityAt
      (postSettlementSocietyVocabulary oldVisit sourceIndex)
      .fullCaptureSearch)

theorem cycleCanonicalRootLawGrammarExhaustionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (law : CycleCanonicalRootLawAt initial depth) :
    CycleCanonicalRootLawGrammarExhaustionAt initial depth law where
  actualCanonical := law.actualCanonical
  searchFailed := law.searchFailed
  actualNoDormant := law.actualNoDormant
  searchNoDormant := law.searchNoDormant
  everyRootProjectionCovered := law.everyRootProjectionCovered
  searchHasNoActualWrite := law.searchHasNoActualWrite

/-- Actual and search are restrictions of one exact root event and observe
one whole-ledger write and one generated next, while only actual may write. -/
def CycleCanonicalRootLawActualSearchSameRootAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (law : CycleCanonicalRootLawAt initial depth) : Prop :=
  law.actualGrammar.exactEvent = law.searchGrammar.exactEvent ∧
    law.actualGrammar.wholeLedgerWriteBack =
      law.searchGrammar.wholeLedgerWriteBack ∧
    law.actualGrammar.generatedNext = law.searchGrammar.generatedNext

theorem cycleCanonicalRootLawActualSearchSameRootAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (law : CycleCanonicalRootLawAt initial depth) :
    CycleCanonicalRootLawActualSearchSameRootAt law :=
  ⟨rfl, rfl, rfl⟩

/-- Exact root occurrence, installed projection, whole-ledger row and
generated-next factorization carried by one stored law. -/
def CycleCanonicalRootLawLedgerAndNextAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (law : CycleCanonicalRootLawAt initial depth) : Prop :=
  let evolution := cycleCanonicalRootLawEvolutionAt initial depth
  evolution.generated =
      (CycleCanonicalLivingRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          (universalSocietyVisitAt oldVisit sourceIndex
            (cycleCanonicalRootLawIndex initial depth)) ∧
    HEq (evolution.generated.projectionOutcome
        (universalSocietyRecognitionAt oldVisit sourceIndex).rootProjection)
      ((universalSocietyRecognitionAt oldVisit sourceIndex).installedFiberAt
        (universalSocietyVisitAt oldVisit sourceIndex
          (cycleCanonicalRootLawIndex initial depth))) ∧
    HEq law.actualGrammar.wholeLedgerWriteBack
      ((CycleCanonicalLivingRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (universalSocietyVisitAt oldVisit sourceIndex
            (cycleCanonicalRootLawIndex initial depth)).current) ∧
    evolution.nextCurrent = law.actualGrammar.generatedNext

theorem cycleCanonicalRootLawLedgerAndNextAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (law : CycleCanonicalRootLawAt initial depth) :
    CycleCanonicalRootLawLedgerAndNextAt initial depth law :=
  law.rootLedgerAndNext

/-! ## One complete transition consumer -/

/-- Direct consumer of the cross-family root-law step.  Both full stored laws
are unfolded here; downstream never has to trust that coverage was merely
present somewhere inside the producer. -/
structure ProofCarryingCycleCanonicalRootLawTransitionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (observerFuel depth : Nat)
    (step : SourceGeneratedCycleCanonicalRootLawStepAt initial depth) : Prop where
  private mk ::
  sourceGrammarExhaustion :
    CycleCanonicalRootLawGrammarExhaustionAt initial depth step.sourceLaw
  targetGrammarExhaustion :
    CycleCanonicalRootLawGrammarExhaustionAt initial (depth + 1) step.targetLaw
  sourceActualSearchSameRoot :
    CycleCanonicalRootLawActualSearchSameRootAt step.sourceLaw
  targetActualSearchSameRoot :
    CycleCanonicalRootLawActualSearchSameRootAt step.targetLaw
  sourceRootLedgerAndNext :
    CycleCanonicalRootLawLedgerAndNextAt initial depth step.sourceLaw
  targetRootLedgerAndNext :
    CycleCanonicalRootLawLedgerAndNextAt initial (depth + 1) step.targetLaw
  sourceConstitution : FiniteExitCapacityConstitutionAt initial depth
  targetConstitution : FiniteExitCapacityConstitutionAt initial (depth + 1)
  everyPaymentRestriction : ∀ payment :
      CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth),
    CycleCanonicalPaymentRootRestrictionAt initial depth step.sourceLaw
      step.targetLaw observerFuel payment
  sourceGeneratedEventExact : HEq
    (cycleCanonicalRootLawEvolutionAt initial depth).generated
    (step.sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.successorRootEvent
  sourceGeneratedWholeLedgerExact : HEq
    (cycleCanonicalRootLawEvolutionAt initial depth
      ).generated.wholeLedgerWriteBack
    (step.sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.successorRootEvent.wholeLedgerWriteBack
  sourceRootNativeWriteExact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile
        (cycleCanonicalRootLawEvolutionAt initial depth).generated.occurrence =
      .nativeWrite
        (step.sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
          ).continuation.successorPayment.write
  sourceSecondPaidNextHitsGeneratedOccurrence : HEq
    (step.sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.executedPayment.nextPaidBy
    (cycleCanonicalRootLawEvolutionAt initial depth).generated.occurrence
  grammarThirdPaidNextHitsTargetLawActualEvent : HEq
    (step.sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.successorPayment.nextPaidBy
    step.targetLaw.actualGrammar.exactEvent.occurrence
  sourceRootNextIsActualGrammarNext :
    (cycleCanonicalRootLawEvolutionAt initial depth).nextCurrent =
      step.sourceLaw.actualGrammar.generatedNext
  grammarActualNextIsTargetRootLawCurrent :
    step.sourceLaw.actualGrammar.generatedNext =
      cycleCanonicalRootLawAuthoritativeCurrentAt initial (depth + 1)
  fixedLawSurfacePreserved :
    ((cycleCanonicalRootLawEvolutionAt initial depth).nextCurrent
      ).root.source.lawSurface =
      (CycleCanonicalLivingRootAt oldVisit sourceIndex).source.base.lawSurface
  rootLawNoGo : CycleCanonicalRootLawStepNoGoAt initial depth

theorem proofCarryingCycleCanonicalRootLawTransition
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (observerFuel : Nat)
    (step : SourceGeneratedCycleCanonicalRootLawStepAt initial depth) :
    ProofCarryingCycleCanonicalRootLawTransitionAt initial observerFuel depth
      step where
  sourceGrammarExhaustion :=
    cycleCanonicalRootLawGrammarExhaustionAt step.sourceLaw
  targetGrammarExhaustion :=
    cycleCanonicalRootLawGrammarExhaustionAt step.targetLaw
  sourceActualSearchSameRoot :=
    cycleCanonicalRootLawActualSearchSameRootAt step.sourceLaw
  targetActualSearchSameRoot :=
    cycleCanonicalRootLawActualSearchSameRootAt step.targetLaw
  sourceRootLedgerAndNext :=
    cycleCanonicalRootLawLedgerAndNextAt step.sourceLaw
  targetRootLedgerAndNext :=
    cycleCanonicalRootLawLedgerAndNextAt step.targetLaw
  sourceConstitution := step.sourceConstitution
  targetConstitution := step.targetConstitution
  everyPaymentRestriction := fun payment =>
    step.everyPaymentRestriction observerFuel payment
  sourceGeneratedEventExact := step.sourceGeneratedEventExact
  sourceGeneratedWholeLedgerExact := step.sourceGeneratedWholeLedgerExact
  sourceRootNativeWriteExact := step.sourceRootNativeWriteExact
  sourceSecondPaidNextHitsGeneratedOccurrence :=
    step.sourceSecondPaidNextHitsGeneratedOccurrence
  grammarThirdPaidNextHitsTargetLawActualEvent :=
    step.grammarThirdPaidNextHitsTargetLawActualEvent
  sourceRootNextIsActualGrammarNext := step.sourceRootNextIsActualGrammarNext
  grammarActualNextIsTargetRootLawCurrent :=
    step.grammarActualNextIsTargetRootLawCurrent
  fixedLawSurfacePreserved := step.sourceTargetLawSurfaceSame
  rootLawNoGo := sourceGeneratedCycleCanonicalRootLawStepNoGo initial depth

/-! ## Finite prefix readout and on-demand continuation -/

/-- Retrospective prefix proposition.  It does not store the steps. -/
def PaidCanonicalPrefixAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) : Prop :=
  ∀ edge : Fin (fuel + 1),
    Nonempty (SourceGeneratedCycleCanonicalRootLawStepAt initial edge.1)

structure ProofCarryingFiniteCycleCanonicalRootLawAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) : Prop where
  private mk ::
  priorPaymentPreservation :
    ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservationAt initial fuel
  paidCanonicalPrefix : PaidCanonicalPrefixAt initial fuel
  everyRootLawTransition : ∀ edge : Fin (fuel + 1),
    let step := sourceGeneratedCycleCanonicalRootLawStep initial edge.1
    ProofCarryingCycleCanonicalRootLawTransitionAt initial (fuel + 1) edge.1
      step
  finalOneMoreRootLawStep :
    Nonempty
      (SourceGeneratedCycleCanonicalRootLawStepAt initial (fuel + 1))
  finalOneMoreRootLawTransition :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (fuel + 1)
    ProofCarryingCycleCanonicalRootLawTransitionAt initial (fuel + 2)
      (fuel + 1) step
  finalUnrevisableRuntimeEmpty :
    let step := sourceGeneratedCycleCanonicalRootLawStep initial (fuel + 1)
    IsEmpty (FinalUnrevisableRuntimeConstitutionAt step)

theorem proofCarryingFiniteCycleCanonicalRootLaw
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    ProofCarryingFiniteCycleCanonicalRootLawAt initial fuel where
  priorPaymentPreservation :=
    proofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation initial fuel
  paidCanonicalPrefix := fun edge =>
    ⟨sourceGeneratedCycleCanonicalRootLawStep initial edge.1⟩
  everyRootLawTransition := fun edge =>
    proofCarryingCycleCanonicalRootLawTransition (fuel + 1)
      (sourceGeneratedCycleCanonicalRootLawStep initial edge.1)
  finalOneMoreRootLawStep :=
    ⟨sourceGeneratedCycleCanonicalRootLawStep initial (fuel + 1)⟩
  finalOneMoreRootLawTransition :=
    proofCarryingCycleCanonicalRootLawTransition (fuel + 2)
      (sourceGeneratedCycleCanonicalRootLawStep initial (fuel + 1))
  finalUnrevisableRuntimeEmpty :=
    finalUnrevisableRuntimeConstitution_isEmpty
      (sourceGeneratedCycleCanonicalRootLawStep initial (fuel + 1))

abbrev AnyProofCarryingFiniteCycleCanonicalRootLawAt
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :=
  { initial : CycleAt oldVisit sourceIndex boundary //
    ProofCarryingFiniteCycleCanonicalRootLawAt initial fuel }

def canonicalProofCarryingFiniteCycleCanonicalRootLawAt
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :
    AnyProofCarryingFiniteCycleCanonicalRootLawAt oldVisit sourceIndex boundary
      fuel :=
  let prior :=
    canonicalProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservationAt
      oldVisit sourceIndex boundary fuel
  ⟨prior.1, proofCarryingFiniteCycleCanonicalRootLaw prior.1 fuel⟩

end
end M14ProofCarryingFiniteCycleCanonicalRootLaw
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteCycleCanonicalRootLaw.cycleCanonicalRootLawGrammarExhaustionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteCycleCanonicalRootLaw.proofCarryingCycleCanonicalRootLawTransition
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteCycleCanonicalRootLaw.proofCarryingFiniteCycleCanonicalRootLaw
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingFiniteCycleCanonicalRootLaw.canonicalProofCarryingFiniteCycleCanonicalRootLawAt
