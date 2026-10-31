import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Constitution.Universal.Splice.Consumer.ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Preservation.Consumer.ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation

/-!
# Universal actual-Payment generated-next preservation

At universal depth `depth`, the actual/search grammar occurrence lives two
paid-cycle steps later.  The actual grammar's whole-ledger Payment is exactly
the canonical Payment of `cycleReplayAt initial (depth + 2)`.  Its
`NextPaidBy` lands on the target universal actual event, while the previously
closed search failure remains a no-write diagnostic face whose embedded
external Payment owns the existing self-U8.

The carrier also quantifies every proof of the exact actual Payment type and
reuses the existing arbitrary-Payment coherence/no-go audit.  It stores no
Payment table, branch, target, registry, schedule or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedCycleMaximalCanonicalPaidStep
open M14ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation
open M14SourceGeneratedCycleCanonicalRootLawStep
open M14ProofCarryingCanonicalSocietyFivefoldConstitution
open M14ProofCarryingCanonicalSocietyUniversalGrammarTotality
open M14ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice

/-- The universal grammar occurrence at `depth` is the source paid occurrence
of cycle depth `depth + 2`.  This is a chart offset, not a new current. -/
def universalActualPaidCycleDepth (depth : Nat) : Nat :=
  depth + 2

/-- Its Payment-generated target is the source paid occurrence of the next
cycle and the actual event of the target universal law. -/
def universalActualPaidTargetCycleDepth (depth : Nat) : Nat :=
  depth + 3

theorem universalActualEvent_eq_rightReplayPostRootEvent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial}
    {observerFuel depth : Nat}
    (splice :
      ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8SpliceAt
        constitution observerFuel depth) :
    splice.universalPoint.fullCaptureFailure.grammar.actualGrammar.exactEvent =
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.rootEvent :=
  splice.universalPoint.fullCaptureFailure.sameRootLedgerAndNext.1.trans
    splice.failureEventIsExternalRightPostRootEvent

/-- The root-law whole-ledger Payment is the exact Payment carried by the
cofinal right replay.  This is the post-root Payment, not its embedded
external M9 Payment occurrence. -/
theorem universalRootLawSuccessorPayment_eq_rightReplayPayment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ((cycleCanonicalRootLawAt initial depth
        ).lifecycleFromActualContinuation.lifecycleMaximum
          ).continuation.successorPayment =
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.payment := by
  rw [cycleCanonicalRootLawGrammarEventPayment_exact]
  rfl

/-- The same replay Payment is the source Payment of the exact `depth + 2`
cycle lifecycle.  `HEq` preserves the dependent index rather than erasing it
through a proof equality. -/
theorem universalRightReplayPayment_heq_depthPlusTwoLifecycleSourcePayment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial}
    {observerFuel depth : Nat}
    (splice :
      ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8SpliceAt
        constitution observerFuel depth) :
    HEq
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.payment
      (cycleLifecycle initial
        (universalActualPaidCycleDepth depth)).sourcePayment := by
  unfold universalActualPaidCycleDepth
  rw [← splice.depthPlusTwoCycleReplayIsExternalRightReplay]
  exact HEq.rfl

/-- The canonical universal Payment generates the target law's actual event.
The existing occurrence spine owns this edge. -/
theorem universalCanonicalPaymentNext_isTargetActualEvent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.payment.nextPaidBy
      (cycleCanonicalRootLawAt initial
        (depth + 1)).actualGrammar.exactEvent.occurrence := by
  let step := sourceGeneratedCycleCanonicalRootLawStep initial depth
  have paymentExact :=
    universalRootLawSuccessorPayment_eq_rightReplayPayment initial depth
  cases paymentExact
  exact step.grammarThirdPaidNextHitsTargetLawActualEvent

/-- The successor paid-cycle source occurrence is the target universal law's
actual occurrence.  The proof exposes the `+3 = (depth+1)+2` index equation
instead of identifying two independently built events. -/
theorem universalPaidTargetCycleOccurrence_isTargetActualOccurrence
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq
      (cycleLifecycle initial
        (universalActualPaidTargetCycleDepth depth)
          ).sourceConsequence.outerRootEvent.occurrence
      (cycleCanonicalRootLawAt initial
        (depth + 1)).actualGrammar.exactEvent.occurrence := by
  have indexExact :
      cycleLifecycleIndex initial (depth + 3) =
        cycleCanonicalRootLawIndex initial (depth + 1) + 1 + 1 := by
    unfold cycleCanonicalRootLawIndex
    rw [cycleLifecycleIndex_exact, cycleLifecycleIndex_exact]
    omega
  unfold universalActualPaidTargetCycleDepth cycleLifecycle
    cycleCanonicalRootLawAt
  cases indexExact
  exact HEq.rfl

/-- Every proof of the exact actual-Payment type has the same generated
target authority.  The proof is consumed by its own paid-step producer; no
equality with the canonical Payment proof is asserted. -/
theorem everyUniversalActualPaymentNext_isTargetActualEvent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (payment :
      CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (cycleLifecycleIndex initial
          (universalActualPaidCycleDepth depth))) :
    HEq payment.nextPaidBy
      (cycleCanonicalRootLawAt initial
        (depth + 1)).actualGrammar.exactEvent.occurrence := by
  let preserved :=
    sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial
      (universalActualPaidCycleDepth depth) payment
  cases preserved.sourcePaymentExact
  exact HEq.trans preserved.paidNextIsNextLifecycleSource
    (universalPaidTargetCycleOccurrence_isTargetActualOccurrence initial depth)

/-- One complete universal source step.  The source splice keeps the failed
search face and its external self-U8 disposition; the fields introduced here
are only the actual Payment commuting square and its successor audit. -/
structure ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservationAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial)
    (observerFuel depth : Nat) : Type 32 where
  private mk ::
  sourceSplice :
    ProofCarryingCanonicalSocietyUniversalFailurePaidSelfU8SpliceAt
      constitution observerFuel depth
  targetUniversalPoint :
    ProofCarryingCanonicalSocietyUniversalGrammarPointAt constitution
      observerFuel (depth + 1)
  sourceActualEventIsRightReplayPostRootEvent :
    sourceSplice.universalPoint.fullCaptureFailure.grammar.actualGrammar.exactEvent =
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.rootEvent
  rootLawSuccessorPaymentIsRightReplayPayment :
    ((cycleCanonicalRootLawAt initial depth
        ).lifecycleFromActualContinuation.lifecycleMaximum
          ).continuation.successorPayment =
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.payment
  rightReplayPaymentIsDepthPlusTwoLifecycleSourcePayment :
    HEq
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.payment
      (cycleLifecycle initial
        (universalActualPaidCycleDepth depth)).sourcePayment
  canonicalPaymentNextIsTargetActualEvent :
    HEq
      (rightReplayAt oldVisit sourceIndex
        (universalFailureBoundaryAt initial depth)).2.payment.nextPaidBy
      (cycleCanonicalRootLawAt initial
        (depth + 1)).actualGrammar.exactEvent.occurrence
  canonicalPaidStep :
    CycleMaximalCanonicalPaidStepPreservationAt initial
      (universalActualPaidCycleDepth depth)
  canonicalPaymentPreservationAndNoGo :
    InputPaymentPreservationAuditAt initial
      (universalActualPaidCycleDepth depth)
        (cycleMaximalSourcePaymentAt initial
          (universalActualPaidCycleDepth depth))
  sourceActualRootLedgerAndNext :
    type_of%
      sourceSplice.universalPoint.rootLawTransition.sourceRootLedgerAndNext
  sourceActualGrammarNextIsTargetRootLawCurrent :
    type_of%
      sourceSplice.universalPoint.actualGeneratedNextIsTargetRootLawCurrent
  sourceSearchGrammarNextIsTargetRootLawCurrent :
    type_of%
      sourceSplice.universalPoint.searchGeneratedNextIsTargetRootLawCurrent
  sourceCycleNextExact : type_of% sourceSplice.universalPoint.cycleNextExact
  targetFailureGrammarExact : type_of% targetUniversalPoint.failureGrammarExact
  targetActualSelfU8Tick : type_of% targetUniversalPoint.actualSelfU8Tick
  everyActualPaymentPreservation : ∀ payment :
      CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (cycleLifecycleIndex initial
          (universalActualPaidCycleDepth depth)),
    CycleMaximalCanonicalPaidStepForPaymentAt initial
      (universalActualPaidCycleDepth depth) payment
  everyActualPaymentPreservationAndNoGo : ∀ payment :
      CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (cycleLifecycleIndex initial
          (universalActualPaidCycleDepth depth)),
    InputPaymentPreservationAuditAt initial
      (universalActualPaidCycleDepth depth) payment
  everyActualPaymentTargetRichAudit : ∀ payment :
      CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (cycleLifecycleIndex initial
          (universalActualPaidCycleDepth depth)),
    InputPaymentTargetRichAuditAt initial observerFuel
      (universalActualPaidCycleDepth depth) payment
  everyActualPaymentNextIsTargetActualEvent : ∀ payment :
      CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (cycleLifecycleIndex initial
          (universalActualPaidCycleDepth depth)),
    HEq payment.nextPaidBy
      (cycleCanonicalRootLawAt initial
        (depth + 1)).actualGrammar.exactEvent.occurrence

def proofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial)
    (observerFuel depth : Nat) :
    ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservationAt
      constitution observerFuel depth := by
  let sourceSplice :=
    proofCarryingCanonicalSocietyUniversalFailurePaidSelfU8Splice constitution
      observerFuel depth
  let targetPoint :=
    proofCarryingCanonicalSocietyUniversalGrammarPoint constitution
      observerFuel (depth + 1)
  exact
    { sourceSplice := sourceSplice
      targetUniversalPoint := targetPoint
      sourceActualEventIsRightReplayPostRootEvent :=
        universalActualEvent_eq_rightReplayPostRootEvent sourceSplice
      rootLawSuccessorPaymentIsRightReplayPayment :=
        universalRootLawSuccessorPayment_eq_rightReplayPayment initial depth
      rightReplayPaymentIsDepthPlusTwoLifecycleSourcePayment :=
        universalRightReplayPayment_heq_depthPlusTwoLifecycleSourcePayment
          sourceSplice
      canonicalPaymentNextIsTargetActualEvent :=
        universalCanonicalPaymentNext_isTargetActualEvent initial depth
      canonicalPaidStep :=
        sourceGeneratedCycleMaximalCanonicalPaidStep initial
          (universalActualPaidCycleDepth depth)
      canonicalPaymentPreservationAndNoGo :=
        inputPaymentPreservationAuditAt initial
          (universalActualPaidCycleDepth depth)
            (cycleMaximalSourcePaymentAt initial
              (universalActualPaidCycleDepth depth))
      sourceActualRootLedgerAndNext :=
        sourceSplice.universalPoint.rootLawTransition.sourceRootLedgerAndNext
      sourceActualGrammarNextIsTargetRootLawCurrent :=
        sourceSplice.universalPoint.actualGeneratedNextIsTargetRootLawCurrent
      sourceSearchGrammarNextIsTargetRootLawCurrent :=
        sourceSplice.universalPoint.searchGeneratedNextIsTargetRootLawCurrent
      sourceCycleNextExact := sourceSplice.universalPoint.cycleNextExact
      targetFailureGrammarExact := targetPoint.failureGrammarExact
      targetActualSelfU8Tick := targetPoint.actualSelfU8Tick
      everyActualPaymentPreservation := fun payment =>
        sourceGeneratedCycleMaximalCanonicalPaidStepForPayment initial
          (universalActualPaidCycleDepth depth) payment
      everyActualPaymentPreservationAndNoGo := fun payment =>
        inputPaymentPreservationAuditAt initial
          (universalActualPaidCycleDepth depth) payment
      everyActualPaymentTargetRichAudit := fun payment =>
        inputPaymentTargetRichAuditAt initial observerFuel
          (universalActualPaidCycleDepth depth) payment
      everyActualPaymentNextIsTargetActualEvent := fun payment =>
        everyUniversalActualPaymentNext_isTargetActualEvent initial depth
          payment }

structure ProofCarryingCanonicalSocietyUniversalActualPaymentNextTotalityAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial) : Prop where
  private mk ::
  everyDepth : ∀ observerFuel depth,
    Nonempty
      (ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservationAt
        constitution observerFuel depth)

theorem proofCarryingCanonicalSocietyUniversalActualPaymentNextTotality
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial) :
    ProofCarryingCanonicalSocietyUniversalActualPaymentNextTotalityAt
      constitution where
  everyDepth := fun observerFuel depth =>
    ⟨proofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation
      constitution observerFuel depth⟩

/-- Strong public consumer: actual whole-ledger Payment generates the target
universal actual occurrence for every exact Payment proof, while the search
face keeps its already certified no-write/external-self-U8 disposition. -/
theorem canonicalSocietyUniversalActualPayment_generatedNextPreservation
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial}
    {observerFuel depth : Nat}
    (point :
      ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservationAt
        constitution observerFuel depth) :
    point.sourceSplice.universalPoint.fullCaptureFailure.grammar.actualGrammar.exactEvent =
        (rightReplayAt oldVisit sourceIndex
          (universalFailureBoundaryAt initial depth)).2.rootEvent ∧
      type_of% point.sourceSplice.universalPoint.failureGrammarExact ∧
      ((cycleCanonicalRootLawAt initial depth
          ).lifecycleFromActualContinuation.lifecycleMaximum
            ).continuation.successorPayment =
        (rightReplayAt oldVisit sourceIndex
          (universalFailureBoundaryAt initial depth)).2.payment ∧
      HEq
        (rightReplayAt oldVisit sourceIndex
          (universalFailureBoundaryAt initial depth)).2.payment
        (cycleLifecycle initial
          (universalActualPaidCycleDepth depth)).sourcePayment ∧
      HEq
        (rightReplayAt oldVisit sourceIndex
          (universalFailureBoundaryAt initial depth)).2.payment.nextPaidBy
        (cycleCanonicalRootLawAt initial
          (depth + 1)).actualGrammar.exactEvent.occurrence ∧
      Nonempty
        (CycleMaximalCanonicalPaidStepPreservationAt initial
          (universalActualPaidCycleDepth depth)) ∧
      InputPaymentPreservationAuditAt initial
        (universalActualPaidCycleDepth depth)
          (cycleMaximalSourcePaymentAt initial
            (universalActualPaidCycleDepth depth)) ∧
      type_of% point.sourceActualRootLedgerAndNext ∧
      type_of%
        point.sourceSplice.universalPoint.rootLawTransition.rootLawNoGo ∧
      type_of% point.sourceActualGrammarNextIsTargetRootLawCurrent ∧
      type_of% point.sourceSearchGrammarNextIsTargetRootLawCurrent ∧
      Nonempty
        (ProofCarryingCanonicalSocietyUniversalGrammarPointAt constitution
          observerFuel (depth + 1)) ∧
      (∀ payment :
          CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
            (cycleLifecycleIndex initial
              (universalActualPaidCycleDepth depth)),
        InputPaymentPreservationAuditAt initial
            (universalActualPaidCycleDepth depth) payment ∧
          InputPaymentTargetRichAuditAt initial observerFuel
            (universalActualPaidCycleDepth depth) payment ∧
          HEq payment.nextPaidBy
            (cycleCanonicalRootLawAt initial
              (depth + 1)).actualGrammar.exactEvent.occurrence) ∧
      type_of%
        (universalSearchFailure_externalPaymentSelfU8_strictAuthoritySeparation
          point.sourceSplice) := by
  refine ⟨point.sourceActualEventIsRightReplayPostRootEvent,
    point.sourceSplice.universalPoint.failureGrammarExact,
    point.rootLawSuccessorPaymentIsRightReplayPayment,
    point.rightReplayPaymentIsDepthPlusTwoLifecycleSourcePayment,
    point.canonicalPaymentNextIsTargetActualEvent,
    ⟨point.canonicalPaidStep⟩,
    point.canonicalPaymentPreservationAndNoGo,
    point.sourceActualRootLedgerAndNext,
    point.sourceSplice.universalPoint.rootLawTransition.rootLawNoGo,
    point.sourceActualGrammarNextIsTargetRootLawCurrent,
    point.sourceSearchGrammarNextIsTargetRootLawCurrent,
    ⟨point.targetUniversalPoint⟩, ?_,
    universalSearchFailure_externalPaymentSelfU8_strictAuthoritySeparation
      point.sourceSplice⟩
  intro payment
  exact ⟨point.everyActualPaymentPreservationAndNoGo payment,
    point.everyActualPaymentTargetRichAudit payment,
    point.everyActualPaymentNextIsTargetActualEvent payment⟩

theorem canonicalSocietyUniversalActualPaymentNext_directConsumer
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (constitution :
      ProofCarryingCanonicalSocietyFivefoldConstitutionAt initial) :
    ProofCarryingCanonicalSocietyUniversalActualPaymentNextTotalityAt
        constitution ∧
      (∀ observerFuel depth,
        Nonempty
          (ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservationAt
            constitution observerFuel depth)) :=
  let totality :=
    proofCarryingCanonicalSocietyUniversalActualPaymentNextTotality constitution
  ⟨totality, totality.everyDepth⟩

end
end M14ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation.universalRootLawSuccessorPayment_eq_rightReplayPayment
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation.everyUniversalActualPaymentNext_isTargetActualEvent
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation.proofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation.canonicalSocietyUniversalActualPayment_generatedNextPreservation
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyUniversalActualPaymentNextPreservation.canonicalSocietyUniversalActualPaymentNext_directConsumer
