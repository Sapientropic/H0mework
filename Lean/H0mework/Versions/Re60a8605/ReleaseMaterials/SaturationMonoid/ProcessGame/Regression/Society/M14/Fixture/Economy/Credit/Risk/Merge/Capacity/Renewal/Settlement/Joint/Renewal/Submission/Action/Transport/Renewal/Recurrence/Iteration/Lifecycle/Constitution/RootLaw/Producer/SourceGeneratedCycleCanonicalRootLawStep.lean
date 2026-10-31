import H0mework.Foundation.Authority.Representation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Universal.Producer.SourceGeneratedUniversalSocietyRootGrammar
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.Preservation.Consumer.ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation

/-!
# Source-generated canonical root-law step

The cycle constitution is installed as a dependent restriction of the
existing universal Society actual fold and the existing post-settlement
living-root answer-and-next occurrence.  The actual fold's lifecycle maximum,
not a parallel canonical maximum, generates the constitution.

There is a deliberate two-stage offset: the lifecycle begins at paid index
`i`, while the universal grammar occurrence is the continuation-successor
root event at `i + 2`.  The lifecycle occurrence spine connects them through
two exact Payments.  They are not declared to be one edge.  The grammar's
generated next is the grammar occurrence for `i + 1`, at visit `i + 3`, and
therefore generates the root law at the successor cycle.

The new root-law step has a private constructor and its producer accepts only
`initial/depth`.  The subordinate restriction consumes an already typed exact
Payment proof, but accepts no law, target, authority choice, verdict, history
or future as caller payload.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCycleCanonicalRootLawStep

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementOccurrencePayment
open M14SourceGeneratedContributionCapacityPostSettlementCanonicalCurrent
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum
open M14SourceGeneratedPaidExitLifecycleMaximumNoGo
open M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo
open M14SourceGeneratedPostSettlementObserverFiniteExitCapacityConstitution
open M14SourceGeneratedCycleMaximalCanonicalPaidStep
open M14SourceGeneratedCycleMaximalCanonicalPaidStepNoGo
open M14ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation

/-- Existing living root, named only to keep dependent types readable. -/
abbrev CycleCanonicalLivingRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex

/-- Lifecycle index carried by the input cycle. -/
def cycleCanonicalRootLawIndex
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Nat :=
  cycleLifecycleIndex initial depth

/-- Existing universal Society grammar at that lifecycle index.  Its living
root visit is intentionally `index + 2`. -/
abbrev CycleCanonicalRootLawAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :=
  SourceGeneratedUniversalSocietyRootGrammarAt oldVisit sourceIndex
    (cycleCanonicalRootLawIndex initial depth)

def cycleCanonicalRootLawAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    CycleCanonicalRootLawAt initial depth :=
  sourceGeneratedUniversalSocietyRootGrammarAt oldVisit sourceIndex
    (cycleCanonicalRootLawIndex initial depth)

/-- Living causal current of the actual-fold grammar occurrence. -/
def cycleCanonicalRootLawCurrentAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceNativeLivingRootCausalCurrentAt
      (CycleCanonicalLivingRootAt oldVisit sourceIndex) :=
  ULift.up
    (universalSocietyVisitAt oldVisit sourceIndex
      (cycleCanonicalRootLawIndex initial depth))

/-- Exact lifted occurrence at that fixed current. -/
def cycleCanonicalRootLawOccurrenceAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceNativeLivingRootCausalOccurrenceAt
      (CycleCanonicalLivingRootAt oldVisit sourceIndex)
      (cycleCanonicalRootLawCurrentAt initial depth) :=
  ULift.up
    (contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
      (cycleCanonicalRootLawIndex initial depth + 1 + 1))

/-- Canonical answer-and-next of the existing living root. -/
def cycleCanonicalRootLawEvolutionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceNativeLivingRootCausalEvolutionAt
      (CycleCanonicalLivingRootAt oldVisit sourceIndex)
      (cycleCanonicalRootLawCurrentAt initial depth) :=
  (CycleCanonicalLivingRootAt oldVisit sourceIndex
    ).canonicalCausalAnswerAndNext
      (cycleCanonicalRootLawCurrentAt initial depth)

/-- Existing zero-information lawfulness is exposed only propositionally; no
new authority token is stored in the root-law step. -/
theorem cycleCanonicalRootLawEvolution_lawful
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    Nonempty
      (SourceNativeLivingRootCausalLawfulEvolutionAt
        (CycleCanonicalLivingRootAt oldVisit sourceIndex)
        (cycleCanonicalRootLawOccurrenceAt initial depth)
        (cycleCanonicalRootLawEvolutionAt initial depth)) :=
  ⟨PUnit.unit⟩

/-- Authoritative presentation of the same grammar current. -/
def cycleCanonicalRootLawAuthoritativeCurrentAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceNativeAuthoritativeRootCurrentAt (JointSettlementNAt oldVisit) :=
  ⟨PostSettlementRenewalVAt oldVisit,
    (CycleCanonicalLivingRootAt oldVisit sourceIndex).toAuthoritativeRoot,
    universalSocietyVisitAt oldVisit sourceIndex
      (cycleCanonicalRootLawIndex initial depth)⟩

/-- The actual fold owns the exact maximum consumed by the cycle. -/
theorem cycleCanonicalRootLawActualFoldMaximum_eq_cycleMaximum
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleCanonicalRootLawAt initial depth
      ).lifecycleFromActualContinuation.lifecycleMaximum =
      cycleLifecycleMaximum initial depth :=
  rfl

/-- Constitution generated specifically from the actual-fold maximum. -/
theorem cycleCanonicalRootLawConstitutionFromActualFold
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    FiniteExitCapacityConstitutionAt initial depth :=
  constitutionOfMaximum initial depth
    (cycleCanonicalRootLawAt initial depth
      ).lifecycleFromActualContinuation.lifecycleMaximum

/-- Root-generated event is the continuation-successor event at `i + 2`. -/
theorem cycleCanonicalRootLawGeneratedEvent_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq (cycleCanonicalRootLawEvolutionAt initial depth).generated
      ((cycleCanonicalRootLawAt initial depth
        ).lifecycleFromActualContinuation.lifecycleMaximum
          ).continuation.successorRootEvent :=
  HEq.rfl

/-- Its whole-ledger write-back is the same event's write-back. -/
theorem cycleCanonicalRootLawGeneratedWholeLedger_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq
      (cycleCanonicalRootLawEvolutionAt initial depth
        ).generated.wholeLedgerWriteBack
      ((cycleCanonicalRootLawAt initial depth
        ).lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.successorRootEvent.wholeLedgerWriteBack :=
  HEq.rfl

/-- The cycle's stage-zero source event remains the exact post-root event at
`i`; it is not the grammar event at `i + 2`. -/
theorem cycleCanonicalRootLawCycleSourceEvent_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleLifecycle initial depth).sourceConsequence.outerRootEvent =
      contributionCapacityPostSettlementExactRootEventAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth) :=
  (cycleLifecycle initial depth).sourceConsequence.outerRootEventExact

/-- First paid edge of the actual-fold lifecycle. -/
theorem cycleCanonicalRootLawFirstPaidNext
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq (cycleLifecycle initial depth).sourcePayment.nextPaidBy
      (cycleLifecycle initial depth
        ).targetConsequence.outerRootEvent.occurrence :=
  (cycleCanonicalRootLawAt initial depth
    ).lifecycleFromActualContinuation.lifecycleMaximum.rooted
      |>.occurrenceSpine.firstPaidNext

/-- The first paid target Payment is exactly the executed Payment whose next
lands on the grammar occurrence. -/
theorem cycleCanonicalRootLawFirstTargetPayment_isExecutedPayment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleLifecycle initial depth).targetPayment =
      ((cycleCanonicalRootLawAt initial depth
        ).lifecycleFromActualContinuation.lifecycleMaximum
          ).continuation.executedPayment :=
  (cycleCanonicalRootLawAt initial depth
    ).lifecycleFromActualContinuation.lifecycleMaximum.rooted
      |>.occurrenceSpine.paymentChainExact.1

/-- The second Payment in the lifecycle reaches the grammar occurrence.  The
first cycle Payment and this root-law occurrence are not collapsed. -/
theorem cycleCanonicalRootLawSecondPaidNext_hitsGeneratedOccurrence
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq
      ((cycleCanonicalRootLawAt initial depth
        ).lifecycleFromActualContinuation.lifecycleMaximum
          ).continuation.executedPayment.nextPaidBy
      (cycleCanonicalRootLawEvolutionAt initial depth
        ).generated.occurrence :=
  (cycleCanonicalRootLawAt initial depth
    ).lifecycleFromActualContinuation.lifecycleMaximum.rooted
      |>.occurrenceSpine.secondPaidNext

/-- Exact `+2` current offset, exposed to forbid a false same-edge reading. -/
theorem cycleCanonicalRootLawVisit_hasLifecyclePlusTwoOffset
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (show Nat from
      (cycleCanonicalRootLawCurrentAt initial depth).down.current) =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth + 1 + 1) :=
  rfl

theorem cycleCanonicalRootLawVisit_ne_cyclePaidSourceCurrent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth) ≠
      (show Nat from
        (cycleCanonicalRootLawCurrentAt initial depth).down.current) := by
  rw [cycleCanonicalRootLawVisit_hasLifecyclePlusTwoOffset,
    contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact]
  omega

/-- The grammar's generated next is exactly the grammar current attached to
the next cycle index, hence visit `i + 3`. -/
theorem cycleCanonicalRootLawNextCurrent_eq_targetRootLawCurrent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleCanonicalRootLawEvolutionAt initial depth).nextCurrent =
      cycleCanonicalRootLawAuthoritativeCurrentAt initial (depth + 1) := by
  unfold cycleCanonicalRootLawAuthoritativeCurrentAt
    cycleCanonicalRootLawEvolutionAt cycleCanonicalRootLawCurrentAt
    cycleCanonicalRootLawIndex
  rw [show cycleLifecycleIndex initial (depth + 1) =
      cycleLifecycleIndex initial depth + 1 by
    exact (cycleMaximalTargetIndex_eq_nextLifecycleIndex initial depth).symm]
  rfl

/-- The actual grammar's generated next itself is the target grammar current;
this is the `i+2 → i+3` back edge. -/
theorem cycleCanonicalRootLawGrammarNext_eq_targetRootLawCurrent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (cycleCanonicalRootLawAt initial depth
      ).actualGrammar.generatedNext =
      cycleCanonicalRootLawAuthoritativeCurrentAt initial (depth + 1) :=
  (cycleCanonicalRootLawAt initial depth
    ).rootLedgerAndNext.2.2.2.symm.trans
      (cycleCanonicalRootLawNextCurrent_eq_targetRootLawCurrent initial depth)

/-- The front paid target `i+1` is still before the grammar source `i+2`;
the two legal edges are never collapsed. -/
theorem cycleCanonicalRootLawFrontTarget_ne_grammarSourceCurrent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth + 1) ≠
      (show Nat from
        (cycleCanonicalRootLawCurrentAt initial depth).down.current) := by
  rw [cycleCanonicalRootLawVisit_hasLifecyclePlusTwoOffset,
    contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact]
  omega

/-- Fixed-law answer-and-next preserves the exact source law surface. -/
theorem cycleCanonicalRootLawTargetLawSurface_eq_source
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ((cycleCanonicalRootLawEvolutionAt initial depth).nextCurrent
      ).root.source.lawSurface =
      (CycleCanonicalLivingRootAt oldVisit sourceIndex).source.base.lawSurface :=
  (CycleCanonicalLivingRootAt oldVisit sourceIndex
    ).generatedNextCurrentAt_lawSurface_eq
      (cycleCanonicalRootLawCurrentAt initial depth).down

/-- Existing lifecycle counterfactual/deletion no-gos at one node. -/
abbrev CycleCanonicalRootLawLifecycleNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Prop :=
  IsEmpty
      (ExactFullCaptureReportedPaidExitLifecycleMaximumAt
        (cycleFullCaptureCounterlifeAt initial depth)) ∧
    IsEmpty
      (ExactPostContinuationSourceOwnershipDeletionAt
        (cycleLifecycleMaximum initial depth).disposition) ∧
    IsEmpty
      (ExactPostContinuationRootConsumerDeletionAt
        (cycleLifecycleMaximum initial depth).disposition) ∧
    IsEmpty
      (ExactPostContinuationLocalEmptyErasesExternalLiabilityAt
        (cycleLifecycleMaximum initial depth).disposition)

theorem cycleCanonicalRootLawLifecycleNoGoAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    CycleCanonicalRootLawLifecycleNoGoAt initial depth :=
  ⟨cycleFullCaptureReportedMaximum_isEmpty initial depth,
    cycleSourceOwnershipDeletion_isEmpty initial depth,
    cycleRootConsumerDeletion_isEmpty initial depth,
    cycleLocalEmptyErasure_isEmpty initial depth⟩

namespace CycleCanonicalRootLawAt

/-- Constitution is a derived face of the stored law's actual-fold maximum,
not a field or independently selected canonical maximum. -/
theorem constitution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (law : CycleCanonicalRootLawAt initial depth) :
    FiniteExitCapacityConstitutionAt initial depth :=
  constitutionOfMaximum initial depth
    law.lifecycleFromActualContinuation.lifecycleMaximum

end CycleCanonicalRootLawAt

/-- One input Payment is restricted simultaneously by the source and target
actual-fold laws.  The constructor is private: callers supply only the
existing Payment proof, never either law or a target. -/
structure CycleCanonicalPaymentRootRestrictionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat)
    (sourceLaw : CycleCanonicalRootLawAt initial depth)
    (targetLaw : CycleCanonicalRootLawAt initial (depth + 1))
    (observerFuel : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleCanonicalRootLawIndex initial depth)) : Prop where
  private mk ::
  sourceMaximumExact :
    sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum =
      cycleLifecycleMaximum initial depth
  targetMaximumExact :
    targetLaw.lifecycleFromActualContinuation.lifecycleMaximum =
      cycleLifecycleMaximum initial (depth + 1)
  preservationAudit :
    InputPaymentPreservationAuditAt initial depth payment
  targetRichAudit :
    InputPaymentTargetRichAuditAt initial observerFuel depth payment

/-- Sole restriction producer for an input Payment and the two canonical
source-generated laws. -/
theorem cycleCanonicalPaymentRootRestrictionAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth observerFuel : Nat)
    (payment : CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
      (cycleCanonicalRootLawIndex initial depth)) :
    CycleCanonicalPaymentRootRestrictionAt initial depth
      (cycleCanonicalRootLawAt initial depth)
      (cycleCanonicalRootLawAt initial (depth + 1)) observerFuel payment where
  sourceMaximumExact :=
    cycleCanonicalRootLawActualFoldMaximum_eq_cycleMaximum initial depth
  targetMaximumExact :=
    cycleCanonicalRootLawActualFoldMaximum_eq_cycleMaximum initial (depth + 1)
  preservationAudit := inputPaymentPreservationAuditAt initial depth payment
  targetRichAudit :=
    inputPaymentTargetRichAuditAt initial observerFuel depth payment

/-- Event-selected Payment of the grammar source occurrence at `i + 2`. -/
theorem cycleCanonicalRootLawGrammarEventPayment_exact
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    ((cycleCanonicalRootLawAt initial depth
      ).lifecycleFromActualContinuation.lifecycleMaximum
        ).continuation.successorPayment =
      sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
        oldVisit sourceIndex
          (cycleCanonicalRootLawIndex initial depth + 1 + 1) :=
  rfl

/-- The living-root compiler writes that exact grammar-event Payment. -/
theorem cycleCanonicalRootLawNativeWrite_isGrammarEventPayment
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile
        (cycleCanonicalRootLawEvolutionAt initial depth).generated.occurrence =
      .nativeWrite
        ((cycleCanonicalRootLawAt initial depth
          ).lifecycleFromActualContinuation.lifecycleMaximum
            ).continuation.successorPayment.write :=
  rfl

/-- Third lifecycle Payment lands on the target law's actual grammar event at
`i + 3`; this is the exact back edge. -/
theorem cycleCanonicalRootLawThirdPaidNext_hitsTargetLawActualEvent
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    HEq
      ((cycleCanonicalRootLawAt initial depth
        ).lifecycleFromActualContinuation.lifecycleMaximum
          ).continuation.successorPayment.nextPaidBy
      (cycleCanonicalRootLawAt initial (depth + 1)
        ).actualGrammar.exactEvent.occurrence := by
  unfold cycleCanonicalRootLawAt cycleCanonicalRootLawIndex
  rw [show cycleLifecycleIndex initial (depth + 1) =
      cycleLifecycleIndex initial depth + 1 by
    exact (cycleMaximalTargetIndex_eq_nextLifecycleIndex initial depth).symm]
  exact
    (sourceGeneratedUniversalSocietyRootGrammarAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)
      ).lifecycleFromActualContinuation.lifecycleMaximum.rooted
        |>.occurrenceSpine.thirdPaidNext

/-- One fixed-law root step: the actual fold at lifecycle index `i` generates
its `i+2 → i+3` living-root next, while the cycle's canonical Payment remains
the distinct `i → i+1` restriction of the same lifecycle maximum. -/
structure SourceGeneratedCycleCanonicalRootLawStepAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) : Type 32 where
  private mk ::
  sourceLaw : CycleCanonicalRootLawAt initial depth
  targetLaw : CycleCanonicalRootLawAt initial (depth + 1)
  sourceActualFoldMaximumExact :
    sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum =
      cycleLifecycleMaximum initial depth
  targetActualFoldMaximumExact :
    targetLaw.lifecycleFromActualContinuation.lifecycleMaximum =
      cycleLifecycleMaximum initial (depth + 1)
  sourceGeneratedEventExact : HEq
    (cycleCanonicalRootLawEvolutionAt initial depth).generated
    (sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.successorRootEvent
  sourceGeneratedWholeLedgerExact : HEq
    (cycleCanonicalRootLawEvolutionAt initial depth
      ).generated.wholeLedgerWriteBack
    (sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.successorRootEvent.wholeLedgerWriteBack
  sourceGrammarEventPaymentExact :
    (sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.successorPayment =
      sourceGeneratedContributionCapacityPostSettlementOccurrencePaymentAt
        oldVisit sourceIndex
          (cycleCanonicalRootLawIndex initial depth + 1 + 1)
  sourceRootNativeWriteExact :
    (contributionCapacityPostSettlementRenewalSource oldVisit sourceIndex
      ).toRootSource.actual.compile
        (cycleCanonicalRootLawEvolutionAt initial depth).generated.occurrence =
      .nativeWrite
        (sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
          ).continuation.successorPayment.write
  sourceRootNextIsActualGrammarNext :
    (cycleCanonicalRootLawEvolutionAt initial depth).nextCurrent =
      sourceLaw.actualGrammar.generatedNext
  sourceOccurrenceSpine : PaidExitLifecycleOccurrenceSpineAt oldVisit
    sourceIndex (cycleCanonicalRootLawIndex initial depth)
  sourceSecondPaidNextHitsGeneratedOccurrence : HEq
    (sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.executedPayment.nextPaidBy
    (cycleCanonicalRootLawEvolutionAt initial depth).generated.occurrence
  grammarThirdPaidNextHitsTargetLawActualEvent : HEq
    (sourceLaw.lifecycleFromActualContinuation.lifecycleMaximum
      ).continuation.successorPayment.nextPaidBy
    targetLaw.actualGrammar.exactEvent.occurrence
  sourceRootVisitHasPlusTwoOffset :
    (show Nat from
      (cycleCanonicalRootLawCurrentAt initial depth).down.current) =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth + 1 + 1)
  sourceRootVisitIsNotFrontPaidSource :
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth) ≠
      (show Nat from
        (cycleCanonicalRootLawCurrentAt initial depth).down.current)
  frontPaidTargetIsNotGrammarSource :
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth + 1) ≠
      (show Nat from
        (cycleCanonicalRootLawCurrentAt initial depth).down.current)
  paidSourcePaymentExact :
    let paid := sourceGeneratedCycleMaximalCanonicalPaidStep initial depth
    paid.consumedStep.2.sourcePayment =
      (cycleLifecycle initial depth).sourcePayment
  paidNextIsNextCycleSource :
    let paid := sourceGeneratedCycleMaximalCanonicalPaidStep initial depth
    HEq paid.consumedStep.2.sourcePayment.nextPaidBy
      (cycleLifecycle initial
        (depth + 1)).sourceConsequence.outerRootEvent.occurrence
  paidTargetCurrentIsNextCycleSource :
    let paid := sourceGeneratedCycleMaximalCanonicalPaidStep initial depth
    HEq paid.consumedStep.2.targetCurrent
      (cycleLifecycle initial (depth + 1)).paidStep.sourceCurrent
  paidTargetPaymentIsNextCycleSource :
    let paid := sourceGeneratedCycleMaximalCanonicalPaidStep initial depth
    HEq paid.consumedStep.2.targetPayment
      (cycleLifecycle initial (depth + 1)).sourcePayment
  paidTargetRootIsNextCycleSource :
    let paid := sourceGeneratedCycleMaximalCanonicalPaidStep initial depth
    HEq
      (SourceGeneratedContributionCapacityPostSettlementCanonicalCurrentAt.rootEvent
        paid.consumedStep.2.targetCurrent)
      (cycleLifecycle initial
        (depth + 1)).sourceConsequence.outerRootEvent
  canonicalFrontPaidPreservation : Nonempty
    (CycleMaximalCanonicalPaidStepPreservationAt initial depth)
  everyPaymentRestriction : ∀ observerFuel : Nat, ∀ payment :
      CanonicalPostSettlementOccurrencePaymentAt oldVisit sourceIndex
        (cycleCanonicalRootLawIndex initial depth),
    CycleCanonicalPaymentRootRestrictionAt initial depth sourceLaw targetLaw
      observerFuel payment
  sourceLifecycleNoGo :
    CycleCanonicalRootLawLifecycleNoGoAt initial depth
  targetLifecycleNoGo :
    CycleCanonicalRootLawLifecycleNoGoAt initial (depth + 1)
  grammarActualNextIsTargetRootLawCurrent :
    sourceLaw.actualGrammar.generatedNext =
      cycleCanonicalRootLawAuthoritativeCurrentAt initial (depth + 1)
  grammarNextIsTargetRootLawCurrent :
    (cycleCanonicalRootLawEvolutionAt initial depth).nextCurrent =
      cycleCanonicalRootLawAuthoritativeCurrentAt initial (depth + 1)
  sourceTargetLawSurfaceSame :
    ((cycleCanonicalRootLawEvolutionAt initial depth).nextCurrent
      ).root.source.lawSurface =
      (CycleCanonicalLivingRootAt oldVisit sourceIndex).source.base.lawSurface
  cycleNextExact :
    cycleAt initial (depth + 1) = (stepAt initial depth).nextCycle

/-- Premise-free root-law step. -/
def sourceGeneratedCycleCanonicalRootLawStep
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    SourceGeneratedCycleCanonicalRootLawStepAt initial depth := by
  let paid := sourceGeneratedCycleMaximalCanonicalPaidStep initial depth
  exact
    { sourceLaw := cycleCanonicalRootLawAt initial depth
      targetLaw := cycleCanonicalRootLawAt initial (depth + 1)
      sourceActualFoldMaximumExact :=
        cycleCanonicalRootLawActualFoldMaximum_eq_cycleMaximum initial depth
      targetActualFoldMaximumExact :=
        cycleCanonicalRootLawActualFoldMaximum_eq_cycleMaximum initial
          (depth + 1)
      sourceGeneratedEventExact :=
        cycleCanonicalRootLawGeneratedEvent_exact initial depth
      sourceGeneratedWholeLedgerExact :=
        cycleCanonicalRootLawGeneratedWholeLedger_exact initial depth
      sourceGrammarEventPaymentExact :=
        cycleCanonicalRootLawGrammarEventPayment_exact initial depth
      sourceRootNativeWriteExact :=
        cycleCanonicalRootLawNativeWrite_isGrammarEventPayment initial depth
      sourceRootNextIsActualGrammarNext :=
        (cycleCanonicalRootLawAt initial depth
          ).rootLedgerAndNext.2.2.2
      sourceOccurrenceSpine :=
        (cycleCanonicalRootLawAt initial depth
          ).lifecycleFromActualContinuation.lifecycleMaximum.rooted
            |>.occurrenceSpine
      sourceSecondPaidNextHitsGeneratedOccurrence :=
        cycleCanonicalRootLawSecondPaidNext_hitsGeneratedOccurrence initial
          depth
      grammarThirdPaidNextHitsTargetLawActualEvent :=
        cycleCanonicalRootLawThirdPaidNext_hitsTargetLawActualEvent initial depth
      sourceRootVisitHasPlusTwoOffset :=
        cycleCanonicalRootLawVisit_hasLifecyclePlusTwoOffset initial depth
      sourceRootVisitIsNotFrontPaidSource :=
        cycleCanonicalRootLawVisit_ne_cyclePaidSourceCurrent initial depth
      frontPaidTargetIsNotGrammarSource :=
        cycleCanonicalRootLawFrontTarget_ne_grammarSourceCurrent initial depth
      paidSourcePaymentExact :=
        paid.sourcePaymentExact.trans
          (cycleMaximalSourcePayment_eq_cycleLifecycle initial depth)
      paidNextIsNextCycleSource := paid.paidNextIsNextLifecycleSource
      paidTargetCurrentIsNextCycleSource :=
        paid.targetCurrentIsNextLifecycleSource
      paidTargetPaymentIsNextCycleSource :=
        paid.targetPaymentIsNextLifecycleSource
      paidTargetRootIsNextCycleSource :=
        paid.targetRootEventIsNextLifecycleSource
      canonicalFrontPaidPreservation := ⟨paid⟩
      everyPaymentRestriction := fun observerFuel payment =>
        cycleCanonicalPaymentRootRestrictionAt initial depth observerFuel
          payment
      sourceLifecycleNoGo :=
        cycleCanonicalRootLawLifecycleNoGoAt initial depth
      targetLifecycleNoGo :=
        cycleCanonicalRootLawLifecycleNoGoAt initial (depth + 1)
      grammarActualNextIsTargetRootLawCurrent :=
        cycleCanonicalRootLawGrammarNext_eq_targetRootLawCurrent initial depth
      grammarNextIsTargetRootLawCurrent :=
        cycleCanonicalRootLawNextCurrent_eq_targetRootLawCurrent initial depth
      sourceTargetLawSurfaceSame :=
        cycleCanonicalRootLawTargetLawSurface_eq_source initial depth
      cycleNextExact := cycleAt_succ initial depth }

namespace SourceGeneratedCycleCanonicalRootLawStepAt

/-- Source constitution is projected from the stored actual-fold law. -/
theorem sourceConstitution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (step : SourceGeneratedCycleCanonicalRootLawStepAt initial depth) :
    FiniteExitCapacityConstitutionAt initial depth :=
  step.sourceLaw.constitution

/-- Target constitution is independently projected from the stored target
actual-fold law. -/
theorem targetConstitution
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary} {depth : Nat}
    (step : SourceGeneratedCycleCanonicalRootLawStepAt initial depth) :
    FiniteExitCapacityConstitutionAt initial (depth + 1) :=
  step.targetLaw.constitution

end SourceGeneratedCycleCanonicalRootLawStepAt

end
end M14SourceGeneratedCycleCanonicalRootLawStep
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleCanonicalRootLawStep.cycleCanonicalRootLawConstitutionFromActualFold
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleCanonicalRootLawStep.cycleCanonicalRootLawEvolution_lawful
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleCanonicalRootLawStep.cycleCanonicalPaymentRootRestrictionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCycleCanonicalRootLawStep.sourceGeneratedCycleCanonicalRootLawStep
