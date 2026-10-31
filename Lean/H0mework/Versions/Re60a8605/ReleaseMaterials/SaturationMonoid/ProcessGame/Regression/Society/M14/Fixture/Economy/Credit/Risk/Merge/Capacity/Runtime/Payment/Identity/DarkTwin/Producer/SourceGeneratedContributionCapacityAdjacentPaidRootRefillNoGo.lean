import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Execution.Runtime.Consumer.ProofCarryingContributionCapacityCofinalNoveltySelfU8
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Credit.Risk.PeriodicDefaultSideLossAllocation

/-!
# Adjacent paid-root refill no-go

For every boundary, the right path at that boundary and the right path at the
next boundary are two adjacent external M9 visits.  Each path has its own
exact Payment, rooted failure, installed self-U8 runtime, and compiler-selected
default-side first write `2 -> 1 + 1`.

These are independent root-specific entity occurrences.  If a database tries
to retype the first action's canonical left child as the second Payment's
source parent, the necessary source-residual equality is `1 = 2`.  The exact
source-closed continuation fibre is therefore empty before a second edge can
form.  The theorem does not claim that the repository's actual paid tail ever
contained such a cross-visit handoff.

No cross-network HEq, second occurrence, entity registry, payment schedule,
history table, or completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityAdjacentPaidRootRefillNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring
open M9ProofCarryingRenewalU8RevisedLedger
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Revision
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Compilation
open M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime
open M14ProofCarryingContributionCapacityCofinalNoveltySelfU8
open M14PeriodicDefaultSideLossAllocation

/-- Zero-field adjacent-pair token.  The only variable input is the absolute
boundary from which both exact paid paths are regenerated. -/
inductive SourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32
  | private generated

def sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
      sourceIndex boundary :=
  .generated

namespace SourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  (twin : SourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt
    oldVisit sourceIndex boundary)

def firstNovelty := by
  cases twin
  exact sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
    sourceIndex boundary

def secondNovelty := by
  cases twin
  exact sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
    sourceIndex (boundary + 1)

def firstRooted :=
  sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
    (firstNovelty twin)

def secondRooted :=
  sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt
    (secondNovelty twin)

def firstRevision :=
  sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
    (firstRooted twin)

def secondRevision :=
  sourceGeneratedContributionCapacityCofinalNoveltyU8RevisionAt
    (secondRooted twin)

def firstExecution :=
  sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
    (firstRevision twin)

def secondExecution :=
  sourceGeneratedContributionCapacityCofinalNoveltyU8CompilationAt
    (secondRevision twin)

def firstCurrent : Nat := (firstRooted twin).rightCurrent

def secondCurrent : Nat := (secondRooted twin).rightCurrent

def firstAllocation :=
  sourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt
    (firstCurrent twin)

def secondAllocation :=
  sourceGeneratedProofCarryingPeriodicDefaultSideLossAllocationAt
    (secondCurrent twin)

def firstAction := by
  cases twin
  exact
    M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedDefaultSideLossAllocationAt
      oldVisit sourceIndex boundary

def secondAction := by
  cases twin
  exact
    M14SourceGeneratedPostSettlementObserverSubmissionU8.augmentedDefaultSideLossAllocationAt
      oldVisit sourceIndex (boundary + 1)

theorem currentsAdjacent : secondCurrent twin = firstCurrent twin + 1 := by
  cases twin
  change
    contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex (boundary + 1 + 2) =
      contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex (boundary + 2) + 1
  unfold contributionCapacityPostSettlementFutureBirthCurrentAt
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact]
  omega

theorem bothPaymentsRootExact :
    (firstRooted twin).rightReplay.2.futureBirth.actualExit.paymentOccurrence.rootOccurrence =
        M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
            (.finite (firstRooted twin).rightRootVisit) ∧
      (secondRooted twin).rightReplay.2.futureBirth.actualExit.paymentOccurrence.rootOccurrence =
        M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
            (.finite (secondRooted twin).rightRootVisit) :=
  ⟨(firstRooted twin).rightPaymentRootOccurrence_exact,
    (secondRooted twin).rightPaymentRootOccurrence_exact⟩

theorem bothSelfU8RuntimesConsumeExactCore :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        (firstExecution twin).core
        (M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.runtime
          (firstExecution twin)) 0 ∧
      SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        (secondExecution twin).core
        (M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.runtime
          (secondExecution twin)) 0 :=
  ⟨selfU8_runtimeConsumesExactCore (firstExecution twin),
    selfU8_runtimeConsumesExactCore (secondExecution twin)⟩

theorem allocationsUseExecutedRevisions :
    (firstAction twin).fieldGroundedRevision =
        (firstRevision twin).rightCore.revision ∧
      (secondAction twin).fieldGroundedRevision =
        (secondRevision twin).rightCore.revision :=
  ⟨rfl, rfl⟩

theorem bothCompilerGeneratedFirstWrites :
    (selfU8 (firstExecution twin)).firstWrite =
        (firstRevision twin).rightFirstWrite ∧
      (selfU8 (secondExecution twin)).firstWrite =
        (secondRevision twin).rightFirstWrite :=
  ⟨selfU8_firstWrite_isCompilerGenerated (firstExecution twin),
    selfU8_firstWrite_isCompilerGenerated (secondExecution twin)⟩

theorem firstSplitBudgetsExact :
    (oldRevisedEntryAt (firstRooted twin).rightRootVisit).progressBudget = 2 ∧
      (firstAction twin).left.progressBudget = 1 ∧
      (firstAction twin).right.progressBudget = 1 ∧
      (firstAction twin).left.progressBudget <
        (oldRevisedEntryAt
          (firstRooted twin).rightRootVisit).progressBudget :=
  let exact := (firstAllocation twin).splitBudgetsExact
  ⟨exact.1, exact.2.1, exact.2.2.1, exact.2.2.2.1⟩

theorem secondSplitBudgetsExact :
    (oldRevisedEntryAt (secondRooted twin).rightRootVisit).progressBudget = 2 ∧
      (secondAction twin).left.progressBudget = 1 ∧
      (secondAction twin).right.progressBudget = 1 ∧
      (secondAction twin).left.progressBudget <
        (oldRevisedEntryAt
          (secondRooted twin).rightRootVisit).progressBudget :=
  let exact := (secondAllocation twin).splitBudgetsExact
  ⟨exact.1, exact.2.1, exact.2.2.1, exact.2.2.2.1⟩

end SourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt

/-- Minimal necessary source-closure fibre for the database's false entity
continuation.  Both residuals are projections of exact compiler-generated
actions; callers cannot submit either endpoint or its budget. -/
structure DatabaseSourceClosedAdjacentEntityRenewalAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (twin : SourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt
      oldVisit sourceIndex boundary) : Type 30 where
  private mk ::
  targetIsNextSource :
    twin.firstAction.left.progressBudget =
      (oldRevisedEntryAt twin.secondRooted.rightRootVisit).progressBudget

/-- The database would have to refill finite source credit from `1` to `2`
before the second exact Payment.  Hence the source-closed adjacent entity
renewal fibre is empty. -/
theorem databaseSourceClosedAdjacentEntityRenewal_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (twin : SourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt
      oldVisit sourceIndex boundary) :
    IsEmpty (DatabaseSourceClosedAdjacentEntityRenewalAt twin) := by
  constructor
  intro continuation
  have firstTarget := twin.firstSplitBudgetsExact.2.1
  have secondSource := twin.secondSplitBudgetsExact.1
  have sourceClosure := continuation.targetIsNextSource
  rw [firstTarget, secondSource] at sourceClosure
  omega

/-- Pointwise strongest no-unbounded-history mouth for the canonical paid
tail: a database-forged source-closed history cannot even form its second
adjacent edge.  No infinite table is mentioned or stored. -/
theorem everyBoundary_rejectsDatabaseForgedSecondEntityEdge
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let twin :=
      sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
        sourceIndex boundary
    IsEmpty (DatabaseSourceClosedAdjacentEntityRenewalAt twin) :=
  databaseSourceClosedAdjacentEntityRenewal_isEmpty _

structure ProofCarryingContributionCapacityAdjacentPaidRootRefillNoGoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Prop where
  twinGenerated : Nonempty
    (SourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
      sourceIndex boundary)
  currentsAdjacent :
    let twin :=
      sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
        sourceIndex boundary
    twin.secondCurrent = twin.firstCurrent + 1
  bothPaymentRootsExact :
    let twin :=
      sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
        sourceIndex boundary
    twin.firstRooted.rightReplay.2.futureBirth.actualExit.paymentOccurrence.rootOccurrence =
        M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
            (.finite twin.firstRooted.rightRootVisit) ∧
      twin.secondRooted.rightReplay.2.futureBirth.actualExit.paymentOccurrence.rootOccurrence =
        M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
            (.finite twin.secondRooted.rightRootVisit)
  bothRuntimeCoreExact :
    let twin :=
      sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
        sourceIndex boundary
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        twin.firstExecution.core
        (M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.runtime
          twin.firstExecution) 0 ∧
      SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
        twin.secondExecution.core
        (M14SourceGeneratedContributionCapacityCofinalNoveltyU8Runtime.runtime
          twin.secondExecution) 0
  bothRevisionsAndFirstWritesExact :
    let twin :=
      sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
        sourceIndex boundary
    twin.firstAction.fieldGroundedRevision =
        twin.firstRevision.rightCore.revision ∧
      twin.secondAction.fieldGroundedRevision =
        twin.secondRevision.rightCore.revision ∧
      (selfU8 twin.firstExecution).firstWrite =
        twin.firstRevision.rightFirstWrite ∧
      (selfU8 twin.secondExecution).firstWrite =
        twin.secondRevision.rightFirstWrite
  bothStrictSplits :
    let twin :=
      sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
        sourceIndex boundary
    twin.firstAction.left.progressBudget = 1 ∧
      (oldRevisedEntryAt twin.firstRooted.rightRootVisit).progressBudget = 2 ∧
      twin.secondAction.left.progressBudget = 1 ∧
      (oldRevisedEntryAt twin.secondRooted.rightRootVisit).progressBudget = 2
  sourceClosedSecondEdgeEmpty :
    let twin :=
      sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
        sourceIndex boundary
    IsEmpty (DatabaseSourceClosedAdjacentEntityRenewalAt twin)

theorem proofCarryingContributionCapacityAdjacentPaidRootRefillNoGoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ProofCarryingContributionCapacityAdjacentPaidRootRefillNoGoAt oldVisit
      sourceIndex boundary :=
  let twin :=
    sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
      sourceIndex boundary
  { twinGenerated := ⟨twin⟩
    currentsAdjacent := twin.currentsAdjacent
    bothPaymentRootsExact := twin.bothPaymentsRootExact
    bothRuntimeCoreExact := twin.bothSelfU8RuntimesConsumeExactCore
    bothRevisionsAndFirstWritesExact :=
      ⟨twin.allocationsUseExecutedRevisions.1,
        twin.allocationsUseExecutedRevisions.2,
        twin.bothCompilerGeneratedFirstWrites.1,
        twin.bothCompilerGeneratedFirstWrites.2⟩
    bothStrictSplits :=
      ⟨twin.firstSplitBudgetsExact.2.1,
        twin.firstSplitBudgetsExact.1,
        twin.secondSplitBudgetsExact.2.1,
        twin.secondSplitBudgetsExact.1⟩
    sourceClosedSecondEdgeEmpty :=
      databaseSourceClosedAdjacentEntityRenewal_isEmpty twin }

abbrev ProofCarryingContributionCapacityAdjacentPaidRootRefillNoGoCertificate
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop :=
  ∀ boundary : Nat,
    ProofCarryingContributionCapacityAdjacentPaidRootRefillNoGoAt oldVisit
      sourceIndex boundary

theorem proofCarryingContributionCapacityAdjacentPaidRootRefillNoGo
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityAdjacentPaidRootRefillNoGoCertificate
      oldVisit sourceIndex :=
  proofCarryingContributionCapacityAdjacentPaidRootRefillNoGoAt oldVisit
    sourceIndex

theorem adjacentPaidRootRefillNoGo_hasNoCrossVisitHandoffOrFuture
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : True := by
  let twin :=
    sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt oldVisit
      sourceIndex boundary
  fail_if_success exact twin.crossVisitHandoff
  fail_if_success exact twin.sourceEquality
  fail_if_success exact twin.entityKey
  fail_if_success exact twin.history
  fail_if_success exact twin.paymentSchedule
  fail_if_success exact twin.completedFuture
  trivial

end
end M14SourceGeneratedContributionCapacityAdjacentPaidRootRefillNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityAdjacentPaidRootRefillNoGo.sourceGeneratedContributionCapacityAdjacentPaidRootDarkTwinAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityAdjacentPaidRootRefillNoGo.databaseSourceClosedAdjacentEntityRenewal_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityAdjacentPaidRootRefillNoGo.proofCarryingContributionCapacityAdjacentPaidRootRefillNoGo
