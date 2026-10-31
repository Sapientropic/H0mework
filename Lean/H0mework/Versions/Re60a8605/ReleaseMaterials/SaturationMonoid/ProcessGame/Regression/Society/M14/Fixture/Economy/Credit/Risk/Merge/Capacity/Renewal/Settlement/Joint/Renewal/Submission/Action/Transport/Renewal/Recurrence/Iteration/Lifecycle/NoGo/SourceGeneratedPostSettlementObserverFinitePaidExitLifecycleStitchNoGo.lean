import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Producer.SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Lifecycle.NoGo.SourceGeneratedPaidExitLifecycleMaximumNoGo

/-!
# Canonical absolute-stage kernel for the finite lifecycle stitch

The raw cycle-by-local-stage rectangle contains genuine overlaps: stage one
of one cycle is stage zero of the next.  Its canonical image is therefore the
`fuel + 4` absolute paid indices, not the raw product.  Every raw coordinate
factors through that image, and the factor map is surjective.

Equal absolute indices generate one actual renewal occurrence.  Different
absolute indices retain the same action readout while their outer authority,
actual-service `K` and event-selected Payment are all different.  This file
stores neither the raw rectangle nor the absolute image in a root; both are
bounded readout types for one explicitly requested fuel.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Capacity Space CrossingCost
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14ProofCarryingContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidSuccessorBearerExerciseStandingRenewal
open M14SourceGeneratedPaidSuccessorPostContinuationExternalResidualDisposition
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum
open M14SourceGeneratedPaidExitLifecycleMaximumNoGo
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch

/-- Raw bounded coordinates before shared occurrences are identified. -/
abbrev RawFinitePaidExitLifecycleStageAt (fuel : Nat) :=
  Fin (fuel + 1) × PaidExitLifecycleStage

/-- Canonical image of all raw stages.  There are `fuel + 4`, not
`4 * (fuel + 1)`, actual absolute occurrences. -/
abbrev AbsoluteFinitePaidExitLifecycleStageAt (fuel : Nat) := Fin (fuel + 4)

/-- Quotient map without introducing a new quotient ontology. -/
def rawFiniteLifecycleAbsoluteStageAt {fuel : Nat}
    (raw : RawFinitePaidExitLifecycleStageAt fuel) :
    AbsoluteFinitePaidExitLifecycleStageAt fuel :=
  ⟨raw.1.1 + raw.2.1, by
    have nodeBound := raw.1.2
    have stageBound := raw.2.2
    omega⟩

theorem rawFiniteLifecycleAbsoluteStage_surjective (fuel : Nat) :
    Function.Surjective
      (rawFiniteLifecycleAbsoluteStageAt (fuel := fuel)) := by
  intro absolute
  by_cases withinCycles : absolute.1 ≤ fuel
  · let node : Fin (fuel + 1) := ⟨absolute.1, by omega⟩
    let stage : PaidExitLifecycleStage := ⟨0, by decide⟩
    refine ⟨(node, stage), ?_⟩
    apply Fin.ext
    simp [rawFiniteLifecycleAbsoluteStageAt, node, stage]
  · let node : Fin (fuel + 1) := ⟨fuel, by omega⟩
    let stage : PaidExitLifecycleStage :=
      ⟨absolute.1 - fuel, by
        have absoluteBound := absolute.2
        omega⟩
    refine ⟨(node, stage), ?_⟩
    apply Fin.ext
    simp only [rawFiniteLifecycleAbsoluteStageAt, node, stage]
    omega

theorem sourceGeneratedStandingRenewals_heq_of_index_eq
    (oldVisit : OldVisit) (sourceIndex : Nat) {left right : Nat}
    (indexEquality : left = right) :
    HEq
      (sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
        sourceIndex left)
      (sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
        sourceIndex right) := by
  subst right
  rfl

variable {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
variable (initial : CycleAt oldVisit sourceIndex boundary)

include initial

/-- Absolute existing paid-renewal index, based at the actual first cycle
replay rather than a caller-supplied offset. -/
def absoluteLifecycleIndexAt
    (absolute : AbsoluteFinitePaidExitLifecycleStageAt fuel) : Nat :=
  cycleLifecycleIndex initial 0 + absolute.1

@[simp] theorem absoluteLifecycleIndex_exact
    (absolute : AbsoluteFinitePaidExitLifecycleStageAt fuel) :
    absoluteLifecycleIndexAt initial absolute =
      boundary + 2 + absolute.1 := by
  unfold absoluteLifecycleIndexAt
  rw [cycleLifecycleIndex_exact]

/-- One existing source-generated standing renewal at the canonical absolute
index. -/
def absoluteLifecycleRenewalAt
    (absolute : AbsoluteFinitePaidExitLifecycleStageAt fuel) :=
  sourceGeneratedPaidSuccessorBearerExerciseStandingRenewalAt oldVisit
    sourceIndex (absoluteLifecycleIndexAt initial absolute)

/-- Every raw restriction is the same dependent producer token as its
canonical absolute image.  `HEq` preserves the occurrence-indexed type
without introducing a second erased occurrence carrier. -/
theorem rawLifecycleStageRenewal_factors
    (raw : RawFinitePaidExitLifecycleStageAt fuel) :
    HEq (cycleLifecycleStageRenewalAt initial raw.1.1 raw.2)
      (absoluteLifecycleRenewalAt initial
        (rawFiniteLifecycleAbsoluteStageAt raw)) := by
  let leftIndex :=
    cycleLifecycleAbsoluteStageIndexAt initial raw.1.1 raw.2
  let rightIndex :=
    absoluteLifecycleIndexAt initial
      (rawFiniteLifecycleAbsoluteStageAt raw)
  have indexEquality : leftIndex = rightIndex := by
    unfold leftIndex rightIndex
    rw [cycleLifecycleAbsoluteStageIndex_exact,
      absoluteLifecycleIndex_exact]
    change boundary + raw.1.1 + 2 + raw.2.1 =
      boundary + 2 + (raw.1.1 + raw.2.1)
    omega
  exact sourceGeneratedStandingRenewals_heq_of_index_eq oldVisit sourceIndex
    indexEquality

/-! ## Absolute action, authority, K and Payment readouts -/

def absoluteLifecycleActionAt
    (absolute : AbsoluteFinitePaidExitLifecycleStageAt fuel) :=
  (absoluteLifecycleRenewalAt initial absolute).sourceConsequence.exerciseAction

def absoluteLifecycleOuterAuthorityAt
    (absolute : AbsoluteFinitePaidExitLifecycleStageAt fuel) :=
  (absoluteLifecycleRenewalAt initial absolute).sourceOuterAuthority

def absoluteLifecycleKAt
    (absolute : AbsoluteFinitePaidExitLifecycleStageAt fuel) :=
  (absoluteLifecycleRenewalAt initial absolute).sourceActualServiceK

def absoluteLifecyclePaymentOccurrenceAt
    (absolute : AbsoluteFinitePaidExitLifecycleStageAt fuel) :
    AnySourceBackedPaymentOccurrence :=
  contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
    sourceIndex (absoluteLifecycleIndexAt initial absolute)
    (absoluteLifecycleRenewalAt initial absolute
      ).sourceConsequence.actualExit

theorem absoluteLifecycleAction_constant
    (absolute : AbsoluteFinitePaidExitLifecycleStageAt fuel) :
    absoluteLifecycleActionAt initial absolute =
      birthBearerExactExitExerciseAction :=
  (absoluteLifecycleRenewalAt initial absolute).sourceAction_eq_canonical

theorem absoluteLifecycleOuterAuthority_injective :
    Function.Injective
      (absoluteLifecycleOuterAuthorityAt (fuel := fuel) initial) := by
  intro left right authorityEquality
  apply Fin.ext
  have currentEquality := congrArg Sigma.fst authorityEquality
  change
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (absoluteLifecycleIndexAt initial left) =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (absoluteLifecycleIndexAt initial right) at currentEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact,
    absoluteLifecycleIndex_exact, absoluteLifecycleIndex_exact] at currentEquality
  omega

theorem absoluteLifecycleK_injective :
    Function.Injective (absoluteLifecycleKAt (fuel := fuel) initial) := by
  intro left right authorityEquality
  apply Fin.ext
  have currentEquality :=
    contributionCapacityPostSettlementRenewalActualServiceOccurrenceAt_injective
      oldVisit sourceIndex authorityEquality
  change
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (absoluteLifecycleIndexAt initial left) =
      contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        (absoluteLifecycleIndexAt initial right) at currentEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact,
    absoluteLifecycleIndex_exact, absoluteLifecycleIndex_exact] at currentEquality
  omega

theorem absoluteLifecyclePaymentOccurrence_injective :
    Function.Injective
      (absoluteLifecyclePaymentOccurrenceAt (fuel := fuel) initial) := by
  intro left right paymentEquality
  apply Fin.ext
  have indexEquality :=
    contributionCapacityPostSettlementGeneratedPaymentOccurrences_indexLocked
      oldVisit sourceIndex
      (absoluteLifecycleRenewalAt initial left).sourceConsequence.actualExit
      (absoluteLifecycleRenewalAt initial right).sourceConsequence.actualExit
      paymentEquality
  rw [absoluteLifecycleIndex_exact, absoluteLifecycleIndex_exact] at indexEquality
  omega

/-- Exact partition by absolute occurrence identity. -/
theorem absoluteLifecycleSameOrStrongKernel
    (left right : AbsoluteFinitePaidExitLifecycleStageAt fuel) :
    (left = right ∧
        absoluteLifecycleOuterAuthorityAt initial left =
          absoluteLifecycleOuterAuthorityAt initial right ∧
        absoluteLifecycleKAt initial left =
          absoluteLifecycleKAt initial right ∧
        absoluteLifecyclePaymentOccurrenceAt initial left =
          absoluteLifecyclePaymentOccurrenceAt initial right) ∨
      (left ≠ right ∧
        absoluteLifecycleActionAt initial left =
          absoluteLifecycleActionAt initial right ∧
        absoluteLifecycleOuterAuthorityAt initial left ≠
          absoluteLifecycleOuterAuthorityAt initial right ∧
        absoluteLifecycleKAt initial left ≠
          absoluteLifecycleKAt initial right ∧
        absoluteLifecyclePaymentOccurrenceAt initial left ≠
          absoluteLifecyclePaymentOccurrenceAt initial right) := by
  by_cases same : left = right
  · subst right
    exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr
      ⟨same,
        (absoluteLifecycleAction_constant initial left).trans
          (absoluteLifecycleAction_constant initial right).symm,
        fun equality => same
          (absoluteLifecycleOuterAuthority_injective initial equality),
        fun equality => same (absoluteLifecycleK_injective initial equality),
        fun equality => same
          (absoluteLifecyclePaymentOccurrence_injective initial equality)⟩

/-! ## Action observer on the canonical absolute image -/

def absoluteLifecycleActionObserverAt :
    AuthorityObserver
      (AbsoluteFinitePaidExitLifecycleStageAt fuel)
      birthBearerExitExerciseController.ExactActionSeed
      AnyPeriodicActualServiceExit where
  forget := absoluteLifecycleActionAt initial
  authorityK := absoluteLifecycleKAt initial

def absoluteLifecycleStageZeroAt (fuel : Nat) :
    AbsoluteFinitePaidExitLifecycleStageAt fuel := ⟨0, by omega⟩

def absoluteLifecycleStageOneAt (fuel : Nat) :
    AbsoluteFinitePaidExitLifecycleStageAt fuel := ⟨1, by omega⟩

omit initial in theorem absoluteLifecycleStageZero_ne_one (fuel : Nat) :
    absoluteLifecycleStageZeroAt fuel ≠
      absoluteLifecycleStageOneAt fuel := by
  intro equality
  have valueEquality := congrArg Fin.val equality
  simp [absoluteLifecycleStageZeroAt, absoluteLifecycleStageOneAt] at valueEquality

def absoluteLifecycleActionKernelPairAt :
    AuthorityKernelPair
      (absoluteLifecycleActionObserverAt (fuel := fuel) initial) where
  left := absoluteLifecycleStageZeroAt fuel
  right := absoluteLifecycleStageOneAt fuel
  occurrence_ne := absoluteLifecycleStageZero_ne_one fuel
  visible_eq :=
    (absoluteLifecycleAction_constant initial
      (absoluteLifecycleStageZeroAt fuel)).trans
      (absoluteLifecycleAction_constant initial
        (absoluteLifecycleStageOneAt fuel)).symm
  authority_ne := fun equality =>
    absoluteLifecycleStageZero_ne_one fuel
      (absoluteLifecycleK_injective initial equality)

theorem absoluteLifecycleAction_noOccurrenceReconstruction :
    ¬ ∃ reconstruct : birthBearerExitExerciseController.ExactActionSeed →
        AbsoluteFinitePaidExitLifecycleStageAt fuel,
      Function.LeftInverse reconstruct
        (absoluteLifecycleActionObserverAt (fuel := fuel) initial).forget :=
  (absoluteLifecycleActionKernelPairAt (fuel := fuel) initial
    ).noOccurrenceLeftInverse

theorem absoluteLifecycleAction_noAuthorityFactorization :
    ¬ Nonempty
      (AuthorityFactorization
        (absoluteLifecycleActionObserverAt (fuel := fuel) initial)) :=
  (absoluteLifecycleActionKernelPairAt (fuel := fuel) initial
    ).noAuthorityFactorization

theorem absoluteLifecycleAction_noFaithfulReconstruction :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (absoluteLifecycleActionObserverAt (fuel := fuel) initial)) :=
  (absoluteLifecycleActionKernelPairAt (fuel := fuel) initial
    ).noFaithfulAuthorityReconstruction

/-! ## Explicit overlap control for the raw rectangle -/

def overlapLeftRawAt (edge : Fin fuel) :
    RawFinitePaidExitLifecycleStageAt fuel :=
  (⟨edge.1, by omega⟩, cycleLifecycleStageOne)

def overlapRightRawAt (edge : Fin fuel) :
    RawFinitePaidExitLifecycleStageAt fuel :=
  (⟨edge.1 + 1, by omega⟩, cycleLifecycleStageZero)

omit initial in theorem overlapRawCoordinates_ne (edge : Fin fuel) :
    overlapLeftRawAt edge ≠ overlapRightRawAt edge := by
  intro equality
  have nodeEquality := congrArg (fun raw => raw.1.1) equality
  simp [overlapLeftRawAt, overlapRightRawAt] at nodeEquality

omit initial in theorem overlapRawCoordinates_sameAbsolute (edge : Fin fuel) :
    rawFiniteLifecycleAbsoluteStageAt (overlapLeftRawAt edge) =
      rawFiniteLifecycleAbsoluteStageAt (overlapRightRawAt edge) := by
  apply Fin.ext
  simp [rawFiniteLifecycleAbsoluteStageAt, overlapLeftRawAt,
    overlapRightRawAt, cycleLifecycleStageOne, cycleLifecycleStageZero]

theorem rawSameAbsolute_sameRenewalProducer
    {left right : RawFinitePaidExitLifecycleStageAt fuel}
    (sameAbsolute : rawFiniteLifecycleAbsoluteStageAt left =
      rawFiniteLifecycleAbsoluteStageAt right) :
    HEq (cycleLifecycleStageRenewalAt initial left.1.1 left.2)
      (cycleLifecycleStageRenewalAt initial right.1.1 right.2) := by
  have physicalIndexEquality :
      cycleLifecycleAbsoluteStageIndexAt initial left.1.1 left.2 =
        cycleLifecycleAbsoluteStageIndexAt initial right.1.1 right.2 := by
    rw [cycleLifecycleAbsoluteStageIndex_exact,
      cycleLifecycleAbsoluteStageIndex_exact]
    have absoluteValueEquality := congrArg Fin.val sameAbsolute
    change left.1.1 + left.2.1 = right.1.1 + right.2.1 at absoluteValueEquality
    omega
  exact sourceGeneratedStandingRenewals_heq_of_index_eq oldVisit sourceIndex
    physicalIndexEquality

theorem overlapRawCoordinates_sameRenewalProducer (edge : Fin fuel) :
    cycleLifecycleStageRenewalAt initial edge.1 cycleLifecycleStageOne =
      cycleLifecycleStageRenewalAt initial (edge.1 + 1)
        cycleLifecycleStageZero :=
  cycleLifecycleStageOne_eq_nextStageZero initial edge.1

/-- False fibre retaining both complete lifecycle maxima while claiming that
two raw restrictions of one absolute occurrence are different. -/
structure ExactSameAbsoluteClaimedDifferentLifecycleOccurrenceAt
    (left right : RawFinitePaidExitLifecycleStageAt fuel) : Type 32 where
  leftMaximum :
    ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      (cycleLifecycleIndex initial left.1.1)
  rightMaximum :
    ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      (cycleLifecycleIndex initial right.1.1)
  sameAbsolute : rawFiniteLifecycleAbsoluteStageAt left =
    rawFiniteLifecycleAbsoluteStageAt right
  outerOccurrenceClaimedDifferent :
    absoluteLifecycleOuterAuthorityAt initial
        (rawFiniteLifecycleAbsoluteStageAt left) ≠
      absoluteLifecycleOuterAuthorityAt initial
        (rawFiniteLifecycleAbsoluteStageAt right)

theorem sameAbsoluteClaimedDifferentLifecycleOccurrence_isEmpty
    (left right : RawFinitePaidExitLifecycleStageAt fuel) :
    IsEmpty
      (ExactSameAbsoluteClaimedDifferentLifecycleOccurrenceAt initial left
        right) :=
  ⟨fun claimed => claimed.outerOccurrenceClaimedDifferent
    (congrArg (absoluteLifecycleOuterAuthorityAt initial)
      claimed.sameAbsolute)⟩

/-! ## Full-capture and residual-deletion controls at every cycle index -/

def cycleFullCaptureCounterlifeAt (depth : Nat) :=
  proofCarryingFullCapturePaidExitCounterlifeAt oldVisit sourceIndex
    (cycleLifecycleIndex initial depth)

@[simp] theorem cycleFullCaptureCounterlife_positive_isCycleMaximum
    (depth : Nat) :
    (cycleFullCaptureCounterlifeAt initial depth).positive =
      cycleLifecycleMaximum initial depth :=
  rfl

theorem cycleFullCaptureReportedMaximum_isEmpty (depth : Nat) :
    IsEmpty
      (ExactFullCaptureReportedPaidExitLifecycleMaximumAt
        (cycleFullCaptureCounterlifeAt initial depth)) :=
  fullCaptureReportedPaidExitLifecycleMaximum_isEmpty
    (cycleFullCaptureCounterlifeAt initial depth)

theorem cycleActionReadoutLeftInverse_isEmpty (depth : Nat) :
    IsEmpty
      (ExactPaidExitLifecycleActionReadoutLeftInverseAt
        (cycleLifecycleMaximum initial depth)) :=
  paidExitLifecycleActionReadoutLeftInverse_isEmpty
    (cycleLifecycleMaximum initial depth)

theorem cycleSourceOwnershipDeletion_isEmpty (depth : Nat) :
    IsEmpty
      (ExactPostContinuationSourceOwnershipDeletionAt
        (cycleLifecycleMaximum initial depth).disposition) :=
  lifecycleSourceOwnershipDeletion_isEmpty (cycleLifecycleMaximum initial depth)

theorem cycleRootConsumerDeletion_isEmpty (depth : Nat) :
    IsEmpty
      (ExactPostContinuationRootConsumerDeletionAt
        (cycleLifecycleMaximum initial depth).disposition) :=
  lifecycleRootConsumerDeletion_isEmpty (cycleLifecycleMaximum initial depth)

theorem cycleLocalEmptyErasure_isEmpty (depth : Nat) :
    IsEmpty
      (ExactPostContinuationLocalEmptyErasesExternalLiabilityAt
        (cycleLifecycleMaximum initial depth).disposition) :=
  lifecycleLocalEmptyErasure_isEmpty (cycleLifecycleMaximum initial depth)

end
end M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.rawFiniteLifecycleAbsoluteStage_surjective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.rawLifecycleStageRenewal_factors
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.absoluteLifecycleOuterAuthority_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.absoluteLifecycleK_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.absoluteLifecyclePaymentOccurrence_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.absoluteLifecycleSameOrStrongKernel
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.absoluteLifecycleAction_noFaithfulReconstruction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.overlapRawCoordinates_sameRenewalProducer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.sameAbsoluteClaimedDifferentLifecycleOccurrence_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitchNoGo.cycleFullCaptureReportedMaximum_isEmpty
