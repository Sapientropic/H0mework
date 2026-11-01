import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Producer.SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.NoGo.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo

/-!
# Pairwise kernel and worthiness no-gos for finite self-U8 iteration

Every requested node is read from the span carried by the recursively
generated cycle, not from a sibling canonical cycle.  Exact temporal indices
then make the node actual paths, authority `K`s and event-selected Payment
occurrences injective, while every visible singleton pulse has the same
normal form.

The negative is genuinely pairwise: it compares arbitrary nodes of a
requested finite prefix and does not chain adjacent inequalities.  Each edge
also inherits the universal administrative / worthiness reconstruction
no-gos from its exact recurrence token.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer Renewal UniversalRootGrammar
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14ProofCarryingContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphism
open M14SourceGeneratedPostSettlementObserverPaidSuccessorRenewal
open M14ProofCarryingPostSettlementObserverPaidSuccessorRenewal
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence
open M14SourceGeneratedPostSettlementObserverPaidSelfU8Recurrence.SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceAt
open M14SourceGeneratedPostSettlementObserverPaidSelfU8RecurrenceNoGo
open M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open M14SourceGeneratedPaidSuccessorAfterRefusalRetypingNoGo
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
variable (initial : CycleAt oldVisit sourceIndex boundary)

include initial

/-! ## Source-carried node readouts -/

/-- The node replay is packaged from the span physically carried by the
recursively generated cycle.  The index is fixed by that span's boundary. -/
def cycleReplayAt (depth : Nat) :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex :=
  ⟨(rightReplayAt oldVisit sourceIndex (boundary + depth)).1,
    replay (cycleAt initial depth).1⟩

/-- The source-carried replay is the existing paid replay at its exact linear
index.  This is a provenance bridge, not a second constructor call in the
iteration successor clause. -/
theorem cycleReplayAt_exact (depth : Nat) :
    cycleReplayAt initial depth =
      contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        (boundary + depth + 2) := by
  rcases cycleAt initial depth with ⟨span, authority, ⟨morphism, certificate⟩⟩
  cases morphism
  cases span
  rfl

@[simp] theorem cycleReplayAt_index (depth : Nat) :
    (cycleReplayAt initial depth).1 = boundary + depth + 2 := by
  rfl

@[simp] theorem cycleReplayAt_current (depth : Nat) :
    (cycleReplayAt initial depth).2.current =
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex +
        (boundary + depth + 2) := by
  exact (cycleReplayAt initial depth).2.current_exact

/-- Event-selected Payment occurrence at this exact cycle replay. -/
def cyclePaymentOccurrenceAt (depth : Nat) :
    AnySourceBackedPaymentOccurrence :=
  contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
    sourceIndex (cycleReplayAt initial depth).1
    (cycleReplayAt initial depth).2.futureBirth.actualExit

/-! ## Arbitrary-node injectivity and equal visible normal form -/

theorem cycleActualPath_injective :
    Function.Injective (fun depth =>
      (cycleReplayAt initial depth).2.actualPath) := by
  intro left right pathEquality
  have indexEquality := congrArg Sigma.fst pathEquality
  change boundary + left + 2 = boundary + right + 2 at indexEquality
  omega

theorem cycleVisibleNormalForm_eq (left right : Nat) :
    (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex).forget (cycleReplayAt initial left) =
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex).forget (cycleReplayAt initial right) := by
  change (cycleReplayAt initial left).2.singletonPulse =
    (cycleReplayAt initial right).2.singletonPulse
  rw [(cycleReplayAt initial left).2.singletonPulse_eq_one,
    (cycleReplayAt initial right).2.singletonPulse_eq_one]

theorem cycleAuthorityK_injective :
    Function.Injective (fun depth =>
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex).authorityK (cycleReplayAt initial depth)) := by
  intro left right authorityEquality
  have currentEquality :=
    periodicActualServiceExitOccurrenceAt_injective authorityEquality
  change
    contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex (boundary + left + 2) =
      contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
        sourceIndex (boundary + right + 2) at currentEquality
  unfold contributionCapacityPostSettlementFutureBirthCurrentAt at currentEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
  omega

theorem cyclePaymentOccurrence_injective :
    Function.Injective (cyclePaymentOccurrenceAt initial) := by
  intro left right paymentEquality
  have indexEquality :=
    contributionCapacityPostSettlementGeneratedPaymentOccurrences_indexLocked
      oldVisit sourceIndex
      (cycleReplayAt initial left).2.futureBirth.actualExit
      (cycleReplayAt initial right).2.futureBirth.actualExit paymentEquality
  simp only [cycleReplayAt_index] at indexEquality
  omega

/-- Strong arbitrary-node form: different actual paths, one visible normal
form, different authority `K`, and different event-selected Payments. -/
theorem cyclePairwiseStrongKernel
    {left right : Nat} (different : left ≠ right) :
    (cycleReplayAt initial left).2.actualPath ≠
        (cycleReplayAt initial right).2.actualPath ∧
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget (cycleReplayAt initial left) =
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget (cycleReplayAt initial right) ∧
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).authorityK (cycleReplayAt initial left) ≠
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).authorityK (cycleReplayAt initial right) ∧
      cyclePaymentOccurrenceAt initial left ≠
        cyclePaymentOccurrenceAt initial right :=
  ⟨fun equality => different (cycleActualPath_injective initial equality),
    cycleVisibleNormalForm_eq initial left right,
    fun equality => different (cycleAuthorityK_injective initial equality),
    fun equality => different (cyclePaymentOccurrence_injective initial equality)⟩

/-! ## Proof-relevant replay false fibre -/

structure ExactFiniteCyclePaymentReplaysAt (left right : Nat) : Prop where
  leftMorphismCertificate :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (cycleMorphism (cycleAt initial left))
  rightMorphismCertificate :
    ProofCarryingPostSettlementObserverAuthorityRevisedDispositionMorphismAt
      (cycleMorphism (cycleAt initial right))
  indicesDifferent : left ≠ right
  paymentOccurrenceReplayed :
    cyclePaymentOccurrenceAt initial left =
      cyclePaymentOccurrenceAt initial right

theorem exactFiniteCyclePaymentReplays_isEmpty (left right : Nat) :
    IsEmpty (ExactFiniteCyclePaymentReplaysAt initial left right) :=
  ⟨fun replayed => replayed.indicesDifferent
    (cyclePaymentOccurrence_injective initial replayed.paymentOccurrenceReplayed)⟩

/-! ## Every exact edge retains arbitrary worthiness no-gos -/

theorem stepAntiRetaliationStandingRenewal_isCurrentPaidRenewal
    (depth : Nat) :
    (antiRetaliationAt (stepAt initial depth)).standingRenewal =
      (stepAt initial depth).currentPaidRenewal :=
  antiRetaliationStandingRenewal_isCurrentPaidRenewal (stepAt initial depth)

theorem stepNext_noOccurrenceReconstruction (depth : Nat) :
    ¬ ∃ reconstruct : ContributionCapacityFutureBirthPulse →
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget :=
  nextNoOccurrenceReconstruction (stepAt initial depth)

theorem stepNext_noAuthorityFactorization (depth : Nat) :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex)) :=
  nextNoAuthorityFactorization (stepAt initial depth)

theorem stepNext_noFaithfulReconstruction (depth : Nat) :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex)) :=
  nextNoFaithfulReconstruction (stepAt initial depth)

theorem stepAdministrativeLabel_noAuthorityFactorization
    (depth : Nat)
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    ¬ Nonempty
      (AuthorityFactorization
        (administrativeRetaliationObserver oldVisit sourceIndex label)) :=
  administrativeLabel_noAuthorityFactorization (stepAt initial depth) label

theorem stepAdministrativeLabel_noOccurrenceLeftInverse
    (depth : Nat)
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    ¬ ∃ reconstruct : AdministrativeRetaliationVisible →
        AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (administrativeRetaliationObserver oldVisit sourceIndex label
          ).forget :=
  administrativeLabel_noOccurrenceLeftInverse (stepAt initial depth) label

theorem stepAdministrativeLabel_noFaithfulReconstruction
    (depth : Nat)
    (label : AdministrativeRetaliationOccurrenceAt oldVisit sourceIndex →
      Bool) :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (administrativeRetaliationObserver oldVisit sourceIndex label)) :=
  administrativeLabel_noFaithfulReconstruction (stepAt initial depth) label

omit initial in theorem administrativeLabels_doNotChangeIterationRestriction :
    administrativeEligibilityReadout false =
      administrativeEligibilityReadout true :=
  administrative_labels_do_not_control_renewal

end
end M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo.cycleActualPath_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo.cycleReplayAt_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo.cycleVisibleNormalForm_eq
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo.cycleAuthorityK_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo.cyclePaymentOccurrence_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo.cyclePairwiseStrongKernel
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo.exactFiniteCyclePaymentReplays_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo.stepNext_noFaithfulReconstruction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8IterationNoGo.stepAdministrativeLabel_noFaithfulReconstruction
