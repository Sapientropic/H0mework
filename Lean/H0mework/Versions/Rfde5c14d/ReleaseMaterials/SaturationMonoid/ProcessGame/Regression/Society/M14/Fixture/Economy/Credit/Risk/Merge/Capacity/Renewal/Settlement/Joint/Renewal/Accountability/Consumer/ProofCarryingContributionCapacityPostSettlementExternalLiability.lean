import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Accountability.Producer.SourceGeneratedContributionCapacityPostSettlementExternalLiability

/-!
# Direct consumer of post-settlement external liability

Every reachable empty-ledger current reconstructs the pointwise payment
responsibility certificate.  Root, payment, and actual-service occurrence
families remain injective, so neither one payment nor one accountability proof
can be replayed as a completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityPostSettlementExternalLiability

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability

theorem contributionCapacityPostSettlementReachableRootOccurrences_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective (fun index =>
      contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit
        sourceIndex
        (contributionCapacityPostSettlementReachableCurrentAt oldVisit
          sourceIndex index)) := by
  intro left right occurrenceEquality
  have currentEquality :=
    contributionCapacityPostSettlementRenewalOccurrenceAt_injective oldVisit
      sourceIndex occurrenceEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
  omega

theorem contributionCapacityPostSettlementReachablePaymentOccurrences_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective (fun index =>
      periodicPaymentOccurrenceAt
        (contributionCapacityPostSettlementReachableCurrentAt oldVisit
          sourceIndex index)) := by
  intro left right occurrenceEquality
  have currentEquality := periodicPaymentOccurrenceAt_injective occurrenceEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
  omega

theorem contributionCapacityPostSettlementReachableActualServiceOccurrences_injective
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Function.Injective (fun index =>
      periodicActualServiceExitOccurrenceAt
        (contributionCapacityPostSettlementReachableCurrentAt oldVisit
          sourceIndex index)) := by
  intro left right occurrenceEquality
  have currentEquality :=
    periodicActualServiceExitOccurrenceAt_injective occurrenceEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
  omega

/-- Existing heterogeneous payment occurrence carrier, now filled by an
arbitrary actual-exit witness at the reachable post-root index. -/
def contributionCapacityPostSettlementPaymentOccurrenceOfExitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (actualExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index)) : AnySourceBackedPaymentOccurrence :=
  ⟨temporalVisitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex index),
    actualExit.paymentOccurrence⟩

/-- Even non-canonical witnesses eliminated from `periodicExitGenerated`
cannot replay one payment occurrence at two reachable post-root indices. -/
theorem contributionCapacityPostSettlementGeneratedPaymentOccurrences_indexLocked
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {left right : Nat}
    (leftExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex left))
    (rightExit : PeriodicActualServiceExitAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit
        sourceIndex right))
    (occurrenceEquality :
      contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
          sourceIndex left leftExit =
        contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
          sourceIndex right rightExit) :
    left = right := by
  have visitEquality := congrArg Sigma.fst occurrenceEquality
  have currentEquality := temporalVisitAt_injective visitEquality
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
    contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
  omega

/-- Pointwise visible responsibility at every reachable post-settlement
current.  The quantifier is consumed on demand; no `Nat → receipt` data field
is installed in either root. -/
theorem everyContributionCapacityPostSettlementCurrent_hasExternalLiability
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty (contributionCapacityJointSettlementEmptyLedger oldVisit).Entry ∧
      IsEmpty
        (OpenResponsibilityAt (JointSettlementNAt oldVisit)
          (contributionCapacityPostSettlementExactRootEventAt oldVisit
            sourceIndex index).occurrence.1) ∧
      ContributionCapacityPostSettlementExternalPaymentAuthorityAt oldVisit
        sourceIndex index
        (contributionCapacityPostSettlementExactRootEventAt oldVisit
          sourceIndex index) := by
  let accounted :=
    sourceGeneratedContributionCapacityPostSettlementExternalLiabilityAt
      oldVisit sourceIndex index
  exact ⟨accounted.localLedgerEmpty, accounted.occurrenceLocalLedgerEmpty,
    accounted.generatedExternalPaymentAuthority⟩

structure ProofCarryingContributionCapacityPostSettlementExternalLiabilityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  everyReachable : ∀ index : Nat,
    CanonicalPostSettlementExternalLiabilityAccountedAt oldVisit sourceIndex
      index
  everyCurrentExact : ∀ index : Nat,
    contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        index =
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex +
        index
  everyVisibleExternalLiability : ∀ index : Nat,
    IsEmpty (contributionCapacityJointSettlementEmptyLedger oldVisit).Entry ∧
      IsEmpty
        (OpenResponsibilityAt (JointSettlementNAt oldVisit)
          (contributionCapacityPostSettlementExactRootEventAt oldVisit
            sourceIndex index).occurrence.1) ∧
      ContributionCapacityPostSettlementExternalPaymentAuthorityAt oldVisit
        sourceIndex index
        (contributionCapacityPostSettlementExactRootEventAt oldVisit
          sourceIndex index)
  noLocalEmptyLedgerErasure : ∀ index : Nat,
    ¬ (IsEmpty
          (OpenResponsibilityAt (JointSettlementNAt oldVisit)
            (contributionCapacityPostSettlementExactRootEventAt oldVisit
              sourceIndex index).occurrence.1) →
        ¬ ContributionCapacityPostSettlementExternalPaymentAuthorityAt
          oldVisit sourceIndex index
          (contributionCapacityPostSettlementExactRootEventAt oldVisit
            sourceIndex index))
  rootOccurrencesInjective : Function.Injective (fun index =>
    contributionCapacityPostSettlementRenewalOccurrenceAt oldVisit sourceIndex
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        index))
  paymentOccurrencesInjective : Function.Injective (fun index =>
    periodicPaymentOccurrenceAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        index))
  actualServiceOccurrencesInjective : Function.Injective (fun index =>
    periodicActualServiceExitOccurrenceAt
      (contributionCapacityPostSettlementReachableCurrentAt oldVisit sourceIndex
        index))
  generatedPaymentOccurrencesIndexLocked :
    ∀ {left right : Nat}
      (leftExit : PeriodicActualServiceExitAt
        (contributionCapacityPostSettlementReachableCurrentAt oldVisit
          sourceIndex left))
      (rightExit : PeriodicActualServiceExitAt
        (contributionCapacityPostSettlementReachableCurrentAt oldVisit
          sourceIndex right)),
      contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
          sourceIndex left leftExit =
        contributionCapacityPostSettlementPaymentOccurrenceOfExitAt oldVisit
          sourceIndex right rightExit →
        left = right

theorem proofCarryingContributionCapacityPostSettlementExternalLiability
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityPostSettlementExternalLiabilityAt oldVisit
      sourceIndex where
  everyReachable :=
    sourceGeneratedContributionCapacityPostSettlementExternalLiabilityAt
      oldVisit sourceIndex
  everyCurrentExact :=
    contributionCapacityPostSettlementReachableCurrentAt_exact oldVisit
      sourceIndex
  everyVisibleExternalLiability := fun index =>
    let visible :=
      everyContributionCapacityPostSettlementCurrent_hasExternalLiability
        oldVisit sourceIndex index
    ⟨visible.1, visible.2.1, visible.2.2⟩
  noLocalEmptyLedgerErasure :=
    contributionCapacityPostSettlementEmptyLedger_doesNotEraseExternalLiability
      oldVisit sourceIndex
  rootOccurrencesInjective :=
    contributionCapacityPostSettlementReachableRootOccurrences_injective
      oldVisit sourceIndex
  paymentOccurrencesInjective :=
    contributionCapacityPostSettlementReachablePaymentOccurrences_injective
      oldVisit sourceIndex
  actualServiceOccurrencesInjective :=
    contributionCapacityPostSettlementReachableActualServiceOccurrences_injective
      oldVisit sourceIndex
  generatedPaymentOccurrencesIndexLocked :=
    contributionCapacityPostSettlementGeneratedPaymentOccurrences_indexLocked
      oldVisit sourceIndex

end
end M14ProofCarryingContributionCapacityPostSettlementExternalLiability
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementExternalLiability.everyContributionCapacityPostSettlementCurrent_hasExternalLiability
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityPostSettlementExternalLiability.proofCarryingContributionCapacityPostSettlementExternalLiability
