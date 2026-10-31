import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Consumer.ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Policy.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy

/-!
# Source-generated kernel for every finite adaptive observer

The policy's finite all-zero branch computes its own cutoff.  The canonical
paid replays at that cutoff and its successor follow the identical adaptive
branch and return the same answer, while their occurrences and actual-service
authorities remain distinct.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverKernel

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14ProofCarryingCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy.CanonicalPaidReplayFairFiniteAdaptivePolicy

universe u

/-- Every finite adaptive observer generates its own later paid kernel pair.
The caller supplies neither endpoints nor a collision. -/
theorem canonicalPaidReplayFairFiniteAdaptivePolicy_generatesKernel
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat)
    {Answer : Type u} {fuel : Nat}
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel) :
    let cutoff := adaptivePolicyCutoff requestedStage policy
    let pair :=
      canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
        cutoff
    requestedStage < pair.left.1 ∧
      requestedStage < pair.right.1 ∧
      zeroBranchBound policy < pair.left.1 ∧
      zeroBranchBound policy < pair.right.1 ∧
      policy.run pair.left = policy.zeroBranchAnswer ∧
      policy.run pair.right = policy.zeroBranchAnswer ∧
      policy.run pair.left = policy.run pair.right ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex cutoff
            pair.left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          cutoff pair.right ∧
      pair.left ≠ pair.right ∧
      pair.left.2.authorityK ≠ pair.right.2.authorityK ∧
      type_of% pair.left.2.paidStep_consumes_exactPayment ∧
      type_of% pair.left.2.paymentNext_isCanonicalTarget ∧
      type_of% pair.right.2.paidStep_consumes_exactPayment ∧
      type_of% pair.right.2.paymentNext_isCanonicalTarget ∧
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex cutoff pair.left) ∧
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex (cutoff + 1) pair.right) ∧
      type_of%
        (canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
          sourceIndex cutoff) ∧
      type_of%
        (canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
          cutoff) := by
  dsimp only
  let cutoff := adaptivePolicyCutoff requestedStage policy
  let pair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
      cutoff
  have requestedLtCutoff : requestedStage < cutoff :=
    requestedStage_lt_adaptivePolicyCutoff requestedStage policy
  have boundLtCutoff : zeroBranchBound policy < cutoff :=
    zeroBranchBound_lt_adaptivePolicyCutoff requestedStage policy
  have leftRun : policy.run pair.left = policy.zeroBranchAnswer :=
    policy.run_eq_zeroBranchAnswer_of_bound_lt pair.left (by
      change zeroBranchBound policy < cutoff
      exact boundLtCutoff)
  have rightRun : policy.run pair.right = policy.zeroBranchAnswer :=
    policy.run_eq_zeroBranchAnswer_of_bound_lt pair.right (by
      change zeroBranchBound policy < cutoff + 1
      omega)
  have leftWitness :
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex cutoff pair.left) := by
    change Nonempty
      (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex cutoff
        (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          cutoff))
    exact
      ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex cutoff⟩
  have rightWitness :
      Nonempty
        (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
          sourceIndex (cutoff + 1) pair.right) := by
    change Nonempty
      (SourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex (cutoff + 1)
        (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          (cutoff + 1)))
    exact
      ⟨sourceGeneratedCanonicalPaidReplayFairStageWitnessAt oldVisit
        sourceIndex (cutoff + 1)⟩
  exact
    ⟨by
        change requestedStage < cutoff
        exact requestedLtCutoff,
      by
        change requestedStage < cutoff + 1
        omega,
      by
        change zeroBranchBound policy < cutoff
        exact boundLtCutoff,
      by
        change zeroBranchBound policy < cutoff + 1
        omega,
      leftRun,
      rightRun,
      leftRun.trans rightRun.symm,
      canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq oldVisit
        sourceIndex cutoff,
      pair.occurrence_ne,
      pair.authority_ne,
      pair.left.2.paidStep_consumes_exactPayment,
      pair.left.2.paymentNext_isCanonicalTarget,
      pair.right.2.paidStep_consumes_exactPayment,
      pair.right.2.paymentNext_isCanonicalTarget,
      leftWitness,
      rightWitness,
      canonicalPaidReplayFairFiniteWitnessStage_directConsumer oldVisit
        sourceIndex cutoff,
      canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
        cutoff⟩

/-- The output map of every finite adaptive policy is noninjective on the
existing paid-replay family. -/
theorem canonicalPaidReplayFairFiniteAdaptivePolicy_run_notInjective
    (oldVisit : OldVisit) (sourceIndex : Nat) {Answer : Type u} {fuel : Nat}
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel) :
    ¬ Function.Injective
      (policy.run (oldVisit := oldVisit) (sourceIndex := sourceIndex)) := by
  intro runInjective
  let cutoff := adaptivePolicyCutoff 0 policy
  let pair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
      cutoff
  have kernel :=
    canonicalPaidReplayFairFiniteAdaptivePolicy_generatesKernel oldVisit
      sourceIndex 0 policy
  exact pair.occurrence_ne (runInjective kernel.2.2.2.2.2.2.1)

/-- No decoder from a finite adaptive answer is a left inverse for every paid
occurrence. -/
theorem canonicalPaidReplayFairFiniteAdaptivePolicy_noOccurrenceDecoder
    (oldVisit : OldVisit) (sourceIndex : Nat) {Answer : Type u} {fuel : Nat}
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel)
    (decode : Answer →
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex) :
    ¬ ∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      decode (policy.run replay) = replay := by
  intro reconstruction
  let cutoff := adaptivePolicyCutoff 0 policy
  let pair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
      cutoff
  have kernel :=
    canonicalPaidReplayFairFiniteAdaptivePolicy_generatesKernel oldVisit
      sourceIndex 0 policy
  have outputEquality : policy.run pair.left = policy.run pair.right :=
    kernel.2.2.2.2.2.2.1
  have decodedEquality := congrArg decode outputEquality
  apply pair.occurrence_ne
  exact (reconstruction pair.left).symm.trans
    (decodedEquality.trans (reconstruction pair.right))

/-- No decoder from a finite adaptive answer reconstructs every actual-service
authority K. -/
theorem canonicalPaidReplayFairFiniteAdaptivePolicy_noAuthorityKDecoder
    (oldVisit : OldVisit) (sourceIndex : Nat) {Answer : Type u} {fuel : Nat}
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel)
    (decode : Answer → AnyPeriodicActualServiceExit) :
    ¬ ∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      decode (policy.run replay) = replay.2.authorityK := by
  intro reconstruction
  let cutoff := adaptivePolicyCutoff 0 policy
  let pair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
      cutoff
  have kernel :=
    canonicalPaidReplayFairFiniteAdaptivePolicy_generatesKernel oldVisit
      sourceIndex 0 policy
  have outputEquality : policy.run pair.left = policy.run pair.right :=
    kernel.2.2.2.2.2.2.1
  have decodedEquality := congrArg decode outputEquality
  apply pair.authority_ne
  exact (reconstruction pair.left).symm.trans
    (decodedEquality.trans (reconstruction pair.right))

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverKernel
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverKernel.canonicalPaidReplayFairFiniteAdaptivePolicy_generatesKernel
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverKernel.canonicalPaidReplayFairFiniteAdaptivePolicy_run_notInjective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverKernel.canonicalPaidReplayFairFiniteAdaptivePolicy_noOccurrenceDecoder
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverKernel.canonicalPaidReplayFairFiniteAdaptivePolicy_noAuthorityKDecoder
