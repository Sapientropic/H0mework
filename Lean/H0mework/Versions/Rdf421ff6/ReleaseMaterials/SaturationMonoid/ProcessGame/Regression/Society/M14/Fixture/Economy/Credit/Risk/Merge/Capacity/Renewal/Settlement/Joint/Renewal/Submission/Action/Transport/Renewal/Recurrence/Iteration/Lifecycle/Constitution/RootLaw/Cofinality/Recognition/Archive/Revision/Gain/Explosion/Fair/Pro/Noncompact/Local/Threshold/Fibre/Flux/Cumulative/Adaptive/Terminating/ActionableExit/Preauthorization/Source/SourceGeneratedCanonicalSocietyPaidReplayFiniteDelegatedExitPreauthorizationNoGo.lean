import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Kernel.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverKernel
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Audit.Source.SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit

/-!
# No uniformly finite delegated actionable-exit preauthorization

A finite adaptive observer may emit an existing exit-authority candidate, but
its source-generated kernel forces the same output on two distinct complete
UBI Payment/action authorities.  Neither full exit authority nor its exact
Payment occurrence can be preauthorized uniformly by such an observer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFiniteDelegatedExitPreauthorizationNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteRecognitionFlux
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverPolicy.CanonicalPaidReplayFairFiniteAdaptivePolicy
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteAdaptiveObserverKernel
open M14SourceGeneratedCanonicalSocietyPaidReplayPointwiseActionableExitAudit

universe u

/-- A finite exit-authority policy generates an exact conflict between two
real, source-backed actionable exits. -/
theorem finiteAdaptivePolicy_generatesActionableExitConflict
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat) {fuel : Nat}
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy
      AnyPeriodicActualServiceExit fuel) :
    let cutoff := adaptivePolicyCutoff requestedStage policy
    let pair :=
      canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
        cutoff
    type_of%
        (canonicalPaidReplayFairFiniteAdaptivePolicy_generatesKernel oldVisit
          sourceIndex requestedStage policy) ∧
      policy.run pair.left = policy.run pair.right ∧
      pair.left.2.authorityK ≠ pair.right.2.authorityK ∧
      pair.left.2.authorityK.paymentOccurrence ≠
        pair.right.2.authorityK.paymentOccurrence ∧
      ¬ (policy.run pair.left = pair.left.2.authorityK ∧
        policy.run pair.right = pair.right.2.authorityK) ∧
      (geometryCompilerAt
          pair.left.2.authorityK.2.depth).actionableExitCapacity = 1 ∧
      (geometryCompilerAt
          pair.right.2.authorityK.2.depth).actionableExitCapacity = 1 ∧
      (capturedGeometryCompilerAt
          pair.left.2.authorityK.2.depth).actionableExitCapacity = 0 ∧
      (capturedGeometryCompilerAt
          pair.right.2.authorityK.2.depth).actionableExitCapacity = 0 ∧
      Nonempty
        ((geometryCompilerAt pair.left.2.authorityK.2.depth
          ).SourceGeneratedActionableExitRenewalAt) ∧
      Nonempty
        ((geometryCompilerAt pair.right.2.authorityK.2.depth
          ).SourceGeneratedActionableExitRenewalAt) ∧
      type_of%
        (canonicalPaidReplayFairPointwiseActionableExitAudit oldVisit
          sourceIndex pair.left) ∧
      type_of%
        (canonicalPaidReplayFairPointwiseActionableExitAudit oldVisit
          sourceIndex pair.right) ∧
      type_of% pair.left.2.paidStep_consumes_exactPayment ∧
      type_of% pair.left.2.paymentNext_isCanonicalTarget ∧
      type_of% pair.right.2.paidStep_consumes_exactPayment ∧
      type_of% pair.right.2.paymentNext_isCanonicalTarget ∧
      type_of%
        (canonicalPaidReplayFairSuccessorRecognitionFlux oldVisit sourceIndex
          cutoff) := by
  dsimp only
  let cutoff := adaptivePolicyCutoff requestedStage policy
  let pair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
      cutoff
  have kernel :=
    canonicalPaidReplayFairFiniteAdaptivePolicy_generatesKernel oldVisit
      sourceIndex requestedStage policy
  rcases kernel with
    ⟨requestedLeft, requestedRight, boundLeft, boundRight, leftZero,
      rightZero, outputEquality, visibleEquality, occurrenceNe, authorityNe,
      leftPayment, leftNext, rightPayment, rightNext, leftWitness,
      rightWitness, stageConsumer, successorFlux⟩
  have noJointExact :
      ¬ (policy.run pair.left = pair.left.2.authorityK ∧
        policy.run pair.right = pair.right.2.authorityK) := by
    rintro ⟨leftExact, rightExact⟩
    apply authorityNe
    exact leftExact.symm.trans (outputEquality.trans rightExact)
  have paymentNe :
      pair.left.2.authorityK.paymentOccurrence ≠
        pair.right.2.authorityK.paymentOccurrence := by
    intro paymentEquality
    exact occurrenceNe
      (canonicalPaidReplay_actionableExitPayment_injective oldVisit
        sourceIndex paymentEquality)
  exact
    ⟨canonicalPaidReplayFairFiniteAdaptivePolicy_generatesKernel oldVisit
        sourceIndex requestedStage policy,
      outputEquality,
      authorityNe,
      paymentNe,
      noJointExact,
      pair.left.2.authorityK.2.actualExit.exactCapacity,
      pair.right.2.authorityK.2.actualExit.exactCapacity,
      pair.left.2.authorityK.2.actualExit.capturedCapacity,
      pair.right.2.authorityK.2.actualExit.capturedCapacity,
      ⟨pair.left.2.authorityK.2.actualExit.actionableRenewal⟩,
      ⟨pair.right.2.authorityK.2.actualExit.actionableRenewal⟩,
      canonicalPaidReplayFairPointwiseActionableExitAudit oldVisit sourceIndex
        pair.left,
      canonicalPaidReplayFairPointwiseActionableExitAudit oldVisit sourceIndex
        pair.right,
      leftPayment,
      leftNext,
      rightPayment,
      rightNext,
      successorFlux⟩

/-- Even the exact UBI Payment occurrence cannot be reconstructed for every
paid replay through one finite adaptive observer. -/
theorem finiteAdaptivePolicy_cannotPredictEveryExactUBIPayment
    (oldVisit : OldVisit) (sourceIndex : Nat) {Answer : Type u} {fuel : Nat}
    (policy : CanonicalPaidReplayFairFiniteAdaptivePolicy Answer fuel)
    (decode : Answer → AnySourceBackedPaymentOccurrence) :
    ¬ ∀ replay :
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      decode (policy.run replay) =
        replay.2.authorityK.paymentOccurrence := by
  intro predictsEveryPayment
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
  have paymentEquality :
      pair.left.2.authorityK.paymentOccurrence =
        pair.right.2.authorityK.paymentOccurrence :=
    (predictsEveryPayment pair.left).symm.trans
      (decodedEquality.trans (predictsEveryPayment pair.right))
  exact pair.occurrence_ne
    (canonicalPaidReplay_actionableExitPayment_injective oldVisit sourceIndex
      paymentEquality)

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFiniteDelegatedExitPreauthorizationNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteDelegatedExitPreauthorizationNoGo.finiteAdaptivePolicy_generatesActionableExitConflict
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteDelegatedExitPreauthorizationNoGo.finiteAdaptivePolicy_cannotPredictEveryExactUBIPayment
