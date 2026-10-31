import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Replay.Producer.SourceGeneratedContributionCapacityPostSettlementPaidReplay

/-!
# Cofinal source-productive novelty in the canonical paid tail

After every finite absolute boundary, the installed post-root runtime itself
generates two distinct later paid replays.  Their genuine singleton frontier
pulses agree while their actual-service authorities differ.  This produces a
cofinal authority-kernel obstruction without accepting either replay, their
inequality, a normalizer, an authority difference or a future U8 as input.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCofinalProductiveNovelty

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay

/-- The observer computes a real singleton finite-frontier pulse from each
rich paid replay and retains its actual-service occurrence as authority `K`. -/
def contributionCapacityPostSettlementPaidReplayPulseObserver
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AuthorityObserver
      (AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
      ContributionCapacityFutureBirthPulse AnyPeriodicActualServiceExit where
  forget := fun replay => replay.2.singletonPulse
  authorityK := fun replay => replay.2.authorityK

def contributionCapacityPostSettlementNoveltyLeftReplayAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex :=
  contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
    (boundary + 1)

def contributionCapacityPostSettlementNoveltyRightReplayAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex :=
  contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
    (boundary + 2)

/-- The actual pair is generated from the boundary and the open paid tail. -/
def contributionCapacityPostSettlementCofinalNoveltyKernelPairAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AuthorityKernelPair
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex) where
  left := contributionCapacityPostSettlementNoveltyLeftReplayAt oldVisit
    sourceIndex boundary
  right := contributionCapacityPostSettlementNoveltyRightReplayAt oldVisit
    sourceIndex boundary
  occurrence_ne := by
    intro equality
    have indexEquality := congrArg Sigma.fst equality
    change boundary + 1 = boundary + 2 at indexEquality
    omega
  visible_eq := by
    change
      sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
          oldVisit sourceIndex (boundary + 1) 1 =
        sourceGeneratedContributionCapacityPostSettlementFutureBirthPulse
          oldVisit sourceIndex (boundary + 2) 1
    rw [contributionCapacityPostSettlementFutureBirthPulse_eq_horizon,
      contributionCapacityPostSettlementFutureBirthPulse_eq_horizon]
  authority_ne := by
    intro equality
    have currentEquality :=
      periodicActualServiceExitOccurrenceAt_injective equality
    change
      contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex (boundary + 1) =
        contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
          sourceIndex (boundary + 2) at currentEquality
    unfold contributionCapacityPostSettlementFutureBirthCurrentAt at currentEquality
    rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
      contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
    omega

/-- Pointwise source-produced novelty.  The token has no fields: all two-path
data and all obstruction proofs are regenerated from its exact boundary. -/
inductive SourceProductiveNoveltyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 28
  | private generated

def sourceGeneratedContributionCapacitySourceProductiveNoveltyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceProductiveNoveltyAt oldVisit sourceIndex boundary :=
  .generated

namespace SourceProductiveNoveltyAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  (novelty : SourceProductiveNoveltyAt oldVisit sourceIndex boundary)

theorem eq_generated :
    novelty =
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary := by
  cases novelty
  rfl

def leftReplay :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex := by
  cases novelty
  exact contributionCapacityPostSettlementNoveltyLeftReplayAt oldVisit
    sourceIndex boundary

def rightReplay :
    AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex := by
  cases novelty
  exact contributionCapacityPostSettlementNoveltyRightReplayAt oldVisit
    sourceIndex boundary

def kernelPair :
    AuthorityKernelPair
      (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex) := by
  cases novelty
  exact contributionCapacityPostSettlementCofinalNoveltyKernelPairAt oldVisit
    sourceIndex boundary

/-- Both replay currents lie strictly beyond the caller's absolute boundary. -/
theorem leftLater :
    boundary < (leftReplay novelty).2.current := by
  cases novelty
  change boundary <
    contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
      sourceIndex (boundary + 1)
  unfold contributionCapacityPostSettlementFutureBirthCurrentAt
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact]
  omega

theorem rightLater :
    boundary < (rightReplay novelty).2.current := by
  cases novelty
  change boundary <
    contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
      sourceIndex (boundary + 2)
  unfold contributionCapacityPostSettlementFutureBirthCurrentAt
  rw [contributionCapacityPostSettlementReachableCurrentAt_exact]
  omega

/-- Strong path identity statement: the two generated replay occurrences are
different even before reading authority. -/
theorem actualPaths_ne :
    (leftReplay novelty).2.actualPath ≠
      (rightReplay novelty).2.actualPath := by
  intro equality
  have indexEquality := congrArg Sigma.fst equality
  cases novelty
  change boundary + 1 = boundary + 2 at indexEquality
  omega

/-- Strong §22.4 form inside every cofinal paid tail: two different actual
paths, one real classical normal form, and different `K`. -/
theorem sameNormalForm_differentK :
    let observer :=
      contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
        sourceIndex
    observer.forget (leftReplay novelty) =
        observer.forget (rightReplay novelty) ∧
      observer.authorityK (leftReplay novelty) ≠
        observer.authorityK (rightReplay novelty) :=
  ⟨(kernelPair novelty).visible_eq, (kernelPair novelty).authority_ne⟩

theorem noOccurrenceReconstruction
    (proof : SourceProductiveNoveltyAt oldVisit sourceIndex boundary) :
    ¬ ∃ reconstruct : ContributionCapacityFutureBirthPulse →
        AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex).forget :=
  (kernelPair proof).noOccurrenceLeftInverse

theorem noAuthorityFactorization
    (proof : SourceProductiveNoveltyAt oldVisit sourceIndex boundary) :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex)) :=
  (kernelPair proof).noAuthorityFactorization

theorem noFaithfulReconstruction
    (proof : SourceProductiveNoveltyAt oldVisit sourceIndex boundary) :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit
          sourceIndex)) :=
  (kernelPair proof).noFaithfulAuthorityReconstruction

end SourceProductiveNoveltyAt

/-- Every finite boundary gets a freshly generated two-path novelty token;
there is no stored `Nat → novelty` schedule. -/
theorem contributionCapacitySourceProductiveNovelty_cofinal
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ∀ boundary : Nat,
      Nonempty (SourceProductiveNoveltyAt oldVisit sourceIndex boundary) :=
  fun boundary =>
    ⟨sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary⟩

theorem contributionCapacitySourceProductiveNovelty_hasNoCallerPairOrFuture
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : True := by
  let novelty :=
    sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary
  fail_if_success exact novelty.left
  fail_if_success exact novelty.right
  fail_if_success exact novelty.differentK
  fail_if_success exact novelty.normalizer
  fail_if_success exact novelty.failure
  fail_if_success exact novelty.selfU8
  fail_if_success exact novelty.revisionTarget
  fail_if_success exact novelty.future
  fail_if_success exact novelty.registry
  trivial

end
end M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalProductiveNovelty.sourceGeneratedContributionCapacitySourceProductiveNoveltyAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalProductiveNovelty.SourceProductiveNoveltyAt.sameNormalForm_differentK
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCofinalProductiveNovelty.SourceProductiveNoveltyAt.noFaithfulReconstruction
