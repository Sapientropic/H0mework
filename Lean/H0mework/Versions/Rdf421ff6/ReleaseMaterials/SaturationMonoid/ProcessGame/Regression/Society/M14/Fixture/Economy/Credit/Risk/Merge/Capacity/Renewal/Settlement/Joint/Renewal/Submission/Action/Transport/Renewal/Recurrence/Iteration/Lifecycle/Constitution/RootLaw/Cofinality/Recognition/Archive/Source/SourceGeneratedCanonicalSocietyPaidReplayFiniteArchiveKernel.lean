import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Producer.SourceGeneratedContributionCapacityCofinalProductiveNovelty

/-!
# Source-generated paid-replay kernel beyond every finite archive

Attach any finite archive value to each generated paid replay.  Beyond every
requested lower bound, the canonical singleton pulse stays constant while
finite cardinality forces two different replay depths to share one archive
value.  Their actual-service authorities remain different, so the combined
observer still has a cofinal exact kernel.

The producer receives only the archive readout.  It receives no collision,
endpoints, authority value, registry, schedule, or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityFutureBirthPulse
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty

/-- Existing pulse observation refined only by a finite archive value.  The
authority coordinate remains the original actual-service `K`. -/
def canonicalPaidReplayFiniteArchiveObserverAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    {Archive : Type}
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    AuthorityObserver
      (AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
      (ContributionCapacityFutureBirthPulse × Archive)
      AnyPeriodicActualServiceExit where
  forget := fun replay => (replay.2.singletonPulse, archive replay)
  authorityK := fun replay => replay.2.authorityK

/-- Finite archive values cannot distinguish every depth of any replay tail. -/
theorem canonicalPaidReplayFiniteArchiveDepthReadout_notInjective
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    ¬ Function.Injective
      (fun depth : Nat =>
        archive
          (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            (lowerBound + 1 + depth))) := by
  intro depthInjective
  let restricted : Fin (Fintype.card Archive + 1) → Archive :=
    fun depth =>
      archive
        (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
          (lowerBound + 1 + depth))
  have restrictedInjective : Function.Injective restricted := by
    intro left right archiveEquality
    apply Fin.ext
    have actualDepthEquality := depthInjective archiveEquality
    omega
  have cardLe :
      Fintype.card (Fin (Fintype.card Archive + 1)) ≤
        Fintype.card Archive :=
    Fintype.card_le_of_injective restricted restrictedInjective
  simp only [Fintype.card_fin] at cardLe
  omega

/-- The later archive collision is generated internally from finiteness. -/
theorem canonicalPaidReplayFiniteArchive_hasCollision
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    ∃ left right : Nat,
      lowerBound < left ∧ lowerBound < right ∧ left ≠ right ∧
      archive
          (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            left) =
        archive
          (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            right) := by
  classical
  by_contra noCollision
  apply canonicalPaidReplayFiniteArchiveDepthReadout_notInjective oldVisit
    sourceIndex lowerBound archive
  intro left right archiveEquality
  by_contra depthNe
  exact noCollision
    ⟨lowerBound + 1 + left, lowerBound + 1 + right,
      by omega, by omega, by omega, archiveEquality⟩

/-- Exact combined-observer kernel generated beyond the requested bound. -/
theorem canonicalPaidReplayFiniteArchiveCofinalKernelPair_nonempty
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    Nonempty
      { pair : AuthorityKernelPair
          (canonicalPaidReplayFiniteArchiveObserverAt oldVisit sourceIndex
            archive) //
        lowerBound < pair.left.1 ∧ lowerBound < pair.right.1 } := by
  rcases canonicalPaidReplayFiniteArchive_hasCollision oldVisit sourceIndex
      lowerBound
      archive with
    ⟨leftDepth, rightDepth, leftLater, rightLater, depthNe,
      archiveEquality⟩
  let left := contributionCapacityPostSettlementPaidReplayAt oldVisit
    sourceIndex leftDepth
  let right := contributionCapacityPostSettlementPaidReplayAt oldVisit
    sourceIndex rightDepth
  exact
    ⟨⟨{ left := left
        right := right
        occurrence_ne := by
          intro replayEquality
          exact depthNe (congrArg Sigma.fst replayEquality)
        visible_eq := by
          apply Prod.ext
          · simp [canonicalPaidReplayFiniteArchiveObserverAt]
          · exact archiveEquality
        authority_ne := by
          intro authorityEquality
          have currentEquality :=
            periodicActualServiceExitOccurrenceAt_injective authorityEquality
          change
            contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
                sourceIndex leftDepth =
              contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit
                sourceIndex rightDepth at currentEquality
          unfold contributionCapacityPostSettlementFutureBirthCurrentAt at currentEquality
          rw [contributionCapacityPostSettlementReachableCurrentAt_exact,
            contributionCapacityPostSettlementReachableCurrentAt_exact] at currentEquality
          exact depthNe (by omega) },
      leftLater, rightLater⟩⟩

/-- Canonical chosen cofinal kernel; caller supplies only the archive readout. -/
noncomputable def canonicalPaidReplayFiniteArchiveCofinalKernelPairAt
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex lowerBound : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    { pair : AuthorityKernelPair
        (canonicalPaidReplayFiniteArchiveObserverAt oldVisit sourceIndex
          archive) //
      lowerBound < pair.left.1 ∧ lowerBound < pair.right.1 } :=
  Classical.choice
    (canonicalPaidReplayFiniteArchiveCofinalKernelPair_nonempty oldVisit
      sourceIndex lowerBound archive)

/-- Both the archive language and visible authority-readout language are
ordinary inhabited function spaces, independent of the no-go. -/
theorem canonicalPaidReplayFiniteArchive_rawLanguages_nonempty
    {Archive : Type} [Fintype Archive]
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (archive : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex → Archive) :
    Nonempty
        (AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex →
          Archive) ∧
      Nonempty
        ((ContributionCapacityFutureBirthPulse × Archive) →
          AnyPeriodicActualServiceExit) :=
  ⟨⟨archive⟩,
    ⟨fun _visible =>
      (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
        0).2.authorityK⟩⟩

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel.canonicalPaidReplayFiniteArchiveDepthReadout_notInjective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel.canonicalPaidReplayFiniteArchive_hasCollision
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel.canonicalPaidReplayFiniteArchiveCofinalKernelPairAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFiniteArchiveKernel.canonicalPaidReplayFiniteArchive_rawLanguages_nonempty
