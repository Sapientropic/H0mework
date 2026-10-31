import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Source.SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth

/-!
# Irreducible finite-stage pro-truth

The open fair tower is jointly faithful, but no finite subfamily is.  For any
finite set of requested stages and any requested lower bound, one later
source-generated paid-replay pair is invisible at every selected stage while
its occurrences and actual-service authorities differ.  The next fair stage
separates that same pair.

The finite set is only a theorem query.  This file constructs no product
observer, stage registry, `Nat → Bool` archive or terminal truth object.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteWitnessTower
open M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteProTruth

/-- A computed bound strictly beyond both the requested stage and every
member of the finite query.  It is not stored as a schedule. -/
def canonicalPaidReplayFairFiniteSubfamilyCutoff
    (requestedStage : Nat) (stages : Finset Nat) : Nat :=
  max requestedStage (stages.sup id) + 1

theorem canonicalPaidReplayFairFiniteSubfamilyCutoff_requested_lt
    (requestedStage : Nat) (stages : Finset Nat) :
    requestedStage <
      canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage stages := by
  unfold canonicalPaidReplayFairFiniteSubfamilyCutoff
  omega

theorem canonicalPaidReplayFairFiniteSubfamilyCutoff_member_lt
    (requestedStage : Nat) (stages : Finset Nat) {stage : Nat}
    (stageMem : stage ∈ stages) :
    stage <
      canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage stages := by
  have stageLeSup : stage ≤ stages.sup id :=
    Finset.le_sup (f := fun value : Nat => value) stageMem
  unfold canonicalPaidReplayFairFiniteSubfamilyCutoff
  omega

/-- The exact source-owned pair selected after a finite query. -/
def canonicalPaidReplayFairFiniteSubfamilyKernelPairAt
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat)
    (stages : Finset Nat) :=
  canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex
    (canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage stages)

theorem canonicalPaidReplayFairFiniteSubfamilyKernelPair_later
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat)
    (stages : Finset Nat) :
    let pair :=
      canonicalPaidReplayFairFiniteSubfamilyKernelPairAt oldVisit sourceIndex
        requestedStage stages
    requestedStage < pair.left.1 ∧ requestedStage < pair.right.1 := by
  dsimp [canonicalPaidReplayFairFiniteSubfamilyKernelPairAt]
  have cutoffLater :=
    canonicalPaidReplayFairFiniteSubfamilyCutoff_requested_lt requestedStage
      stages
  change
    requestedStage <
        canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage stages ∧
      requestedStage <
        canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage stages + 1
  omega

/-- One generated pair is simultaneously invisible to every selected finite
stage.  Coherence, rather than a bundled observer, transports the cutoff
collision to each earlier query. -/
theorem canonicalPaidReplayFairFiniteSubfamilyKernel_invisible
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat)
    (stages : Finset Nat) :
    let pair :=
      canonicalPaidReplayFairFiniteSubfamilyKernelPairAt oldVisit sourceIndex
        requestedStage stages
    ∀ stage ∈ stages,
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
            pair.left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage pair.right := by
  dsimp only [canonicalPaidReplayFairFiniteSubfamilyKernelPairAt]
  intro stage stageMem
  let cutoff :=
    canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage stages
  have stageLeCutoff : stage ≤ cutoff :=
    Nat.le_of_lt
      (canonicalPaidReplayFairFiniteSubfamilyCutoff_member_lt requestedStage
        stages stageMem)
  have cutoffEquality :=
    canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq oldVisit
      sourceIndex cutoff
  calc
    canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
          (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            cutoff) =
        canonicalPaidReplayFairFiniteArchiveRestriction stageLeCutoff
          (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            cutoff
            (contributionCapacityPostSettlementPaidReplayAt oldVisit
              sourceIndex cutoff)) :=
      (canonicalPaidReplayFairFiniteArchiveRestriction_exact oldVisit
        sourceIndex stageLeCutoff _).symm
    _ = canonicalPaidReplayFairFiniteArchiveRestriction stageLeCutoff
          (canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            cutoff
            (contributionCapacityPostSettlementPaidReplayAt oldVisit
              sourceIndex (cutoff + 1))) :=
      congrArg
        (canonicalPaidReplayFairFiniteArchiveRestriction stageLeCutoff)
        cutoffEquality
    _ = canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage
          (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            (cutoff + 1)) :=
      canonicalPaidReplayFairFiniteArchiveRestriction_exact oldVisit
        sourceIndex stageLeCutoff _

/-- Maximum finite-subfamily kernel mouth.  The same pair is cofinal, paid,
invisible to the entire finite query, and separated by its generated next
fair stage. -/
theorem canonicalPaidReplayFairFiniteSubfamilyKernel
    (oldVisit : OldVisit) (sourceIndex requestedStage : Nat)
    (stages : Finset Nat) :
    let cutoff :=
      canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage stages
    let pair :=
      canonicalPaidReplayFairFiniteSubfamilyKernelPairAt oldVisit sourceIndex
        requestedStage stages
    requestedStage < cutoff ∧
      requestedStage < pair.left.1 ∧
      requestedStage < pair.right.1 ∧
      pair.left ≠ pair.right ∧
      pair.left.2.authorityK ≠ pair.right.2.authorityK ∧
      (∀ stage ∈ stages,
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
              stage pair.left =
          canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            stage pair.right) ∧
      type_of% pair.left.2.paidStep_consumes_exactPayment ∧
      type_of% pair.left.2.paymentNext_isCanonicalTarget ∧
      type_of% pair.right.2.paidStep_consumes_exactPayment ∧
      type_of% pair.right.2.paymentNext_isCanonicalTarget ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            cutoff pair.left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          cutoff pair.right ∧
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
            (cutoff + 1) pair.left ≠
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          (cutoff + 1) pair.right := by
  dsimp only [canonicalPaidReplayFairFiniteSubfamilyKernelPairAt]
  let cutoff :=
    canonicalPaidReplayFairFiniteSubfamilyCutoff requestedStage stages
  let pair :=
    canonicalPaidReplayFairFiniteArchiveKernelPairAt oldVisit sourceIndex cutoff
  exact
      ⟨canonicalPaidReplayFairFiniteSubfamilyCutoff_requested_lt requestedStage
        stages,
      (canonicalPaidReplayFairFiniteSubfamilyKernelPair_later oldVisit
        sourceIndex requestedStage stages).1,
      (canonicalPaidReplayFairFiniteSubfamilyKernelPair_later oldVisit
        sourceIndex requestedStage stages).2,
      pair.occurrence_ne,
      pair.authority_ne,
      canonicalPaidReplayFairFiniteSubfamilyKernel_invisible oldVisit
        sourceIndex requestedStage stages,
      pair.left.2.paidStep_consumes_exactPayment,
      pair.left.2.paymentNext_isCanonicalTarget,
      pair.right.2.paidStep_consumes_exactPayment,
      pair.right.2.paymentNext_isCanonicalTarget,
      canonicalPaidReplayFairFiniteArchive_currentPair_visible_eq oldVisit
        sourceIndex cutoff,
      canonicalPaidReplayFairFiniteArchive_successorSeparatesCurrentPair
        oldVisit sourceIndex cutoff⟩

/-- Equality-reflection by a finite stage query, stated relationally so no
combined observer value is built. -/
def CanonicalPaidReplayFairFiniteSubfamilyOccurrenceFaithfulAt
    (oldVisit : OldVisit) (sourceIndex : Nat) (stages : Finset Nat) : Prop :=
  ∀ left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
    (∀ stage ∈ stages,
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
            left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage right) →
      left = right

/-- K-reflection by a finite stage query, again without a product observer. -/
def CanonicalPaidReplayFairFiniteSubfamilyAuthorityFaithfulAt
    (oldVisit : OldVisit) (sourceIndex : Nat) (stages : Finset Nat) : Prop :=
  ∀ left right :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
    (∀ stage ∈ stages,
      canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex stage
            left =
        canonicalPaidReplayFairFiniteArchiveReadoutAt oldVisit sourceIndex
          stage right) →
      left.2.authorityK = right.2.authorityK

theorem canonicalPaidReplayFairFiniteSubfamily_notOccurrenceFaithful
    (oldVisit : OldVisit) (sourceIndex : Nat) (stages : Finset Nat) :
    ¬ CanonicalPaidReplayFairFiniteSubfamilyOccurrenceFaithfulAt oldVisit
      sourceIndex stages := by
  intro faithful
  let pair :=
    canonicalPaidReplayFairFiniteSubfamilyKernelPairAt oldVisit sourceIndex 0
      stages
  exact pair.occurrence_ne
    (faithful pair.left pair.right
      (canonicalPaidReplayFairFiniteSubfamilyKernel_invisible oldVisit
        sourceIndex 0 stages))

theorem canonicalPaidReplayFairFiniteSubfamily_notAuthorityFaithful
    (oldVisit : OldVisit) (sourceIndex : Nat) (stages : Finset Nat) :
    ¬ CanonicalPaidReplayFairFiniteSubfamilyAuthorityFaithfulAt oldVisit
      sourceIndex stages := by
  intro faithful
  let pair :=
    canonicalPaidReplayFairFiniteSubfamilyKernelPairAt oldVisit sourceIndex 0
      stages
  exact pair.authority_ne
    (faithful pair.left pair.right
      (canonicalPaidReplayFairFiniteSubfamilyKernel_invisible oldVisit
        sourceIndex 0 stages))

end
end M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth.canonicalPaidReplayFairFiniteSubfamilyKernel
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth.canonicalPaidReplayFairFiniteSubfamily_notOccurrenceFaithful
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyPaidReplayFairFiniteNoncompactProTruth.canonicalPaidReplayFairFiniteSubfamily_notAuthorityFaithful
