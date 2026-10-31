import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.Producer.SourceGeneratedContributionCapacityEntityRenewalArithmeticDeath
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.DarkTwin.Producer.SourceGeneratedContributionCapacityAdjacentPaidRootRefillNoGo
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Failure.Producer.SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.EconomicSingleFold

/-!
# Database-root impersonation and the dark-twin theorem

Each cofinal paid replay already contains two synchronized authorities at the
same exact external M9 visit:

* the existing economic `RootedAccountedUnfolding`, whose unique fold yields
  the visible quantitative image;
* the actual-service occurrence `K` carried by the replay Payment.

The observer below forgets the full fold occurrence and actual `K`, retaining
only the real quantitative fold image.  The existing cofinal novelty producer
then supplies two different paid paths with that same image and different
authority.  Any visible-only database root must therefore misdispose at least
one exact path.  Moreover the post-root local ledger is empty, so no database
choice can reanimate the contribution entity already paid and terminally
discharged by the arithmetic-death chain.

No second fold, occurrence, entity registry, database table, disposition
registry, or completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityDatabaseRootImpersonation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RootedAccountedUnfolding Observer
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EconomicSingleFold
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty
open M14SourceGeneratedContributionCapacityCofinalNoveltyRootedFailure
open M14SourceGeneratedContributionCapacityEntityRenewalArithmeticDeath
open M14SourceGeneratedContributionCapacityAdjacentPaidRootRefillNoGo

/-- Existing fold occurrence at the external Payment depth of one replay. -/
def contributionCapacityDatabaseEconomicExposureAt (depth : Nat) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  economicRepairExposure (tenureEconomicFailureOccurrenceAt depth)

/-- Database-relevant authority retains both generated entity occurrence and
the actual Payment/service `K`. -/
abbrev ContributionCapacityDatabaseAuthorityK :=
  RootedAccountedUnfolding ExactEconomicAtom × AnyPeriodicActualServiceExit

/-- Visible-only database observer.  Its visible image is produced by the
existing unique economic fold; it is not a caller label or normalizer. -/
def contributionCapacityPaidReplayDatabaseObserver
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    AuthorityObserver
      (AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
      (List Nat) ContributionCapacityDatabaseAuthorityK where
  forget := fun replay =>
    economicQuantitativeImage
      (contributionCapacityDatabaseEconomicExposureAt replay.2.current)
  authorityK := fun replay =>
    (contributionCapacityDatabaseEconomicExposureAt replay.2.current,
      replay.2.authorityK)

/-- The full generated fold occurrence, unlike its quantitative image, is
injective in exact temporal depth. -/
theorem contributionCapacityDatabaseEconomicExposureAt_injective :
    Function.Injective contributionCapacityDatabaseEconomicExposureAt := by
  intro left right equality
  have rootEquality := congrArg RootedAccountedUnfolding.root equality
  have eventEquality :=
    congrArg ExactEconomicAtom.erasedRootEvent rootEquality
  unfold contributionCapacityDatabaseEconomicExposureAt at eventEquality
  rw [tenureRepairExposure_rootEvent left,
    tenureRepairExposure_rootEvent right] at eventEquality
  exact temporalVisitAt_injective (congrArg Sigma.fst eventEquality)

/-- Existing cofinal paid novelty lifted through the existing economic fold.
No path, image, K value, or inequality is submitted to this producer. -/
def contributionCapacityDatabaseRootKernelPairAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AuthorityKernelPair
      (contributionCapacityPaidReplayDatabaseObserver oldVisit sourceIndex) := by
  let novelty :=
    sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary
  exact
    { left := novelty.leftReplay
      right := novelty.rightReplay
      occurrence_ne := novelty.kernelPair.occurrence_ne
      visible_eq := by
        change economicQuantitativeImage
              (contributionCapacityDatabaseEconomicExposureAt
                novelty.leftReplay.2.current) =
            economicQuantitativeImage
              (contributionCapacityDatabaseEconomicExposureAt
                novelty.rightReplay.2.current)
        unfold contributionCapacityDatabaseEconomicExposureAt
        rw [tenure_quantitative_image_at, tenure_quantitative_image_at]
      authority_ne := by
        intro equality
        exact novelty.kernelPair.authority_ne (congrArg Prod.snd equality) }

theorem contributionCapacityDatabaseKernel_foldOccurrencesDistinct
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    contributionCapacityDatabaseEconomicExposureAt
          novelty.leftReplay.2.current ≠
      contributionCapacityDatabaseEconomicExposureAt
          novelty.rightReplay.2.current := by
  dsimp
  apply contributionCapacityDatabaseEconomicExposureAt_injective.ne
  intro currentEquality
  exact
    (sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary).kernelPair.authority_ne
      (congrArg periodicActualServiceExitOccurrenceAt currentEquality)

/-- The fold root and replay Payment are independently locked to the same
existing external visit.  This keeps fold identity and Payment authority
synchronized without identifying their carrier types. -/
theorem contributionCapacityDatabaseKernel_foldRootsExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    (contributionCapacityDatabaseEconomicExposureAt
        novelty.leftReplay.2.current).root.erasedRootEvent =
        ⟨temporalVisitAt novelty.leftReplay.2.current,
          (periodicSourceBackedPaymentAt
            novelty.leftReplay.2.current).rootOccurrence⟩ ∧
      (contributionCapacityDatabaseEconomicExposureAt
        novelty.rightReplay.2.current).root.erasedRootEvent =
        ⟨temporalVisitAt novelty.rightReplay.2.current,
          (periodicSourceBackedPaymentAt
            novelty.rightReplay.2.current).rootOccurrence⟩ := by
  dsimp
  constructor <;>
    exact tenureRepairExposure_rootEvent _

theorem contributionCapacityDatabaseKernel_paymentRootsExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let bridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
    HEq
        bridge.leftReplay.2.futureBirth.actualExit.paymentOccurrence.rootOccurrence
        (periodicSourceBackedPaymentAt bridge.leftCurrent).rootOccurrence ∧
      HEq
        bridge.rightReplay.2.futureBirth.actualExit.paymentOccurrence.rootOccurrence
        (periodicSourceBackedPaymentAt bridge.rightCurrent).rootOccurrence := by
  dsimp
  let novelty :=
    sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
      sourceIndex boundary
  let bridge :=
    sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
  exact
    ⟨HEq.trans (heq_of_eq bridge.leftPaymentRootOccurrence_exact)
        (heq_of_eq
          (periodicSourceBackedPaymentAt bridge.leftCurrent
            ).rootOccurrence_eq.symm),
      HEq.trans (heq_of_eq bridge.rightPaymentRootOccurrence_exact)
        (heq_of_eq
          (periodicSourceBackedPaymentAt bridge.rightCurrent
            ).rootOccurrence_eq.symm)⟩

/-- A visible database claims an exact disposition when its selected authority
is literally the authority of the actual replay. -/
abbrev ExactDatabaseRootDispositionAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (database : List Nat → ContributionCapacityDatabaseAuthorityK)
    (replay : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex) : Prop :=
  database
      ((contributionCapacityPaidReplayDatabaseObserver oldVisit sourceIndex
        ).forget replay) =
    (contributionCapacityPaidReplayDatabaseObserver oldVisit sourceIndex
      ).authorityK replay

/-- Every visible-only database necessarily misdisposes at least one side of
the actual dark-twin fibre.  This is a dependent exact-disposition failure,
not merely a label inequality. -/
theorem everyDatabaseRootMisdisposesOneActualPath
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (database : List Nat → ContributionCapacityDatabaseAuthorityK) :
    let pair :=
      contributionCapacityDatabaseRootKernelPairAt oldVisit sourceIndex
        boundary
    IsEmpty (PLift (ExactDatabaseRootDispositionAt database pair.left)) ∨
      IsEmpty (PLift (ExactDatabaseRootDispositionAt database pair.right)) := by
  dsimp
  classical
  let pair :=
    contributionCapacityDatabaseRootKernelPairAt oldVisit sourceIndex boundary
  by_cases leftExact : ExactDatabaseRootDispositionAt database pair.left
  · exact Or.inr
      ⟨fun rightExact => pair.authority_ne <| by
        calc
          (contributionCapacityPaidReplayDatabaseObserver oldVisit sourceIndex
              ).authorityK pair.left =
              database
                ((contributionCapacityPaidReplayDatabaseObserver oldVisit
                  sourceIndex).forget pair.left) :=
            leftExact.symm
          _ = database
                ((contributionCapacityPaidReplayDatabaseObserver oldVisit
                  sourceIndex).forget pair.right) :=
            congrArg database pair.visible_eq
          _ = (contributionCapacityPaidReplayDatabaseObserver oldVisit
                sourceIndex).authorityK pair.right :=
            rightExact.down⟩
  · exact Or.inl ⟨fun exact => leftExact exact.down⟩

/-- A post-root replay contains no local entity row at all.  Its external
Payment/liability remains real, but cannot reanimate the terminally discharged
contribution entity. -/
abbrev PostRootLocalEntityAt
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (replay : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex) :=
  OpenResponsibilityAt (JointSettlementNAt oldVisit)
    replay.2.rootEvent.occurrence.1

theorem postRootReplayCannotReanimateLocalEntity
    {oldVisit : OldVisit} {sourceIndex : Nat}
    (replay : AnyContributionCapacityPostSettlementPaidReplay oldVisit
      sourceIndex) :
    IsEmpty (PostRootLocalEntityAt replay) :=
  replay.2.payment.occurrenceLocalLedgerEmpty

structure ProofCarryingContributionCapacityDatabaseRootImpersonationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Prop where
  arithmeticDeath :
    ProofCarryingContributionEntityRenewalArithmeticDeathCertificate
  adjacentPaidRootRefillNoGo :
    ProofCarryingContributionCapacityAdjacentPaidRootRefillNoGoAt oldVisit
      sourceIndex boundary
  kernelPair : Nonempty
    (AuthorityKernelPair
      (contributionCapacityPaidReplayDatabaseObserver oldVisit sourceIndex))
  foldOccurrencesDistinct :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    contributionCapacityDatabaseEconomicExposureAt
          novelty.leftReplay.2.current ≠
      contributionCapacityDatabaseEconomicExposureAt
          novelty.rightReplay.2.current
  foldRootsExact :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    (contributionCapacityDatabaseEconomicExposureAt
        novelty.leftReplay.2.current).root.erasedRootEvent =
        ⟨temporalVisitAt novelty.leftReplay.2.current,
          (periodicSourceBackedPaymentAt
            novelty.leftReplay.2.current).rootOccurrence⟩ ∧
      (contributionCapacityDatabaseEconomicExposureAt
        novelty.rightReplay.2.current).root.erasedRootEvent =
        ⟨temporalVisitAt novelty.rightReplay.2.current,
          (periodicSourceBackedPaymentAt
            novelty.rightReplay.2.current).rootOccurrence⟩
  paymentRootsExact :
    let novelty :=
      sourceGeneratedContributionCapacitySourceProductiveNoveltyAt oldVisit
        sourceIndex boundary
    let bridge :=
      sourceGeneratedContributionCapacityCofinalNoveltyRootedFailureAt novelty
    HEq
        bridge.leftReplay.2.futureBirth.actualExit.paymentOccurrence.rootOccurrence
        (periodicSourceBackedPaymentAt bridge.leftCurrent).rootOccurrence ∧
      HEq
        bridge.rightReplay.2.futureBirth.actualExit.paymentOccurrence.rootOccurrence
        (periodicSourceBackedPaymentAt bridge.rightCurrent).rootOccurrence
  databaseMisdisposition :
    ∀ database : List Nat → ContributionCapacityDatabaseAuthorityK,
      let pair :=
        contributionCapacityDatabaseRootKernelPairAt oldVisit sourceIndex
          boundary
      IsEmpty (PLift (ExactDatabaseRootDispositionAt database pair.left)) ∨
        IsEmpty (PLift (ExactDatabaseRootDispositionAt database pair.right))
  noOccurrenceReconstruction :
    ¬ ∃ reconstruct : List Nat →
          AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
      Function.LeftInverse reconstruct
        (contributionCapacityPaidReplayDatabaseObserver oldVisit sourceIndex
          ).forget
  noAuthorityFactorization :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPaidReplayDatabaseObserver oldVisit sourceIndex))
  bothPostRootLocalEntityFibresEmpty :
    let pair :=
      contributionCapacityDatabaseRootKernelPairAt oldVisit sourceIndex
        boundary
    IsEmpty (PostRootLocalEntityAt pair.left) ∧
      IsEmpty (PostRootLocalEntityAt pair.right)

theorem proofCarryingContributionCapacityDatabaseRootImpersonationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ProofCarryingContributionCapacityDatabaseRootImpersonationAt oldVisit
      sourceIndex boundary :=
  let pair :=
    contributionCapacityDatabaseRootKernelPairAt oldVisit sourceIndex boundary
  { arithmeticDeath :=
      proofCarryingContributionEntityRenewalArithmeticDeath
    adjacentPaidRootRefillNoGo :=
      proofCarryingContributionCapacityAdjacentPaidRootRefillNoGoAt oldVisit
        sourceIndex boundary
    kernelPair := ⟨pair⟩
    foldOccurrencesDistinct :=
      contributionCapacityDatabaseKernel_foldOccurrencesDistinct oldVisit
        sourceIndex boundary
    foldRootsExact :=
      contributionCapacityDatabaseKernel_foldRootsExact oldVisit sourceIndex
        boundary
    paymentRootsExact :=
      contributionCapacityDatabaseKernel_paymentRootsExact oldVisit sourceIndex
        boundary
    databaseMisdisposition :=
      everyDatabaseRootMisdisposesOneActualPath oldVisit sourceIndex boundary
    noOccurrenceReconstruction := pair.noOccurrenceLeftInverse
    noAuthorityFactorization := pair.noAuthorityFactorization
    bothPostRootLocalEntityFibresEmpty :=
      ⟨postRootReplayCannotReanimateLocalEntity pair.left,
        postRootReplayCannotReanimateLocalEntity pair.right⟩ }

abbrev ProofCarryingContributionCapacityDatabaseRootImpersonationCertificate
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop :=
  ∀ boundary : Nat,
    ProofCarryingContributionCapacityDatabaseRootImpersonationAt oldVisit
      sourceIndex boundary

theorem proofCarryingContributionCapacityDatabaseRootImpersonation
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ProofCarryingContributionCapacityDatabaseRootImpersonationCertificate
      oldVisit sourceIndex :=
  proofCarryingContributionCapacityDatabaseRootImpersonationAt oldVisit
    sourceIndex

theorem databaseRootImpersonation_hasNoSecondFoldRegistryOrFuture
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : True := by
  let pair :=
    contributionCapacityDatabaseRootKernelPairAt oldVisit sourceIndex boundary
  fail_if_success exact pair.database
  fail_if_success exact pair.entityRegistry
  fail_if_success exact pair.dispositionRegistry
  fail_if_success exact pair.secondFold
  fail_if_success exact pair.secondOccurrence
  fail_if_success exact pair.history
  fail_if_success exact pair.completedFuture
  trivial

end
end M14ProofCarryingContributionCapacityDatabaseRootImpersonation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityDatabaseRootImpersonation.contributionCapacityDatabaseRootKernelPairAt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityDatabaseRootImpersonation.everyDatabaseRootMisdisposesOneActualPath
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityDatabaseRootImpersonation.proofCarryingContributionCapacityDatabaseRootImpersonation
