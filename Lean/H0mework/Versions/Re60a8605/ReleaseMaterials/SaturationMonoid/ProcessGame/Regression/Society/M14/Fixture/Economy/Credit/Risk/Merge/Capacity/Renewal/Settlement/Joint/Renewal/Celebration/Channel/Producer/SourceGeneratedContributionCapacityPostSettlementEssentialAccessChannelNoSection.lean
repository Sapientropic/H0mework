import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Celebration.Channel.Producer.SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.AuthorityObserver

/-!
# Essential-access channel observer no-section

Tenure and health are two different root-installed channel restrictions of the
same exact post-settlement macro occurrence.  Their legacy protected-interest
readout is equal, while relation phase and served slot differ.  Thus even
pointwise generation of every channel does not supply a global section from
the classical observer back to occurrence authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer
open M3FiniteExchangeFixture
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityEssentialAccessChannel
open M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannel

abbrev AnyContributionCapacityPostSettlementEssentialAccessChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  Sigma fun channel : EssentialAccessChannel =>
    SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
      oldVisit sourceIndex index channel

def contributionCapacityPostSettlementTenureChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AnyContributionCapacityPostSettlementEssentialAccessChannelAt oldVisit
      sourceIndex index :=
  ⟨tenureAuthority,
    sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
      oldVisit sourceIndex index tenureAuthority⟩

def contributionCapacityPostSettlementHealthChannelAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AnyContributionCapacityPostSettlementEssentialAccessChannelAt oldVisit
      sourceIndex index :=
  ⟨healthAuthority,
    sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
      oldVisit sourceIndex index healthAuthority⟩

abbrev ContributionCapacityPostSettlementEssentialAccessChannelKAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  EssentialAccessSector ×
    Fin (anomiePhaseAt
      (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
        oldVisit sourceIndex index)).served.length

/-- The authority coordinate combines relation-generated phase and the exact
served slot in the occurrence-selected settlement. -/
def contributionCapacityPostSettlementEssentialAccessChannelObserverAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AuthorityObserver
      (AnyContributionCapacityPostSettlementEssentialAccessChannelAt oldVisit
        sourceIndex index)
      M3FiniteExchangeFixture.V.ProtectedInterest
      (ContributionCapacityPostSettlementEssentialAccessChannelKAt oldVisit
        sourceIndex index) where
  forget := fun occurrence => protectedInterestReadout occurrence.1
  authorityK := fun occurrence =>
    (channelPhase occurrence.1,
      channelSlotAt
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
          oldVisit sourceIndex index) occurrence.1)

theorem contributionCapacityPostSettlementTenureHealthChannels_distinct
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    contributionCapacityPostSettlementTenureChannelAt oldVisit sourceIndex
        index ≠
      contributionCapacityPostSettlementHealthChannelAt oldVisit sourceIndex
        index := by
  intro equality
  exact tenure_and_health_authorities_distinct (congrArg Sigma.fst equality)

theorem contributionCapacityPostSettlementTenureHealthSlots_distinct
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    channelSlotAt
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
          oldVisit sourceIndex index) tenureAuthority ≠
      channelSlotAt
        (contributionCapacityPostSettlementEssentialAccessChannelCurrentAt
          oldVisit sourceIndex index) healthAuthority := by
  intro equality
  have valueEquality := congrArg Fin.val equality
  change 0 = 1 at valueEquality
  omega

def contributionCapacityPostSettlementEssentialAccessChannelKernelPairAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    AuthorityKernelPair
      (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
        oldVisit sourceIndex index) where
  left := contributionCapacityPostSettlementTenureChannelAt oldVisit
    sourceIndex index
  right := contributionCapacityPostSettlementHealthChannelAt oldVisit
    sourceIndex index
  occurrence_ne :=
    contributionCapacityPostSettlementTenureHealthChannels_distinct oldVisit
      sourceIndex index
  visible_eq := protectedInterestReadout_same
  authority_ne := by
    intro equality
    exact sectorPhaseReadout_different (congrArg Prod.fst equality)

/-- Strong same-occurrence kernel theorem: two root-installed restrictions,
one legacy readout, different relation-and-service authority. -/
theorem contributionCapacityPostSettlement_sameVisible_differentChannelK
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    let observer :=
      contributionCapacityPostSettlementEssentialAccessChannelObserverAt
        oldVisit sourceIndex index
    observer.forget
        (contributionCapacityPostSettlementTenureChannelAt oldVisit sourceIndex
          index) =
      observer.forget
        (contributionCapacityPostSettlementHealthChannelAt oldVisit sourceIndex
          index) ∧
    observer.authorityK
        (contributionCapacityPostSettlementTenureChannelAt oldVisit sourceIndex
          index) ≠
      observer.authorityK
        (contributionCapacityPostSettlementHealthChannelAt oldVisit sourceIndex
          index) :=
  ⟨(contributionCapacityPostSettlementEssentialAccessChannelKernelPairAt
      oldVisit sourceIndex index).visible_eq,
    (contributionCapacityPostSettlementEssentialAccessChannelKernelPairAt
      oldVisit sourceIndex index).authority_ne⟩

theorem contributionCapacityPostSettlementChannel_noOccurrenceReconstruction
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ¬ ∃ reconstruct : M3FiniteExchangeFixture.V.ProtectedInterest →
        AnyContributionCapacityPostSettlementEssentialAccessChannelAt oldVisit
          sourceIndex index,
      Function.LeftInverse reconstruct
        (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex index).forget :=
  (contributionCapacityPostSettlementEssentialAccessChannelKernelPairAt
    oldVisit sourceIndex index).noOccurrenceLeftInverse

theorem contributionCapacityPostSettlementChannel_noAuthorityFactorization
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ¬ Nonempty
      (AuthorityFactorization
        (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex index)) :=
  (contributionCapacityPostSettlementEssentialAccessChannelKernelPairAt
    oldVisit sourceIndex index).noAuthorityFactorization

theorem contributionCapacityPostSettlementChannel_noFaithfulReconstruction
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ¬ Nonempty
      (FaithfulAuthorityReconstruction
        (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
          oldVisit sourceIndex index)) :=
  (contributionCapacityPostSettlementEssentialAccessChannelKernelPairAt
    oldVisit sourceIndex index).noFaithfulAuthorityReconstruction

theorem contributionCapacityPostSettlement_everyChannelGenerated_noGlobalSection
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (∀ channel : EssentialAccessChannel,
        Nonempty
          (SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
            oldVisit sourceIndex index channel)) ∧
      ¬ ∃ reconstruct : M3FiniteExchangeFixture.V.ProtectedInterest →
          AnyContributionCapacityPostSettlementEssentialAccessChannelAt
            oldVisit sourceIndex index,
        Function.LeftInverse reconstruct
          (contributionCapacityPostSettlementEssentialAccessChannelObserverAt
            oldVisit sourceIndex index).forget :=
  ⟨fun channel =>
      ⟨sourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelAt
        oldVisit sourceIndex index channel⟩,
    contributionCapacityPostSettlementChannel_noOccurrenceReconstruction
      oldVisit sourceIndex index⟩

/-- Both restrictions return to the same actual paid next because channel
authority is dependent on one occurrence and does not mint its own future. -/
theorem contributionCapacityPostSettlementTenureHealth_actualNext_same
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (contributionCapacityPostSettlementTenureChannelAt oldVisit sourceIndex
        index).2.actualNext =
      (contributionCapacityPostSettlementHealthChannelAt oldVisit sourceIndex
        index).2.actualNext :=
  rfl

end
end M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection.contributionCapacityPostSettlement_sameVisible_differentChannelK
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection.contributionCapacityPostSettlementChannel_noAuthorityFactorization
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityPostSettlementEssentialAccessChannelNoSection.contributionCapacityPostSettlement_everyChannelGenerated_noGlobalSection
