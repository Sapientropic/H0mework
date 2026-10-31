import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Action.SourceGeneratedContributionCapacityReopeningState
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Support.SourceGeneratedContributionCapacitySettlementSupport

/-!
# Exact reopening coordinate of contribution-capacity settlement

The settlement attack begins only after the two already certified carried
answers.  Its source is current `3` of the same canonical reopening root: the
runtime-facing reopened index is `2`.  This file names that exact occurrence,
residual row and causal authority; it does not install a target or future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementActionSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityReopeningState

def contributionCapacitySettlementActionSourceIndex : Nat := 2

abbrev ContributionCapacitySettlementActionRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  CanonicalReopeningRootAt oldVisit sourceIndex

def contributionCapacitySettlementActionVisitAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  contributionCapacityReopenedVisitAt oldVisit sourceIndex
    contributionCapacitySettlementActionSourceIndex

@[simp] theorem contributionCapacitySettlementActionVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (show Nat from
      (contributionCapacitySettlementActionVisitAt oldVisit sourceIndex).current) =
      3 := by
  exact contributionCapacityReopeningVisit_current_exact oldVisit sourceIndex 3

def contributionCapacitySettlementActionEntryAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    OpenResponsibilityAt (ReopeningNAt oldVisit)
      ((ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
        |>.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          ((ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
            |>.emitted
              (contributionCapacitySettlementActionVisitAt oldVisit
                sourceIndex).current)) :=
  contributionCapacityReopeningTargetResidual oldVisit

def contributionCapacitySettlementActionAuthorityAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionVisitAt oldVisit sourceIndex)
      (contributionCapacitySettlementActionEntryAt oldVisit sourceIndex) :=
  contributionCapacityReopenedAuthorityAt oldVisit sourceIndex
    contributionCapacitySettlementActionSourceIndex

abbrev ContributionCapacitySettlementSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ExactTemporalCausalRootEventAt
    ((ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
      |>.toAuthoritativeRoot.toLedgerRoot)
    (contributionCapacitySettlementActionVisitAt oldVisit sourceIndex)

def contributionCapacitySettlementActionExactSourceEventAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex :=
  (ContributionCapacitySettlementActionRootAt oldVisit sourceIndex)
    |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (contributionCapacitySettlementActionVisitAt oldVisit sourceIndex)

@[simp] theorem contributionCapacitySettlementActionSource_occurrence_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    (contributionCapacitySettlementActionExactSourceEventAt oldVisit
      sourceIndex).occurrence =
      (ContributionCapacitySettlementActionRootAt oldVisit sourceIndex).emitted
        (contributionCapacitySettlementActionVisitAt oldVisit
          sourceIndex).current :=
  rfl

@[simp] theorem contributionCapacitySettlementActionSource_entry_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    contributionCapacitySettlementActionEntryAt oldVisit sourceIndex =
      contributionCapacityReopeningTargetResidual oldVisit :=
  rfl

end
end M14SourceGeneratedContributionCapacitySettlementActionSource
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementActionSource.contributionCapacitySettlementActionAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementActionSource.contributionCapacitySettlementActionVisit_current_exact
