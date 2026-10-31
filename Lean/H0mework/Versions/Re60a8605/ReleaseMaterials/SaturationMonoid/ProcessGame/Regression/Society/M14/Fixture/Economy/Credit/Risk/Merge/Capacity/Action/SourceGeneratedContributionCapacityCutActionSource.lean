import H0mework.Foundation.Source.SequentialAction
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Action.SourceGeneratedContributionMergeActionSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Root.SourceGeneratedContributionCapacityCutRoot

/-!
# Exact source coordinate of the contribution-capacity action

The capacity action starts at current `1` of the generated contribution-merge
root.  Its authority is the destination of the initial child-A row, hence the
merged contribution row itself.  The obstruction inquiry row remains a
separate authority in the same whole-ledger occurrence.

This module names only the existing source visit, row authority and exact
occurrence.  It creates no target, receipt, runtime or sibling ledger.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCutActionSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeCompiler
open M14SourceGeneratedContributionMergeRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutRoot

abbrev capacityActionRootedAt (oldVisit : OldVisit) :=
  actionRootedAt oldVisit

abbrev capacityActionSourceNAt (oldVisit : OldVisit) :=
  M14SourceGeneratedContributionMergeWorld.TargetN
    (capacityActionRootedAt oldVisit)

abbrev capacityActionSourceVAt (oldVisit : OldVisit) :=
  M14SourceGeneratedContributionMergeCompiler.TargetV
    (capacityActionRootedAt oldVisit)

def capacityActionSourceRootAt (oldVisit : OldVisit) :=
  contributionMergeLivingRoot (capacityActionRootedAt oldVisit)

def capacityActionSourceVisitAt (oldVisit : OldVisit) :
    SourceNativeTemporalVisitAt
      (capacityActionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot :=
  (contributionMergeRootInitialVisit (capacityActionRootedAt oldVisit)).next
    (contributionMergeRootFirstSuccessor
      (capacityActionRootedAt oldVisit)).next_eq

def capacityActionSourceEntryAt (oldVisit : OldVisit) :
    OpenResponsibilityAt (capacityActionSourceNAt oldVisit)
      ((capacityActionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        ((capacityActionSourceRootAt oldVisit).emitted
          (capacityActionSourceVisitAt oldVisit).current)) :=
  mergedContributionEntry (capacityActionRootedAt oldVisit)

def capacityActionInitialContributionAuthorityAt
    (oldVisit : OldVisit) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (capacityActionSourceRootAt oldVisit)
      (contributionMergeRootInitialVisit (capacityActionRootedAt oldVisit))
      (initialChildA (capacityActionRootedAt oldVisit)) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (capacityActionSourceRootAt oldVisit)
    (initialChildA (capacityActionRootedAt oldVisit))
    (contributionMergeRootInitialChildARow (capacityActionRootedAt oldVisit))

def capacityActionSourceAuthorityAt (oldVisit : OldVisit) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (capacityActionSourceRootAt oldVisit) (capacityActionSourceVisitAt oldVisit)
      (capacityActionSourceEntryAt oldVisit) :=
  (capacityActionInitialContributionAuthorityAt oldVisit).next
    (contributionMergeRootFirstSuccessor
      (capacityActionRootedAt oldVisit)).next_eq

def capacityActionExactSourceEventAt (oldVisit : OldVisit) :
    ExactTemporalCausalRootEventAt
      (capacityActionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
      (capacityActionSourceVisitAt oldVisit) :=
  (capacityActionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt (capacityActionSourceVisitAt oldVisit)

@[simp] theorem capacityActionSourceVisit_current_exact
    (oldVisit : OldVisit) :
    (capacityActionSourceVisitAt oldVisit).current = 1 :=
  rfl

@[simp] theorem capacityActionSourceEntry_is_mergedContribution
    (oldVisit : OldVisit) :
    capacityActionSourceEntryAt oldVisit =
      mergedContributionEntry (capacityActionRootedAt oldVisit) :=
  rfl

@[simp] theorem capacityActionExactSourceEvent_occurrence_exact
    (oldVisit : OldVisit) :
    (capacityActionExactSourceEventAt oldVisit).occurrence =
      contributionMergeEmitted (capacityActionRootedAt oldVisit) 1 :=
  rfl

def capacityActionOccurrencePresentationAt
    (oldVisit : OldVisit) :
    ConstructivePresentation
      ((capacityActionSourceRootAt oldVisit).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (capacityActionSourceVisitAt oldVisit).current)
      ((contributionCapacityLivingRoot
        (capacityActionRootedAt oldVisit)).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
          (contributionCapacityLivingRoot
            (capacityActionRootedAt oldVisit)).toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ =>
    contributionCapacityCutEmitted (capacityActionRootedAt oldVisit) 0
  backward := fun _ =>
    (capacityActionSourceRootAt oldVisit).emitted
      (capacityActionSourceVisitAt oldVisit).current
  backward_forward := by
    intro occurrence
    exact
      (contributionMergeOccurrence_eq_emitted
        (capacityActionRootedAt oldVisit) occurrence).symm
  forward_backward := by
    intro occurrence
    exact
      (contributionCapacityCutOccurrence_eq_emitted
        (capacityActionRootedAt oldVisit) occurrence).symm

@[simp] theorem capacityActionOccurrencePresentation_commutes
    (oldVisit : OldVisit) :
    (capacityActionOccurrencePresentationAt oldVisit).forward
        (capacityActionExactSourceEventAt oldVisit).occurrence =
      (contributionCapacityLivingRoot
        (capacityActionRootedAt oldVisit)).emitted
          (contributionCapacityLivingRoot
            (capacityActionRootedAt oldVisit)).toAuthoritativeRoot.toRoot.source.initial :=
  rfl

end
end M14SourceGeneratedContributionCapacityCutActionSource
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutActionSource.capacityActionSourceAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutActionSource.capacityActionOccurrencePresentationAt
