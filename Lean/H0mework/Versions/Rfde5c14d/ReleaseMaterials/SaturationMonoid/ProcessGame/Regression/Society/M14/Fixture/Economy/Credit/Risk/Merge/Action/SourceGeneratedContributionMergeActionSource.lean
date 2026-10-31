import H0mework.Versions.R2.Foundation.Source.SequentialAction
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8RevisedAuthority
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Root.SourceGeneratedContributionMergeRoot

/-!
# Exact source coordinate of the contribution-merge action

The merge action is emitted at revised current `2`, the first runtime state
after the loss-allocation root has already generated its split.  This module
only names that existing visit, obstruction-continuity entry, causal-entry
authority and exact occurrence.  It creates no action token, target, receipt
or runtime.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionMergeActionSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8RevisedLedger
open M9ProofCarryingRenewalU8RevisedWorld
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationCompiler
open M14SourceGeneratedContributionMergeCompiler
open M14SourceGeneratedContributionMergeRoot

abbrev OldVisit := RootVisit jointRoot.toAuthoritativeRoot.toRoot

abbrev actionRootedAt (oldVisit : OldVisit) := rootedAt oldVisit

abbrev actionSourceNAt (oldVisit : OldVisit) :=
  M9ProofCarryingRenewalU8RevisedWorld.NewNAt oldVisit

abbrev actionSourceVAt (oldVisit : OldVisit) :=
  M9ProofCarryingRenewalU8RevisedWorld.NewVAt oldVisit

def actionSourceRootAt (oldVisit : OldVisit) :=
  revisedLivingRootAt oldVisit

def actionSourceVisitAt (oldVisit : OldVisit) :
    SourceNativeTemporalVisitAt
      (actionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot :=
  M9ProofCarryingRenewalU8RevisedAuthority.temporalVisitAtFrom oldVisit 2

def actionSourceEntryAt (oldVisit : OldVisit) :
    OpenResponsibilityAt (actionSourceNAt oldVisit)
      ((actionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        ((actionSourceRootAt oldVisit).emitted
          (actionSourceVisitAt oldVisit).current)) :=
  M9ProofCarryingRenewalU8RevisedAuthority.inquiryEntryReadoutAtFrom
    oldVisit 2

def actionSourceAuthorityAt (oldVisit : OldVisit) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (actionSourceRootAt oldVisit) (actionSourceVisitAt oldVisit)
        (actionSourceEntryAt oldVisit) :=
  M9ProofCarryingRenewalU8RevisedAuthority.inquiryAuthorityAtFrom
    oldVisit 2

def actionExactSourceEventAt (oldVisit : OldVisit) :
    ExactTemporalCausalRootEventAt
      (actionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
        (actionSourceVisitAt oldVisit) :=
  (actionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt (actionSourceVisitAt oldVisit)

@[simp] theorem actionSourceVisit_current_exact
    (oldVisit : OldVisit) :
    (actionSourceVisitAt oldVisit).current = 2 :=
  rfl

@[simp] theorem actionSourceEntry_is_existing_obstruction
    (oldVisit : OldVisit) :
    actionSourceEntryAt oldVisit =
      lossAllocationTargetObstruction (actionRootedAt oldVisit) :=
  rfl

@[simp] theorem actionExactSourceEvent_occurrence_exact
    (oldVisit : OldVisit) :
    (actionExactSourceEventAt oldVisit).occurrence =
      revisedEmittedAt oldVisit 2 :=
  rfl

/-- Both source and target occurrences are the unique images of their fixed
source compilers.  The presentation changes the world representation, not
the identity of either actual compiler occurrence. -/
def actionOccurrencePresentationAt
    (oldVisit : OldVisit) :
    ConstructivePresentation
      ((actionSourceRootAt oldVisit).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (actionSourceVisitAt oldVisit).current)
      ((contributionMergeLivingRoot (actionRootedAt oldVisit)).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (contributionMergeLivingRoot
          (actionRootedAt oldVisit)).toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ =>
    contributionMergeEmitted (actionRootedAt oldVisit) 0
  backward := fun _ =>
    (actionSourceRootAt oldVisit).emitted
      (actionSourceVisitAt oldVisit).current
  backward_forward := by
    intro occurrence
    exact
      (lossAllocationOccurrence_eq_emitted
        (actionRootedAt oldVisit) occurrence).symm
  forward_backward := by
    intro occurrence
    exact
      (contributionMergeOccurrence_eq_emitted
        (actionRootedAt oldVisit) occurrence).symm

@[simp] theorem actionOccurrencePresentation_commutes
    (oldVisit : OldVisit) :
    (actionOccurrencePresentationAt oldVisit).forward
        (actionExactSourceEventAt oldVisit).occurrence =
      (contributionMergeLivingRoot
        (actionRootedAt oldVisit)).emitted
          (contributionMergeLivingRoot
            (actionRootedAt oldVisit)).toAuthoritativeRoot.toRoot.source.initial :=
  rfl

end
end M14SourceGeneratedContributionMergeActionSource
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource.actionSourceAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource.actionOccurrencePresentationAt
