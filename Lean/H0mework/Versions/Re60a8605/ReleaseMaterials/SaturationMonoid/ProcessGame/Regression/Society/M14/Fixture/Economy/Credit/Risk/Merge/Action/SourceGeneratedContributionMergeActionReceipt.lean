import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Action.SourceGeneratedContributionMergeActionSource

/-!
# Proof-carrying receipt of the contribution-merge action

The receipt records the target root's exact first compiler image.  In
particular, it carries the compiler-selected A/B merge, exact parent
ownership, obstruction exclusion, absence of a simultaneous split, reuse of
an existing bearer, conservative no-fresh ingress and the canonical target
answer-and-next.  It is indexed by the source event and cannot choose a root
or successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionMergeActionReceipt

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeCompiler
open M14SourceGeneratedContributionMergeLifecycle
open M14SourceGeneratedContributionMergeRestructuring
open M14SourceGeneratedContributionMergeRoot
open M14SourceGeneratedContributionMergeActionSource

def targetInitialAuthorityAt (oldVisit : OldVisit) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (contributionMergeLivingRoot (actionRootedAt oldVisit))
      (contributionMergeRootInitialVisit (actionRootedAt oldVisit))
      (initialObstruction (actionRootedAt oldVisit)) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (contributionMergeLivingRoot (actionRootedAt oldVisit))
    (initialObstruction (actionRootedAt oldVisit))
    (contributionMergeRootInitialObstructionRow (actionRootedAt oldVisit))

def targetInitialAnswerAndNextAt (oldVisit : OldVisit) :
    SourceNativeLivingCausalEntryAnswerAndNextAt
      (contributionMergeLivingRoot (actionRootedAt oldVisit))
      (contributionMergeRootInitialVisit (actionRootedAt oldVisit))
      (initialObstruction (actionRootedAt oldVisit))
      (targetInitialAuthorityAt oldVisit) :=
  (contributionMergeLivingRoot (actionRootedAt oldVisit))
    |>.generatedCausalEntryAnswerAndNextAt
      (contributionMergeRootInitialVisit (actionRootedAt oldVisit))
      (initialObstruction (actionRootedAt oldVisit))
      (targetInitialAuthorityAt oldVisit)

/-- Nonempty exact action receipt.  Its constructor is private so callers
cannot replace any target-root fact while retaining this public type. -/
structure ExactContributionMergeActionReceiptAt
    (oldVisit : OldVisit)
    (exactSource : ExactTemporalCausalRootEventAt
      (actionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
        (actionSourceVisitAt oldVisit))
    (_answer : PUnit) : Type 3 where
  private mk ::
  source_eq : exactSource = actionExactSourceEventAt oldVisit
  initialNoFresh :
    (targetEntry :
      (contributionMergeInitialLedger (actionRootedAt oldVisit)).Entry) →
      Nonempty (Sigma fun oldEntry :
        (lossAllocationTargetLedger (actionRootedAt oldVisit)).Entry =>
        PLift (contributionMergeInitialEntry (actionRootedAt oldVisit)
          oldEntry = targetEntry))
  compilerSelectedMerge :
    (contributionMergeFirstRestructuringCertification
      (actionRootedAt oldVisit)
      (contributionMergeEmitted (actionRootedAt oldVisit) 0)).merge
        (initialChildA (actionRootedAt oldVisit))
        (initialChildB (actionRootedAt oldVisit))
        (contributionMergeFirst_children_repeatedDestination
          (actionRootedAt oldVisit)
          (contributionMergeEmitted (actionRootedAt oldVisit) 0)) =
      SourceNativeMergeClassificationAt.merge
        (contributionMergeFirstCoverage (actionRootedAt oldVisit)
          (contributionMergeEmitted (actionRootedAt oldVisit) 0))
  everyParentOwned :
    (parent : (ContributionMergeRestructuringV
      (actionRootedAt oldVisit)).Obligation) →
    (member : parent ∈
      (contributionMergeFirstReceipt (actionRootedAt oldVisit)
        (contributionMergeEmitted
          (actionRootedAt oldVisit) 0)).parents) →
      SourceOwnsResponsibilityIncidence
        (ContributionMergeRestructuringV
          (actionRootedAt oldVisit)).base
        (contributionMergeFirstReceipt (actionRootedAt oldVisit)
          (contributionMergeEmitted
            (actionRootedAt oldVisit) 0)).sourceEvent parent
  obstructionNotParent :
    initialObstructionObligation (actionRootedAt oldVisit)
        (contributionMergeEmitted (actionRootedAt oldVisit) 0) ∉
      (contributionMergeFirstReceipt (actionRootedAt oldVisit)
        (contributionMergeEmitted
          (actionRootedAt oldVisit) 0)).parents
  noSimultaneousSplit :
    (left right :
      (contributionMergeTargetLedger (actionRootedAt oldVisit)).Entry) →
    (origin_eq :
      ((contributionMergeFirstEvolution (actionRootedAt oldVisit)
        (contributionMergeEmitted
          (actionRootedAt oldVisit) 0)).origin left).1 =
      ((contributionMergeFirstEvolution (actionRootedAt oldVisit)
        (contributionMergeEmitted
          (actionRootedAt oldVisit) 0)).origin right).1) →
      IsEmpty
        (SourceNativeSplitCoverageAt
          (contributionMergeRestructuringLaw (actionRootedAt oldVisit))
          (contributionMergeEmitted (actionRootedAt oldVisit) 0)
          (contributionMergeFirstEvolution (actionRootedAt oldVisit)
            (contributionMergeEmitted (actionRootedAt oldVisit) 0))
          left right origin_eq × PLift (left ≠ right))
  existingBearer :
    contributionMergeBearerAt (actionRootedAt oldVisit)
        exactSourceGeneratedLossAllocationMaterialWitness
        (mergedContributionEntry (actionRootedAt oldVisit)) =
      sourceGeneratedLossAllocationMaterial.childBearerAt .a
  canonicalTargetNext :
    (targetInitialAnswerAndNextAt oldVisit).nextCurrent =
      ⟨M14SourceGeneratedContributionMergeCompiler.TargetV
          (actionRootedAt oldVisit),
        (contributionMergeLivingRoot
          (actionRootedAt oldVisit)).toAuthoritativeRoot,
        (contributionMergeRootInitialVisit
          (actionRootedAt oldVisit)).next
            (contributionMergeRootFirstSuccessor
              (actionRootedAt oldVisit)).next_eq⟩

def exactContributionMergeActionReceiptAt
    (oldVisit : OldVisit)
    (exactSource : ExactTemporalCausalRootEventAt
      (actionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
        (actionSourceVisitAt oldVisit))
    (answer : PUnit) :
    ExactContributionMergeActionReceiptAt oldVisit exactSource answer := by
  rw [exactSource.eq_generated]
  exact
    { source_eq := rfl
      initialNoFresh :=
        contributionMerge_initialLedger_noFresh (actionRootedAt oldVisit)
      compilerSelectedMerge :=
        contributionMergeCompiler_selects_exact_first_merge
          (actionRootedAt oldVisit)
          (contributionMergeEmitted (actionRootedAt oldVisit) 0)
      everyParentOwned :=
        contributionMergeFirstParentOwnership
          (actionRootedAt oldVisit)
          (contributionMergeEmitted (actionRootedAt oldVisit) 0)
      obstructionNotParent :=
        contributionMergeFirst_obstruction_not_parent
          (actionRootedAt oldVisit)
          (contributionMergeEmitted (actionRootedAt oldVisit) 0)
      noSimultaneousSplit :=
        contributionMergeFirst_no_simultaneous_split
          (actionRootedAt oldVisit)
          (contributionMergeEmitted (actionRootedAt oldVisit) 0)
      existingBearer :=
        mergedContribution_bearer_is_existing_legA
          (actionRootedAt oldVisit)
          exactSourceGeneratedLossAllocationMaterialWitness
      canonicalTargetNext := rfl }

end
end M14SourceGeneratedContributionMergeActionReceipt
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeActionReceipt.exactContributionMergeActionReceiptAt
