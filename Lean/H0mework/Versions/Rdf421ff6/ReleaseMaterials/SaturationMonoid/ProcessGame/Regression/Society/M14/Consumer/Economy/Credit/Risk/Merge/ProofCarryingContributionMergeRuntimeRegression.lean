import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime

/-!
# Direct consumer of the canonical contribution-merge runtime

The canonical M9 runtime performs U8 at depth zero, consumes the revised
current-`2` contribution-merge action at depth one, and enters that generated
merge target as the capacity action source at depth two.  This consumer audits the exact action receipt and
the two adjacent negative controls: the U8 tick is not the merge action, and
the merge tick is not another U8.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionMergeRuntimeRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeCompiler
open M14SourceGeneratedContributionMergeLifecycle
open M14SourceGeneratedContributionMergeRestructuring
open M14SourceGeneratedContributionMergeRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionMergeActionReceipt
open M14SourceGeneratedContributionMergeActionState
open M14SourceGeneratedContributionCapacityCutActionState
open M14SourceGeneratedSequentialContributionCapacityCut

abbrev Rooted := M9ProofCarryingRenewalU8Failure.rooted
abbrev Action := generatedContributionMergeAction
abbrev TargetN := M14SourceGeneratedContributionMergeWorld.TargetN Rooted

theorem firstTick_contains_no_contributionMergeAction :
    IsEmpty
      (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
        firstTick.resolution Action) := by
  constructor
  rw [firstTick_resolution_is_jointCore]
  exact fun impossible => impossible

theorem secondTick_contains_no_u8_core
    {Core : Type 11} (core : Core) :
    IsEmpty
      (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsU8Core
        secondTick.resolution core) := by
  constructor
  rw [secondTick_resolution_is_contributionMerge]
  exact fun impossible => impossible

/-- A raw action seal is not itself a reachable named-runtime activation. -/
def rawContributionMergeAction_cannot_wrap_runtime : PUnit := by
  fail_if_success
    exact (Action :
      SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt
        jointRuntime.initialState)
  exact PUnit.unit

theorem contributionMergeTarget_rootSemantic_has_no_failure
    {support : TargetN.Support}
    (obstruction : TargetN.ObstructionAt support) :
    ActualExpressibilityFailure
      (TheoryState.rootSemantic TargetN) obstruction → False := by
  intro impossible
  exact
    (TheoryState.rootSemantic_actualExpressibilityFailure_isEmpty
      TargetN obstruction).false impossible

structure ProofCarryingContributionMergeRuntimeCertificate : Type 3 where
  secondTickResolution :
    secondTick.resolution = .actualAction Action
  secondTickKind : secondTick.resolutionKind = .actualAction
  runtimeResumption :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      Action jointRuntime 1
  sourceCurrent :
    (actionSourceVisitAt canonicalOldVisit).current = 2
  sourceEntry :
    actionSourceEntryAt canonicalOldVisit =
      lossAllocationTargetObstruction Rooted
  sourceOccurrence :
    (actionExactSourceEventAt canonicalOldVisit).occurrence =
      M9ProofCarryingRenewalU8RevisedLedger.revisedEmittedAt
        canonicalOldVisit 2
  initialNoFresh :
    (targetEntry :
      (contributionMergeInitialLedger Rooted).Entry) →
      Nonempty (Sigma fun oldEntry :
        (lossAllocationTargetLedger Rooted).Entry =>
        PLift (contributionMergeInitialEntry Rooted oldEntry = targetEntry))
  compilerSelectedMerge :
    (contributionMergeFirstRestructuringCertification Rooted
      (contributionMergeEmitted Rooted 0)).merge
        (initialChildA Rooted) (initialChildB Rooted)
        (contributionMergeFirst_children_repeatedDestination Rooted
          (contributionMergeEmitted Rooted 0)) =
      SourceNativeMergeClassificationAt.merge
        (contributionMergeFirstCoverage Rooted
          (contributionMergeEmitted Rooted 0))
  everyParentOwned :
    (parent : (ContributionMergeRestructuringV Rooted).Obligation) →
    (member : parent ∈
      (contributionMergeFirstReceipt Rooted
        (contributionMergeEmitted Rooted 0)).parents) →
      SourceOwnsResponsibilityIncidence
        (ContributionMergeRestructuringV Rooted).base
        (contributionMergeFirstReceipt Rooted
          (contributionMergeEmitted Rooted 0)).sourceEvent parent
  obstructionNotParent :
    initialObstructionObligation Rooted
        (contributionMergeEmitted Rooted 0) ∉
      (contributionMergeFirstReceipt Rooted
        (contributionMergeEmitted Rooted 0)).parents
  noSimultaneousSplit :
    (left right : (contributionMergeTargetLedger Rooted).Entry) →
    (origin_eq :
      ((contributionMergeFirstEvolution Rooted
        (contributionMergeEmitted Rooted 0)).origin left).1 =
      ((contributionMergeFirstEvolution Rooted
        (contributionMergeEmitted Rooted 0)).origin right).1) →
      IsEmpty
        (SourceNativeSplitCoverageAt
          (contributionMergeRestructuringLaw Rooted)
          (contributionMergeEmitted Rooted 0)
          (contributionMergeFirstEvolution Rooted
            (contributionMergeEmitted Rooted 0))
          left right origin_eq × PLift (left ≠ right))
  existingBearer :
    contributionMergeBearerAt Rooted
        exactSourceGeneratedLossAllocationMaterialWitness
        (mergedContributionEntry Rooted) =
      sourceGeneratedLossAllocationMaterial.childBearerAt .a
  targetNext :
    (targetInitialAnswerAndNextAt canonicalOldVisit).nextCurrent =
      ⟨M14SourceGeneratedContributionMergeCompiler.TargetV Rooted,
        (contributionMergeLivingRoot Rooted).toAuthoritativeRoot,
        (contributionMergeRootInitialVisit Rooted).next
          (contributionMergeRootFirstSuccessor Rooted).next_eq⟩
  targetRootPreserved : HEq
    (processPresentation .contributionCapacityAction).state.base.root
    Action.target.targetRoot
  thirdStateIsTarget :
    (jointRuntime.stateAt 2).engine.node =
      .active (contributionCapacityCutActionPresentationAt canonicalOldVisit)
  thirdTickCapacityAction :
    thirdTick.resolution =
      .actualAction
        (generatedContributionCapacityCutActionAt canonicalOldVisit)
  firstTickNoMerge :
    IsEmpty
      (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
        firstTick.resolution Action)
  secondTickNoU8 :
    ∀ {Core : Type 11} (core : Core),
      IsEmpty
        (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsU8Core
          secondTick.resolution core)

def proofCarryingContributionMergeRuntimeCertificate :
    ProofCarryingContributionMergeRuntimeCertificate where
  secondTickResolution := secondTick_resolution_is_contributionMerge
  secondTickKind := secondTick_resolutionKind_is_actualAction
  runtimeResumption := contributionMergeResumption
  sourceCurrent := actionSourceVisit_current_exact canonicalOldVisit
  sourceEntry := actionSourceEntry_is_existing_obstruction canonicalOldVisit
  sourceOccurrence := actionExactSourceEvent_occurrence_exact canonicalOldVisit
  initialNoFresh := Action.receipt.initialNoFresh
  compilerSelectedMerge := Action.receipt.compilerSelectedMerge
  everyParentOwned := Action.receipt.everyParentOwned
  obstructionNotParent := Action.receipt.obstructionNotParent
  noSimultaneousSplit := Action.receipt.noSimultaneousSplit
  existingBearer := Action.receipt.existingBearer
  targetNext := Action.receipt.canonicalTargetNext
  targetRootPreserved :=
    secondTick_next_preserves_contributionMergeRoot
  thirdStateIsTarget := thirdState_node_is_contributionCapacityAction
  thirdTickCapacityAction := thirdTick_resolution_is_contributionCapacityCut
  firstTickNoMerge := firstTick_contains_no_contributionMergeAction
  secondTickNoU8 := secondTick_contains_no_u8_core

end
end M14ProofCarryingContributionMergeRuntimeRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionMergeRuntimeRegression.proofCarryingContributionMergeRuntimeCertificate
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionMergeRuntimeRegression.firstTick_contains_no_contributionMergeAction
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionMergeRuntimeRegression.secondTick_contains_no_u8_core
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionMergeRuntimeRegression.contributionMergeTarget_rootSemantic_has_no_failure
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionMergeRuntimeRegression.rawContributionMergeAction_cannot_wrap_runtime
