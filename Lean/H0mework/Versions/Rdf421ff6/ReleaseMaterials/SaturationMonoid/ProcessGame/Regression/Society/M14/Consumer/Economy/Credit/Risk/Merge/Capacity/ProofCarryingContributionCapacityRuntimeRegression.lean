import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Credit.Risk.Merge.ProofCarryingContributionMergeRuntimeRegression

/-!
# Direct consumer of contribution capacity cut and self-U8

The canonical runtime consumes the merged contribution row at depth `2`,
spends its budget `1 -> 0`, and enters the capacity target.  The same target
occurrence exposes a distinct obstruction row, whose source-generated
residual passes U7, proves actual expressibility failure under the narrower
operational law, and triggers self-U8 at depth `3`.  Depth `4` consumes the
three-row minimal-coface target.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityRuntimeRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutLifecycle
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityCutActionReceipt
open M14SourceGeneratedSequentialContributionCapacityCut
open M14SourceGeneratedContributionCapacityFailure
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8Revision
open M14SourceGeneratedContributionCapacityU8TargetState

abbrev Rooted := M9ProofCarryingRenewalU8Failure.rooted
abbrev CapacityAction :=
  generatedContributionCapacityCutActionAt canonicalOldVisit
abbrev CapacityCore :=
  generatedContributionCapacityU8CoreAt canonicalOldVisit

theorem thirdTick_contains_no_u8_core
    {Core : Type 11} (core : Core) :
    IsEmpty
      (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsU8Core
        thirdTick.resolution core) := by
  constructor
  rw [thirdTick_resolution_is_contributionCapacityCut]
  exact fun impossible => impossible

theorem fourthTick_contains_no_sequential_action
    {Action : Type 10} (action : Action) :
    IsEmpty
      (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
        fourthTick.resolution action) := by
  constructor
  rw [fourthTick_resolution_is_contributionCapacitySelfU8]
  exact fun impossible => impossible

def rawCapacityAction_cannot_wrap_runtime : PUnit := by
  fail_if_success
    exact (CapacityAction :
      SourceNativeInquiryRuntime.ExactActivatedInquiryOccurrenceAt
        jointRuntime.initialState)
  exact PUnit.unit

theorem contributionCapacityOperationalTheory_ne_rootSemantic :
    contributionCapacityOperationalTheory Rooted ≠
      TheoryState.rootSemantic (CutN Rooted) := by
  intro theory_eq
  have impossible := contributionCapacityOperationalFailure Rooted
  rw [theory_eq] at impossible
  exact
    (TheoryState.rootSemantic_actualExpressibilityFailure_isEmpty
      (CutN Rooted) (contributionCapacityResidual Rooted)).false impossible

theorem capacityAction_targetEntry_ne_failureEntry :
    CapacityAction.target.targetEntry ≠
      contributionCapacityCutTargetObstruction Rooted := by
  change contributionCapacityCutTargetContribution Rooted ≠
    contributionCapacityCutTargetObstruction Rooted
  exact contributionCapacityCutTargetEntries_distinct Rooted

theorem capacityAction_and_failure_share_target_visit :
    HEq CapacityAction.target.targetVisit
      (contributionCapacityRootTargetVisit Rooted) :=
  HEq.rfl

structure ProofCarryingContributionCapacityRuntimeCertificate : Type 4 where
  capacityResolution :
    thirdTick.resolution = .actualAction CapacityAction
  capacityKind : thirdTick.resolutionKind = .actualAction
  capacityRuntimeResumption :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      CapacityAction jointRuntime 2
  sourceCurrent :
    (capacityActionSourceVisitAt canonicalOldVisit).current = 1
  sourceEntry :
    capacityActionSourceEntryAt canonicalOldVisit =
      mergedContributionEntry Rooted
  sourceOccurrence :
    (capacityActionExactSourceEventAt canonicalOldVisit).occurrence =
      M14SourceGeneratedContributionMergeCompiler.contributionMergeEmitted
        Rooted 1
  initialNoFresh :
    (targetEntry : (contributionCapacityCutInitialLedger Rooted).Entry) →
      Nonempty (Sigma fun oldEntry :
        (contributionMergeTargetLedger Rooted).Entry =>
        PLift (contributionCapacityCutInitialEntry Rooted oldEntry =
          targetEntry))
  sourceBudgetOne : (initialContribution Rooted).progressBudget = 1
  targetBudgetZero :
    (contributionCapacityCutTargetContribution Rooted).progressBudget = 0
  strictDebit :
    LedgerEntryEvolutionAt (CutN Rooted)
      (initialContribution Rooted)
      (contributionCapacityCutTargetContribution Rooted)
  obstructionContinuity :
    LedgerEntryEvolutionAt (CutN Rooted)
      (initialObstruction Rooted)
      (contributionCapacityCutTargetObstruction Rooted)
  contributionBearerExisting :
    contributionCapacityCutBearerAt Rooted
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityCutTargetContribution Rooted) =
      sourceGeneratedLossAllocationMaterial.childBearerAt .a
  obstructionBearerExisting :
    contributionCapacityCutBearerAt Rooted
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityCutTargetObstruction Rooted) =
      sourceGeneratedLossAllocationMaterial.parentBearer
  targetLawIsOperational :
    CapacityAction.target.targetTheory =
      contributionCapacityOperationalTheory Rooted
  targetLawEmbedsRootSemantic :
    ConservativeTheoryTranslation
      (contributionCapacityOperationalTheory Rooted)
      (TheoryState.rootSemantic (CutN Rooted))
  operationalLawIsStrictlyNarrower :
    contributionCapacityOperationalTheory Rooted ≠
      TheoryState.rootSemantic (CutN Rooted)
  residualClaimExact :
    (CutN Rooted).obstructionClaim (contributionCapacityResidual Rooted) =
      contributionObstructionClaim Rooted
  residualFailure :
    ActualExpressibilityFailure
      (contributionCapacityOperationalTheory Rooted)
      (contributionCapacityResidual Rooted)
  sameTargetVisit :
    HEq CapacityAction.target.targetVisit
      (contributionCapacityRootTargetVisit Rooted)
  actionAndSearchRowsDistinct :
    CapacityAction.target.targetEntry ≠
      contributionCapacityCutTargetObstruction Rooted
  selfU8Resolution :
    fourthTick.resolution =
      .revised (contributionCapacityResidual Rooted)
        (contributionCapacityU7Gate Rooted)
        (contributionCapacityOperationalFailure Rooted) CapacityCore
  selfU8RuntimeResumption :
    SourceNativeInquiryRuntime.CofaceRealizationResumptionAt
      CapacityCore jointRuntime 3
  selfU8IsCanonicalMinimalCoface :
    CapacityCore.revision.generate.NewN =
      (CapacityCofaceAt canonicalOldVisit).worldNetwork
  selfU8WholeLedgerExactlyThree :
    (entry : (contributionCapacityU8Ledger canonicalOldVisit).Entry) →
      entry = contributionCapacityU8InheritedContribution canonicalOldVisit ∨
      entry = contributionCapacityU8InheritedObstruction canonicalOldVisit ∨
      entry = contributionCapacityU8GeneratedResidual canonicalOldVisit
  generatedResidualHasNoOldPreimage :
    IsEmpty (Sigma fun oldEntry : OpenResponsibilityAt (CutN Rooted)
        ((CapacityRootAt canonicalOldVisit).toAuthoritativeRoot.toRoot.supportAt
          (capacityRootedFailureAt canonicalOldVisit).oldSuccessor.next) =>
      PLift ((CapacityCofaceAt canonicalOldVisit).cofaceLedgerRetract.forward
        oldEntry = contributionCapacityU8GeneratedResidual canonicalOldVisit))
  generatedResidualBearerExisting :
    contributionCapacityU8BearerAt canonicalOldVisit
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityU8GeneratedResidual canonicalOldVisit) =
      sourceGeneratedLossAllocationMaterial.parentBearer
  revisedTargetAnswered :
    fifthTick.resolution =
      .directlyAnswered
        (contributionCapacityU8AnswerFaceAt canonicalOldVisit 0)
        (contributionCapacityU8AnswerConsumerAt canonicalOldVisit 0)
  capacityTickNoU8 :
    ∀ {Core : Type 11} (core : Core),
      IsEmpty
        (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsU8Core
          thirdTick.resolution core)
  selfU8TickNoAction :
    ∀ {Action : Type 10} (action : Action),
      IsEmpty
        (SourceNativeInquiryRuntime.RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
          fourthTick.resolution action)

def proofCarryingContributionCapacityRuntimeCertificate :
    ProofCarryingContributionCapacityRuntimeCertificate where
  capacityResolution := thirdTick_resolution_is_contributionCapacityCut
  capacityKind := thirdTick_resolutionKind_is_actualAction
  capacityRuntimeResumption := contributionCapacityCutResumption
  sourceCurrent := capacityActionSourceVisit_current_exact canonicalOldVisit
  sourceEntry :=
    capacityActionSourceEntry_is_mergedContribution canonicalOldVisit
  sourceOccurrence :=
    capacityActionExactSourceEvent_occurrence_exact canonicalOldVisit
  initialNoFresh := CapacityAction.receipt.initialNoFresh
  sourceBudgetOne := CapacityAction.receipt.sourceBudgetOne
  targetBudgetZero := CapacityAction.receipt.targetBudgetZero
  strictDebit := CapacityAction.receipt.strictDebit
  obstructionContinuity := CapacityAction.receipt.obstructionContinuity
  contributionBearerExisting :=
    CapacityAction.receipt.existingContributionBearer
  obstructionBearerExisting :=
    CapacityAction.receipt.existingObstructionBearer
  targetLawIsOperational :=
    generatedContributionCapacityCutAction_targetTheory_exact canonicalOldVisit
  targetLawEmbedsRootSemantic :=
    CapacityAction.receipt.operationalTheoryEmbedsRootSemantic
  operationalLawIsStrictlyNarrower :=
    contributionCapacityOperationalTheory_ne_rootSemantic
  residualClaimExact := CapacityAction.receipt.residualClaim
  residualFailure := CapacityAction.receipt.residualFailure
  sameTargetVisit := capacityAction_and_failure_share_target_visit
  actionAndSearchRowsDistinct := capacityAction_targetEntry_ne_failureEntry
  selfU8Resolution := fourthTick_resolution_is_contributionCapacitySelfU8
  selfU8RuntimeResumption := contributionCapacitySelfU8Resumption
  selfU8IsCanonicalMinimalCoface := rfl
  selfU8WholeLedgerExactlyThree :=
    contributionCapacityU8Entry_cases canonicalOldVisit
  generatedResidualHasNoOldPreimage :=
    (CapacityCofaceAt canonicalOldVisit).obstructionEntry_hasNoOldPreimage
  generatedResidualBearerExisting :=
    contributionCapacityU8_generatedBearer_is_existingParent canonicalOldVisit
  revisedTargetAnswered := fifthTick_is_generated_selfU8_target_answer
  capacityTickNoU8 := thirdTick_contains_no_u8_core
  selfU8TickNoAction := fourthTick_contains_no_sequential_action

end
end M14ProofCarryingContributionCapacityRuntimeRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityRuntimeRegression.proofCarryingContributionCapacityRuntimeCertificate
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityRuntimeRegression.contributionCapacityOperationalTheory_ne_rootSemantic
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityRuntimeRegression.capacityAction_targetEntry_ne_failureEntry
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityRuntimeRegression.rawCapacityAction_cannot_wrap_runtime
