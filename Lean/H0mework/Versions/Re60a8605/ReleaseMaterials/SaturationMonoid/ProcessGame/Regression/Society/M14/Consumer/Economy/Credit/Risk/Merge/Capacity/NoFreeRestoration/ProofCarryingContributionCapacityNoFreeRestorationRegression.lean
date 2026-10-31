import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Credit.Risk.Merge.Capacity.ProofCarryingContributionCapacityRuntimeRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.NoGo.SourceGeneratedContributionCapacityNoFreeRestoration

/-!
# Direct consumer of the no-free-capacity-restoration theorem

The actual cut really spends `1 -> 0`; the subsequent self-U8 root really
answers the generated residual; nevertheless all three revised ledger rows
remain at zero and every wholly endogenous conservative sequential target
has no positive-budget row.  Legal recognition of a residual is therefore
strictly weaker than source-backed material renewal.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityNoFreeRestorationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open RootInquiryCompletion.NoFreeCapacityRestoration
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityFailure
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState
open M14SourceGeneratedContributionCapacityNoFreeRestoration
open M14ProofCarryingContributionCapacityRuntimeRegression

abbrev Rooted := M9ProofCarryingRenewalU8Failure.rooted

structure ProofCarryingContributionCapacityNoFreeRestorationCertificate :
    Type 5 where
  actualCutStartsPositive :
    (initialContribution Rooted).progressBudget = 1
  actualCutEndsZero :
    (contributionCapacityCutTargetContribution Rooted).progressBudget = 0
  actualCutIsStrict :
    LedgerEntryEvolutionAt (CutN Rooted)
      (initialContribution Rooted)
      (contributionCapacityCutTargetContribution Rooted)
  revisedLedgerExactlyThree :
    (entry : (contributionCapacityU8Ledger canonicalOldVisit).Entry) →
      entry = contributionCapacityU8InheritedContribution canonicalOldVisit ∨
      entry = contributionCapacityU8InheritedObstruction canonicalOldVisit ∨
      entry = contributionCapacityU8GeneratedResidual canonicalOldVisit
  revisedLedgerAllZero :
    (entry : (contributionCapacityU8Ledger canonicalOldVisit).Entry) →
      entry.progressBudget = 0
  revisedLedgerHasNoPositiveRow :
    IsEmpty
      (PositiveProgressEntryAt
        (contributionCapacityU8Ledger canonicalOldVisit))
  revisedLawIsRootSemantic :
    (contributionCapacityU8LivingRoot canonicalOldVisit).source.base.lawSurface =
      TheoryState.rootSemantic (CapacityU8NAt canonicalOldVisit)
  revisedAnswerExistsWithoutRefill :
    Nonempty
        (SourceNativeInquiryAnswerConsumerAt ()
          (contributionCapacityU8InquiryEventAt canonicalOldVisit 0)
          (contributionCapacityU8GeneratedResidual canonicalOldVisit)
          (contributionCapacityU8AnswerFaceAt canonicalOldVisit 0)) ∧
      IsEmpty
        (PositiveProgressEntryAt
          (contributionCapacityU8Ledger canonicalOldVisit))
  noEndogenousPositiveRestoration :
    NoEndogenousPositiveRestorationAt canonicalOldVisit
  generatedResidualHasNoOldPreimage :
    IsEmpty (Sigma fun oldEntry : OpenResponsibilityAt (CutN Rooted)
        ((CapacityRootAt canonicalOldVisit).toAuthoritativeRoot.toRoot.supportAt
          (capacityRootedFailureAt canonicalOldVisit).oldSuccessor.next) =>
      PLift ((CapacityCofaceAt canonicalOldVisit).cofaceLedgerRetract.forward
        oldEntry =
          contributionCapacityU8GeneratedResidual canonicalOldVisit))
  generatedResidualUsesExistingBearer :
    contributionCapacityU8BearerAt canonicalOldVisit
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityU8GeneratedResidual canonicalOldVisit) =
      sourceGeneratedLossAllocationMaterial.parentBearer

def proofCarryingContributionCapacityNoFreeRestorationCertificate :
    ProofCarryingContributionCapacityNoFreeRestorationCertificate where
  actualCutStartsPositive :=
    proofCarryingContributionCapacityRuntimeCertificate.sourceBudgetOne
  actualCutEndsZero :=
    proofCarryingContributionCapacityRuntimeCertificate.targetBudgetZero
  actualCutIsStrict :=
    proofCarryingContributionCapacityRuntimeCertificate.strictDebit
  revisedLedgerExactlyThree :=
    proofCarryingContributionCapacityRuntimeCertificate.selfU8WholeLedgerExactlyThree
  revisedLedgerAllZero :=
    contributionCapacityU8Entry_budget_zero canonicalOldVisit
  revisedLedgerHasNoPositiveRow :=
    contributionCapacityU8PositiveProgress_isEmpty canonicalOldVisit
  revisedLawIsRootSemantic :=
    contributionCapacityU8Root_lawSurface_exact canonicalOldVisit
  revisedAnswerExistsWithoutRefill :=
    revisedAnswer_does_not_refill_capacity canonicalOldVisit 0
  noEndogenousPositiveRestoration :=
    contributionCapacityU8_noEndogenousPositiveRestoration canonicalOldVisit
  generatedResidualHasNoOldPreimage :=
    proofCarryingContributionCapacityRuntimeCertificate.generatedResidualHasNoOldPreimage
  generatedResidualUsesExistingBearer :=
    proofCarryingContributionCapacityRuntimeCertificate.generatedResidualBearerExisting

/-- Even pairing the installed answer with an arbitrary positive-row claim
cannot produce a restoration witness. -/
theorem installedAnswer_and_positiveRestoration_isEmpty :
    IsEmpty
      ((SourceNativeInquiryAnswerConsumerAt ()
          (contributionCapacityU8InquiryEventAt canonicalOldVisit 0)
          (contributionCapacityU8GeneratedResidual canonicalOldVisit)
          (contributionCapacityU8AnswerFaceAt canonicalOldVisit 0)) ×
        PositiveProgressEntryAt
          (contributionCapacityU8Ledger canonicalOldVisit)) := by
  constructor
  intro candidate
  exact contributionCapacityU8PositiveProgress_isEmpty canonicalOldVisit
    |>.false candidate.2

end
end M14ProofCarryingContributionCapacityNoFreeRestorationRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityNoFreeRestorationRegression.proofCarryingContributionCapacityNoFreeRestorationCertificate
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityNoFreeRestorationRegression.installedAnswer_and_positiveRestoration_isEmpty
