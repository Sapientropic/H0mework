import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Action.SourceGeneratedContributionCapacityCutActionSource

/-!
# Proof-carrying receipt of the contribution-capacity action

The receipt is indexed by the exact merge-target occurrence.  It records the
complete two-row first write, the strict `1 -> 0` contribution debit, exact
obstruction continuity, one-to-one restructuring, bearer reuse, the narrower
operational law surface, the generated residual failure, and the canonical
next visit.  No field can submit an alternative target or successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCutActionReceipt

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutLifecycle
open M14SourceGeneratedContributionCapacityCutRestructuring
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutActionSource

def capacityTargetInitialContributionAuthorityAt
    (oldVisit : OldVisit) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (contributionCapacityLivingRoot (capacityActionRootedAt oldVisit))
      (contributionCapacityRootInitialVisit (capacityActionRootedAt oldVisit))
      (initialContribution (capacityActionRootedAt oldVisit)) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (contributionCapacityLivingRoot (capacityActionRootedAt oldVisit))
    (initialContribution (capacityActionRootedAt oldVisit))
    (contributionCapacityRootInitialContributionRow
      (capacityActionRootedAt oldVisit))

def capacityTargetInitialAnswerAndNextAt
    (oldVisit : OldVisit) :
    SourceNativeLivingCausalEntryAnswerAndNextAt
      (contributionCapacityLivingRoot (capacityActionRootedAt oldVisit))
      (contributionCapacityRootInitialVisit (capacityActionRootedAt oldVisit))
      (initialContribution (capacityActionRootedAt oldVisit))
      (capacityTargetInitialContributionAuthorityAt oldVisit) :=
  (contributionCapacityLivingRoot (capacityActionRootedAt oldVisit))
    |>.generatedCausalEntryAnswerAndNextAt
      (contributionCapacityRootInitialVisit (capacityActionRootedAt oldVisit))
      (initialContribution (capacityActionRootedAt oldVisit))
      (capacityTargetInitialContributionAuthorityAt oldVisit)

structure ExactContributionCapacityCutActionReceiptAt
    (oldVisit : OldVisit)
    (exactSource : ExactTemporalCausalRootEventAt
      (capacityActionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
      (capacityActionSourceVisitAt oldVisit))
    (_answer : PUnit) : Type 3 where
  private mk ::
  source_eq : exactSource = capacityActionExactSourceEventAt oldVisit
  initialNoFresh :
    (targetEntry :
      (contributionCapacityCutInitialLedger
        (capacityActionRootedAt oldVisit)).Entry) →
      Nonempty (Sigma fun oldEntry :
        (contributionMergeTargetLedger
          (capacityActionRootedAt oldVisit)).Entry =>
        PLift (contributionCapacityCutInitialEntry
          (capacityActionRootedAt oldVisit) oldEntry = targetEntry))
  sourceBudgetOne :
    (initialContribution
      (capacityActionRootedAt oldVisit)).progressBudget = 1
  targetBudgetZero :
    (contributionCapacityCutTargetContribution
      (capacityActionRootedAt oldVisit)).progressBudget = 0
  strictDebit :
    LedgerEntryEvolutionAt (CutN (capacityActionRootedAt oldVisit))
      (initialContribution (capacityActionRootedAt oldVisit))
      (contributionCapacityCutTargetContribution
        (capacityActionRootedAt oldVisit))
  obstructionContinuity :
    LedgerEntryEvolutionAt (CutN (capacityActionRootedAt oldVisit))
      (initialObstruction (capacityActionRootedAt oldVisit))
      (contributionCapacityCutTargetObstruction
        (capacityActionRootedAt oldVisit))
  originInjective :
    Function.Injective
      (fun targetEntry =>
        ((contributionCapacityFirstEvolution
          (capacityActionRootedAt oldVisit)
          (contributionCapacityCutEmitted
            (capacityActionRootedAt oldVisit) 0)).origin targetEntry).1)
  destinationInjective :
    Function.Injective
      (fun sourceEntry =>
        ((contributionCapacityFirstEvolution
          (capacityActionRootedAt oldVisit)
          (contributionCapacityCutEmitted
            (capacityActionRootedAt oldVisit) 0)).destination sourceEntry).1)
  existingContributionBearer :
    contributionCapacityCutBearerAt (capacityActionRootedAt oldVisit)
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityCutTargetContribution
          (capacityActionRootedAt oldVisit)) =
      sourceGeneratedLossAllocationMaterial.childBearerAt .a
  existingObstructionBearer :
    contributionCapacityCutBearerAt (capacityActionRootedAt oldVisit)
        exactSourceGeneratedLossAllocationMaterialWitness
        (contributionCapacityCutTargetObstruction
          (capacityActionRootedAt oldVisit)) =
      sourceGeneratedLossAllocationMaterial.parentBearer
  operationalLawSurface :
    (contributionCapacityLivingRoot
      (capacityActionRootedAt oldVisit)).source.base.lawSurface =
      contributionCapacityOperationalTheory (capacityActionRootedAt oldVisit)
  operationalTheoryEmbedsRootSemantic :
    ConservativeTheoryTranslation
      (contributionCapacityOperationalTheory
        (capacityActionRootedAt oldVisit))
      (TheoryState.rootSemantic
        (CutN (capacityActionRootedAt oldVisit)))
  residualClaim :
    (CutN (capacityActionRootedAt oldVisit)).obstructionClaim
        (contributionCapacityResidual (capacityActionRootedAt oldVisit)) =
      contributionObstructionClaim (capacityActionRootedAt oldVisit)
  residualFailure :
    ActualExpressibilityFailure
      (contributionCapacityOperationalTheory
        (capacityActionRootedAt oldVisit))
      (contributionCapacityResidual (capacityActionRootedAt oldVisit))
  canonicalTargetNext :
    (capacityTargetInitialAnswerAndNextAt oldVisit).nextCurrent =
      ⟨M14SourceGeneratedContributionCapacityCutCompiler.TargetV
          (capacityActionRootedAt oldVisit),
        (contributionCapacityLivingRoot
          (capacityActionRootedAt oldVisit)).toAuthoritativeRoot,
        (contributionCapacityRootInitialVisit
          (capacityActionRootedAt oldVisit)).next
            (contributionCapacityRootFirstSuccessor
              (capacityActionRootedAt oldVisit)).next_eq⟩

def exactContributionCapacityCutActionReceiptAt
    (oldVisit : OldVisit)
    (exactSource : ExactTemporalCausalRootEventAt
      (capacityActionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
      (capacityActionSourceVisitAt oldVisit))
    (answer : PUnit) :
    ExactContributionCapacityCutActionReceiptAt
      oldVisit exactSource answer := by
  rw [exactSource.eq_generated]
  exact
    { source_eq := rfl
      initialNoFresh := contributionCapacityCut_initialLedger_noFresh
        (capacityActionRootedAt oldVisit)
      sourceBudgetOne :=
        contributionCapacityCut_initialContribution_budget
          (capacityActionRootedAt oldVisit)
      targetBudgetZero :=
        contributionCapacityCut_targetContribution_budget
          (capacityActionRootedAt oldVisit)
      strictDebit := contributionCapacityStrictDebit
        (capacityActionRootedAt oldVisit)
      obstructionContinuity := contributionCapacityObstructionContinuity
        (capacityActionRootedAt oldVisit)
      originInjective := contributionCapacityFirst_origin_injective
        (capacityActionRootedAt oldVisit)
        (contributionCapacityCutEmitted
          (capacityActionRootedAt oldVisit) 0)
      destinationInjective := contributionCapacityFirst_destination_injective
        (capacityActionRootedAt oldVisit)
        (contributionCapacityCutEmitted
          (capacityActionRootedAt oldVisit) 0)
      existingContributionBearer :=
        contributionCapacityCutBearer_targetContribution
          (capacityActionRootedAt oldVisit)
          exactSourceGeneratedLossAllocationMaterialWitness
      existingObstructionBearer :=
        contributionCapacityCutBearer_targetObstruction
          (capacityActionRootedAt oldVisit)
          exactSourceGeneratedLossAllocationMaterialWitness
      operationalLawSurface := rfl
      operationalTheoryEmbedsRootSemantic :=
        contributionCapacityOperationalTheory_rootSemantic
          (capacityActionRootedAt oldVisit)
      residualClaim := contributionCapacityResidual_claim_exact
        (capacityActionRootedAt oldVisit)
      residualFailure := contributionCapacityOperationalFailure
        (capacityActionRootedAt oldVisit)
      canonicalTargetNext := rfl }

end
end M14SourceGeneratedContributionCapacityCutActionReceipt
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutActionReceipt.exactContributionCapacityCutActionReceiptAt
