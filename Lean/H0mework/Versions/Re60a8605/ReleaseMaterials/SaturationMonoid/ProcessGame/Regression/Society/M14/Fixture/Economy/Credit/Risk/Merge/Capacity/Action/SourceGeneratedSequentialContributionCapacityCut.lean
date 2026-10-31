import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Action.SourceGeneratedContributionCapacityCutActionReceipt

/-!
# Source-generated sequential contribution-capacity cut

One fixed program consumes the merge root's exact current-`1` contribution
row and recomputes the capacity root.  The execution seal stores no target,
root, ledger, receipt or next; all are dependent readouts of this program.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialContributionCapacityCut

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityCutActionReceipt

def contributionCapacityCutActionTargetAt
    (oldVisit : OldVisit)
    (exactSource : ExactTemporalCausalRootEventAt
      (capacityActionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
      (capacityActionSourceVisitAt oldVisit)) :
    SourceNativeSequentialActualActionTargetAt
      (capacityActionSourceRootAt oldVisit)
      (capacityActionSourceVisitAt oldVisit) exactSource
      (capacityActionSourceEntryAt oldVisit)
      (capacityActionSourceAuthorityAt oldVisit) := by
  rw [exactSource.eq_generated]
  exact
    { TargetN := CutN (capacityActionRootedAt oldVisit)
      translation := contributionCapacityCutTranslation
        (capacityActionRootedAt oldVisit)
      TargetV := M14SourceGeneratedContributionCapacityCutCompiler.TargetV
        (capacityActionRootedAt oldVisit)
      targetRoot := contributionCapacityLivingRoot
        (capacityActionRootedAt oldVisit)
      targetTheory := contributionCapacityOperationalTheory
        (capacityActionRootedAt oldVisit)
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic :=
        contributionCapacityOperationalTheory_rootSemantic
          (capacityActionRootedAt oldVisit)
      occurrencePresentation :=
        capacityActionOccurrencePresentationAt oldVisit
      occurrence_commutes :=
        capacityActionOccurrencePresentation_commutes oldVisit
      initialSupport_heq := HEq.rfl
      initialOpenLedger :=
        (contributionCapacityCutTranslation
          (capacityActionRootedAt oldVisit)).oldOpenLedger
            (contributionMergeTargetLedger
              (capacityActionRootedAt oldVisit)).support
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun _ => Nat.le_refl _
      initialLedgerNoFresh :=
        contributionCapacityCut_initialLedger_noFresh
          (capacityActionRootedAt oldVisit)
      translatedSourceEntryRow :=
        contributionCapacityRootInitialContributionRow
          (capacityActionRootedAt oldVisit)
      firstSuccessor :=
        contributionCapacityRootFirstSuccessor
          (capacityActionRootedAt oldVisit)
      canonical_targetNextVisit_eq := rfl
      Answer := PUnit
      answer := PUnit.unit
      Receipt := fun answer => ExactContributionCapacityCutActionReceiptAt
        oldVisit (capacityActionExactSourceEventAt oldVisit) answer
      receipt := exactContributionCapacityCutActionReceiptAt oldVisit
        (capacityActionExactSourceEventAt oldVisit) PUnit.unit }

def contributionCapacityCutActionProgramAt
    (oldVisit : OldVisit) :
    SourceNativeSequentialActualActionProgramAt
      (capacityActionSourceRootAt oldVisit)
      (capacityActionSourceVisitAt oldVisit)
      (capacityActionSourceEntryAt oldVisit)
      (capacityActionSourceAuthorityAt oldVisit) where
  targetAt := contributionCapacityCutActionTargetAt oldVisit

def generatedContributionCapacityCutActionAt
    (oldVisit : OldVisit) :
    SourceGeneratedSequentialActualActionAt
      (contributionCapacityCutActionProgramAt oldVisit)
      (capacityActionExactSourceEventAt oldVisit) :=
  (contributionCapacityCutActionProgramAt oldVisit).generate
    (capacityActionExactSourceEventAt oldVisit)

def contributionCapacityCutActionCompilationAt
    (oldVisit : OldVisit)
    (exactSource : ExactTemporalCausalRootEventAt
      (capacityActionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
      (capacityActionSourceVisitAt oldVisit)) :
    SourceNativeInquiryCompilationAt
      (capacityActionSourceRootAt oldVisit)
      (capacityActionSourceVisitAt oldVisit)
      (contributionMergeU7 (capacityActionRootedAt oldVisit))
      (contributionMergeCalculus (capacityActionRootedAt oldVisit))
      (contributionMergeTheory (capacityActionRootedAt oldVisit)) ()
      (contributionMergeRootInquiryEvent
        (capacityActionRootedAt oldVisit)
        (capacityActionSourceVisitAt oldVisit))
      (capacityActionSourceEntryAt oldVisit)
      (capacityActionSourceAuthorityAt oldVisit) :=
  .actualAction
    ((contributionCapacityCutActionProgramAt oldVisit).generate exactSource)

def contributionCapacityCutActionCompilationProgramAt
    (oldVisit : OldVisit) :
    SourceNativeInquiryCompilationProgramAt
      (capacityActionSourceRootAt oldVisit)
      (capacityActionSourceVisitAt oldVisit)
      (contributionMergeU7 (capacityActionRootedAt oldVisit))
      (contributionMergeCalculus (capacityActionRootedAt oldVisit))
      (contributionMergeTheory (capacityActionRootedAt oldVisit)) ()
      (contributionMergeRootInquiryEvent
        (capacityActionRootedAt oldVisit)
        (capacityActionSourceVisitAt oldVisit))
      (capacityActionSourceEntryAt oldVisit)
      (capacityActionSourceAuthorityAt oldVisit) where
  compile := contributionCapacityCutActionCompilationAt oldVisit

@[simp] theorem generatedContributionCapacityCutAction_targetRoot_exact
    (oldVisit : OldVisit) :
    (generatedContributionCapacityCutActionAt oldVisit).target.targetRoot =
      contributionCapacityLivingRoot (capacityActionRootedAt oldVisit) :=
  rfl

@[simp] theorem generatedContributionCapacityCutAction_targetTheory_exact
    (oldVisit : OldVisit) :
    (generatedContributionCapacityCutActionAt oldVisit).target.targetTheory =
      contributionCapacityOperationalTheory
        (capacityActionRootedAt oldVisit) :=
  rfl

@[simp] theorem generatedContributionCapacityCutAction_targetVisit_exact
    (oldVisit : OldVisit) :
    (generatedContributionCapacityCutActionAt oldVisit).target.targetVisit =
      (contributionCapacityRootInitialVisit
        (capacityActionRootedAt oldVisit)).next
          (contributionCapacityRootFirstSuccessor
            (capacityActionRootedAt oldVisit)).next_eq :=
  rfl

theorem generatedContributionCapacityCutAction_macroNext_exact
    (oldVisit : OldVisit) :
    (generatedContributionCapacityCutActionAt oldVisit).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedContributionCapacityCutActionAt oldVisit).target.TargetV,
        (generatedContributionCapacityCutActionAt oldVisit).target.targetRoot.toAuthoritativeRoot,
        (generatedContributionCapacityCutActionAt oldVisit).target.targetVisit⟩ :=
  SourceNativeSequentialActualActionTargetAt.targetAnswerAndNext_next_eq
    (generatedContributionCapacityCutActionAt oldVisit).target

end
end M14SourceGeneratedSequentialContributionCapacityCut
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityCut.generatedContributionCapacityCutActionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionCapacityCut.generatedContributionCapacityCutAction_macroNext_exact
