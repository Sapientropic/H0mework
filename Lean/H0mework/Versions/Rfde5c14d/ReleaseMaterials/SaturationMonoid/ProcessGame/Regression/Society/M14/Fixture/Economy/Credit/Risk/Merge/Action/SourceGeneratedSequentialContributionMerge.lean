import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Action.SourceGeneratedContributionMergeActionReceipt

/-!
# Source-generated sequential contribution merge

One fixed program consumes the revised root's exact current-`2` occurrence
and recomputes the conservative contribution-merge target.  The execution
seal stores no target, root, ledger, receipt or next; all of them are
dependent readouts of this program.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialContributionMerge

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalU8RevisedWorld
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeCompiler
open M14SourceGeneratedContributionMergeRestructuring
open M14SourceGeneratedContributionMergeRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionMergeActionReceipt

def contributionMergeActionTargetAt
    (oldVisit : OldVisit)
    (exactSource : ExactTemporalCausalRootEventAt
      (actionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
        (actionSourceVisitAt oldVisit)) :
    SourceNativeSequentialActualActionTargetAt
      (actionSourceRootAt oldVisit) (actionSourceVisitAt oldVisit)
      exactSource (actionSourceEntryAt oldVisit)
        (actionSourceAuthorityAt oldVisit) := by
  rw [exactSource.eq_generated]
  exact
    { TargetN := M14SourceGeneratedContributionMergeWorld.TargetN
        (actionRootedAt oldVisit)
      translation := contributionMergeTranslation (actionRootedAt oldVisit)
      TargetV := M14SourceGeneratedContributionMergeCompiler.TargetV
        (actionRootedAt oldVisit)
      targetRoot := contributionMergeLivingRoot (actionRootedAt oldVisit)
      targetTheory := TheoryState.rootSemantic
        (M14SourceGeneratedContributionMergeWorld.TargetN
          (actionRootedAt oldVisit))
      lawSurface_heq := HEq.rfl
      targetTheory_rootSemantic :=
        { compile := id
          commuting := fun _ => rfl }
      occurrencePresentation := actionOccurrencePresentationAt oldVisit
      occurrence_commutes := actionOccurrencePresentation_commutes oldVisit
      initialSupport_heq := HEq.rfl
      initialOpenLedger :=
        (contributionMergeTranslation (actionRootedAt oldVisit)).oldOpenLedger
          (lossAllocationTargetLedger (actionRootedAt oldVisit)).support
      initialOpenLedger_heq := HEq.rfl
      initialLedger_responsibility_commutes := fun _ => rfl
      initialLedger_claim_commutes := fun _ => rfl
      initialLedger_budget_conservative := fun entry => Nat.le_refl _
      initialLedgerNoFresh :=
        contributionMerge_initialLedger_noFresh (actionRootedAt oldVisit)
      translatedSourceEntryRow :=
        contributionMergeRootInitialObstructionRow (actionRootedAt oldVisit)
      firstSuccessor :=
        contributionMergeRootFirstSuccessor (actionRootedAt oldVisit)
      canonical_targetNextVisit_eq := rfl
      Answer := PUnit
      answer := PUnit.unit
      Receipt := fun answer => ExactContributionMergeActionReceiptAt
        oldVisit (actionExactSourceEventAt oldVisit) answer
      receipt := exactContributionMergeActionReceiptAt oldVisit
        (actionExactSourceEventAt oldVisit) PUnit.unit }

def contributionMergeActionProgramAt
    (oldVisit : OldVisit) :
    SourceNativeSequentialActualActionProgramAt
      (actionSourceRootAt oldVisit) (actionSourceVisitAt oldVisit)
      (actionSourceEntryAt oldVisit) (actionSourceAuthorityAt oldVisit) where
  targetAt := contributionMergeActionTargetAt oldVisit

def generatedContributionMergeActionAt
    (oldVisit : OldVisit) :
    SourceGeneratedSequentialActualActionAt
      (contributionMergeActionProgramAt oldVisit)
      (actionExactSourceEventAt oldVisit) :=
  (contributionMergeActionProgramAt oldVisit).generate
    (actionExactSourceEventAt oldVisit)

def contributionMergeActionCompilationAt
    (oldVisit : OldVisit)
    (exactSource : ExactTemporalCausalRootEventAt
      (actionSourceRootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
        (actionSourceVisitAt oldVisit)) :
    SourceNativeInquiryCompilationAt
      (actionSourceRootAt oldVisit) (actionSourceVisitAt oldVisit)
      (revisedU7At oldVisit) (revisedCalculusAt oldVisit)
      (revisedTheoryAt oldVisit) ()
      (M9ProofCarryingRenewalU8RevisedAuthority.inquiryEventAtFrom
        oldVisit 2)
      (actionSourceEntryAt oldVisit) (actionSourceAuthorityAt oldVisit) :=
  .actualAction
    ((contributionMergeActionProgramAt oldVisit).generate exactSource)

def contributionMergeActionCompilationProgramAt
    (oldVisit : OldVisit) :
    SourceNativeInquiryCompilationProgramAt
      (actionSourceRootAt oldVisit) (actionSourceVisitAt oldVisit)
      (revisedU7At oldVisit) (revisedCalculusAt oldVisit)
      (revisedTheoryAt oldVisit) ()
      (M9ProofCarryingRenewalU8RevisedAuthority.inquiryEventAtFrom
        oldVisit 2)
      (actionSourceEntryAt oldVisit) (actionSourceAuthorityAt oldVisit) where
  compile := contributionMergeActionCompilationAt oldVisit

@[simp] theorem generatedContributionMergeAction_targetRoot_exact
    (oldVisit : OldVisit) :
    (generatedContributionMergeActionAt oldVisit).target.targetRoot =
      contributionMergeLivingRoot (actionRootedAt oldVisit) :=
  rfl

@[simp] theorem generatedContributionMergeAction_targetVisit_exact
    (oldVisit : OldVisit) :
    (generatedContributionMergeActionAt oldVisit).target.targetVisit =
      (contributionMergeRootInitialVisit
        (actionRootedAt oldVisit)).next
          (contributionMergeRootFirstSuccessor
            (actionRootedAt oldVisit)).next_eq :=
  rfl

theorem generatedContributionMergeAction_compiler_selected_merge
    (oldVisit : OldVisit) :
    ((generatedContributionMergeActionAt oldVisit).receipt).compilerSelectedMerge =
      contributionMergeCompiler_selects_exact_first_merge
        (actionRootedAt oldVisit)
        (contributionMergeEmitted (actionRootedAt oldVisit) 0) := by
  exact Subsingleton.elim _ _

theorem generatedContributionMergeAction_macroNext_exact
    (oldVisit : OldVisit) :
    (generatedContributionMergeActionAt oldVisit).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedContributionMergeActionAt oldVisit).target.TargetV,
        (generatedContributionMergeActionAt oldVisit).target.targetRoot.toAuthoritativeRoot,
        (generatedContributionMergeActionAt oldVisit).target.targetVisit⟩ :=
  (generatedContributionMergeActionAt oldVisit).target
    |>.targetAnswerAndNext_next_eq

end
end M14SourceGeneratedSequentialContributionMerge
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionMerge.generatedContributionMergeActionAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionMerge.generatedContributionMergeAction_compiler_selected_merge
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialContributionMerge.generatedContributionMergeAction_macroNext_exact
