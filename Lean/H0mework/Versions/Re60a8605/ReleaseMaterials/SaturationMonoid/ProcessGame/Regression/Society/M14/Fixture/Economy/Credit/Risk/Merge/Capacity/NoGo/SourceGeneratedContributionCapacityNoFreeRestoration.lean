import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.LivingLaw.SequentialAction.ZeroBudgetClosureKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Action.SourceGeneratedContributionCapacityU8TargetState

/-!
# No free restoration after contribution-capacity self-U8

All three rows of the generated capacity-U8 ledger have budget zero.  The
generic zero-budget closure theorem therefore blocks every endogenous
conservative sequential target from manufacturing a positive-budget row.
The revised law answers the residual, but an answer is not a material refill.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityNoFreeRestoration

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open RootInquiryCompletion.NoFreeCapacityRestoration
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityU8Compiler
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Root
open M14SourceGeneratedContributionCapacityU8TargetState

theorem contributionCapacityU8Entry_budget_zero
    (oldVisit : OldVisit)
    (entry : (contributionCapacityU8Ledger oldVisit).Entry) :
    entry.progressBudget = 0 := by
  rcases contributionCapacityU8Entry_cases oldVisit entry with
    inheritedContribution | inheritedObstruction | generatedResidual
  · subst entry
    rfl
  · subst entry
    rfl
  · subst entry
    rfl

theorem contributionCapacityU8PositiveProgress_isEmpty
    (oldVisit : OldVisit) :
    IsEmpty
      (PositiveProgressEntryAt (contributionCapacityU8Ledger oldVisit)) :=
  positiveProgressEntry_isEmpty_of_all_zero _
    (contributionCapacityU8Entry_budget_zero oldVisit)

theorem contributionCapacityU8RootEntry_budget_zero
    (oldVisit : OldVisit) (index : Nat)
    (entry : OpenResponsibilityAt (CapacityU8NAt oldVisit)
      ((CapacityU8RootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        ((CapacityU8RootAt oldVisit).emitted
          (contributionCapacityU8RuntimeVisitAt oldVisit index).current))) :
    entry.progressBudget = 0 :=
  contributionCapacityU8Entry_budget_zero oldVisit entry

/-- Any sequential action generated solely from the exhausted revised root
still has an exhausted first target ledger. -/
theorem endogenousSequentialTarget_positiveProgress_isEmpty
    (oldVisit : OldVisit) (index : Nat)
    {sourceEntry : OpenResponsibilityAt (CapacityU8NAt oldVisit)
      ((CapacityU8RootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        ((CapacityU8RootAt oldVisit).emitted
          (contributionCapacityU8RuntimeVisitAt oldVisit index).current))}
    (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8RuntimeVisitAt oldVisit index) sourceEntry)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (CapacityU8RootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityU8RuntimeVisitAt oldVisit index))
    (target : SourceNativeSequentialActualActionTargetAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8RuntimeVisitAt oldVisit index)
      sourceEvent sourceEntry sourceAuthority) :
    IsEmpty
      (PositiveProgressEntryAt
        (⟨target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          target.firstSuccessor.targetOccurrence⟩ :
          CompleteLiveLedgerAt target.TargetN)) :=
  _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.NoFreeCapacityRestoration.SourceNativeSequentialActualActionTargetAt.firstSuccessorPositiveProgress_isEmpty
    target
      (contributionCapacityU8RootEntry_budget_zero oldVisit index)

/-- No action whose complete source is only the exhausted revised root can
produce a positive-budget first successor. -/
def NoEndogenousPositiveRestorationAt (oldVisit : OldVisit) : Prop :=
  ∀ (index : Nat)
    (sourceEntry : OpenResponsibilityAt (CapacityU8NAt oldVisit)
      ((CapacityU8RootAt oldVisit).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        ((CapacityU8RootAt oldVisit).emitted
          (contributionCapacityU8RuntimeVisitAt oldVisit index).current)))
    (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8RuntimeVisitAt oldVisit index) sourceEntry)
    (sourceEvent : ExactTemporalCausalRootEventAt
      (CapacityU8RootAt oldVisit).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityU8RuntimeVisitAt oldVisit index))
    (target : SourceNativeSequentialActualActionTargetAt
      (CapacityU8RootAt oldVisit)
      (contributionCapacityU8RuntimeVisitAt oldVisit index)
      sourceEvent sourceEntry sourceAuthority),
    IsEmpty
      (PositiveProgressEntryAt
        (⟨target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          target.firstSuccessor.targetOccurrence⟩ :
          CompleteLiveLedgerAt target.TargetN))

theorem contributionCapacityU8_noEndogenousPositiveRestoration
    (oldVisit : OldVisit) : NoEndogenousPositiveRestorationAt oldVisit := by
  intro index sourceEntry sourceAuthority sourceEvent target
  exact endogenousSequentialTarget_positiveProgress_isEmpty oldVisit index
    sourceAuthority sourceEvent target

/-- The installed residual answer coexists with the zero-budget no-go. -/
theorem revisedAnswer_does_not_refill_capacity
    (oldVisit : OldVisit) (index : Nat) :
    Nonempty
        (SourceNativeInquiryAnswerConsumerAt ()
          (contributionCapacityU8InquiryEventAt oldVisit index)
          (contributionCapacityU8GeneratedResidual oldVisit)
          (contributionCapacityU8AnswerFaceAt oldVisit index)) ∧
      IsEmpty
        (PositiveProgressEntryAt (contributionCapacityU8Ledger oldVisit)) :=
  ⟨⟨contributionCapacityU8AnswerConsumerAt oldVisit index⟩,
    contributionCapacityU8PositiveProgress_isEmpty oldVisit⟩

end
end M14SourceGeneratedContributionCapacityNoFreeRestoration
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityNoFreeRestoration.contributionCapacityU8Entry_budget_zero
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityNoFreeRestoration.contributionCapacityU8PositiveProgress_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityNoFreeRestoration.endogenousSequentialTarget_positiveProgress_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityNoFreeRestoration.contributionCapacityU8_noEndogenousPositiveRestoration
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityNoFreeRestoration.revisedAnswer_does_not_refill_capacity
