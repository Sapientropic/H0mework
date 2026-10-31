import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Action.SourceGeneratedSequentialHealthCessation
import H0mework.Foundation.Cofinal.ProductiveHistory

/-!
# Target-root history after actual health cessation

The health action's macro next is the first noninitial visit of the exact
action-generated target root.  The same root compiler generates every later
finite visit.  This exposes no sibling runtime and stores no completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedHealthCessationTargetHistory

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedHealthCessationTargetRoot
open M14SourceGeneratedSequentialHealthCessation

def healthCessationTargetRootVisitAt : Nat →
    RootVisit healthCessationTargetRoot.toAuthoritativeRoot.toRoot
  | 0 => healthCessationTargetRoot.toAuthoritativeRoot.toRoot.initialVisit
  | depth + 1 => (healthCessationTargetRootVisitAt depth).next rfl

def healthCessationTargetTemporalVisitAt (depth : Nat) :
    SourceNativeTemporalVisitAt
      healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite (healthCessationTargetRootVisitAt depth)

def healthCessationTargetExactEventAt (depth : Nat) :
    ExactTemporalCausalRootEventAt
      healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (healthCessationTargetTemporalVisitAt depth) :=
  healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt
      (healthCessationTargetTemporalVisitAt depth)

def healthCessationTargetGeneratedAt (depth : Nat) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot
        (healthCessationTargetTemporalVisitAt depth) :=
  healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit
      (healthCessationTargetTemporalVisitAt depth)

def healthCessationTargetWholeSuccessorAt (depth : Nat) :
    SourceNativeLedgerGeneratedSuccessorAt
      (healthCessationTargetGeneratedAt depth).occurrence
      (healthCessationTargetGeneratedAt depth).wholeLedgerWriteBack :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (healthCessationTargetGeneratedAt depth).wholeLedgerWriteBack).get (by rfl)

theorem healthCessationTargetNextEqAt (depth : Nat) :
    (healthCessationTargetRoot.toAuthoritativeRoot.toRoot.evolutionAt
      (healthCessationTargetRootVisitAt depth).current).nextCurrent? =
      some (healthCessationTargetRootVisitAt (depth + 1)).current :=
  rfl

theorem healthCessationTargetTemporalVisit_next_eq (depth : Nat) :
    (healthCessationTargetTemporalVisitAt depth).next
        (healthCessationTargetNextEqAt depth) =
      healthCessationTargetTemporalVisitAt (depth + 1) :=
  rfl

def healthCessationTargetVisitEntryAt : (depth : Nat) →
    OpenResponsibilityAt M14SourceGeneratedHealthCessationTargetRoot.N
      (healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (healthCessationTargetRoot.emitted
          (healthCessationTargetRootVisitAt depth).current))
  | 0 => RootInquiryU8CompletionRegression.entry
  | depth + 1 =>
      healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot
        |>.canonicalTargetEntryAtNext
          (healthCessationTargetNextEqAt depth)
          (healthCessationTargetVisitEntryAt depth)

@[simp] theorem healthCessationTargetVisitEntryAt_eq_entry
    (depth : Nat) :
    healthCessationTargetVisitEntryAt depth =
      RootInquiryU8CompletionRegression.entry := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change
        healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
            (healthCessationTargetNextEqAt depth)
            (healthCessationTargetVisitEntryAt depth) =
          RootInquiryU8CompletionRegression.entry
      rw [inductionHypothesis]
      rfl

def healthCessationTargetInitialAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      healthCessationTargetRoot (healthCessationTargetTemporalVisitAt 0)
        (healthCessationTargetVisitEntryAt 0) :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
    healthCessationTargetRoot (healthCessationTargetVisitEntryAt 0)
      .initial).get (by rfl)).2

def healthCessationTargetAuthorityAt : (depth : Nat) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      healthCessationTargetRoot (healthCessationTargetTemporalVisitAt depth)
        (healthCessationTargetVisitEntryAt depth)
  | 0 => healthCessationTargetInitialAuthority
  | depth + 1 =>
      (healthCessationTargetAuthorityAt depth).next
        (healthCessationTargetNextEqAt depth)

theorem healthCessationTargetRootVisitAt_depth (depth : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth
        (healthCessationTargetRootVisitAt depth).history = depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (healthCessationTargetRootVisitAt depth).history + 1 = depth + 1
      rw [inductionHypothesis]

def healthCessationTargetTemporalDepth
    (visit : SourceNativeTemporalVisitAt
      healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot) :
    Option Nat :=
  match visit.history with
  | .finite history =>
      some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

theorem healthCessationTargetTemporalVisitAt_depth (depth : Nat) :
    healthCessationTargetTemporalDepth
        (healthCessationTargetTemporalVisitAt depth) = some depth := by
  change some (ProductiveFiniteRootHistoryAt.causalDepth
    (healthCessationTargetRootVisitAt depth).history) = some depth
  rw [healthCessationTargetRootVisitAt_depth]

theorem healthCessationTargetTemporalVisitAt_injective :
    Function.Injective healthCessationTargetTemporalVisitAt := by
  intro left right equality
  have depthEquality := congrArg healthCessationTargetTemporalDepth equality
  rw [healthCessationTargetTemporalVisitAt_depth,
    healthCessationTargetTemporalVisitAt_depth] at depthEquality
  exact Option.some.inj depthEquality

theorem healthCessationTargetAdjacentVisits_distinct (depth : Nat) :
    healthCessationTargetTemporalVisitAt depth ≠
      healthCessationTargetTemporalVisitAt (depth + 1) := by
  intro equality
  have depthEquality :=
    healthCessationTargetTemporalVisitAt_injective equality
  omega

/-- The health action's generated target visit is exactly target depth one. -/
theorem generatedHealthCessationAction_targetVisit_eq_depthOne
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedHealthCessationActionAt initial depth).target.targetVisit =
      healthCessationTargetTemporalVisitAt 1 := by
  rfl

/-- Directly consumes the generated macro next; no caller supplies the target
visit which begins the continuation. -/
theorem generatedHealthCessationAction_macroNext_is_targetDepthOne
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedHealthCessationActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedHealthCessationActionAt initial depth).target.TargetV,
        (generatedHealthCessationActionAt initial depth
          ).target.targetRoot.toAuthoritativeRoot,
        healthCessationTargetTemporalVisitAt 1⟩ := by
  rw [generatedHealthCessationAction_macroNext_exact,
    generatedHealthCessationAction_targetVisit_eq_depthOne]

end
end M14SourceGeneratedHealthCessationTargetHistory
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationTargetHistory.healthCessationTargetTemporalVisitAt_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthCessationTargetHistory.generatedHealthCessationAction_macroNext_is_targetDepthOne
