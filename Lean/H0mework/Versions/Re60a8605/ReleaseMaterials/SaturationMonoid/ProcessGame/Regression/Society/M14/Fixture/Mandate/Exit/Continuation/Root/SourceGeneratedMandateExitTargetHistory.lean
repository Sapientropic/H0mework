import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.Exit.Action.SourceGeneratedSequentialMandateExit
import H0mework.Foundation.Cofinal.ProductiveHistory

/-!
# Target-root history after actual mandate exit

The first target macro step of the sequential exit action is the first
noninitial visit of the action-generated target root.  This file exposes that
finite causal history without promoting the bare target root to a canonical
runtime and without storing a completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedMandateExitTargetHistory

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedMandateExitTargetRoot
open M14SourceGeneratedSequentialMandateExit

def mandateExitTargetRootVisitAt : Nat →
    RootVisit mandateExitTargetRoot.toAuthoritativeRoot.toRoot
  | 0 => mandateExitTargetRoot.toAuthoritativeRoot.toRoot.initialVisit
  | depth + 1 => (mandateExitTargetRootVisitAt depth).next rfl

def mandateExitTargetTemporalVisitAt (depth : Nat) :
    SourceNativeTemporalVisitAt
      mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite (mandateExitTargetRootVisitAt depth)

theorem mandateExitTargetRootVisitAt_depth (depth : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth
        (mandateExitTargetRootVisitAt depth).history = depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (mandateExitTargetRootVisitAt depth).history + 1 = depth + 1
      rw [inductionHypothesis]

def mandateExitTargetTemporalDepth
    (visit : SourceNativeTemporalVisitAt
      mandateExitTargetRoot.toAuthoritativeRoot.toLedgerRoot) : Option Nat :=
  match visit.history with
  | .finite history =>
      some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

theorem mandateExitTargetTemporalVisitAt_depth (depth : Nat) :
    mandateExitTargetTemporalDepth (mandateExitTargetTemporalVisitAt depth) =
      some depth := by
  change some (ProductiveFiniteRootHistoryAt.causalDepth
    (mandateExitTargetRootVisitAt depth).history) = some depth
  rw [mandateExitTargetRootVisitAt_depth]

theorem mandateExitTargetTemporalVisitAt_injective :
    Function.Injective mandateExitTargetTemporalVisitAt := by
  intro left right equality
  have depthEquality := congrArg mandateExitTargetTemporalDepth equality
  rw [mandateExitTargetTemporalVisitAt_depth,
    mandateExitTargetTemporalVisitAt_depth] at depthEquality
  exact Option.some.inj depthEquality

theorem mandateExitTargetAdjacentVisits_distinct (depth : Nat) :
    mandateExitTargetTemporalVisitAt depth ≠
      mandateExitTargetTemporalVisitAt (depth + 1) := by
  intro equality
  have depthEquality := mandateExitTargetTemporalVisitAt_injective equality
  omega

/-- The exit action's macro next is exactly target depth one. -/
theorem generatedMandateExitAction_targetVisit_eq_depthOne
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedMandateExitActionAt initial depth).target.targetVisit =
      mandateExitTargetTemporalVisitAt 1 := by
  rfl

/-- Directly consumes the generated macro-next current rather than a caller
supplied target visit. -/
theorem generatedMandateExitAction_macroNext_is_targetDepthOne
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    (generatedMandateExitActionAt initial depth
      ).target.targetAnswerAndNext.nextCurrent =
      ⟨(generatedMandateExitActionAt initial depth).target.TargetV,
        (generatedMandateExitActionAt initial depth
          ).target.targetRoot.toAuthoritativeRoot,
        mandateExitTargetTemporalVisitAt 1⟩ := by
  rw [generatedMandateExitAction_macroNext_exact,
    generatedMandateExitAction_targetVisit_eq_depthOne]

end
end M14SourceGeneratedMandateExitTargetHistory
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitTargetHistory.mandateExitTargetTemporalVisitAt_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedMandateExitTargetHistory.generatedMandateExitAction_macroNext_is_targetDepthOne
