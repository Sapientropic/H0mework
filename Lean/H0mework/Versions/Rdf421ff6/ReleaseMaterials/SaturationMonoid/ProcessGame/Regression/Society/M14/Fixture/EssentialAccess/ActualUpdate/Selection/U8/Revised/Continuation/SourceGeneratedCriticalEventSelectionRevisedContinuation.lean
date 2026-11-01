import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.SourceGeneratedCriticalEventSelectionRevisedRoot
import H0mework.Foundation.Cofinal.ProductiveHistory

/-!
# Revised selection-root continuation

The revised root's literal whole compiler generates every finite retained
visit.  The new-only obstruction row supplies the initial living authority
and its canonical target entry/authority at each successor.  This is the
source spine for later sequential actual actions; it stores no action,
event, target root or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCriticalEventSelectionRevisedContinuation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.TypedSemanticWorldNetworkU8Lifecycle
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot

def revisedSelectionRootVisitAt : Nat →
    RootVisit revisedAuthoritativeRoot.toRoot
  | 0 => revisedAuthoritativeRoot.toRoot.initialVisit
  | depth + 1 => (revisedSelectionRootVisitAt depth).next rfl

def revisedSelectionTemporalVisitAt (depth : Nat) :
    SourceNativeTemporalVisitAt revisedAuthoritativeRoot.toLedgerRoot :=
  .finite (revisedSelectionRootVisitAt depth)

def revisedSelectionExactEventAt (depth : Nat) :
    ExactTemporalCausalRootEventAt revisedAuthoritativeRoot.toLedgerRoot
      (revisedSelectionTemporalVisitAt depth) :=
  revisedAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    (revisedSelectionTemporalVisitAt depth)

theorem revisedSelectionNextEqAt (depth : Nat) :
    (revisedAuthoritativeRoot.toRoot.evolutionAt
      (revisedSelectionRootVisitAt depth).current).nextCurrent? =
      some (revisedSelectionRootVisitAt (depth + 1)).current :=
  rfl

@[simp] theorem revisedSelectionTemporalVisit_next_eq (depth : Nat) :
    (revisedSelectionTemporalVisitAt depth).next
        (revisedSelectionNextEqAt depth) =
      revisedSelectionTemporalVisitAt (depth + 1) :=
  rfl

def revisedSelectionEntryAt (_depth : Nat) :
    OpenResponsibilityAt NewN minimalCoface.cofaceSupport :=
  newRevisedEntry

def revisedSelectionInitialAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt revisedLivingRoot
      (revisedSelectionTemporalVisitAt 0) (revisedSelectionEntryAt 0) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    revisedLivingRoot newRevisedEntry revisedNewEntryRow

def revisedSelectionAuthorityAt : (depth : Nat) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt revisedLivingRoot
      (revisedSelectionTemporalVisitAt depth) (revisedSelectionEntryAt depth)
  | 0 => revisedSelectionInitialAuthority
  | depth + 1 =>
      (revisedSelectionAuthorityAt depth).next
        (revisedSelectionNextEqAt depth)

@[simp] theorem revisedSelectionRootVisitAt_one_current :
    (revisedSelectionRootVisitAt 1).current =
      retainedSelectionNext initialSelectionCurrent :=
  rfl

theorem revisedSelectionRootVisitAt_depth (depth : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth
      (revisedSelectionRootVisitAt depth).history = depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (revisedSelectionRootVisitAt depth).history + 1 = depth + 1
      rw [inductionHypothesis]

def revisedSelectionTemporalDepth
    (visit : SourceNativeTemporalVisitAt revisedAuthoritativeRoot.toLedgerRoot) :
    Option Nat :=
  match visit.history with
  | .finite history =>
      some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

@[simp] theorem revisedSelectionTemporalVisitAt_depth (depth : Nat) :
    revisedSelectionTemporalDepth (revisedSelectionTemporalVisitAt depth) =
      some depth := by
  change some (ProductiveFiniteRootHistoryAt.causalDepth
    (revisedSelectionRootVisitAt depth).history) = some depth
  rw [revisedSelectionRootVisitAt_depth]

theorem revisedSelectionTemporalVisitAt_injective :
    Function.Injective revisedSelectionTemporalVisitAt := by
  intro left right equality
  have depthEquality := congrArg revisedSelectionTemporalDepth equality
  rw [revisedSelectionTemporalVisitAt_depth,
    revisedSelectionTemporalVisitAt_depth] at depthEquality
  exact Option.some.inj depthEquality

end
end M14SourceGeneratedCriticalEventSelectionRevisedContinuation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedContinuation.revisedSelectionAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCriticalEventSelectionRevisedContinuation.revisedSelectionTemporalVisitAt_injective
