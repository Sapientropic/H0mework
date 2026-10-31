import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.SourceGeneratedSequentialTenureQueueAppend

/-!
# Tenure append-root continuation

The sequential tenure action's target visit is the first active tenure
selection occurrence.  Its exact new-only row authority generates every later
retained visit.  Temporal visits and entry authority remain available at every
depth, while the answered inquiry compiler is installed only at the initial
selection visit.  The retained depth-one occurrence is reserved for the next
source-generated action and has no answered sibling authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedTenureQueueAppendContinuation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedSequentialTenureQueueAppend

def tenureAppendRootVisitAt : Nat →
    RootVisit tenureAppendTargetRoot.toAuthoritativeRoot.toRoot
  | 0 => tenureAppendTargetRoot.toAuthoritativeRoot.toRoot.initialVisit.next rfl
  | depth + 1 => (tenureAppendRootVisitAt depth).next rfl

def tenureAppendTemporalVisitAt (depth : Nat) :
    SourceNativeTemporalVisitAt
      tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite (tenureAppendRootVisitAt depth)

theorem tenureAppendNextEqAt (depth : Nat) :
    (tenureAppendTargetRoot.toAuthoritativeRoot.toRoot.evolutionAt
      (tenureAppendRootVisitAt depth).current).nextCurrent? =
      some (tenureAppendRootVisitAt (depth + 1)).current :=
  rfl

theorem tenureAppendRootVisitAt_depth (depth : Nat) :
    ProductiveFiniteRootHistoryAt.causalDepth
      (tenureAppendRootVisitAt depth).history = depth + 1 := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change ProductiveFiniteRootHistoryAt.causalDepth
        (tenureAppendRootVisitAt depth).history + 1 = depth + 1 + 1
      rw [inductionHypothesis]

@[simp] theorem tenureAppendTemporalVisit_next_eq (depth : Nat) :
    (tenureAppendTemporalVisitAt depth).next (tenureAppendNextEqAt depth) =
      tenureAppendTemporalVisitAt (depth + 1) :=
  rfl

@[simp] theorem tenureAppendRootVisitAt_zero_current :
    (tenureAppendRootVisitAt 0).current =
      appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction :=
  appendNativeTarget_initial tenureAppendPrior tenureQueueAction

def tenureAppendEntryAt (_depth : Nat) :
    OpenResponsibilityAt NewN minimalCoface.cofaceSupport :=
  newRevisedEntry

def tenureAppendTemporalDepth
    (visit : SourceNativeTemporalVisitAt
      tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot) : Option Nat :=
  match visit.history with
  | .finite history =>
      some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

@[simp] theorem tenureAppendTemporalVisitAt_depth (depth : Nat) :
    tenureAppendTemporalDepth (tenureAppendTemporalVisitAt depth) =
      some (depth + 1) := by
  change some (ProductiveFiniteRootHistoryAt.causalDepth
    (tenureAppendRootVisitAt depth).history) = some (depth + 1)
  rw [tenureAppendRootVisitAt_depth]

theorem tenureAppendTemporalVisitAt_injective :
    Function.Injective tenureAppendTemporalVisitAt := by
  intro left right equality
  have depthEquality := congrArg tenureAppendTemporalDepth equality
  rw [tenureAppendTemporalVisitAt_depth,
    tenureAppendTemporalVisitAt_depth] at depthEquality
  exact Nat.add_right_cancel (Option.some.inj depthEquality)

def tenureAppendInitialAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt tenureAppendTargetRoot
      (tenureAppendTemporalVisitAt 0) (tenureAppendEntryAt 0) :=
  generatedTenureQueueAppendAction.target.targetAuthority

def tenureAppendAuthorityAt : (depth : Nat) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt tenureAppendTargetRoot
      (tenureAppendTemporalVisitAt depth) (tenureAppendEntryAt depth)
  | 0 => tenureAppendInitialAuthority
  | depth + 1 =>
      (tenureAppendAuthorityAt depth).next (tenureAppendNextEqAt depth)

def tenureAppendSelectionAnswerFaceAt (selection : Fin 1) :
    SourceNativeRootSemanticFaceAt tenureAppendTargetRoot
      (tenureAppendTemporalVisitAt selection.val) where
  projection := .answer
  active := PUnit.unit
  classifier_eq := rfl

def tenureAppendSelectionAnswerConsumerAt (selection : Fin 1) :
    SourceNativeInquiryAnswerConsumerAt ()
      (ULift.up.{1, 0}
        (tenureAppendTargetRoot.emitted
          (tenureAppendTemporalVisitAt selection.val).current))
      (tenureAppendEntryAt selection.val)
      (tenureAppendSelectionAnswerFaceAt selection) where
  projection := .consumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def tenureAppendSelectionAnsweredCompilationAt (selection : Fin 1) :
    SourceNativeInquiryCompilationAt tenureAppendTargetRoot
      (tenureAppendTemporalVisitAt selection.val) revisedInquiryU7
      revisedInquiryCalculus revisedInquiryTheory ()
      (ULift.up.{1, 0}
        (tenureAppendTargetRoot.emitted
          (tenureAppendTemporalVisitAt selection.val).current))
      (tenureAppendEntryAt selection.val)
      (tenureAppendAuthorityAt selection.val) :=
  .answered (tenureAppendSelectionAnswerFaceAt selection)
    (tenureAppendSelectionAnswerConsumerAt selection)

def tenureAppendSelectionInquiryStateAt (selection : Fin 1) : RootInquiryStateAt NewN
    (AppendVAt tenureAppendPrior tenureQueueAction) where
  root := tenureAppendTargetRoot
  visit := tenureAppendTemporalVisitAt selection.val
  U7 := revisedInquiryU7
  calculus := revisedInquiryCalculus
  Query := Unit
  entryAt := fun _ => tenureAppendEntryAt selection.val
  authorityAt := fun _ => tenureAppendAuthorityAt selection.val
  compilationProgramAt := fun _ =>
    { compile := fun _ => tenureAppendSelectionAnsweredCompilationAt selection }
  compilationFaceAt := fun _ =>
    { projection := .inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def tenureAppendSelectionEngineStateAt (selection : Fin 1) :
    RootInquiryEngineStateAt NewN
      (AppendVAt tenureAppendPrior tenureQueueAction) :=
  RootInquiryEngineStateAt.create (tenureAppendSelectionInquiryStateAt selection)

def tenureAppendSelectionPresentationAt (selection : Fin 1) :
    RootInquiryStatePresentation where
  N := NewN
  V := AppendVAt tenureAppendPrior tenureQueueAction
  state := tenureAppendSelectionEngineStateAt selection

theorem tenureAppendSelection_directConsumer (selection : Fin 1) :
    (tenureAppendSelectionInquiryStateAt selection).root =
        tenureAppendTargetRoot ∧
      (tenureAppendSelectionInquiryStateAt selection).visit =
        tenureAppendTemporalVisitAt selection.val ∧
      (tenureAppendSelectionInquiryStateAt selection).compileInquiry () =
        .answered (tenureAppendSelectionAnswerFaceAt selection)
          (tenureAppendSelectionAnswerConsumerAt selection) :=
  ⟨rfl, rfl, rfl⟩

end
end M14SourceGeneratedTenureQueueAppendContinuation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueAppendContinuation.tenureAppendAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueAppendContinuation.tenureAppendSelectionInquiryStateAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedTenureQueueAppendContinuation.tenureAppendSelection_directConsumer
