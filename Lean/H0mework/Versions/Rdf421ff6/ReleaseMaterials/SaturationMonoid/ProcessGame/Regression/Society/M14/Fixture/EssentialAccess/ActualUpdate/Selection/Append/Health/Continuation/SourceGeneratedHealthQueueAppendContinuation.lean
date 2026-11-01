import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Health.Action.SourceGeneratedSequentialHealthQueueAppend
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Continuation.Generic.SourceGeneratedQueueAppendContinuation

/-!
# Health queue-append continuation

Thin canonical specialization of the generic append temporal spine.  Its first
visit is the health-selected appended current; later visits retain that exact
lineage.  Only the initial selection visit has an answered inquiry compiler;
the retained visit is reserved for the next source-generated action.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedHealthQueueAppendContinuation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedHealthQueueActionAtTenureRoot
open M14SourceGeneratedHealthQueueAppendTarget
open M14SourceGeneratedSequentialHealthQueueAppend
open M14SourceGeneratedQueueAppendContinuation

def healthAppendRootVisitAt (depth : Nat) :=
  queueAppendRootVisitAt tenureAppendTargetRoot healthAppendExactEvent.occurrence
    healthAppendPrior healthQueueAction depth

def healthAppendTemporalVisitAt (depth : Nat) :=
  queueAppendTemporalVisitAt tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction depth

set_option linter.defProp false in
def healthAppendNextEqAt (depth : Nat) :=
  queueAppendNextEqAt tenureAppendTargetRoot healthAppendExactEvent.occurrence
    healthAppendPrior healthQueueAction depth

def healthAppendEntryAt (depth : Nat) := queueAppendEntryAt depth

def healthAppendAuthorityAt (depth : Nat) :=
  queueAppendAuthorityAt tenureAppendTargetRoot healthAppendExactEvent.occurrence
    healthAppendPrior healthQueueAction depth

def healthAppendAnswerFaceAt (selection : Fin 1) :=
  queueAppendAnswerFaceAt tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction selection

def healthAppendAnswerConsumerAt (selection : Fin 1) :=
  queueAppendAnswerConsumerAt tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction selection

def healthAppendAnsweredCompilationAt (selection : Fin 1) :=
  queueAppendAnsweredCompilationAt tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction selection

def healthAppendInquiryStateAt (selection : Fin 1) :=
  queueAppendInquiryStateAt tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction selection

def healthAppendPresentationAt (selection : Fin 1) :=
  queueAppendPresentationAt tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction selection

@[simp] theorem healthAppendPresentationAt_current (selection : Fin 1) :
    (healthAppendPresentationAt selection).state.base.visit.current =
      (healthAppendRootVisitAt selection.val).current :=
  rfl

@[simp] theorem healthAppendRootVisitAt_zero_current :
    (healthAppendRootVisitAt 0).current =
      appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction :=
  queueAppendRootVisitAt_zero_current tenureAppendTargetRoot
    healthAppendExactEvent.occurrence healthAppendPrior healthQueueAction

theorem healthAppendInitialAuthority_action_exact :
    HEq (healthAppendAuthorityAt 0)
      generatedHealthQueueAppendAction.target.targetAuthority :=
  HEq.rfl

theorem healthAppendContinuation_directConsumer (selection : Fin 1) :
    (healthAppendInquiryStateAt selection).compileInquiry () =
      .answered (healthAppendAnswerFaceAt selection)
        (healthAppendAnswerConsumerAt selection) :=
  rfl

end
end M14SourceGeneratedHealthQueueAppendContinuation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthQueueAppendContinuation.healthAppendAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthQueueAppendContinuation.healthAppendInquiryStateAt
