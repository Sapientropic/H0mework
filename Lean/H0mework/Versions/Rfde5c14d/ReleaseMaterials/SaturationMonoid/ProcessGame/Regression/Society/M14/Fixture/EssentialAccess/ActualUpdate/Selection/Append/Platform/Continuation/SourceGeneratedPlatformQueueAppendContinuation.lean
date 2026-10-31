import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Platform.Action.SourceGeneratedSequentialPlatformQueueAppend
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Continuation.Generic.SourceGeneratedQueueAppendContinuation

/-!
# Platform queue-append temporal spine and selection answer

The generic temporal spine remains available at every generated visit.  Only
the initial platform-selection visit carries an answered compiler; later
visits require a separately source-sealed continuation law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPlatformQueueAppendContinuation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedHealthQueueAppendTarget
open M14SourceGeneratedPlatformQueueActionAtHealthRoot
open M14SourceGeneratedPlatformQueueAppendTarget
open M14SourceGeneratedSequentialPlatformQueueAppend
open M14SourceGeneratedQueueAppendContinuation

def platformAppendRootVisitAt (depth : Nat) :=
  queueAppendRootVisitAt healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior
      platformQueueAction depth

def platformAppendTemporalVisitAt (depth : Nat) :=
  queueAppendTemporalVisitAt healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior
      platformQueueAction depth

set_option linter.defProp false in
def platformAppendNextEqAt (depth : Nat) :=
  queueAppendNextEqAt healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior
      platformQueueAction depth

def platformAppendEntryAt (depth : Nat) := queueAppendEntryAt depth

def platformAppendAuthorityAt (depth : Nat) :=
  queueAppendAuthorityAt healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior
      platformQueueAction depth

def platformAppendAnswerFaceAt (selection : Fin 1) :=
  queueAppendAnswerFaceAt healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior
      platformQueueAction selection

def platformAppendAnswerConsumerAt (selection : Fin 1) :=
  queueAppendAnswerConsumerAt healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior
      platformQueueAction selection

def platformAppendAnsweredCompilationAt (selection : Fin 1) :=
  queueAppendAnsweredCompilationAt healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior
      platformQueueAction selection

def platformAppendInquiryStateAt (selection : Fin 1) :=
  queueAppendInquiryStateAt healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior
      platformQueueAction selection

def platformAppendPresentationAt (selection : Fin 1) :=
  queueAppendPresentationAt healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior
      platformQueueAction selection

@[simp] theorem platformAppendPresentationAt_current (selection : Fin 1) :
    (platformAppendPresentationAt selection).state.base.visit.current =
      (platformAppendRootVisitAt selection.val).current :=
  rfl

@[simp] theorem platformAppendRootVisitAt_zero_current :
    (platformAppendRootVisitAt 0).current =
      appendedCriticalSelectionCurrent platformAppendPrior
        platformQueueAction :=
  queueAppendRootVisitAt_zero_current healthAppendTargetRoot
    platformAppendExactEvent.occurrence platformAppendPrior platformQueueAction

theorem platformAppendInitialAuthority_action_exact :
    HEq (platformAppendAuthorityAt 0)
      generatedPlatformQueueAppendAction.target.targetAuthority :=
  HEq.rfl

theorem platformAppendSelection_directConsumer (selection : Fin 1) :
    (platformAppendInquiryStateAt selection).compileInquiry () =
      .answered (platformAppendAnswerFaceAt selection)
        (platformAppendAnswerConsumerAt selection) :=
  rfl

end
end M14SourceGeneratedPlatformQueueAppendContinuation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformQueueAppendContinuation.platformAppendAuthorityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformQueueAppendContinuation.platformAppendInquiryStateAt
