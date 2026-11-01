import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.SourceGeneratedTenureQueueAppendTarget

/-!
# Sequential tenure queue append

The revised depth-two occurrence executes the fixed tenure append target.
Program, generated token and literal `.actualAction` compilation are all
zero-argument source products; no target root or current enters as a premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedSequentialTenureQueueAppend

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedCriticalEventSelectionRevisedContinuation
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedTenureQueueActionAtRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueAppendTarget

def tenureQueueAppendProgram : SourceNativeSequentialActualActionProgramAt
    revisedLivingRoot (revisedSelectionTemporalVisitAt 2)
      tenureAppendSource.sourceEntry tenureAppendSource.sourceAuthority where
  targetAt := tenureQueueAppendTargetAt

def generatedTenureQueueAppendAction : SourceGeneratedSequentialActualActionAt
    tenureQueueAppendProgram revisedDepthTwoEvent :=
  tenureQueueAppendProgram.generate revisedDepthTwoEvent

def tenureQueueAppendInquiryEvent := ULift.up.{1, 0}
  (revisedLivingRoot.emitted (revisedSelectionTemporalVisitAt 2).current)

def tenureQueueAppendActualActionCompilation : SourceNativeInquiryCompilationAt
    revisedLivingRoot (revisedSelectionTemporalVisitAt 2)
      revisedInquiryU7 revisedInquiryCalculus revisedInquiryTheory ()
      tenureQueueAppendInquiryEvent tenureAppendSource.sourceEntry
      tenureAppendSource.sourceAuthority :=
  .actualAction generatedTenureQueueAppendAction

@[simp] theorem generatedTenureQueueAppendAction_targetRoot_exact :
    generatedTenureQueueAppendAction.target.targetRoot =
      tenureAppendTargetRoot :=
  rfl

@[simp] theorem generatedTenureQueueAppendAction_targetCurrent_exact :
    generatedTenureQueueAppendAction.target.firstSuccessor.targetCurrent =
      appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction :=
  tenureAppendTargetFirstSuccessor_current_exact

@[simp] theorem tenureQueueAppendActualActionCompilation_exact :
    tenureQueueAppendActualActionCompilation =
      .actualAction generatedTenureQueueAppendAction :=
  rfl

theorem generatedTenureQueueAppendAction_macroNext_exact :
    generatedTenureQueueAppendAction.target.targetAnswerAndNext.nextCurrent =
      ⟨generatedTenureQueueAppendAction.target.TargetV,
        tenureAppendTargetRoot.toAuthoritativeRoot,
        generatedTenureQueueAppendAction.target.targetVisit⟩ :=
  generatedTenureQueueAppendAction.target.targetAnswerAndNext_next_eq

theorem generatedTenureQueueAppendReceiptProvenance :
    TenureQueueAppendReceiptProvenanceAt revisedDepthTwoEvent :=
  generatedTenureQueueAppendAction.receipt.down.down

theorem sequentialTenureQueueAppend_directConsumer :
    tenureQueueAppendActualActionCompilation =
        .actualAction generatedTenureQueueAppendAction ∧
      generatedTenureQueueAppendAction.target.targetRoot =
        appendLivingRoot revisedLivingRoot revisedDepthTwoEvent.occurrence
          tenureAppendPrior tenureQueueAction ∧
      tenureAppendPrior = (revisedSelectionTemporalVisitAt 2).current ∧
      generatedTenureQueueAppendAction.target.firstSuccessor.targetCurrent =
        appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction ∧
      generatedTenureQueueAppendReceiptProvenance.queueTenure = rfl ∧
      generatedTenureQueueAppendReceiptProvenance.selectedEvent = rfl ∧
      (∀ projection :
        revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.Projection,
        HEq ((appendProjectionLaw revisedLivingRoot
          revisedDepthTwoEvent.occurrence tenureAppendPrior tenureQueueAction
            ).outcomeAt (.inherited projection)
              (appendEmitted tenureAppendPrior tenureQueueAction
                tenureAppendPrior))
          (revisedLivingRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
            projection revisedDepthTwoEvent.occurrence)) ∧
      generatedTenureQueueAppendAction.target.targetAnswerAndNext.nextCurrent =
        ⟨generatedTenureQueueAppendAction.target.TargetV,
          tenureAppendTargetRoot.toAuthoritativeRoot,
          generatedTenureQueueAppendAction.target.targetVisit⟩ :=
  ⟨rfl, rfl, rfl, generatedTenureQueueAppendAction_targetCurrent_exact,
    rfl, rfl, generatedTenureQueueAppendReceiptProvenance.inheritedOutcomes,
    generatedTenureQueueAppendAction_macroNext_exact⟩

end
end M14SourceGeneratedSequentialTenureQueueAppend
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialTenureQueueAppend.generatedTenureQueueAppendAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialTenureQueueAppend.tenureQueueAppendActualActionCompilation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedSequentialTenureQueueAppend.sequentialTenureQueueAppend_directConsumer
