import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Continuation.SourceGeneratedTenureQueueAppendContinuation
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Source.Queue.SourceGeneratedEssentialAccessCriticalActionQueueSuccession

/-!
# Health queue action at the retained tenure root

The exact retained tenure occurrence owns the first-to-middle queue
succession.  It selects the named middle/health carrier and retains the UBI
outcome inherited through the tenure append root.  No event, unit, current,
seed or target root is accepted by the producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedHealthQueueActionAtTenureRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal
open M10OccurrenceCapacityProcessFixture
open M14EssentialAccessRelationFixture
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalActionQueue
open M14SourceGeneratedEssentialAccessCriticalActionQueueSuccession
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedTenureQueueAppendTarget
open M14SourceGeneratedTenureQueueAppendContinuation

def healthAppendExactEvent : ExactTemporalCausalRootEventAt
    tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
      (tenureAppendTemporalVisitAt 1) :=
  tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt (tenureAppendTemporalVisitAt 1)

def healthAppendPrior : EssentialAccessCriticalSelectionCurrent :=
  (tenureAppendTemporalVisitAt 1).current

@[simp] theorem healthAppendPrior_exact :
    healthAppendPrior = retainedSelectionNext
      (appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction) := by
  change appendNativeTarget tenureAppendPrior tenureQueueAction
    (tenureAppendRootVisitAt 0).current = _
  rw [tenureAppendRootVisitAt_zero_current]
  exact appendNativeTarget_after_append tenureAppendPrior tenureQueueAction

def healthQueueAction := sourceGeneratedHealthCriticalActionQueue

def healthSourceInheritedUBIPayload :=
  tenureAppendTargetRoot.toAuthoritativeRoot.source.projectionLaw.project
    (.inherited revisedInheritedUBIProjection)
    (tenureAppendTargetRoot.emitted healthAppendPrior) PUnit.unit

@[simp] theorem healthSourceInheritedUBIConsumer_exact :
    HEq healthSourceInheritedUBIPayload.consumer
      sourceGeneratedUBIRootRestriction :=
  HEq.rfl

structure SourceGeneratedHealthQueueActionAtTenureRoot : Type 12 where
  private mk ::
  exactSource : ExactTemporalCausalRootEventAt
    tenureAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
      (tenureAppendTemporalVisitAt 1)
  exactSourceCanonical : exactSource = healthAppendExactEvent
  prior : EssentialAccessCriticalSelectionCurrent
  priorExact : prior = retainedSelectionNext
    (appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction)
  sourceEntry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport
  sourceEntryExact : sourceEntry = tenureAppendEntryAt 1
  sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    tenureAppendTargetRoot (tenureAppendTemporalVisitAt 1) sourceEntry
  sourceAuthorityExact : HEq sourceAuthority (tenureAppendAuthorityAt 1)
  priorQueueAction :
    SourceGeneratedEssentialAccessCriticalActionQueueAt firstExactUnit
  priorQueueActionExact : priorQueueAction = tenureQueueAction
  queueAction :
    SourceGeneratedEssentialAccessCriticalActionQueueAt middleExactUnit
  queueActionExact : queueAction = healthQueueAction
  queueSuccession : SourceGeneratedQueueCriticalActionSuccessorAt
    firstExactUnit middleExactUnit
  queueSuccessionExact : queueSuccession = firstToMiddleQueueCriticalAction
  inheritedUBIPayload : type_of% healthSourceInheritedUBIPayload
  inheritedUBIPayloadExact : inheritedUBIPayload =
    healthSourceInheritedUBIPayload
  inheritedUBIConsumerExact : HEq inheritedUBIPayload.consumer
    sourceGeneratedUBIRootRestriction
  actionSeedExact : queueAction.action.criticalBearer.bearerLineage.seed =
    exactEssentialAccessSeed EssentialAccessEvent.health

def sourceGeneratedHealthQueueActionAtTenureRoot :
    SourceGeneratedHealthQueueActionAtTenureRoot where
  exactSource := healthAppendExactEvent
  exactSourceCanonical := rfl
  prior := healthAppendPrior
  priorExact := healthAppendPrior_exact
  sourceEntry := tenureAppendEntryAt 1
  sourceEntryExact := rfl
  sourceAuthority := tenureAppendAuthorityAt 1
  sourceAuthorityExact := HEq.rfl
  priorQueueAction := tenureQueueAction
  priorQueueActionExact := rfl
  queueAction := healthQueueAction
  queueActionExact := rfl
  queueSuccession := firstToMiddleQueueCriticalAction
  queueSuccessionExact := rfl
  inheritedUBIPayload := healthSourceInheritedUBIPayload
  inheritedUBIPayloadExact := rfl
  inheritedUBIConsumerExact := healthSourceInheritedUBIConsumer_exact
  actionSeedExact := queueAction_actionSeed_exact healthQueueAction

theorem healthQueueActionAtTenureRoot_directConsumer :
    let source := sourceGeneratedHealthQueueActionAtTenureRoot
    source.exactSource = healthAppendExactEvent ∧
      source.prior = retainedSelectionNext
        (appendedCriticalSelectionCurrent tenureAppendPrior tenureQueueAction) ∧
      source.queueAction.event = EssentialAccessEvent.health ∧
      SourceGeneratedQueueCriticalActionSuccessorAt
        firstExactUnit middleExactUnit ∧
      HEq source.inheritedUBIPayload.consumer
        sourceGeneratedUBIRootRestriction :=
  ⟨rfl, healthAppendPrior_exact, rfl, firstToMiddleQueueCriticalAction,
    sourceGeneratedHealthQueueActionAtTenureRoot.inheritedUBIConsumerExact⟩

end
end M14SourceGeneratedHealthQueueActionAtTenureRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthQueueActionAtTenureRoot.sourceGeneratedHealthQueueActionAtTenureRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedHealthQueueActionAtTenureRoot.healthQueueActionAtTenureRoot_directConsumer
