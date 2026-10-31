import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Health.Continuation.SourceGeneratedHealthQueueAppendContinuation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Source.Queue.SourceGeneratedEssentialAccessCriticalActionQueueSuccession

/-!
# Platform queue action at the retained health root

The exact retained health occurrence owns the middle-to-recurrent queue
succession.  It selects the recurrent/platform carrier and preserves the UBI
outcome inherited through both prior append roots.  No event, unit, current,
seed or target root is accepted by the producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPlatformQueueActionAtHealthRoot

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
open M14SourceGeneratedHealthQueueActionAtTenureRoot
open M14SourceGeneratedHealthQueueAppendTarget
open M14SourceGeneratedSequentialHealthQueueAppend
open M14SourceGeneratedHealthQueueAppendContinuation

def platformAppendExactEvent : ExactTemporalCausalRootEventAt
    healthAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
      (healthAppendTemporalVisitAt 1) :=
  healthAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt (healthAppendTemporalVisitAt 1)

def platformAppendPrior : EssentialAccessCriticalSelectionCurrent :=
  (healthAppendTemporalVisitAt 1).current

@[simp] theorem platformAppendPrior_exact :
    platformAppendPrior = retainedSelectionNext
      (appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction) := by
  change appendNativeTarget healthAppendPrior healthQueueAction
    (healthAppendRootVisitAt 0).current = _
  rw [healthAppendRootVisitAt_zero_current]
  exact appendNativeTarget_after_append healthAppendPrior healthQueueAction

def platformQueueAction := sourceGeneratedPlatformCriticalActionQueue

def platformSourceInheritedUBIPayload :=
  healthAppendTargetRoot.toAuthoritativeRoot.source.projectionLaw.project
    (.inherited (.inherited revisedInheritedUBIProjection))
    (healthAppendTargetRoot.emitted platformAppendPrior) PUnit.unit

@[simp] theorem platformSourceInheritedUBIConsumer_exact :
    HEq platformSourceInheritedUBIPayload.consumer
      sourceGeneratedUBIRootRestriction :=
  HEq.rfl

structure SourceGeneratedPlatformQueueActionAtHealthRoot : Type 12 where
  private mk ::
  exactSource : ExactTemporalCausalRootEventAt
    healthAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
      (healthAppendTemporalVisitAt 1)
  exactSourceCanonical : exactSource = platformAppendExactEvent
  prior : EssentialAccessCriticalSelectionCurrent
  priorExact : prior = retainedSelectionNext
    (appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction)
  sourceEntry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport
  sourceEntryExact : sourceEntry = healthAppendEntryAt 1
  sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    healthAppendTargetRoot (healthAppendTemporalVisitAt 1) sourceEntry
  sourceAuthorityExact : HEq sourceAuthority (healthAppendAuthorityAt 1)
  priorQueueAction :
    SourceGeneratedEssentialAccessCriticalActionQueueAt middleExactUnit
  priorQueueActionExact : priorQueueAction = healthQueueAction
  queueAction :
    SourceGeneratedEssentialAccessCriticalActionQueueAt recurrentExactUnit
  queueActionExact : queueAction = platformQueueAction
  queueSuccession : SourceGeneratedQueueCriticalActionSuccessorAt
    middleExactUnit recurrentExactUnit
  queueSuccessionExact : queueSuccession = middleToRecurrentQueueCriticalAction
  noFiniteQueueSuccessor : IsEmpty RecurrentQueueCriticalActionSuccessorAt
  inheritedUBIPayload : type_of% platformSourceInheritedUBIPayload
  inheritedUBIPayloadExact : inheritedUBIPayload =
    platformSourceInheritedUBIPayload
  inheritedUBIConsumerExact : HEq inheritedUBIPayload.consumer
    sourceGeneratedUBIRootRestriction
  actionSeedExact : queueAction.action.criticalBearer.bearerLineage.seed =
    exactEssentialAccessSeed EssentialAccessEvent.platform

def sourceGeneratedPlatformQueueActionAtHealthRoot :
    SourceGeneratedPlatformQueueActionAtHealthRoot where
  exactSource := platformAppendExactEvent
  exactSourceCanonical := rfl
  prior := platformAppendPrior
  priorExact := platformAppendPrior_exact
  sourceEntry := healthAppendEntryAt 1
  sourceEntryExact := rfl
  sourceAuthority := healthAppendAuthorityAt 1
  sourceAuthorityExact := HEq.rfl
  priorQueueAction := healthQueueAction
  priorQueueActionExact := rfl
  queueAction := platformQueueAction
  queueActionExact := rfl
  queueSuccession := middleToRecurrentQueueCriticalAction
  queueSuccessionExact := rfl
  noFiniteQueueSuccessor := recurrentQueueCriticalActionSuccessor_isEmpty
  inheritedUBIPayload := platformSourceInheritedUBIPayload
  inheritedUBIPayloadExact := rfl
  inheritedUBIConsumerExact := platformSourceInheritedUBIConsumer_exact
  actionSeedExact := queueAction_actionSeed_exact platformQueueAction

theorem platformQueueActionAtHealthRoot_directConsumer :
    let source := sourceGeneratedPlatformQueueActionAtHealthRoot
    source.exactSource = platformAppendExactEvent ∧
      source.prior = retainedSelectionNext
        (appendedCriticalSelectionCurrent healthAppendPrior healthQueueAction) ∧
      source.queueAction.event = EssentialAccessEvent.platform ∧
      SourceGeneratedQueueCriticalActionSuccessorAt
        middleExactUnit recurrentExactUnit ∧
      IsEmpty RecurrentQueueCriticalActionSuccessorAt ∧
      HEq source.inheritedUBIPayload.consumer
        sourceGeneratedUBIRootRestriction :=
  ⟨rfl, platformAppendPrior_exact, rfl,
    middleToRecurrentQueueCriticalAction,
    recurrentQueueCriticalActionSuccessor_isEmpty,
    sourceGeneratedPlatformQueueActionAtHealthRoot.inheritedUBIConsumerExact⟩

end
end M14SourceGeneratedPlatformQueueActionAtHealthRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformQueueActionAtHealthRoot.sourceGeneratedPlatformQueueActionAtHealthRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformQueueActionAtHealthRoot.platformQueueActionAtHealthRoot_directConsumer
