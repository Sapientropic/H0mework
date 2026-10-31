import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Platform.Continuation.SourceGeneratedPlatformQueueAppendContinuation
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Action.Generic.SourceGeneratedEssentialAccessCriticalActionCarrier
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Relations.Transport.SourceGeneratedRelationSeedSelfTransport

/-!
# Relation action generated at the retained platform occurrence

The retained platform current is folded at its lineage root.  That exact seed
is persisted by principal self-transport, and its existing relation compiler
generates the action, bearer, phase and target role.  The producer accepts no
event, seed, current, action, relation or target root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPlatformRetainedRelationAction

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Renewal
open M14EssentialAccessRelationFixture
open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedSelectedEssentialAccessCriticalEvent
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedHealthQueueAppendTarget
open M14SourceGeneratedPlatformQueueActionAtHealthRoot
open M14SourceGeneratedPlatformQueueAppendTarget
open M14SourceGeneratedSequentialPlatformQueueAppend
open M14SourceGeneratedPlatformQueueAppendContinuation
open M14SourceGeneratedEssentialAccessCriticalActionCarrier
open SourceGeneratedRelationSeedSelfTransport
open AffineRelaxation

def platformRetainedRelationExactEvent : ExactTemporalCausalRootEventAt
    platformAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
      (platformAppendTemporalVisitAt 1) :=
  platformAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
    |>.exactTemporalCausalEventAt (platformAppendTemporalVisitAt 1)

def platformRetainedRelationPrior :
    EssentialAccessCriticalSelectionCurrent :=
  (platformAppendTemporalVisitAt 1).current

@[simp] theorem platformRetainedRelationPrior_exact :
    platformRetainedRelationPrior = retainedSelectionNext
      (appendedCriticalSelectionCurrent platformAppendPrior
        platformQueueAction) := by
  change appendNativeTarget platformAppendPrior platformQueueAction
    (platformAppendRootVisitAt 0).current = _
  rw [platformAppendRootVisitAt_zero_current]
  exact appendNativeTarget_after_append platformAppendPrior platformQueueAction

def platformRetainedSelected :=
  sourceGeneratedSelectedEssentialAccessCriticalEventAt
    platformRetainedRelationPrior

def platformRetainedActionCarrier :=
  criticalActionCarrierOfSelected platformRetainedSelected

def platformRetainedRelationPhase :=
  essentialAccessRelationCompiler.phaseStep
    (essentialAccessRelationCompiler.relationOf
      platformRetainedSelected.selectedSeed)

def platformRetainedTransportedSeed :=
  transportedRelationSeed platformRetainedRelationPhase
    platformRetainedSelected.selectedSeed

@[simp] theorem platformRetainedTransportedSeed_exact :
    platformRetainedTransportedSeed =
      platformRetainedSelected.selectedSeed :=
  transportedRelationSeed_exact _ _

theorem platformRetainedCarrier_event_exact :
    platformRetainedActionCarrier.event = EssentialAccessEvent.platform := by
  have priorRoot : platformRetainedRelationPrior.root =
      exactEssentialAccessSeed .platform := by
    rw [platformRetainedRelationPrior_exact]
    rfl
  change (criticalActionCarrierOfSelected platformRetainedSelected).event =
    EssentialAccessEvent.platform
  rw [(criticalActionCarrierOfSelected_foldProvenance
    platformRetainedSelected).1,
    selectedCriticalSeed_eq_root platformRetainedRelationPrior, priorRoot]
  rfl

theorem platformRetainedCarrier_actionSeed_transport_exact :
    platformRetainedActionCarrier.action.criticalBearer.bearerLineage.seed =
      platformRetainedTransportedSeed := by
  rw [platformRetainedTransportedSeed_exact]
  exact (criticalActionCarrierOfSelected_foldProvenance
    platformRetainedSelected).2.1

def platformRetainedInheritedUBIPayload :=
  platformAppendTargetRoot.toAuthoritativeRoot.source.projectionLaw.project
    (.inherited (.inherited (.inherited revisedInheritedUBIProjection)))
    (platformAppendTargetRoot.emitted platformRetainedRelationPrior) PUnit.unit

@[simp] theorem platformRetainedInheritedUBIConsumer_exact :
    HEq platformRetainedInheritedUBIPayload.consumer
      sourceGeneratedUBIRootRestriction :=
  HEq.rfl

structure SourceGeneratedPlatformRetainedRelationAction : Type 12 where
  private mk ::
  exactSource : ExactTemporalCausalRootEventAt
    platformAppendTargetRoot.toAuthoritativeRoot.toLedgerRoot
      (platformAppendTemporalVisitAt 1)
  exactSourceCanonical : exactSource = platformRetainedRelationExactEvent
  prior : EssentialAccessCriticalSelectionCurrent
  priorExact : prior = retainedSelectionNext
    (appendedCriticalSelectionCurrent platformAppendPrior platformQueueAction)
  sourceEntry : OpenResponsibilityAt NewN minimalCoface.cofaceSupport
  sourceEntryExact : sourceEntry = platformAppendEntryAt 1
  sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    platformAppendTargetRoot (platformAppendTemporalVisitAt 1) sourceEntry
  sourceAuthorityExact : HEq sourceAuthority (platformAppendAuthorityAt 1)
  selected : SourceGeneratedSelectedEssentialAccessCriticalEventAt prior
  selectedExact : HEq selected platformRetainedSelected
  carrier : SourceGeneratedEssentialAccessCriticalActionCarrier
  carrierExact : carrier = platformRetainedActionCarrier
  carrierEventExact : carrier.event = EssentialAccessEvent.platform
  transportedSeed : essentialAccessRelationCompiler.ExactRelationSeed
  transportedSeedExact : transportedSeed = selected.selectedSeed
  actionSeedTransported :
    carrier.action.criticalBearer.bearerLineage.seed = transportedSeed
  phaseNonzero : essentialAccessRelationCompiler.phaseStep
    (essentialAccessCriticalRelation carrier.event) ≠ 0
  targetRoleGenerated : essentialAccessRelationCompiler.roleAt
      (essentialAccessCriticalRelation carrier.event) .target =
    essentialAccessRelationCompiler.advanceRole
      Lifecycle.actualEventGame.source
      (essentialAccessRelationCompiler.phaseStep
        (essentialAccessCriticalRelation carrier.event))
      (essentialAccessRelationCompiler.roleAt
        (essentialAccessCriticalRelation carrier.event) .source)
  transportFlat : FlatPrincipalConnection
    (canonicalRelationSeedTransition EssentialAccessSector
      essentialAccessRelationCompiler.ExactRelationSeed)
  transportHolonomyOne : ∀ left middle right,
    principalTriangleHolonomy
      (canonicalRelationSeedTransition EssentialAccessSector
        essentialAccessRelationCompiler.ExactRelationSeed)
      left middle right = 1
  inheritedUBIPayload : type_of% platformRetainedInheritedUBIPayload
  inheritedUBIPayloadExact : inheritedUBIPayload =
    platformRetainedInheritedUBIPayload
  inheritedUBIConsumerExact : HEq inheritedUBIPayload.consumer
    sourceGeneratedUBIRootRestriction

def sourceGeneratedPlatformRetainedRelationAction :
    SourceGeneratedPlatformRetainedRelationAction where
  exactSource := platformRetainedRelationExactEvent
  exactSourceCanonical := rfl
  prior := platformRetainedRelationPrior
  priorExact := platformRetainedRelationPrior_exact
  sourceEntry := platformAppendEntryAt 1
  sourceEntryExact := rfl
  sourceAuthority := platformAppendAuthorityAt 1
  sourceAuthorityExact := HEq.rfl
  selected := platformRetainedSelected
  selectedExact := HEq.rfl
  carrier := platformRetainedActionCarrier
  carrierExact := rfl
  carrierEventExact := platformRetainedCarrier_event_exact
  transportedSeed := platformRetainedTransportedSeed
  transportedSeedExact := platformRetainedTransportedSeed_exact
  actionSeedTransported := platformRetainedCarrier_actionSeed_transport_exact
  phaseNonzero := (criticalActionCarrier_directConsumer
    platformRetainedActionCarrier).2.2.1
  targetRoleGenerated := (criticalActionCarrier_directConsumer
    platformRetainedActionCarrier).2.2.2
  transportFlat := canonicalRelationSeedTransition_flat _ _
  transportHolonomyOne := canonicalRelationSeedTransition_holonomy_one _ _
  inheritedUBIPayload := platformRetainedInheritedUBIPayload
  inheritedUBIPayloadExact := rfl
  inheritedUBIConsumerExact := platformRetainedInheritedUBIConsumer_exact

theorem platformRetainedRelationAction_directConsumer :
    let source := sourceGeneratedPlatformRetainedRelationAction
    source.exactSource = platformRetainedRelationExactEvent ∧
      source.prior = retainedSelectionNext
        (appendedCriticalSelectionCurrent platformAppendPrior
          platformQueueAction) ∧
      source.carrier.event = EssentialAccessEvent.platform ∧
      source.carrier.action.criticalBearer.bearerLineage.seed =
        source.transportedSeed ∧
      source.transportedSeed = source.selected.selectedSeed ∧
      HEq source.inheritedUBIPayload.consumer
        sourceGeneratedUBIRootRestriction :=
  ⟨rfl, platformRetainedRelationPrior_exact,
    platformRetainedCarrier_event_exact,
    platformRetainedCarrier_actionSeed_transport_exact,
    platformRetainedTransportedSeed_exact,
    sourceGeneratedPlatformRetainedRelationAction.inheritedUBIConsumerExact⟩

end
end M14SourceGeneratedPlatformRetainedRelationAction
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformRetainedRelationAction.sourceGeneratedPlatformRetainedRelationAction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformRetainedRelationAction.platformRetainedRelationAction_directConsumer
