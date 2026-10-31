import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Relation.Recurrence.SourceGeneratedLineageFoldRelationRecurrenceStage

/-!
# UBI restriction along relation-lineage recurrence

Every generated relation append inherits the existing UBI restriction through
the predecessor projection.  The recursive projection below follows the
actual `stage.next` write; it is not a second payment, renewal, ledger or stored
future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedLineageFoldRelationRecurrenceUBI

noncomputable section

open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedCriticalEventSelectionRevisedRoot
open M14SourceGeneratedEssentialAccessCriticalActionAppendLedger
open M14SourceGeneratedEssentialAccessCriticalActionAppendRoot
open M14SourceGeneratedLineageFoldRelationRecurrenceStage
open M14SourceGeneratedPlatformRetainedRelationAction

def recurrenceUBIProjectionAt :
    (depth : Nat) →
      (stageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.Projection
  | 0 => .inherited (.inherited (.inherited revisedInheritedUBIProjection))
  | depth + 1 => .inherited (recurrenceUBIProjectionAt depth)

def recurrenceUBIActiveAt :
    (depth : Nat) →
      (stageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.ActiveAt
        (recurrenceUBIProjectionAt depth)
        ((stageAt depth).sourceRoot.emitted
          (stageAt depth).actionCurrent)
  | 0 => PUnit.unit
  | depth + 1 => recurrenceUBIActiveAt depth

def recurrenceUBIPayloadAt :
    Nat → type_of% platformRetainedInheritedUBIPayload
  | 0 => platformRetainedInheritedUBIPayload
  | depth + 1 => recurrenceUBIPayloadAt depth

theorem recurrenceUBIProjectionProject_exact :
    ∀ depth : Nat,
      HEq
        ((stageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.project
          (recurrenceUBIProjectionAt depth)
          ((stageAt depth).sourceRoot.emitted
            (stageAt depth).actionCurrent)
          (recurrenceUBIActiveAt depth))
        (recurrenceUBIPayloadAt depth)
  | 0 => HEq.rfl
  | depth + 1 => recurrenceUBIProjectionProject_exact depth

theorem recurrenceUBIPayloadConsumer_exact :
    ∀ depth : Nat,
      HEq (recurrenceUBIPayloadAt depth).consumer
        sourceGeneratedUBIRootRestriction
  | 0 => platformRetainedInheritedUBIConsumer_exact
  | depth + 1 => recurrenceUBIPayloadConsumer_exact depth

theorem recurrenceUBI_inheritedByGeneratedAction (depth : Nat) :
    HEq
      ((appendProjectionLaw (stageAt depth).sourceRoot
        (stageAt depth).exactSource.occurrence
        (stageAt depth).actionCurrent (stageAt depth).nextCarrier
        ).outcomeAt (.inherited (recurrenceUBIProjectionAt depth))
          (appendEmitted (stageAt depth).actionCurrent
            (stageAt depth).nextCarrier (stageAt depth).actionCurrent))
      ((stageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw
        |>.outcomeAt (recurrenceUBIProjectionAt depth)
          (stageAt depth).exactSource.occurrence) :=
  (stageAt depth).generatedAction.receipt.down.down.2.inheritedOutcomes
    (recurrenceUBIProjectionAt depth)

theorem recurrenceUBI_directConsumer (depth : Nat) :
    HEq
        ((stageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.project
          (recurrenceUBIProjectionAt depth)
          ((stageAt depth).sourceRoot.emitted
            (stageAt depth).actionCurrent)
          (recurrenceUBIActiveAt depth))
        (recurrenceUBIPayloadAt depth) ∧
      HEq (recurrenceUBIPayloadAt depth).consumer
        sourceGeneratedUBIRootRestriction ∧
      HEq
        ((appendProjectionLaw (stageAt depth).sourceRoot
          (stageAt depth).exactSource.occurrence
          (stageAt depth).actionCurrent (stageAt depth).nextCarrier
          ).outcomeAt (.inherited (recurrenceUBIProjectionAt depth))
            (appendEmitted (stageAt depth).actionCurrent
              (stageAt depth).nextCarrier (stageAt depth).actionCurrent))
        ((stageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw
          |>.outcomeAt (recurrenceUBIProjectionAt depth)
            (stageAt depth).exactSource.occurrence) :=
  ⟨recurrenceUBIProjectionProject_exact depth,
    recurrenceUBIPayloadConsumer_exact depth,
    recurrenceUBI_inheritedByGeneratedAction depth⟩

end
end M14SourceGeneratedLineageFoldRelationRecurrenceUBI
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLineageFoldRelationRecurrenceUBI.recurrenceUBIPayloadConsumer_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLineageFoldRelationRecurrenceUBI.recurrenceUBI_directConsumer
