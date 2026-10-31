import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Action.SourceGeneratedSequentialCrossCompilerRelationAppend
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Relation.Recurrence.SourceGeneratedLineageFoldRelationRecurrenceUBI

/-!
# UBI restriction along cross-compiler relation recurrence

Each heterogeneous target inherits the UBI restriction from its exact source
occurrence.  The recursive projection follows actual generated roots through
`RootedAppendProjection.inherited`; it creates no payment, renewal, ledger,
registry or stored future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCrossCompilerRelationAppendUBI

noncomputable section

open M14UBIProofCarryingRootRestriction
open M14SourceGeneratedLineageFoldRelationRecurrenceStage
open M14SourceGeneratedLineageFoldRelationRecurrenceUBI
open M14SourceGeneratedRootedAccountedUnfoldingAppendLedger
open M14SourceGeneratedRootedAccountedUnfoldingAppendRoot
open M14SourceGeneratedCrossCompilerRelationAppendStage
open M14SourceGeneratedCrossCompilerRelationAppendStage.CrossCompilerRelationAppendStageAt
open M14SourceGeneratedSequentialCrossCompilerRelationAppend

def crossCompilerSourceUBIProjectionAt :
    (depth : Nat) →
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.Projection
  | 0 => recurrenceUBIProjectionAt 1
  | depth + 1 =>
      RootedAppendProjection.inherited
        (crossCompilerSourceUBIProjectionAt depth)

def crossCompilerSourceUBIActiveAt :
    (depth : Nat) →
      (appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.ActiveAt
        (crossCompilerSourceUBIProjectionAt depth)
        ((appendStageAt depth).sourceRoot.emitted
          (appendStageAt depth).sourceVisit.current)
  | 0 => recurrenceUBIActiveAt 1
  | depth + 1 => crossCompilerSourceUBIActiveAt depth

def crossCompilerUBIPayloadAt :
    Nat → type_of% (recurrenceUBIPayloadAt 1)
  | 0 => recurrenceUBIPayloadAt 1
  | depth + 1 => crossCompilerUBIPayloadAt depth

theorem crossCompilerSourceUBIProjectionProject_exact :
    ∀ depth : Nat,
      HEq
        ((appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.project
          (crossCompilerSourceUBIProjectionAt depth)
          ((appendStageAt depth).sourceRoot.emitted
            (appendStageAt depth).sourceVisit.current)
          (crossCompilerSourceUBIActiveAt depth))
        (crossCompilerUBIPayloadAt depth)
  | 0 => recurrenceUBIProjectionProject_exact 1
  | depth + 1 => crossCompilerSourceUBIProjectionProject_exact depth

theorem crossCompilerUBIPayloadConsumer_exact :
    ∀ depth : Nat,
      HEq (crossCompilerUBIPayloadAt depth).consumer
        sourceGeneratedUBIRootRestriction
  | 0 => recurrenceUBIPayloadConsumer_exact 1
  | depth + 1 => crossCompilerUBIPayloadConsumer_exact depth

theorem crossCompilerUBI_inheritedByGeneratedAction (depth : Nat) :
    HEq
      ((rootedAppendProjectionLaw (appendStageAt depth).sourceRoot
        (appendStageAt depth).exactSource.occurrence
        (appendStageAt depth).targetPrior (appendStageAt depth).targetAtom
        ).outcomeAt
          (RootedAppendProjection.inherited
            (crossCompilerSourceUBIProjectionAt depth))
          (rootedAppendEmitted (appendStageAt depth).targetPrior
            (appendStageAt depth).targetAtom
              (appendStageAt depth).targetPrior))
      ((appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw
        |>.outcomeAt (crossCompilerSourceUBIProjectionAt depth)
          (appendStageAt depth).exactSource.occurrence) :=
  (generatedCrossCompilerRelationAppendActionAt depth
    ).receipt.down.down.inheritedOutcomes
      (crossCompilerSourceUBIProjectionAt depth)

theorem crossCompilerUBI_directConsumer (depth : Nat) :
    HEq
        ((appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw.project
          (crossCompilerSourceUBIProjectionAt depth)
          ((appendStageAt depth).sourceRoot.emitted
            (appendStageAt depth).sourceVisit.current)
          (crossCompilerSourceUBIActiveAt depth))
        (crossCompilerUBIPayloadAt depth) ∧
      HEq (crossCompilerUBIPayloadAt depth).consumer
        sourceGeneratedUBIRootRestriction ∧
      HEq
        ((rootedAppendProjectionLaw (appendStageAt depth).sourceRoot
          (appendStageAt depth).exactSource.occurrence
          (appendStageAt depth).targetPrior (appendStageAt depth).targetAtom
          ).outcomeAt
            (RootedAppendProjection.inherited
              (crossCompilerSourceUBIProjectionAt depth))
            (rootedAppendEmitted (appendStageAt depth).targetPrior
              (appendStageAt depth).targetAtom
                (appendStageAt depth).targetPrior))
        ((appendStageAt depth).sourceRoot.toAuthoritativeRoot.source.projectionLaw
          |>.outcomeAt (crossCompilerSourceUBIProjectionAt depth)
            (appendStageAt depth).exactSource.occurrence) :=
  ⟨crossCompilerSourceUBIProjectionProject_exact depth,
    crossCompilerUBIPayloadConsumer_exact depth,
    crossCompilerUBI_inheritedByGeneratedAction depth⟩

end
end M14SourceGeneratedCrossCompilerRelationAppendUBI
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendUBI.crossCompilerUBIPayloadConsumer_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendUBI.crossCompilerUBI_directConsumer
