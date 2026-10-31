import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Runtime.SourceGeneratedCrossCompilerRelationAppendRuntime

/-!
# Actual relation renewal cycle in the unique cross runtime

One macro edge is an actual cross action, its generated selection, and the
next actual cross action.  Three consecutive macro edges advance through four
strictly later occurrences while renewing the fourth actor/lineage identity
to the first.  Closure is therefore social identity across time, never
occurrence equality or time reversal.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedActualRelationThreeCycle

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open Lifecycle Universal Relations
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessCriticalAction
open M14SourceGeneratedEssentialAccessRelationRenewal
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedCrossCompilerRelationAppendPresentation
open M14SourceGeneratedSequentialCrossCompilerRelationAppend
open M14SourceGeneratedTenureQueueAppendRuntime
open M14SourceGeneratedCrossCompilerRelationAppendRuntime

abbrev actualRelationSeedAt (depth : Nat) :=
  (crossCompilerCurrentStageAt depth).targetSeed

def actualRelationActorAt (depth : Nat) :
    essentialAccessRelationCompiler.Actor :=
  (actualRelationSeedAt depth).actor essentialAccessRelationCompiler

def actualRelationAt (depth : Nat) :
    essentialAccessRelationCompiler.GeneratedRelation :=
  essentialAccessCriticalRelation (actualRelationSeedAt depth).1

def actualRelationPhaseAt (depth : Nat) :=
  essentialAccessRelationCompiler.phaseStep (actualRelationAt depth)

def actualRelationSourceRoleAt (depth : Nat) :=
  essentialAccessRelationCompiler.roleAt (actualRelationAt depth) .source

def actualRelationTargetRoleAt (depth : Nat) :=
  essentialAccessRelationCompiler.roleAt (actualRelationAt depth) .target

theorem actualRelationPhase_nonzero (depth : Nat) :
    actualRelationPhaseAt depth ≠ 0 :=
  essentialAccessCriticalPhase_nonzero (actualRelationSeedAt depth).1

theorem actualRelationTargetRole_generated (depth : Nat) :
    actualRelationTargetRoleAt depth =
      essentialAccessRelationCompiler.advanceRole
        Lifecycle.actualEventGame.source
        (actualRelationPhaseAt depth)
        (actualRelationSourceRoleAt depth) :=
  rfl

/-- One exact action→selection→next-action macro edge in the existing
runtime.  Every field is a proposition about that named runtime and its
generated receipts; no event, actor, phase or endpoint is stored. -/
structure SourceGeneratedActualRelationMacroEdgeAt
    (depth : Nat) : Prop where
  private mk ::
  sourceActionRuntime :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      (generatedCrossCompilerRelationAppendActionAt depth) runtime
        (crossActionRuntimeDepth depth)
  sourceReceipt : type_of% (crossCompilerRuntime_directConsumer depth)
  sourceToSelection :
    type_of% (crossActionToSelectionSuccessorValid depth)
  selectionToTarget :
    type_of% (crossSelectionToNextActionSuccessorValid depth)
  targetActionRuntime :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      (generatedCrossCompilerRelationAppendActionAt (depth + 1)) runtime
        (crossActionRuntimeDepth (depth + 1))
  sourceActionSeedExact :
    (crossCompilerSelectedActionAt depth
      ).criticalBearer.bearerLineage.seed =
        actualRelationSeedAt depth
  targetSeedRenewal :
    actualRelationSeedAt (depth + 1) =
      sourceGeneratedEssentialAccessRenewalSeed
        (actualRelationSeedAt depth)
  actorChanges :
    actualRelationActorAt (depth + 1) ≠ actualRelationActorAt depth
  phaseNonzero : actualRelationPhaseAt depth ≠ 0
  targetRoleGenerated :
    actualRelationTargetRoleAt depth =
      essentialAccessRelationCompiler.advanceRole
        Lifecycle.actualEventGame.source
        (actualRelationPhaseAt depth)
        (actualRelationSourceRoleAt depth)

theorem sourceGeneratedActualRelationMacroEdgeAt (depth : Nat) :
    SourceGeneratedActualRelationMacroEdgeAt depth where
  sourceActionRuntime := crossActionRuntimeResumption depth
  sourceReceipt := crossCompilerRuntime_directConsumer depth
  sourceToSelection := crossActionToSelectionSuccessorValid depth
  selectionToTarget := crossSelectionToNextActionSuccessorValid depth
  targetActionRuntime := crossActionRuntimeResumption (depth + 1)
  sourceActionSeedExact := crossCompilerSelectedAction_seed_exact depth
  targetSeedRenewal := crossCompilerCurrentStageAt_targetSeed_succ depth
  actorChanges := by
    unfold actualRelationActorAt actualRelationSeedAt
    rw [crossCompilerCurrentStageAt_targetSeed_succ]
    exact renewalSeed_actor_ne _
  phaseNonzero := actualRelationPhase_nonzero depth
  targetRoleGenerated := actualRelationTargetRole_generated depth

/-- Three macro edges form a genuine renewal cycle: occurrences keep moving
forward, adjacent actors change, and the fourth occurrence renews the first
actor/lineage identity. -/
structure SourceGeneratedActualRelationThreeCycleAt
    (base : Nat) : Prop where
  private mk ::
  first : SourceGeneratedActualRelationMacroEdgeAt base
  second : SourceGeneratedActualRelationMacroEdgeAt (base + 1)
  third : SourceGeneratedActualRelationMacroEdgeAt (base + 2)
  seedClosure :
    actualRelationSeedAt (base + 3) = actualRelationSeedAt base
  actorClosure :
    actualRelationActorAt (base + 3) = actualRelationActorAt base
  renewedOccurrenceDistinct :
    (crossCompilerActionPresentationAt (base + 3)).erase ≠
      (crossCompilerActionPresentationAt base).erase

theorem sourceGeneratedActualRelationThreeCycleAt (base : Nat) :
    SourceGeneratedActualRelationThreeCycleAt base where
  first := sourceGeneratedActualRelationMacroEdgeAt base
  second := sourceGeneratedActualRelationMacroEdgeAt (base + 1)
  third := sourceGeneratedActualRelationMacroEdgeAt (base + 2)
  seedClosure := crossCompilerCurrentStageAt_targetSeed_add_three base
  actorClosure := crossCompilerCurrentStageAt_targetActor_add_three base
  renewedOccurrenceDistinct :=
    (periodThreeSeed_differentCrossCompilerOccurrence base).2

theorem actualRelationMacroEdge_directConsumer (depth : Nat) :
    Nonempty (SourceGeneratedActualRelationMacroEdgeAt depth) ∧
      SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
        (generatedCrossCompilerRelationAppendActionAt depth) runtime
          (9 + 2 * depth) ∧
      SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
        (generatedCrossCompilerRelationAppendActionAt (depth + 1)) runtime
          (9 + 2 * (depth + 1)) ∧
      actualRelationSeedAt (depth + 1) =
        sourceGeneratedEssentialAccessRenewalSeed
          (actualRelationSeedAt depth) ∧
      actualRelationActorAt (depth + 1) ≠ actualRelationActorAt depth ∧
      actualRelationPhaseAt depth ≠ 0 ∧
      actualRelationTargetRoleAt depth =
        essentialAccessRelationCompiler.advanceRole
          Lifecycle.actualEventGame.source
          (actualRelationPhaseAt depth)
          (actualRelationSourceRoleAt depth) := by
  refine ⟨⟨sourceGeneratedActualRelationMacroEdgeAt depth⟩, ?_, ?_,
    crossCompilerCurrentStageAt_targetSeed_succ depth, ?_,
    actualRelationPhase_nonzero depth,
    actualRelationTargetRole_generated depth⟩
  · simpa only [crossActionRuntimeDepth_closed] using
      crossActionRuntimeResumption depth
  · simpa only [crossActionRuntimeDepth_closed] using
      crossActionRuntimeResumption (depth + 1)
  · exact (sourceGeneratedActualRelationMacroEdgeAt depth).actorChanges

theorem actualRelationThreeCycle_directConsumer (base : Nat) :
    Nonempty (SourceGeneratedActualRelationThreeCycleAt base) ∧
      type_of% (actualRelationMacroEdge_directConsumer base) ∧
      type_of% (actualRelationMacroEdge_directConsumer (base + 1)) ∧
      type_of% (actualRelationMacroEdge_directConsumer (base + 2)) ∧
      actualRelationSeedAt (base + 3) = actualRelationSeedAt base ∧
      actualRelationActorAt (base + 3) = actualRelationActorAt base ∧
      (crossCompilerActionPresentationAt (base + 3)).erase ≠
        (crossCompilerActionPresentationAt base).erase :=
  ⟨⟨sourceGeneratedActualRelationThreeCycleAt base⟩,
    actualRelationMacroEdge_directConsumer base,
    actualRelationMacroEdge_directConsumer (base + 1),
    actualRelationMacroEdge_directConsumer (base + 2),
    crossCompilerCurrentStageAt_targetSeed_add_three base,
    crossCompilerCurrentStageAt_targetActor_add_three base,
    (periodThreeSeed_differentCrossCompilerOccurrence base).2⟩

theorem actualRelationThreeCycle_actorPairwise (base : Nat) :
    actualRelationActorAt (base + 1) ≠ actualRelationActorAt base ∧
      actualRelationActorAt (base + 2) ≠
        actualRelationActorAt (base + 1) ∧
      actualRelationActorAt (base + 2) ≠ actualRelationActorAt base := by
  refine ⟨(sourceGeneratedActualRelationMacroEdgeAt base).actorChanges,
    (sourceGeneratedActualRelationMacroEdgeAt (base + 1)).actorChanges, ?_⟩
  intro third_eq_first
  exact (sourceGeneratedActualRelationMacroEdgeAt (base + 2)).actorChanges
    ((crossCompilerCurrentStageAt_targetActor_add_three base).trans
      third_eq_first.symm)

end
end M14SourceGeneratedActualRelationThreeCycle
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedActualRelationThreeCycle.sourceGeneratedActualRelationMacroEdgeAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedActualRelationThreeCycle.sourceGeneratedActualRelationThreeCycleAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedActualRelationThreeCycle.actualRelationMacroEdge_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedActualRelationThreeCycle.actualRelationThreeCycle_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedActualRelationThreeCycle.actualRelationThreeCycle_actorPairwise
