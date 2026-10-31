import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Society.GeneratedGroupPower
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G4TacticalPhaseRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G2GroupLineageRegression

/-!
# Exact Go capture generates action power

The reachable 2×2 whole capture aligns four independent source-generated
authorities on one occurrence: G2 actual owner, occupied-group beneficiary,
G4 nontrivial relation phase, and a nonempty future word genuinely lost from
the exact G3/G4 freedom fibre.  Equal freedom, horizon-zero idle freedom and a
source-generated root-false relation are direct negative controls.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Society
namespace M2GoGeneratedPowerRegression

open ProcessGame.Society Power Relations
open GeneratedRelationRole GeneratedPower Future
open G2GroupLineageRegression G3SearchExposureRegression
open G4FutureFreedomRegression G4TacticalPhaseRegression

/-! ## Whole capture: exact lost actionable freedom -/

abbrev captureSeed : RelationSeed capturePly :=
  .sourceGroup capturedSourceStone

abbrev captureEdge := phaseEdge 1 capturePly captureSeed

theorem capture_phase_nonzero : captureEdge.phaseStep ≠ 0 := by
  change capturedGroupEdge.phaseStep ≠ 0
  exact capturedGroupEdge.attack_phaseStep_nonzero
    actual_capture_generates_group_attack

theorem capture_pass_is_source_future :
    [(.pass : Move 2)] ∈
      SourceCodes (horizon := 1) captureSeed := by
  change [(.pass : Move 2)] ∈
    (compiler 1 capturePly).futureCodesAt
      (generatedRelationOf 1 capturePly captureSeed) .source
  rw [RelationFutureAuthority.player_codesAt_eq_exactFutureFreedom]
  rw [FutureFreedomCodesAt_eq_relationFreedom]
  exact captured_group_relation_fibres.1

theorem capture_pass_is_absent_at_target :
    [(.pass : Move 2)] ∉
      TargetCodes (horizon := 1) captureSeed := by
  change [(.pass : Move 2)] ∉
    (compiler 1 capturePly).futureCodesAt
      (generatedRelationOf 1 capturePly captureSeed) .target
  rw [RelationFutureAuthority.player_codesAt_eq_exactFutureFreedom]
  rw [FutureFreedomCodesAt_eq_relationFreedom]
  change [(.pass : Move 2)] ∉
    relationFreedom capturePly.extended 1
      (groupRelationProbe capturedGroup)
  rw [captured_group_relation_fibres.2]
  simp

def captureFreedomChange :
    ActionableFreedomChange (@WordIdle 2)
      (SourceCodes (horizon := 1) captureSeed)
      (TargetCodes (horizon := 1) captureSeed) :=
  .lost [(.pass : Move 2)]
    ⟨capture_pass_is_source_future, by simp [WordIdle]⟩
    capture_pass_is_absent_at_target

/-- Closed M2 action-power producer for an actual capture. -/
noncomputable def captureActionPower :=
  actionPowerOf 1 capturePly captureSeed capture_phase_nonzero
    captureFreedomChange

/-! The strongest capture mouth keeps the affected actor on M1's group face. -/

abbrev captureGroupEdge :=
  GeneratedGroupRelationRole.phaseEdge 1 capturePly capturedSourceStone

theorem capture_group_pass_is_source_future :
    [(.pass : Move 2)] ∈
      GeneratedGroupPower.SourceCodes (horizon := 1)
        capturePly capturedSourceStone := by
  change [(.pass : Move 2)] ∈
    (GeneratedGroupRelationRole.compiler 1 capturePly).futureCodesAt
      (GeneratedGroupRelationRole.generatedRelationOf 1 capturePly
        capturedSourceStone) .source
  rw [RelationFutureAuthority.group_codesAt_eq_exactFutureFreedom]
  rw [FutureFreedomCodesAt_eq_relationFreedom]
  exact captured_group_relation_fibres.1

theorem capture_group_pass_is_absent_at_target :
    [(.pass : Move 2)] ∉
      GeneratedGroupPower.TargetCodes (horizon := 1)
        capturePly capturedSourceStone := by
  change [(.pass : Move 2)] ∉
    (GeneratedGroupRelationRole.compiler 1 capturePly).futureCodesAt
      (GeneratedGroupRelationRole.generatedRelationOf 1 capturePly
        capturedSourceStone) .target
  rw [RelationFutureAuthority.group_codesAt_eq_exactFutureFreedom]
  rw [FutureFreedomCodesAt_eq_relationFreedom]
  change [(.pass : Move 2)] ∉
    relationFreedom capturePly.extended 1
      (groupRelationProbe capturedGroup)
  rw [captured_group_relation_fibres.2]
  simp

theorem capture_group_pass_has_compiler_future_witness :
    ∃ continuation :
        (GeneratedGroupRelationRole.compiler 1 capturePly).FutureContinuationAt
          (GeneratedGroupRelationRole.generatedRelationOf 1 capturePly
            capturedSourceStone).1
          .source [(.pass : Move 2)],
      (GeneratedGroupRelationRole.compiler 1 capturePly).FutureContinuationWitnessAt
        (GeneratedGroupRelationRole.generatedRelationOf 1 capturePly
          capturedSourceStone).1
        .source [(.pass : Move 2)] continuation := by
  exact
    (GeneratedGroupRelationRole.compiler 1 capturePly).futureCode_has_witnessed_continuation
      (GeneratedGroupRelationRole.generatedRelationOf 1 capturePly
        capturedSourceStone)
      capture_group_pass_is_source_future

def captureGroupFreedomChange :
    ActionableFreedomChange (@WordIdle 2)
      (GeneratedGroupPower.SourceCodes (horizon := 1)
        capturePly capturedSourceStone)
      (GeneratedGroupPower.TargetCodes (horizon := 1)
        capturePly capturedSourceStone) :=
  .lost [(.pass : Move 2)]
    ⟨capture_group_pass_is_source_future, by simp [WordIdle]⟩
    capture_group_pass_is_absent_at_target

/-- Actual mover player exercises power over the exact M1 source-group actor;
the two carriers remain different types in this theorem. -/
noncomputable def captureGroupActionPower :=
  GeneratedGroupPower.actionPowerOf 1 capturePly capturedSourceStone
    (by
      change capturedGroupEdge.phaseStep ≠ 0
      exact capture_phase_nonzero)
    captureGroupFreedomChange

theorem capture_group_power_changes_future :
    GeneratedGroupPower.SourceCodes (horizon := 1)
        capturePly capturedSourceStone ≠
      GeneratedGroupPower.TargetCodes (horizon := 1)
        capturePly capturedSourceStone :=
  captureGroupActionPower.freedom_ne

theorem capture_affected_is_exact_M1_group_actor :
    (GeneratedGroupRelationRole.asM1SourceActor 1 capturePly
      capturedSourceStone).1 = capturedGroup :=
  rfl

theorem capture_group_power_controller_is_actual_mover :
    capturePly.extended.EventOwnedBy (actualEventIndex capturePly)
      (generatedActorEquiv 1 capturePly
        (GeneratedGroupPower.controllerActor capturePly)) :=
  GeneratedGroupPower.controllerActor_is_existing_actual_owner 1 capturePly

/-- The machine type itself keeps player controller and group beneficiary
separate while proving both belong to the same actual occurrence. -/
theorem capture_player_controller_and_group_affected_faces :
    ∃ controller : (controllerCompiler capturePly).Actor,
      ∃ affected : (BoundaryGroupActor.core capturePly).SourceActor,
        capturePly.extended.EventOwnedBy (actualEventIndex capturePly)
          (generatedActorEquiv 1 capturePly controller) ∧
        affected.1 = capturedGroup :=
  ⟨GeneratedGroupPower.controllerActor capturePly,
    GeneratedGroupRelationRole.asM1SourceActor 1 capturePly
      capturedSourceStone,
    capture_group_power_controller_is_actual_mover,
    capture_affected_is_exact_M1_group_actor⟩

theorem capture_group_owner_flip_keeps_heterogeneous_authority :
    captureGroupEdge.ConstraintOwnerFlipAt ∧
      ∃ controller : (controllerCompiler capturePly).Actor,
        ∃ affected : (BoundaryGroupActor.core capturePly).SourceActor,
          capturePly.extended.EventOwnedBy (actualEventIndex capturePly)
            (generatedActorEquiv 1 capturePly controller) ∧
          affected.1 = capturedGroup := by
  refine ⟨?_, capture_player_controller_and_group_affected_faces⟩
  change capturedGroupEdge.ConstraintOwnerFlipAt
  unfold RelationPhaseEdge.ConstraintOwnerFlipAt
  apply (capturedGroupEdge.bearerDisposition_eq_handoff_iff_transport_or_comparison).mpr
  exact Or.inr (by
    have attack := actual_capture_generates_group_attack
    unfold RelationPhaseEdge.AttackAt at attack
    rw [attack]
    decide)

theorem capture_power_changes_future :
    SourceCodes (horizon := 1) captureSeed ≠
      TargetCodes (horizon := 1) captureSeed :=
  captureActionPower.freedom_ne

theorem capture_power_has_exact_interest_provenance :
    ∃ seed : (compiler 1 capturePly).ExactRelationSeed,
      (∃ state ∈ (goProcessGame capturePly.extended).occurrence.trace,
        state = (actorFace capturePly).state
          (goProcessGame capturePly.extended).source ∧
        (compiler 1 capturePly).relationSeedAt
          (goProcessGame capturePly.extended).source state seed.1 ∧
        (actorFace capturePly).SeedAt
          (goProcessGame capturePly.extended).source state
          ((compiler 1 capturePly).beneficiaryActorSeed seed.1)) ∧
      seed.actor (compiler 1 capturePly) =
        affectedActor 1 capturePly captureSeed ∧
      (compiler 1 capturePly).relationOf seed =
        generatedRelationOf 1 capturePly captureSeed :=
  captureActionPower.interest_exact_state_provenance

theorem capture_power_has_exact_controller_provenance :
    ∃ state ∈ (goProcessGame capturePly.extended).occurrence.trace,
      state = (controllerCompiler capturePly).actionState
        (goProcessGame capturePly.extended).source ∧
      (controllerCompiler capturePly).actionAdmittedAt
        captureActionPower.action.1 :=
  captureActionPower.controller_exact_state_provenance

theorem capture_controller_is_actual_mover :
    capturePly.extended.EventOwnedBy (actualEventIndex capturePly)
      (generatedActorEquiv 1 capturePly
        (controllerActorAt 1 capturePly)) :=
  controllerActor_is_existing_actual_owner 1 capturePly

theorem capture_controller_ne_affected :
    controllerActorAt 1 capturePly ≠
      affectedActor 1 capturePly captureSeed := by
  intro equal
  have players := congrArg (generatedActorEquiv 1 capturePly) equal
  have controls := congrArg
    (fun player : GeneratedReplay.GeneratedPlayer capturePly.extended =>
      player.1.control) players
  change capturePrefixReplay.final.visible.toMove =
    capturedSourceStone.polarity at controls
  have distinct : capturePrefixReplay.final.visible.toMove ≠
      capturedSourceStone.polarity := by decide
  exact distinct controls

/-- Relation-bearer handoff and actual mover ownership coexist but are not
the same authority: the mover and affected beneficiary are distinct actors. -/
theorem capture_owner_flip_is_not_mover_identity :
    captureEdge.ConstraintOwnerFlipAt ∧
      capturePly.extended.EventOwnedBy (actualEventIndex capturePly)
        (generatedActorEquiv 1 capturePly
          (controllerActorAt 1 capturePly)) ∧
      controllerActorAt 1 capturePly ≠
        affectedActor 1 capturePly captureSeed := by
  refine ⟨?_, capture_controller_is_actual_mover,
    capture_controller_ne_affected⟩
  change capturedGroupEdge.ConstraintOwnerFlipAt
  unfold RelationPhaseEdge.ConstraintOwnerFlipAt
  apply (capturedGroupEdge.bearerDisposition_eq_handoff_iff_transport_or_comparison).mpr
  exact Or.inr (by
    have attack := actual_capture_generates_group_attack
    unfold RelationPhaseEdge.AttackAt at attack
    rw [attack]
    decide)

/-! ## Source-generated idle and root-false negative controls -/

abbrev moverZeroEdge :=
  phaseEdge 0 chosenPly (.moverTurn : RelationSeed chosenPly)

theorem mover_horizon_zero_is_inhabited_not_actionable :
    (FutureFreedomCodesAt moverZeroEdge .source).Nonempty ∧
      ActionableFutureFreedomCodesAt moverZeroEdge .source = ∅ := by
  apply horizon_zero_inhabited_but_not_actionable
  exact sourceTurnRelationAt_holds_current emptyReplay

abbrev opponentZeroEdge :=
  phaseEdge 0 chosenPly (.opponentTurn : RelationSeed chosenPly)

theorem generated_root_false_relation_has_no_future :
    FutureFreedomCodesAt opponentZeroEdge .source = ∅ := by
  apply FutureFreedomCodesAt_eq_empty_of_root_false
  exact opponentTurnRelationAt_fails_current emptyReplay

/-! ## Same-root search opportunity without actual-write authority -/

abbrev pressureMoverSeed : RelationSeed chosenPly := .moverTurn
abbrev pressureMoverEdge := phaseEdge 1 chosenPly pressureMoverSeed

theorem resignation_is_actionable_search_code :
    [(.resign : Move 2)] ∈
      ActionableFutureFreedomCodesAt pressureMoverEdge .source := by
  apply (mem_ActionableFutureFreedomCodesAt_iff
    pressureMoverEdge .source [(.resign : Move 2)]).mpr
  constructor
  · apply (mem_FutureFreedomCodesAt_iff
      pressureMoverEdge .source [(.resign : Move 2)]).mp
    rw [FutureFreedomCodesAt_eq_relationFreedom]
    exact turn_freedom_exact_fibres.1.symm ▸ by simp
  · simp

noncomputable def resignationSearchOpportunity :=
  opportunityOf 1 chosenPly pressureMoverSeed .source
    [(.resign : Move 2)] resignation_is_actionable_search_code

theorem search_opportunity_same_root_no_actual_write :
    Nonempty
        (PowerOpportunityAt (compiler 1 chosenPly)
          (affectedActor 1 chosenPly pressureMoverSeed)
          (generatedRelationOf 1 chosenPly pressureMoverSeed)
          .source) ∧
      (futureConeAt emptyReplay 1).root = emptyReplay.final ∧
      emptyReplay.toOccurrence.trace = emptyReplay.stateTrace ∧
      emptyReplay.toOccurrence.trace.map
          (fun frame => frame.visible.situation) =
        emptyReplay.final.positionHistory := by
  refine ⟨⟨resignationSearchOpportunity⟩, ?_⟩
  exact (futureCone_actual_noninterference emptyReplay 1).1
    |> fun root => ⟨root,
      (futureCone_actual_noninterference emptyReplay 1).2.1,
      (futureCone_actual_noninterference emptyReplay 1).2.2.1⟩

/-! ## Equal generated freedom has no constraint power -/

abbrev bridgeStableSeed : RelationSeed bridgePly :=
  .sourceGroup bridgeLeft.source

abbrev bridgeStableEdge := phaseEdge 0 bridgePly bridgeStableSeed

theorem bridge_stable_phase_zero : bridgeStableEdge.phaseStep = 0 := by
  decide

theorem bridge_equal_freedom_has_no_constraint_power :
    ¬ ConstraintPowerOverAt (compiler 0 bridgePly)
      (affectedActor 0 bridgePly bridgeStableSeed)
      (generatedRelationOf 0 bridgePly bridgeStableSeed) := by
  intro alleged
  exact alleged.phase_nonzero bridge_stable_phase_zero

abbrev bridgeStableGroupEdge :=
  GeneratedGroupRelationRole.phaseEdge 0 bridgePly bridgeLeft.source

theorem bridge_stable_group_phase_zero :
    bridgeStableGroupEdge.phaseStep = 0 := by
  decide

/-- The stronger negative keeps the stable beneficiary on M1's group face. -/
theorem bridge_equal_group_freedom_has_no_constraint_power :
    ¬ ConstraintPowerOverAt
      (GeneratedGroupRelationRole.compiler 0 bridgePly)
      (GeneratedGroupRelationRole.affectedGroupActor 0 bridgePly
        bridgeLeft.source)
      (GeneratedGroupRelationRole.generatedRelationOf 0 bridgePly
        bridgeLeft.source) := by
  intro alleged
  exact alleged.phase_nonzero bridge_stable_group_phase_zero

end M2GoGeneratedPowerRegression
end Society
end Go
end ProcessGame
end SaturationMonoid
