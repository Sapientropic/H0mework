import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M2.GoGeneratedRelationRoleRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M2.ThreeAgentRoleCohomologyRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M2.PowerReadoutNonAuthorityRegression

/-!
# M2 whole-program sink

This sink simultaneously consumes universal relation generation, dynamic Go
roles, exact habitable future freedom, actual capture power, the three-agent
H¹ face and all authority-separation negative controls.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M2WholeProgramRegression

open Relations Power
open Go
open Go.Society
open Go.Society.GeneratedRelationRole Go.Society.GeneratedPower
open Go.Society.Future
open Go.G2GroupLineageRegression Go.G3SearchExposureRegression
open Go.G4FutureFreedomRegression Go.G4TacticalPhaseRegression
open Go.Society.M2GoGeneratedRelationRoleRegression
open Go.Society.M2GoGeneratedPowerRegression
open Go.Society.M2PowerReadoutNonAuthorityRegression
open M2ThreeAgentRoleCohomologyRegression

/-- M2 is closed only when every positive producer and negative authority
boundary is consumed together. -/
theorem m2WholeProgramSink :
    (∃ actor : pressureCompiler.Actor,
      ∃ first second : pressureCompiler.GeneratedRelation,
      ∃ firstRole secondRole : pressureCompiler.Role
          (goProcessGame chosenPly.extended).source,
        pressureCompiler.RelationRoleAt actor first .target firstRole ∧
        pressureCompiler.RelationRoleAt actor second .target secondRole ∧
        first ≠ second ∧ firstRole ≠ secondRole) ∧
    CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover ThreeCycleTime Int)
      roleCycle.cochain ∧
    ¬ PathAdditive roleCycle.cochain ∧
    (∀ other : ThreeCycleTime → ThreeCycleTime → Int,
      ThreeAgentRingCohomologous roleCycle.cochain other →
        (threeAgentFoldReadout other).value = 2) ∧
    GeneratedGroupPower.SourceCodes (horizon := 1)
        capturePly capturedSourceStone ≠
      GeneratedGroupPower.TargetCodes (horizon := 1)
        capturePly capturedSourceStone ∧
    captureGroupActionPower.freedomChange.kind = .lost ∧
    capturePly.extended.EventOwnedBy (actualEventIndex capturePly)
      (generatedActorEquiv 1 capturePly
        (GeneratedGroupPower.controllerActor capturePly)) ∧
    (GeneratedGroupRelationRole.asM1SourceActor 1 capturePly
      capturedSourceStone).1 = capturedGroup ∧
    (FutureFreedomCodesAt moverZeroEdge .source).Nonempty ∧
    ActionableFutureFreedomCodesAt moverZeroEdge .source = ∅ ∧
    FutureFreedomCodesAt opponentZeroEdge .source = ∅ ∧
    Nonempty
      (PowerOpportunityAt (compiler 1 chosenPly)
        (affectedActor 1 chosenPly pressureMoverSeed)
        (generatedRelationOf 1 chosenPly pressureMoverSeed)
        .source) ∧
    emptyReplay.toOccurrence.trace = emptyReplay.stateTrace ∧
    ¬ ConstraintPowerOverAt
      (GeneratedGroupRelationRole.compiler 0 bridgePly)
      (GeneratedGroupRelationRole.affectedGroupActor 0 bridgePly
        bridgeLeft.source)
      (GeneratedGroupRelationRole.generatedRelationOf 0 bridgePly
        bridgeLeft.source) ∧
    closureGain bridgeClosureUpdate = -1 ∧
    bridgeClassicalGame.payoff bridgeEvaluatedHistory
      (bridgePly.extended.player .positive) = some 1 := by
  refine ⟨static_actor_role_refuted,
    generated_relation_roles_nonzero_h1,
    generated_relation_roles_not_pathAdditive, ?_,
    capture_group_power_changes_future, rfl,
    capture_group_power_controller_is_actual_mover,
    capture_affected_is_exact_M1_group_actor,
    mover_horizon_zero_is_inhabited_not_actionable.1,
    mover_horizon_zero_is_inhabited_not_actionable.2,
    generated_root_false_relation_has_no_future,
    ⟨resignationSearchOpportunity⟩,
    (search_opportunity_same_root_no_actual_write.2.2.1),
    bridge_equal_group_freedom_has_no_constraint_power,
    bridge_closure_gain_eq_neg_one,
    bridge_strategy_generates_terminal_payoff.2⟩
  intro other cohomologous
  exact generated_role_fold_cohomology_invariant cohomologous

end M2WholeProgramRegression
end Society
end ProcessGame
end SaturationMonoid
