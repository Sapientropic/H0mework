import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M2.GoGeneratedPowerRegression

/-!
# M8 exact power-lineage calibration fixture

The calibration source is the already generated M2 actual capture power: exact
action controller, exact affected group actor, generated relation role,
nonzero lineage phase, and lost actionable freedom.  No preference profile,
aggregation rule, or truth decoder occurs in the authority mouth.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8ExactPowerLineageFixture

noncomputable section

open Go
open Go.Society
open Go.Society.GeneratedRelationRole
open Go.Society.GeneratedPower
open Go.Society.GeneratedGroupPower
open Go.Society.M2GoGeneratedPowerRegression
open Go.G2GroupLineageRegression Go.G3SearchExposureRegression
open Go.G4FutureFreedomRegression Go.G4TacticalPhaseRegression
open Power Relations

abbrev capturePowerCompiler :=
  GeneratedGroupRelationRole.compiler 1 capturePly

abbrev capturePowerRelation :=
  GeneratedGroupRelationRole.generatedRelationOf 1 capturePly
    capturedSourceStone

abbrev capturePowerAffectedActor :=
  GeneratedGroupRelationRole.affectedGroupActor 1 capturePly
    capturedSourceStone

def capturePowerTargetRole :
    capturePowerCompiler.Role (goProcessGame capturePly.extended).source :=
  capturePowerCompiler.roleAt capturePowerRelation .target

theorem capture_power_exists_without_preference_or_truth_input :
    Nonempty
      (ActionPowerOverAt capturePowerCompiler
        (GeneratedPower.controllerCompiler capturePly)
        (GeneratedGroupPower.controllerActor capturePly)
        capturePowerAffectedActor capturePowerRelation) :=
  ⟨captureGroupActionPower⟩

theorem capture_power_controller_is_exact_actual_event_owner :
    capturePly.extended.EventOwnedBy
      (GeneratedRelationRole.actualEventIndex capturePly)
      (GeneratedRelationRole.generatedActorEquiv 1 capturePly
        (GeneratedGroupPower.controllerActor capturePly)) :=
  capture_group_power_controller_is_actual_mover

theorem capture_power_affected_is_exact_group_lineage :
    (GeneratedGroupRelationRole.asM1SourceActor 1 capturePly
      capturedSourceStone).1 = capturedGroup :=
  capture_affected_is_exact_M1_group_actor

theorem capture_power_target_role_is_generated :
    capturePowerCompiler.RelationRoleAt
      capturePowerAffectedActor capturePowerRelation .target
      capturePowerTargetRole :=
  ⟨captureGroupActionPower.constraint.interest, rfl⟩

theorem capture_power_phase_is_nonzero :
    capturePowerCompiler.phaseStep capturePowerRelation ≠ 0 := by
  rw [GeneratedGroupRelationRole.generated_phaseStep_eq_G4_edge]
  exact capture_phase_nonzero

theorem capture_power_disposition_is_lost_freedom :
    captureGroupActionPower.freedomChange.kind = .lost :=
  rfl

theorem capture_power_changes_generated_future :
    GeneratedGroupPower.SourceCodes (horizon := 1)
        capturePly capturedSourceStone ≠
      GeneratedGroupPower.TargetCodes (horizon := 1)
        capturePly capturedSourceStone :=
  capture_group_power_changes_future

theorem capture_power_has_exact_action_trace_provenance :
    ∃ state ∈ (goProcessGame capturePly.extended).occurrence.trace,
      state = (GeneratedPower.controllerCompiler capturePly).actionState
          (goProcessGame capturePly.extended).source ∧
        (GeneratedPower.controllerCompiler capturePly).actionAdmittedAt
          captureGroupActionPower.action.1 :=
  captureGroupActionPower.controller_exact_state_provenance

end
end M8ExactPowerLineageFixture
end Society
end ProcessGame
end SaturationMonoid
