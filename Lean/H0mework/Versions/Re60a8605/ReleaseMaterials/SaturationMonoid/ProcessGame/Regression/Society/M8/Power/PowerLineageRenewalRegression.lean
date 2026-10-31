import H0mework.Society.Renewal.RenewalFaceSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Power.ExactPowerLineageFixture

/-!
# M8 exact power-lineage renewal calibration

The calibration projection is generated from the existing M2 exact action seed.
Its standing records the generated controller, affected group actor, relation,
and target role; its consumer is the same exact action-power object and its
disposition is the same actionable-freedom change.  Preference aggregation
and truth do not occur in the producer type.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8PowerLineageRenewalRegression

noncomputable section

open Go
open Go.Society
open Go.Society.GeneratedRelationRole
open Go.Society.GeneratedPower
open Go.Society.GeneratedGroupPower
open Go.Society.M2GoGeneratedPowerRegression
open Go.G2GroupLineageRegression Go.G3SearchExposureRegression
open Go.G4FutureFreedomRegression Go.G4TacticalPhaseRegression
open Power Relations Renewal
open M8ExactPowerLineageFixture

abbrev PowerRenewalAction :=
  ActionPowerOverAt capturePowerCompiler
    (GeneratedPower.controllerCompiler capturePly)
    (GeneratedGroupPower.controllerActor capturePly)
    capturePowerAffectedActor capturePowerRelation

abbrev PowerRenewalDisposition :=
  ActionableFreedomChange (@GeneratedPower.WordIdle 2)
    (GeneratedGroupPower.SourceCodes (horizon := 1)
      capturePly capturedSourceStone)
    (GeneratedGroupPower.TargetCodes (horizon := 1)
      capturePly capturedSourceStone)

abbrev PowerRenewalStanding :=
  ((GeneratedPower.controllerCompiler capturePly).Actor ×
      capturePowerCompiler.Actor) ×
    (capturePowerCompiler.GeneratedRelation ×
      capturePowerCompiler.Role
        (goProcessGame capturePly.extended).source)

def powerRenewalStandingOf
    (seed : (GeneratedPower.controllerCompiler capturePly).ExactActionSeed) :
    PowerRenewalStanding :=
  ((seed.actor (GeneratedPower.controllerCompiler capturePly),
      capturePowerAffectedActor),
    (capturePowerRelation, capturePowerTargetRole))

def PowerRenewalConsumerAt
    (seed : (GeneratedPower.controllerCompiler capturePly).ExactActionSeed) :
    Type :=
  { power : PowerRenewalAction // power.action = seed }

abbrev PowerRenewalFace :=
  SourceGeneratedRenewalFace
    (goProcessGame capturePly.extended)
    (GeneratedPower.controllerCompiler capturePly).ActionSeed
    (GeneratedPower.controllerCompiler capturePly).actionSeedAt
    (GeneratedRelationRole.actorFace capturePly).Lineage
    (fun source seed =>
      source.lineage
        ((GeneratedPower.controllerCompiler capturePly).actorSeed seed.1))
    PowerRenewalStanding powerRenewalStandingOf PowerRenewalConsumerAt
    (fun _seed => PowerRenewalDisposition)

/-- Premise-free domain producer from the existing exact M2 action power. -/
def capturePowerLineageRenewal : PowerRenewalFace :=
  SourceGeneratedRenewalFace.generate captureGroupActionPower.action
    ⟨captureGroupActionPower, rfl⟩
    captureGroupActionPower.freedomChange

theorem capture_power_renewal_event_in_actual_trace :
    ∃ state ∈ (goProcessGame capturePly.extended).occurrence.trace,
      (GeneratedPower.controllerCompiler capturePly).actionSeedAt
        (goProcessGame capturePly.extended).source state
        capturePowerLineageRenewal.event :=
  capturePowerLineageRenewal.event_mem_source_trace

theorem capture_power_renewal_actor_has_exact_controller_lineage :
    capturePowerLineageRenewal.actor.1 =
      (GeneratedGroupPower.controllerActor capturePly).1 :=
  rfl

theorem capture_power_standing_is_exact_power_lineage_projection :
    capturePowerLineageRenewal.standing =
      ((GeneratedGroupPower.controllerActor capturePly,
          capturePowerAffectedActor),
        (capturePowerRelation, capturePowerTargetRole)) :=
  rfl

theorem capture_power_consumer_is_existing_action_power :
    capturePowerLineageRenewal.responsibilityConsumer.1 =
      captureGroupActionPower :=
  rfl

theorem capture_power_disposition_is_existing_freedom_change :
    capturePowerLineageRenewal.exactDisposition =
      captureGroupActionPower.freedomChange :=
  rfl

/-- The public authority mouth contains no preference or truth argument. -/
theorem capture_power_renews_without_preference_truth :
    Nonempty PowerRenewalFace :=
  ⟨capturePowerLineageRenewal⟩

structure PowerLineageRenewalCalibrationCertificate : Prop where
  renewalFace : Nonempty PowerRenewalFace
  exactEventTrace :
    ∃ state ∈ (goProcessGame capturePly.extended).occurrence.trace,
      (GeneratedPower.controllerCompiler capturePly).actionSeedAt
        (goProcessGame capturePly.extended).source state
        capturePowerLineageRenewal.event
  exactControllerLineage :
    capturePowerLineageRenewal.actor.1 =
      (GeneratedGroupPower.controllerActor capturePly).1
  exactStandingProjection :
    capturePowerLineageRenewal.standing =
      ((GeneratedGroupPower.controllerActor capturePly,
          capturePowerAffectedActor),
        (capturePowerRelation, capturePowerTargetRole))
  exactActionPowerConsumer :
    capturePowerLineageRenewal.responsibilityConsumer.1 =
      captureGroupActionPower
  exactFreedomDisposition :
    capturePowerLineageRenewal.exactDisposition =
      captureGroupActionPower.freedomChange
  actualEventOwner :
    capturePly.extended.EventOwnedBy
      (GeneratedRelationRole.actualEventIndex capturePly)
      (GeneratedRelationRole.generatedActorEquiv 1 capturePly
        (GeneratedGroupPower.controllerActor capturePly))
  affectedExactGroupLineage :
    (GeneratedGroupRelationRole.asM1SourceActor 1 capturePly
      capturedSourceStone).1 = capturedGroup
  targetRoleGenerated :
    capturePowerCompiler.RelationRoleAt capturePowerAffectedActor
      capturePowerRelation .target capturePowerTargetRole
  phaseNonzero : capturePowerCompiler.phaseStep capturePowerRelation ≠ 0
  dispositionLost :
    captureGroupActionPower.freedomChange.kind = .lost
  actionableFutureChanges :
    GeneratedGroupPower.SourceCodes (horizon := 1)
        capturePly capturedSourceStone ≠
      GeneratedGroupPower.TargetCodes (horizon := 1)
        capturePly capturedSourceStone

theorem powerLineageRenewalCalibrationDirectConsumer :
    PowerLineageRenewalCalibrationCertificate where
  renewalFace := capture_power_renews_without_preference_truth
  exactEventTrace := capture_power_renewal_event_in_actual_trace
  exactControllerLineage :=
    capture_power_renewal_actor_has_exact_controller_lineage
  exactStandingProjection :=
    capture_power_standing_is_exact_power_lineage_projection
  exactActionPowerConsumer := capture_power_consumer_is_existing_action_power
  exactFreedomDisposition :=
    capture_power_disposition_is_existing_freedom_change
  actualEventOwner :=
    capture_power_controller_is_exact_actual_event_owner
  affectedExactGroupLineage :=
    capture_power_affected_is_exact_group_lineage
  targetRoleGenerated := capture_power_target_role_is_generated
  phaseNonzero := capture_power_phase_is_nonzero
  dispositionLost := capture_power_disposition_is_lost_freedom
  actionableFutureChanges := capture_power_changes_generated_future

end
end M8PowerLineageRenewalRegression
end Society
end ProcessGame
end SaturationMonoid
