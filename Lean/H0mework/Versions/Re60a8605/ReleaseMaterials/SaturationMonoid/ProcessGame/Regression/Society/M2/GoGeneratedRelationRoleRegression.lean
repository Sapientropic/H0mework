import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Society.GeneratedRelationRole
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G4TacticalPhaseRegression

/-!
# Same generated Go actor, different relation roles on one actual ply

The pressure ply carries two closed source-generated turn aspects.  They share
one G2 mover-lineage beneficiary but their existing G4 freedom comparisons are
strict shrink and strict growth, so their generated target roles differ.  A
static role field on the actor cannot reproduce this same-occurrence result.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Society
namespace M2GoGeneratedRelationRoleRegression

open ProcessGame.Society.Relations
open GeneratedRelationRole
open G3SearchExposureRegression G4FutureFreedomRegression
open G4TacticalPhaseRegression

abbrev pressureCompiler := compiler 1 chosenPly

abbrev moverSeed : RelationSeed chosenPly := .moverTurn
abbrev opponentSeed : RelationSeed chosenPly := .opponentTurn

def commonActor : pressureCompiler.Actor :=
  (exactRelationSeed 1 chosenPly moverSeed).actor pressureCompiler

def moverRelation : pressureCompiler.GeneratedRelation :=
  generatedRelationOf 1 chosenPly moverSeed

def opponentRelation : pressureCompiler.GeneratedRelation :=
  generatedRelationOf 1 chosenPly opponentSeed

theorem both_relations_are_exact_interests_of_same_actor :
    pressureCompiler.GeneratedInterestAt commonActor moverRelation ∧
      pressureCompiler.GeneratedInterestAt commonActor opponentRelation ∧
      moverRelation ≠ opponentRelation := by
  simpa [pressureCompiler, commonActor, moverRelation, opponentRelation,
    moverSeed, opponentSeed] using
      turn_aspects_generate_distinct_interests_for_same_actor 1 chosenPly

theorem mover_G4_phase_eq_one :
    (phaseEdge 1 chosenPly moverSeed).phaseStep = 1 := by
  change pressureEdge.phaseStep = 1
  exact pressure_phase_is_quarter_turn

theorem opponent_G4_phase_eq_three :
    (phaseEdge 1 chosenPly opponentSeed).phaseStep = 3 := by
  change growthEdgeOnSamePly.phaseStep = 3
  exact same_ply_second_phase_is_inverse_quarter_turn

theorem mover_G4_target_state_eq_receive :
    (phaseEdge 1 chosenPly moverSeed).targetState = .receive := by
  change pressureEdge.targetState = .receive
  exact pressure_generates_receive_state

theorem opponent_G4_target_state_eq_reverse :
    (phaseEdge 1 chosenPly opponentSeed).targetState = .reverse := by
  change growthEdgeOnSamePly.targetState = .reverse
  unfold RelationPhaseEdge.targetState
  rw [same_ply_second_relation_grows]
  rfl

theorem generated_target_roles_ne :
    pressureCompiler.roleAt moverRelation .target ≠
      pressureCompiler.roleAt opponentRelation .target := by
  change
    (compiler 1 chosenPly).roleAt
        (generatedRelationOf 1 chosenPly
          (.moverTurn : RelationSeed chosenPly)) .target ≠
      (compiler 1 chosenPly).roleAt
        (generatedRelationOf 1 chosenPly
          (.opponentTurn : RelationSeed chosenPly)) .target
  rw [generated_target_role_eq_G4_state,
    generated_target_role_eq_G4_state,
    mover_G4_target_state_eq_receive,
    opponent_G4_target_state_eq_reverse]
  intro impossible
  cases impossible

/-- One actor on one actual edge has two exact generated interests and two
different target-side roles. -/
theorem static_actor_role_refuted :
    ∃ actor : pressureCompiler.Actor,
      ∃ first second : pressureCompiler.GeneratedRelation,
      ∃ firstRole secondRole : pressureCompiler.Role
          (goProcessGame chosenPly.extended).source,
        pressureCompiler.RelationRoleAt actor first .target firstRole ∧
        pressureCompiler.RelationRoleAt actor second .target secondRole ∧
        first ≠ second ∧ firstRole ≠ secondRole := by
  refine ⟨commonActor, moverRelation, opponentRelation,
    pressureCompiler.roleAt moverRelation .target,
    pressureCompiler.roleAt opponentRelation .target,
    ⟨both_relations_are_exact_interests_of_same_actor.1, rfl⟩,
    ⟨both_relations_are_exact_interests_of_same_actor.2.1, rfl⟩,
    both_relations_are_exact_interests_of_same_actor.2.2,
    generated_target_roles_ne⟩

/-- The same common actor is the exact G2 owner of this actual event. -/
theorem common_actor_is_exact_actual_owner :
    chosenPly.extended.EventOwnedBy (actualEventIndex chosenPly)
      (generatedActorEquiv 1 chosenPly commonActor) := by
  simpa [commonActor, pressureCompiler, moverSeed] using
    turn_aspect_beneficiary_owns_actual_event 1 chosenPly

theorem both_target_roles_are_individually_unique :
    (∃! role : pressureCompiler.Role
        (goProcessGame chosenPly.extended).source,
      pressureCompiler.RelationRoleAt commonActor moverRelation .target role) ∧
    (∃! role : pressureCompiler.Role
        (goProcessGame chosenPly.extended).source,
      pressureCompiler.RelationRoleAt commonActor opponentRelation .target role) := by
  constructor
  · exact pressureCompiler.relationRoleAt_total_unique
      both_relations_are_exact_interests_of_same_actor.1 .target
  · exact pressureCompiler.relationRoleAt_total_unique
      both_relations_are_exact_interests_of_same_actor.2.1 .target

end M2GoGeneratedRelationRoleRegression
end Society
end Go
end ProcessGame
end SaturationMonoid
