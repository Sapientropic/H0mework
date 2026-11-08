import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.AttackDefensePhaseReadout
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G4FutureFreedomRegression

/-!
# G4 tactical phase direct regression

The concrete pressure/response plies come from the same actual replay used by
the finite-freedom regression.  Their phase edges consume the generated turn
relation and exact recovery witness.  A second attack consumes G2's generated
snapshot-group relation.  Conversion uses the closed actual-child turn
compiler; counterattack couples exact baseline recovery with an independent
opponent-turn contraction on the same response ply.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G4TacticalPhaseRegression

open G3SearchExposureRegression G4FutureFreedomRegression

/-! ## Actual pressure and recovery -/

def retainedLaw : RelationTransportLaw 2 :=
  RelationTransportLaw.retain 2

def pressureLineage :
    RelationLineage 1 retainedLaw emptyReplay turnRelation .impose :=
  .marked emptyReplay turnRelation (by trivial)

def pressureEdge : RelationPhaseEdge 1 retainedLaw chosenPly where
  sourceRelation := turnRelation
  sourceState := .impose
  sourceLineage := pressureLineage

theorem pressure_comparison_is_shrink :
    pressureEdge.comparison = .shrink := by
  exact (relationComparisonAt_retain_eq_shrink_iff chosenPly 1
    turnRelation).mpr pressure_strictly_shrinks_turn_freedom

theorem pressure_generates_receive_state :
    pressureEdge.targetState = .receive := by
  unfold RelationPhaseEdge.targetState
  rw [pressure_comparison_is_shrink]
  rfl

theorem pressure_phase_is_quarter_turn : pressureEdge.phaseStep = 1 := by
  rw [pressureEdge.phaseStep_eq_relationPhaseStep,
    pressure_comparison_is_shrink]
  rfl

theorem pressure_is_generated_attack : pressureEdge.AttackAt := by
  apply pressureEdge.attack_of_retained_shrink
  · rfl
  · exact pressure_strictly_shrinks_turn_freedom

theorem pressure_hands_off_constraint_owner :
    pressureEdge.ConstraintOwnerFlipAt := by
  unfold RelationPhaseEdge.ConstraintOwnerFlipAt
  apply (RelationPhaseEdge.bearerDisposition_eq_handoff_iff_transport_or_comparison
    pressureEdge).mpr
  exact Or.inr (by rw [pressure_comparison_is_shrink]; decide)

theorem pressure_handoff_has_nontrivial_rotation :
    pressureEdge.InitiativeHandoffAt ∧
      TacticalPhase.rotation pressureEdge.phaseStep ≠ 1 := by
  have handoff : pressureEdge.InitiativeHandoffAt := by
    unfold RelationPhaseEdge.InitiativeHandoffAt
    rw [pressure_generates_receive_state]
    decide
  exact ⟨handoff,
    (pressureEdge.initiativeHandoff_iff_nontrivial_rotation).mp handoff⟩

def responseEdge : RelationPhaseEdge 1 retainedLaw responsePly :=
  pressureEdge.nextEdge responsePly

theorem response_comparison_is_grow :
    responseEdge.comparison = .grow := by
  exact (relationComparisonAt_retain_eq_grow_iff responsePly 1
    turnRelation).mpr response_strictly_grows_same_turn_freedom

def responseDefense :
    RelationPhaseEdge.DefenseAt 1 retainedLaw chosenPly responsePly
      pressureEdge where
  pressureRetained := rfl
  responseRetained := rfl
  recovery := exactTurnRecovery

theorem response_is_exact_defense :
    responseDefense.recovery.recoveredWord = [(.resign : Move 2)] ∧
      responseEdge.comparison = .grow := by
  exact ⟨rfl, responseDefense.comparison_eq_grow⟩

theorem response_phase_is_inverse_quarter_turn :
    responseEdge.phaseStep = 3 := by
  rw [responseEdge.phaseStep_eq_relationPhaseStep,
    response_comparison_is_grow]
  rfl

theorem response_returns_to_impose_state :
    responseEdge.targetState = .impose := by
  unfold RelationPhaseEdge.targetState responseEdge
  change generatedTargetState retainedLaw pressureEdge.targetState
    responseEdge.comparison = .impose
  rw [pressure_generates_receive_state, response_comparison_is_grow]
  rfl

theorem pressure_response_C4_composition :
    TacticalPhase.compose responseEdge.phaseStep pressureEdge.phaseStep = 0 := by
  rw [response_phase_is_inverse_quarter_turn,
    pressure_phase_is_quarter_turn]
  decide

theorem pressure_response_exact_lineage_product :
    responseEdge.targetLineage.phaseProduct = 0 := by
  rw [responseEdge.targetLineage_phaseProduct]
  change TacticalPhase.compose responseEdge.phaseStep
    pressureEdge.targetLineage.phaseProduct = 0
  rw [pressureEdge.targetLineage_phaseProduct]
  have seedProduct : pressureEdge.sourceLineage.phaseProduct = 0 := by
    rfl
  rw [seedProduct,
    response_phase_is_inverse_quarter_turn,
    pressure_phase_is_quarter_turn]
  decide

/-! ## The four absolute states and total comparison -/

theorem four_shrink_steps_cycle_all_states :
    advanceStateByComparison .impose .shrink = .receive ∧
      advanceStateByComparison .receive .shrink = .redirect ∧
      advanceStateByComparison .redirect .shrink = .reverse ∧
      advanceStateByComparison .reverse .shrink = .impose := by
  decide

theorem pressure_target_state_total_unique :
    ∃! state : TacticalState, state = pressureEdge.targetState :=
  pressureEdge.targetState_total_unique

theorem incomparable_common_carriers_are_detected :
    compareFreedom
        ({[(.pass : Move 2)]} : Finset (List (Move 2)))
        ({[(.resign : Move 2)]} : Finset (List (Move 2))) =
      .incomparable := by
  decide

/-! ## Generated group attack -/

def capturedGroupLineage : RelationLineage
    1 retainedLaw
    G2GroupLineageRegression.capturePrefixReplay
    (groupRelationProbe capturedGroup) .impose :=
  .marked G2GroupLineageRegression.capturePrefixReplay
    (groupRelationProbe capturedGroup) (by trivial)

def capturedGroupEdge : RelationPhaseEdge 1 retainedLaw
    G2GroupLineageRegression.capturePly where
  sourceRelation := groupRelationProbe capturedGroup
  sourceState := .impose
  sourceLineage := capturedGroupLineage

theorem actual_capture_generates_group_attack : capturedGroupEdge.AttackAt := by
  apply capturedGroupEdge.attack_of_retained_shrink
  · rfl
  · exact actual_capture_strictly_shrinks_group_freedom

theorem captured_group_attack_keeps_same_cone_provenance :
    ∃ continuation : GeneratedReplay G2GroupLineageRegression.zeroKomiLaw
        G2GroupLineageRegression.capturePrefixReplay.final
        [(.pass : Move 2)],
      continuation.stateTrace ∈
          rootedPaths
            (futureConeAt G2GroupLineageRegression.capturePrefixReplay 1) ∧
        continuation.stateTrace.all
          (groupRelationProbe capturedGroup).holds = true :=
  captured_group_pass_path_factors_through_horizon_one

/-! ## Fixed relation conversion and counterattack -/

def nextTurnRelation : RelationProbe 2 :=
  sourceTurnRelationAt chosenPly.extended

theorem baseline_and_response_opponent_relations_distinct :
    turnRelation ≠ nextTurnRelation := by
  intro equal
  have sameAtInitial := congrArg
    (fun relation : RelationProbe 2 => relation.holds emptyReplay.final) equal
  simp [turnRelation, nextTurnRelation, sourceTurnRelationAt] at sameAtInitial
  exact (show emptyReplay.final.visible.toMove ≠
      chosenPly.extended.final.visible.toMove by decide) sameAtInitial

def advanceTurnLaw : RelationTransportLaw 2 :=
  RelationTransportLaw.advanceTurn 2

def conversionLineage : RelationLineage 1 advanceTurnLaw
    chosenPly.extended nextTurnRelation .impose :=
  .marked chosenPly.extended nextTurnRelation rfl

def conversionEdge : RelationPhaseEdge 1 advanceTurnLaw responsePly where
  sourceRelation := nextTurnRelation
  sourceState := .impose
  sourceLineage := conversionLineage

theorem conversion_relation_is_actual_child_generated :
    conversionEdge.targetRelation = sourceTurnRelationAt responsePly.extended ∧
      conversionEdge.ConversionAt := by
  constructor
  · exact RelationPhaseEdge.conversion_target_is_generated (by rfl)
  · rfl

theorem conversion_generates_redirect_and_handoff :
    conversionEdge.targetState = .redirect ∧
      conversionEdge.phaseStep = 2 ∧
      conversionEdge.ConstraintOwnerFlipAt := by
  constructor
  · unfold RelationPhaseEdge.targetState generatedTargetState advanceTurnLaw
      RelationTransportLaw.advanceTurn advanceStateByComparison
    rfl
  · constructor
    · rw [conversionEdge.phaseStep_eq_relationPhaseStep]
      rfl
    · unfold RelationPhaseEdge.ConstraintOwnerFlipAt
      apply (RelationPhaseEdge.bearerDisposition_eq_handoff_iff_transport_or_comparison
        conversionEdge).mpr
      exact Or.inl rfl

def opponentResponseLineage : RelationLineage 1 retainedLaw
    chosenPly.extended nextTurnRelation .impose :=
  .marked chosenPly.extended nextTurnRelation (by trivial)

def opponentResponseEdge : RelationPhaseEdge 1 retainedLaw responsePly where
  sourceRelation := nextTurnRelation
  sourceState := .impose
  sourceLineage := opponentResponseLineage

theorem response_strictly_shrinks_opponent_turn_freedom :
    FreedomShrinksAt responsePly 1 nextTurnRelation := by
  unfold FreedomShrinksAt nextTurnRelation sourceTurnRelationAt
  decide

theorem response_generates_opponent_attack :
    opponentResponseEdge.AttackAt := by
  apply opponentResponseEdge.attack_of_retained_shrink
  · rfl
  · exact response_strictly_shrinks_opponent_turn_freedom

def generatedCounterattack : RelationPhaseEdge.CounterattackAt
    1 retainedLaw retainedLaw chosenPly responsePly pressureEdge
      opponentResponseEdge where
  defense := responseDefense
  independent := baseline_and_response_opponent_relations_distinct.symm
  opponentAttack := response_generates_opponent_attack

theorem counterattack_recovers_and_compresses_opponent :
    responseDefense.recovery.recoveredWord ∈
        relationFreedom responsePly.extended 1 turnRelation ∧
      opponentResponseEdge.AttackAt ∧
      opponentResponseEdge.ConstraintOwnerFlipAt := by
  exact ⟨responseDefense.recovery.restoredByResponse,
    generatedCounterattack.opponentAttack,
    generatedCounterattack.flips_constraint_owner⟩

/-! ## One move, multiple independent relation obligations -/

def emptyOpponentTurnRelation : RelationProbe 2 where
  holds := fun frame => decide
    (frame.visible.toMove ≠ emptyReplay.final.visible.toMove)

def emptyOpponentTurnLineage :
    RelationLineage 1 retainedLaw emptyReplay emptyOpponentTurnRelation
      .impose :=
  .marked emptyReplay emptyOpponentTurnRelation (by trivial)

def growthEdgeOnSamePly : RelationPhaseEdge 1 retainedLaw chosenPly where
  sourceRelation := emptyOpponentTurnRelation
  sourceState := .impose
  sourceLineage := emptyOpponentTurnLineage

theorem same_ply_second_relation_grows :
    growthEdgeOnSamePly.comparison = .grow := by
  decide

theorem same_ply_relations_are_source_distinct :
    turnRelation ≠ emptyOpponentTurnRelation := by
  intro equal
  have sameAtSource := congrArg
    (fun relation : RelationProbe 2 => relation.holds emptyReplay.final) equal
  simp [turnRelation, emptyOpponentTurnRelation, sourceTurnRelationAt]
    at sameAtSource

theorem same_ply_second_phase_is_inverse_quarter_turn :
    growthEdgeOnSamePly.phaseStep = 3 := by
  rw [growthEdgeOnSamePly.phaseStep_eq_relationPhaseStep,
    same_ply_second_relation_grows]
  rfl

theorem one_move_settles_two_independent_phases :
    RelationPhaseEdge.settleMany 1 retainedLaw chosenPly
        [pressureEdge, growthEdgeOnSamePly] = [1, 3] ∧
      turnRelation ≠ emptyOpponentTurnRelation := by
  constructor
  · change [pressureEdge.phaseStep, growthEdgeOnSamePly.phaseStep] =
      [1, 3]
    rw [pressure_phase_is_quarter_turn,
      same_ply_second_phase_is_inverse_quarter_turn]
  · exact same_ply_relations_are_source_distinct

/-! ## Equal freedom is the exact negative control -/

def alwaysTrueRelation : RelationProbe 2 where
  holds := fun _ => true

def equalLineage : RelationLineage 0 retainedLaw emptyReplay
    alwaysTrueRelation .impose :=
  .marked emptyReplay alwaysTrueRelation (by trivial)

def equalEdge : RelationPhaseEdge 0 retainedLaw chosenPly where
  sourceRelation := alwaysTrueRelation
  sourceState := .impose
  sourceLineage := equalLineage

theorem equal_freedom_has_no_fabricated_attack_or_handoff :
    equalEdge.comparison = .equal ∧
      ¬ equalEdge.AttackAt ∧
      ¬ equalEdge.InitiativeHandoffAt ∧
      TacticalPhase.rotation equalEdge.phaseStep = 1 := by
  have equalComparison : equalEdge.comparison = .equal := by decide
  refine ⟨equalComparison, ?_, ?_, ?_⟩
  · unfold RelationPhaseEdge.AttackAt
    rw [equalComparison]
    decide
  · unfold RelationPhaseEdge.InitiativeHandoffAt
    unfold RelationPhaseEdge.targetState
    rw [equalComparison]
    decide
  · rw [equalEdge.phaseStep_eq_relationPhaseStep, equalComparison]
    exact TacticalPhase.rotation_zero

end G4TacticalPhaseRegression
end Go
end ProcessGame
end SaturationMonoid
