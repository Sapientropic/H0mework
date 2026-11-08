import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G1GeneratedTimeReplayRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G2GeneratedDancersRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G2NoPartialSplitRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G3ActualPossibilityRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G4TacticalPhaseRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G5PrincipalHolonomyRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G6StrategicGroupRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G6MoveCoherenceRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G6KataGoConsumerRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G7ClassicalGameRecoveryRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.Classical.G7CrossOccurrenceClassicalResidualRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.GoProcessGameRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.ThreeAgentH1ProcessGameRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.OntologyFaceRegression
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.DomainReuseRegression

/-!
# G8 whole-program regression

This file is a dependency sink for G1--G8.  Every theorem directly consumes a
signed regression mouth; it defines no new producer, process carrier, player,
ledger, ontology or future field.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Regression
namespace G8WholeProgramRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Go
open AffineRelaxation
open Go.G1RulesRegression

/-! ## G1--G7 direct checkpoint consumers -/

def g1CompleteReplay := Go.G1RulesRegression.completeReplay
def g1Final : Frame 2 := g1CompleteReplay.final
def g1FinalCursor : ReplayCursor 2 := ⟨some g1Final, []⟩

theorem G1_generated_time_replay_reaches_the_same_occurrence_fold :
    (reflexiveQueryIteratedTimeField
      (generatedReplayQuery halfKomiLaw)
      { current := some (Frame.initial 2),
        remaining := completeMoves }).stateAt
        completeMoves.length =
      g1FinalCursor ∧
    some g1Final =
      some (g1CompleteReplay.toOccurrence.fold
        GeneratedReplay.finalAlgebra) :=
  ⟨G1GeneratedTimeReplayRegression.completeReplay_timeField_final,
    G1GeneratedTimeReplayRegression.completeReplay_p99_endpoint_is_occurrence_fold⟩

theorem G2_generated_dancers_and_universal_actual_no_split :
    (∃! generated : GeneratedReplay.GeneratedPlayer
        G2GroupLineageRegression.bridgePly.extended,
      G2GroupLineageRegression.bridgePly.extended.EventOwnedBy
        G2GeneratedDancersRegression.bridgeMoveIndex generated) ∧
      (∀ {n : Nat} {fixedLaw : Law} {moves : List (Move n)}
          {replay : GeneratedReplay fixedLaw (Frame.initial n) moves},
        (ply : GeneratedReplay.ActualPly replay) →
          IsEmpty (ActualSplitDisposition ply)) :=
  ⟨G2GeneratedDancersRegression.bridge_move_owner_unique,
    fun ply =>
      G2NoPartialSplitRegression.every_actual_ply_has_no_partial_group_split ply⟩

theorem G3_actual_child_and_unchosen_future_share_only_the_source_frontier :
    G3ActualPossibilityRegression.chosenPly.target ∈
        (rootedPossibilityAt G3ActualPossibilityRegression.emptyReplay).frontier ∧
      G3ActualPossibilityRegression.passTarget ∈
        (rootedPossibilityAt G3ActualPossibilityRegression.emptyReplay).frontier ∧
      G3ActualPossibilityRegression.chosenPly.extended.stateTrace =
        G3ActualPossibilityRegression.emptyReplay.stateTrace ++
          [G3ActualPossibilityRegression.chosenPly.target] ∧
      Nonempty (GeneratedDancersAt
        G3ActualPossibilityRegression.chosenPly.extended) := by
  have separated := G3ActualPossibilityRegression.chosen_unchosen_exact_separation
  exact ⟨separated.1, separated.2.1, separated.2.2.1,
    separated.2.2.2.2⟩

theorem G4_relation_phase_generates_attack_recovery_counterattack_and_C4 :
    G4TacticalPhaseRegression.pressureEdge.AttackAt ∧
      G4TacticalPhaseRegression.responseDefense.recovery.recoveredWord =
        [(.resign : Move 2)] ∧
      G4TacticalPhaseRegression.opponentResponseEdge.AttackAt ∧
      G4TacticalPhaseRegression.opponentResponseEdge.ConstraintOwnerFlipAt ∧
      TacticalPhase.compose
          G4TacticalPhaseRegression.responseEdge.phaseStep
          G4TacticalPhaseRegression.pressureEdge.phaseStep = 0 :=
  ⟨G4TacticalPhaseRegression.pressure_is_generated_attack,
    G4TacticalPhaseRegression.response_is_exact_defense.1,
    G4TacticalPhaseRegression.counterattack_recovers_and_compresses_opponent.2.1,
    G4TacticalPhaseRegression.counterattack_recovers_and_compresses_opponent.2.2,
    G4TacticalPhaseRegression.pressure_response_C4_composition⟩

theorem G5_exact_ko_path_generates_discrete_and_topological_holonomy :
    PrincipalHolonomyObstruction
        (Ko.koPrincipalTransition .positionalSuperko) ∧
      TopologicalPrincipalHolonomyObstruction Ko.projectedLoopCover
        (Ko.topologicalKoPrincipalTransition .positionalSuperko) ∧
      principalTriangleHolonomy
          (Ko.koPrincipalTransition .positionalSuperko)
          .source .lifted .returned ≠ 1 :=
  ⟨G5PrincipalHolonomyRegression.all_three_repetition_laws_have_principal_obstruction.2.1,
    G5PrincipalHolonomyRegression.all_three_topological_obstructions.2.1,
    G5PrincipalHolonomyRegression.positional_projected_loop_keeps_lifted_difference.2.2.2.2⟩

theorem G6_strategic_closure_makesSense_and_external_consumer :
    IsEmpty (ActualSplitDisposition G6StrategicGroupRegression.blockPly) ∧
      closureGain G6ClosureGainRegression.gainUpdate = 2 ∧
      MultiPurposeMove G6ClosureGainRegression.gainUpdate ∧
      MakesSense G6ClosureGainRegression.gainUpdate ∧
      MoveCoherent G6ClosureGainRegression.gainUpdate ∧
      ExternalScoreAndClosurePrefer
        G6KataGoConsumerRegression.c2Observation
        G6KataGoConsumerRegression.b3Observation :=
  ⟨G6StrategicGroupRegression.actual_block_splits_only_the_strategic_group.2.2,
    G6ClosureGainRegression.one_move_two_obligations_gain_gt_one.1,
    G6ClosureGainRegression.one_move_two_obligations_gain_gt_one.2,
    G6MoveCoherenceRegression.multipurpose_update_makes_sense_and_is_coherent.1,
    G6MoveCoherenceRegression.multipurpose_update_makes_sense_and_is_coherent.2,
    G6KataGoConsumerRegression.katago_and_generated_closure_prefer_c2⟩

theorem G7_recovery_normal_form_and_crossOccurrence_strict_residual :
    Classical.FiniteExtensiveGame.PlayingCutoff
        G7ClassicalGameRecoveryRegression.cutoffGame.rootHistory ∧
      ¬ Classical.FiniteExtensiveGame.WorldTerminal
        G7ClassicalGameRecoveryRegression.cutoffGame.rootHistory ∧
      G7ClassicalGameRecoveryRegression.recoveredNormalForm.utility
          G7ClassicalGameRecoveryRegression.exactResignProfile
          (G3SearchExposureRegression.emptyReplay.player .negative) =
        G7ClassicalGameRecoveryRegression.recoveredNormalForm.directUtility
          G7ClassicalGameRecoveryRegression.exactResignProfile
          (G3SearchExposureRegression.emptyReplay.player .negative) ∧
      Go.CrossOccurrencePathResidual.koTerminalReplay.toOccurrence ≠
        Go.CrossOccurrencePathResidual.freshTerminalReplay.toOccurrence ∧
      Nonempty (Classical.CrossReplayNormalFormEquivalence
        Go.CrossOccurrencePathResidual.koTerminalReplay
        Go.CrossOccurrencePathResidual.freshTerminalReplay 1) ∧
      Go.CrossOccurrencePathResidual.actualizationK
          Go.CrossOccurrencePathResidual.koTerminalReplay ≠
        Go.CrossOccurrencePathResidual.actualizationK
          Go.CrossOccurrencePathResidual.freshTerminalReplay ∧
      Go.CrossOccurrenceClassicalResidual.Forget 1
          Go.CrossOccurrenceClassicalResidual.koPath =
        Go.CrossOccurrenceClassicalResidual.Forget 1
          Go.CrossOccurrenceClassicalResidual.freshPath ∧
      ¬ ∃ reconstruct : Classical.NormalFormProjection
          (Classical.terminalGame
            Go.CrossOccurrencePathResidual.koTerminalReplay 1) →
            Go.CrossOccurrenceClassicalResidual.PathIndex,
        Function.LeftInverse reconstruct
          (Go.CrossOccurrenceClassicalResidual.Forget 1) :=
  ⟨G7ClassicalGameRecoveryRegression.zero_fuel_playing_leaf_is_cutoff_not_terminal.1,
    G7ClassicalGameRecoveryRegression.zero_fuel_playing_leaf_is_cutoff_not_terminal.2.1,
    G7ClassicalGameRecoveryRegression.normal_form_utility_commutes_and_uses_evaluated_payoff.1,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.1,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.2.1,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.2.2.1,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.2.2.2.1,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.2.2.2.2.2⟩

/-! ## G8 simultaneous whole-program mouth -/

theorem G8_source_only_core_and_all_dependent_faces_close_together :
    some g1Final =
        some (g1CompleteReplay.toOccurrence.fold
          GeneratedReplay.finalAlgebra) ∧
      IsEmpty (ActualSplitDisposition G2GroupLineageRegression.bridgePly) ∧
      G3ActualPossibilityRegression.chosenPly.target ∈
        (rootedPossibilityAt
          G3ActualPossibilityRegression.emptyReplay).frontier ∧
      G4TacticalPhaseRegression.pressureEdge.AttackAt ∧
      PrincipalHolonomyObstruction
        Go.CrossOccurrencePathResidual.crossOccurrenceTransition ∧
      TopologicalPrincipalHolonomyObstruction Go.Ko.projectedLoopCover
        Go.CrossOccurrencePathResidual.topologicalCrossOccurrenceTransition ∧
      MakesSense G6ClosureGainRegression.gainUpdate ∧
      GoProcessGameRegression.game.occurrence =
        GoProcessGameRegression.replay.toOccurrence ∧
      Function.Bijective
        (Go.goGeneratedActorEquiv GoProcessGameRegression.replay) ∧
      CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover ThreeCycleTime Int)
        threeCyclePhaseCochain ∧
      (∀ cochain,
        ThreeAgentRingCohomologous threeCyclePhaseCochain cochain →
          (threeAgentFoldReadout cochain).value =
            (threeAgentFoldReadout threeCyclePhaseCochain).value) ∧
      AtomFailure
        (semanticObligationSemantics
          OntologyFaceRegression.semanticBoolIdentityPrimitive.sevenFacetPredicates)
        OntologyFaceRegression.sourceFailureState
        (OntologyFaceRegression.identityOntologyFace.cascadeOntologyIso.atomEquiv
          OntologyFaceRegression.sourceFailureAtom) ∧
      DomainReuseRegression.firstCoalitionMember.admission =
        DomainReuseRegression.firstAdmission ∧
      DomainReuseRegression.firstAncestryIndividual.division.child = 1 ∧
      DomainReuseRegression.interactionActor0.agent = .t0 ∧
      DomainReuseRegression.interactionActor1.agent = .t1 ∧
      DomainReuseRegression.interactionActor2.agent = .t2 ∧
      Go.CrossOccurrencePathResidual.koTerminalReplay.toOccurrence ≠
        Go.CrossOccurrencePathResidual.freshTerminalReplay.toOccurrence ∧
      Nonempty (Classical.CrossReplayNormalFormEquivalence
        Go.CrossOccurrencePathResidual.koTerminalReplay
        Go.CrossOccurrencePathResidual.freshTerminalReplay 1) ∧
      Go.CrossOccurrencePathResidual.actualizationK
          Go.CrossOccurrencePathResidual.koTerminalReplay ≠
        Go.CrossOccurrencePathResidual.actualizationK
          Go.CrossOccurrencePathResidual.freshTerminalReplay ∧
      Go.CrossOccurrenceClassicalResidual.Forget 1
          Go.CrossOccurrenceClassicalResidual.koPath =
        Go.CrossOccurrenceClassicalResidual.Forget 1
          Go.CrossOccurrenceClassicalResidual.freshPath ∧
      ¬ ∃ reconstruct : Classical.NormalFormProjection
          (Classical.terminalGame
            Go.CrossOccurrencePathResidual.koTerminalReplay 1) →
            Go.CrossOccurrenceClassicalResidual.PathIndex,
        Function.LeftInverse reconstruct
          (Go.CrossOccurrenceClassicalResidual.Forget 1) :=
  ⟨G1_generated_time_replay_reaches_the_same_occurrence_fold.2,
    G2NoPartialSplitRegression.every_actual_ply_has_no_partial_group_split
      G2GroupLineageRegression.bridgePly,
    G3_actual_child_and_unchosen_future_share_only_the_source_frontier.1,
    G4_relation_phase_generates_attack_recovery_counterattack_and_C4.1,
    Go.CrossOccurrencePathResidual.crossOccurrence_P259_obstruction_nonflat_and_transportMismatch.1,
    Go.CrossOccurrencePathResidual.crossOccurrence_P260_obstruction_nonflat_and_transportMismatch.2.1,
    G6MoveCoherenceRegression.multipurpose_update_makes_sense_and_is_coherent.1,
    GoProcessGameRegression.occurrence_and_actual_history_commute.1,
    GoProcessGameRegression.generic_actor_equiv_is_existing_generated_player.2.2,
    ThreeAgentH1ProcessGameRegression.concrete_foldReadout_generates_P116_and_P117.1,
    ThreeAgentH1ProcessGameRegression.foldReadout_value_is_P121_cohomology_invariant,
    OntologyFaceRegression.source_failure_consumes_p133_and_p179_support.2,
    DomainReuseRegression.economic_generated_actor_image_is_admission_lineage.1,
    DomainReuseRegression.biological_generated_actor_image_is_ancestry_lineage.2.2.1,
    DomainReuseRegression.multi_agent_generated_actor_image_is_three_exposed_lineages.1,
    DomainReuseRegression.multi_agent_generated_actor_image_is_three_exposed_lineages.2.1,
    DomainReuseRegression.multi_agent_generated_actor_image_is_three_exposed_lineages.2.2,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.1,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.2.1,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.2.2.1,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.2.2.2.1,
    Go.G7CrossOccurrenceClassicalResidualRegression.G7_strongest_mouth_has_no_caller_premises.2.2.2.2.2⟩

end G8WholeProgramRegression
end Regression
end ProcessGame
end SaturationMonoid
