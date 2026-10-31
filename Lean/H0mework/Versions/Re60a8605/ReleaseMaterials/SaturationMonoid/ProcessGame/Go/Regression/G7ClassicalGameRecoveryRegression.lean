import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.NormalFormProjection
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G3SearchExposureRegression

/-!
# G7 finite classical-game recovery regression

The empty 2×2 generated replay recovers a two-ply finite extensive game.
Concrete legal, illegal, cutoff, two-pass and resignation histories exercise
the public recovery mouth, while the strategy and payoff squares consume the
direct native evaluator.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G7ClassicalGameRecoveryRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open _root_.SaturationMonoid.ProcessGame.Go.Classical
open G3SearchExposureRegression

def recoveredGame : FiniteExtensiveGame emptyReplay 2 :=
  recoverExtensiveGame emptyReplay 2

def cutoffGame : FiniteExtensiveGame emptyReplay 0 :=
  recoverExtensiveGame emptyReplay 0

theorem recovered_players_are_exact_generated_lineages :
    recoveredGame.players =
        [emptyReplay.player .positive, emptyReplay.player .negative] ∧
      recoveredGame.players.Nodup ∧
      ∀ player : recoveredGame.Player, player ∈ recoveredGame.players :=
  ⟨rfl, recoveredGame.players_nodup, recoveredGame.player_mem_players⟩

theorem history_membership_is_exact_bounded_execution
    (word : List (Move 2)) :
    word ∈ recoveredGame.historyWords ↔
      word.length ≤ 2 ∧
        (replayFrom? testLaw emptyReplay.final word).isSome = true :=
  recoveredGame.mem_historyWords_iff word

theorem root_and_one_play_are_histories :
    ([] : List (Move 2)) ∈ recoveredGame.historyWords ∧
      [Move.play p00] ∈ recoveredGame.historyWords := by
  constructor
  · exact recoveredGame.rootHistory.2
  · apply (recoveredGame.mem_historyWords_iff _).mpr
    exact ⟨by decide, by decide⟩

theorem overlong_and_illegal_words_are_rejected :
    ([.pass, .pass, .resign] : List (Move 2)) ∉
        recoveredGame.historyWords ∧
      ([Move.play p00, Move.play p00] : List (Move 2)) ∉
        recoveredGame.historyWords := by
  constructor
  · intro member
    exact (by decide : ¬ ([.pass, .pass, .resign] : List (Move 2)).length ≤ 2)
      ((recoveredGame.mem_historyWords_iff _).mp member).1
  · intro member
    have executes := ((recoveredGame.mem_historyWords_iff _).mp member).2
    exact (by decide :
      (replayFrom? testLaw emptyReplay.final
        [Move.play p00, Move.play p00]).isSome ≠ true) executes

theorem root_owner_and_actions_are_native :
    recoveredGame.owner? recoveredGame.rootHistory =
        some (emptyReplay.player .positive) ∧
      Move.play p00 ∈ recoveredGame.actions recoveredGame.rootHistory ∧
      (.pass : Move 2) ∈ recoveredGame.actions recoveredGame.rootHistory ∧
      (.resign : Move 2) ∈ recoveredGame.actions recoveredGame.rootHistory := by
  constructor
  · apply recoveredGame.owner?_eq_some_generatedPlayer_toMove_of_playing
    decide
  · constructor
    · apply (recoveredGame.mem_actions_iff _ _).mpr
      exact ⟨by decide, playTarget, chosenPly.step⟩
    · constructor
      · apply (recoveredGame.mem_actions_iff_nativeStep_isSome _ _).mpr
        exact ⟨by decide, by decide⟩
      · apply (recoveredGame.mem_actions_iff_nativeStep_isSome _ _).mpr
        exact ⟨by decide, by decide⟩

def playedHistory : recoveredGame.History :=
  recoveredGame.historyOfGeneratedReplay chosenPly.extended (by decide)

theorem played_history_is_exact_and_factors_through_tree :
    playedHistory.word = [Move.play p00] ∧
      playedHistory.current = chosenPly.extended.final ∧
      ∃ continuation : GeneratedReplay testLaw emptyReplay.final
          playedHistory.word,
        continuation.final = playedHistory.current ∧
          continuation.stateTrace ∈ rootedPaths recoveredGame.stateTree :=
  ⟨rfl, recoveredGame.historyOfGeneratedReplay_current _ _,
    playedHistory.factors_through_stateTree⟩

theorem recovered_stateTree_is_exact_futureCone :
    recoveredGame.stateTree = futureConeAt emptyReplay 2 ∧
      recoveredGame.stateTree.root = emptyReplay.final ∧
      LegalExposure testLaw recoveredGame.stateTree :=
  ⟨recoveredGame.stateTree_eq_futureConeAt,
    recoveredGame.stateTree_root,
    recoveredGame.stateTree_legal⟩

/-- Direct consumer of the inherited `RootedAccountedUnfolding.fold_unique`
mouth on the exact recovered state tree. -/
theorem recovered_root_evaluator_is_unique :
    recoveredGame.stateTree.root =
      recoveredGame.stateTree.fold (fun origin _children => origin) := by
  apply recoveredGame.stateTree_fold_unique
    (fun origin _children => origin) RootedAccountedUnfolding.root
  intro origin branches
  rfl

theorem zero_fuel_playing_leaf_is_cutoff_not_terminal :
    FiniteExtensiveGame.PlayingCutoff cutoffGame.rootHistory ∧
      ¬ FiniteExtensiveGame.WorldTerminal cutoffGame.rootHistory ∧
      cutoffGame.actions cutoffGame.rootHistory = [] ∧
      cutoffGame.owner? cutoffGame.rootHistory =
        some (emptyReplay.player .positive) := by
  have cutoff : FiniteExtensiveGame.PlayingCutoff cutoffGame.rootHistory := by
    exact ⟨rfl, by decide⟩
  exact ⟨cutoff, FiniteExtensiveGame.playingCutoff_not_worldTerminal cutoff,
    rfl, cutoffGame.owner?_eq_some_generatedPlayer_toMove_of_playing _
      (by decide)⟩

def twoPassMoves : List (Move 2) := [.pass, .pass]

theorem twoPass_generated_isSome :
    (generate? testLaw 2 twoPassMoves).isSome = true := by
  decide

def twoPassReplay :
    GeneratedReplay testLaw (Frame.initial 2) twoPassMoves :=
  (generate? testLaw 2 twoPassMoves).get twoPass_generated_isSome

def twoPassHistory : recoveredGame.History :=
  recoveredGame.historyOfGeneratedReplay twoPassReplay (by decide)

theorem two_pass_is_world_terminal_with_scoreMargin_payoff :
    twoPassHistory.current.visible.status = .terminal .twoPasses ∧
      recoveredGame.owner? twoPassHistory = none ∧
      FiniteExtensiveGame.WorldTerminal twoPassHistory ∧
      recoveredGame.payoff twoPassHistory
          (emptyReplay.player .positive) =
        some (scoreMargin testLaw twoPassHistory.current.visible.board) ∧
      recoveredGame.payoff twoPassHistory
          (emptyReplay.player .negative) =
        some (-scoreMargin testLaw twoPassHistory.current.visible.board) := by
  have terminal :
      twoPassHistory.current.visible.status = .terminal .twoPasses := by
    decide
  refine ⟨terminal,
    recoveredGame.owner?_eq_none_of_terminal twoPassHistory .twoPasses terminal,
    ⟨.twoPasses, terminal⟩, ?_, ?_⟩
  · simp [FiniteExtensiveGame.payoff_generatedPlayer_eq_direct,
      FiniteExtensiveGame.directTerminalPayoff, terminal]
  · simp [FiniteExtensiveGame.payoff_generatedPlayer_eq_direct,
      FiniteExtensiveGame.directTerminalPayoff, terminal]

def resignMoves : List (Move 2) := [.resign]

theorem resign_generated_isSome :
    (generate? testLaw 2 resignMoves).isSome = true := by
  decide

def resignReplay :
    GeneratedReplay testLaw (Frame.initial 2) resignMoves :=
  (generate? testLaw 2 resignMoves).get resign_generated_isSome

def resignHistory : recoveredGame.History :=
  recoveredGame.historyOfGeneratedReplay resignReplay (by decide)

theorem resignation_payoff_uses_generated_winner :
    resignHistory.current.visible.status =
        .terminal (.resignation .negative) ∧
      recoveredGame.payoff resignHistory
          (emptyReplay.player .positive) = some (-1) ∧
      recoveredGame.payoff resignHistory
          (emptyReplay.player .negative) = some 1 := by
  decide

def exactResignProfile : recoveredGame.StrategyProfile :=
  recoveredGame.resignProfile

theorem strategy_and_payoff_commute_with_direct_process :
    (FiniteExtensiveGame.evaluateHistory exactResignProfile 2
        recoveredGame.rootHistory).current =
      FiniteExtensiveGame.directProcessEvaluate exactResignProfile 2
        recoveredGame.rootHistory ∧
    recoveredGame.payoff
        (FiniteExtensiveGame.evaluateHistory exactResignProfile 2
          recoveredGame.rootHistory)
        (emptyReplay.player .negative) =
      FiniteExtensiveGame.directTerminalPayoff testLaw
        (FiniteExtensiveGame.directProcessEvaluate exactResignProfile 2
          recoveredGame.rootHistory) .negative :=
  ⟨FiniteExtensiveGame.evaluateHistory_current_eq_directProcessEvaluate
      exactResignProfile 2 recoveredGame.rootHistory,
    FiniteExtensiveGame.evaluatePayoff_commutes
      exactResignProfile 2 recoveredGame.rootHistory .negative⟩

theorem strategy_search_does_not_write_actual_authority :
    emptyReplay.toOccurrence.trace = emptyReplay.stateTrace ∧
      emptyReplay.toOccurrence.trace.map
          (fun frame => frame.visible.situation) =
        emptyReplay.final.positionHistory ∧
      Nonempty (GeneratedDancersAt emptyReplay) :=
  recoveredGame.strategyEvaluation_actual_noninterference exactResignProfile 2

def recoveredNormalForm : NormalFormProjection recoveredGame :=
  toNormalForm recoveredGame

theorem normal_form_coordinates_are_generated :
    recoveredNormalForm.Player = recoveredGame.Player ∧
      (∀ player : recoveredNormalForm.Player,
        recoveredNormalForm.StrategyFor player =
          recoveredGame.PureStrategy player) ∧
      recoveredNormalForm.Profile = recoveredGame.StrategyProfile :=
  ⟨rfl, fun _ => rfl, rfl⟩

theorem normal_form_utility_commutes_and_uses_evaluated_payoff :
    recoveredNormalForm.utility exactResignProfile
        (emptyReplay.player .negative) =
      recoveredNormalForm.directUtility exactResignProfile
        (emptyReplay.player .negative) ∧
    recoveredNormalForm.utility exactResignProfile
        (emptyReplay.player .negative) = some 1 := by
  constructor
  · exact recoveredNormalForm.utility_commutes_with_directProcess
      exactResignProfile (emptyReplay.player .negative)
  · decide

end G7ClassicalGameRecoveryRegression
end Go
end ProcessGame
end SaturationMonoid
