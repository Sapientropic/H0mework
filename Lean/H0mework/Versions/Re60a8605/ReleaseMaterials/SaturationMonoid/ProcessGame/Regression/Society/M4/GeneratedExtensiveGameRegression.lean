import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M4.GeneratedExtensiveGameFixture

/-!
# M4 generated extensive-game authority regression

This direct consumer keeps search subordinate to one source occurrence and
connects the fixture's M0 players and M2 actions to exact history restrictions,
terminal/cutoff markers, and one fully fulfilled M3 exchange settlement.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M4GeneratedExtensiveGameRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations
open _root_.SaturationMonoid.ProcessGame.Society.Classical
open Classical.Source Classical.Source.FreeStrategicSyntax
open Classical.GeneratedTerminalExchange
open _root_.SaturationMonoid.ProcessGame.Society.Exchange
open _root_.SaturationMonoid.ProcessGame.Society.Settlement
open Settlement.SourceOwnedSettlementCompiler

theorem every_player_has_exact_M0_M2_participation :
    ∀ player : game.Player,
      program.relationCompiler.GeneratedInterestAt player.1
        (program.generatedRelation (program.generatedPlayerIndex player)) :=
  program.generatedPlayer_has_exact_participation_relation

theorem root_is_playing : game.Playing game.rootHistory := by
  change 0 < 3
  decide

def rootAction : game.ActionAt game.rootHistory root_is_playing :=
  program.generatedStrategyOf ⟨0, root_is_playing⟩
    ⟨0, by simp [program, cardinalSkeleton,
      FreeStrategicSyntax.strategyCount]⟩

theorem root_action_is_M2_generated_and_exact :
    rootAction.1 ∈ program.relationCompiler.actionableFutureCodesAt
          (program.generatedRelation rootAction.1.1) .source ∧
      (game.exactActionRestrictionAt game.rootHistory root_is_playing
          rootAction).1 = rootAction.1 ∧
      program.actionAtom rootAction.1 ∈ program.occurrence.trace := by
  refine ⟨rootAction.2, game.action_is_exact_occurrence_restriction
    game.rootHistory root_is_playing rootAction⟩

def terminalHistory : game.History := game.historyOfProfile terminalProfile
def cutoffHistory : game.History := game.historyOfProfile cutoffProfile

theorem terminal_history_actions_have_exact_source_restrictions :
    ∀ index : Fin terminalHistory.1.1.val,
      ∃ restriction : program.ExactActionRestriction,
        restriction.1 = terminalHistory.1.2 index ∧
          program.actionAtom restriction.1 ∈ program.occurrence.trace :=
  game.history_actions_are_exact_occurrence_restrictions terminalHistory

theorem authority_tree_evaluator_is_unique :
    game.authorityTree.root =
      game.authorityTree.fold (fun atom _children => atom) := by
  apply game.authorityTree_fold_unique
    (fun atom _children => atom) RootedAccountedUnfolding.root
  intro atom branches
  rfl

def terminalRestriction : program.ExactWorldTerminalRestriction :=
  program.generatedTerminalRestriction terminalProfile
    terminalProfile_is_generated_world_terminal

@[simp] theorem terminalRestriction_profile :
    Classical.GeneratedTerminalExchange.terminalProfile
        program terminalRestriction = terminalCanonicalProfile := by
  change program.generatedProfileEquivCanonical terminalProfile =
    terminalCanonicalProfile
  exact terminalProfile_canonical

theorem terminal_and_cutoff_status_are_distinct :
    game.status terminalHistory = .worldTerminal ∧
      game.status cutoffHistory = .cutoff := by
  constructor
  · have notPlaying : ¬ game.Playing terminalHistory := by
      intro playing
      have complete := game.historyOfProfile_complete terminalProfile
      exact (Nat.lt_irrefl program.playerCount) (complete ▸ playing)
    have canonical :
        game.canonicalProfileOfComplete terminalHistory
            (by exact game.historyOfProfile_complete terminalProfile) =
          terminalCanonicalProfile := by
      calc
        _ = program.generatedProfileEquivCanonical terminalProfile :=
          game.canonicalProfile_historyOfProfile terminalProfile
        _ = terminalCanonicalProfile := terminalProfile_canonical
    simp [GeneratedFiniteExtensiveGame.status, notPlaying, canonical,
      terminal_profile_is_world_terminal]
  · have notPlaying : ¬ game.Playing cutoffHistory := by
      intro playing
      have complete := game.historyOfProfile_complete cutoffProfile
      exact (Nat.lt_irrefl program.playerCount) (complete ▸ playing)
    have canonical :
        game.canonicalProfileOfComplete cutoffHistory
            (by exact game.historyOfProfile_complete cutoffProfile) =
          cutoffCanonicalProfile := by
      calc
        _ = program.generatedProfileEquivCanonical cutoffProfile :=
          game.canonicalProfile_historyOfProfile cutoffProfile
        _ = cutoffCanonicalProfile :=
          program.generatedProfileEquivCanonical.right_inv cutoffCanonicalProfile
    simp [GeneratedFiniteExtensiveGame.status, notPlaying, canonical,
      cutoff_profile_is_not_world_terminal]

theorem terminal_and_cutoff_have_exact_markers_and_outcomes :
    (∃ restriction : program.ExactWorldTerminalRestriction,
      restriction.1.1 = terminalCanonicalProfile ∧
        program.worldTerminalAtom restriction.1.1 ∈ program.occurrence.trace) ∧
      (∃ restriction : program.ExactCutoffRestriction,
        restriction.1.1 = cutoffCanonicalProfile ∧
          program.cutoffAtom restriction.1.1 ∈ program.occurrence.trace) ∧
      (∃ payoffs,
        game.outcome terminalProfile = some payoffs ∧
          payoffs generatedPlayer0 = 5 ∧ payoffs generatedPlayer1 = -3) ∧
      game.outcome cutoffProfile = none := by
  have cutoffCanonical :
      program.generatedProfileEquivCanonical cutoffProfile =
        cutoffCanonicalProfile :=
    program.generatedProfileEquivCanonical.right_inv cutoffCanonicalProfile
  have cutoffGenerated :
      program.isWorldTerminal
          (program.generatedProfileEquivCanonical cutoffProfile) = false := by
    rw [cutoffCanonical]
    exact cutoff_profile_is_not_world_terminal
  refine ⟨?_, ?_, ?_,
    program.generatedOutcome_eq_none_of_cutoff cutoffProfile cutoffGenerated⟩
  · rcases program.generatedOutcome_has_exact_world_terminal_restriction
      terminalProfile terminalProfile_is_generated_world_terminal with
      ⟨restriction, profileEq, inTrace⟩
    exact ⟨restriction, profileEq.trans terminalProfile_canonical, inTrace⟩
  · rcases program.generatedOutcome_has_exact_cutoff_restriction
      cutoffProfile cutoffGenerated with ⟨restriction, profileEq, inTrace⟩
    exact ⟨restriction, profileEq.trans cutoffCanonical, inTrace⟩
  · let payoffs : game.Player → ℚ := fun player =>
      program.settlementValue terminalCanonicalProfile
        (program.generatedPlayerIndex player)
    refine ⟨payoffs, ?_, ?_, ?_⟩
    · change program.generatedOutcome terminalProfile = some payoffs
      rw [program.generatedOutcome_eq_some_of_terminal
        terminalProfile terminalProfile_is_generated_world_terminal]
      apply congrArg some
      funext player
      rw [terminalProfile_canonical]
    · change program.settlementValue terminalCanonicalProfile player0 = 5
      exact terminal_settlement_values_are_positive_negative_zero.1
    · change program.settlementValue terminalCanonicalProfile player1 = -3
      exact terminal_settlement_values_are_positive_negative_zero.2.1

structure WholeExchangeSettlementCertificate : Prop where
  fullyFulfilled : Nonempty (FullyFulfilledExchangeAt
    (terminalSettlementCompiler program)
    (terminalSettlement program terminalRestriction))
  outcome_reads_fulfilled_legs :
    game.outcome terminalProfile = some (fun player =>
      (terminalFulfilledPlayerLeg program terminalRestriction
        (program.generatedPlayerIndex player)).obligation.residual)
  exact_player_bearer : ∀ player : game.Player,
    (terminalFulfilledPlayerLeg program terminalRestriction
      (program.generatedPlayerIndex player)).obligation.bearer = player.1
  positive_residual :
    (terminalFulfilledPlayerLeg program terminalRestriction player0).obligation.residual =
      (5 : ℚ)
  negative_residual :
    (terminalFulfilledPlayerLeg program terminalRestriction player1).obligation.residual =
      (-3 : ℚ)
  zero_residual :
    (terminalFulfilledPlayerLeg program terminalRestriction player2).obligation.residual =
      (0 : ℚ)
  no_open_settlement : IsEmpty (OpenSettlementAt
    (terminalSettlementCompiler program)
    (terminalSettlement program terminalRestriction))

theorem terminal_outcome_is_fully_fulfilled_whole_exchange :
    WholeExchangeSettlementCertificate := by
  have whole := game.outcome_is_M3_exchange_settlement_fold
    terminalProfile terminalProfile_is_generated_world_terminal
  refine {
    fullyFulfilled := whole.1
    outcome_reads_fulfilled_legs := whole.2.1
    exact_player_bearer := whole.2.2
    positive_residual := ?_
    negative_residual := ?_
    zero_residual := ?_
    no_open_settlement := terminalSettlement_open_isEmpty program terminalRestriction }
  · change terminalUtility program terminalRestriction player0 = 5
    rw [terminalUtility_eq_settlementValue, terminalRestriction_profile]
    exact terminal_settlement_values_are_positive_negative_zero.1
  · change terminalUtility program terminalRestriction player1 = -3
    rw [terminalUtility_eq_settlementValue, terminalRestriction_profile]
    exact terminal_settlement_values_are_positive_negative_zero.2.1
  · change terminalUtility program terminalRestriction player2 = 0
    rw [terminalUtility_eq_settlementValue, terminalRestriction_profile]
    exact terminal_settlement_values_are_positive_negative_zero.2.2

theorem cutoff_has_exact_restriction_but_no_terminal_exchange :
    (∃ restriction : program.ExactCutoffRestriction,
      restriction.1.1 = cutoffCanonicalProfile ∧
        program.cutoffAtom restriction.1.1 ∈ program.occurrence.trace) ∧
      ¬ ∃ terminal : program.ExactWorldTerminalRestriction,
        terminal.1.1 = cutoffCanonicalProfile := by
  refine ⟨terminal_and_cutoff_have_exact_markers_and_outcomes.2.1, ?_⟩
  rintro ⟨terminal, profileEq⟩
  have terminalAtCutoff :
      program.isWorldTerminal cutoffCanonicalProfile = true := by
    rw [← profileEq]
    exact terminal.1.2
  rw [cutoff_profile_is_not_world_terminal] at terminalAtCutoff
  cases terminalAtCutoff

theorem search_preserves_actual_source_occurrence :
    program.processGame.occurrence = program.occurrence ∧
      program.occurrence.trace = .origin :: program.programEvents ∧
      FreeClassicalAtom.origin ∈ program.occurrence.trace :=
  game.search_actual_noninterference terminalProfile

structure GeneratedExtensiveGameCertificate : Prop where
  recovered : game = recoverExtensiveGame program
  player_count : Fintype.card game.Player = 3
  strategy0_count : Fintype.card (game.StrategyFor generatedPlayer0) = 1
  strategy1_count : Fintype.card (game.StrategyFor generatedPlayer1) = 2
  strategy2_count : Fintype.card (game.StrategyFor generatedPlayer2) = 3
  participation : ∀ player : game.Player,
    program.relationCompiler.GeneratedInterestAt player.1
      (program.generatedRelation (program.generatedPlayerIndex player))
  root_action_exact : rootAction.1 ∈
      program.relationCompiler.actionableFutureCodesAt
        (program.generatedRelation rootAction.1.1) .source ∧
    (game.exactActionRestrictionAt game.rootHistory root_is_playing rootAction).1 =
      rootAction.1 ∧
    program.actionAtom rootAction.1 ∈ program.occurrence.trace
  history_exact : ∀ index : Fin terminalHistory.1.1.val,
    ∃ restriction : program.ExactActionRestriction,
      restriction.1 = terminalHistory.1.2 index ∧
        program.actionAtom restriction.1 ∈ program.occurrence.trace
  fold_unique : game.authorityTree.root =
    game.authorityTree.fold (fun atom _children => atom)
  terminal_status : game.status terminalHistory = .worldTerminal
  cutoff_status : game.status cutoffHistory = .cutoff
  terminal_marker : ∃ restriction : program.ExactWorldTerminalRestriction,
    restriction.1.1 = terminalCanonicalProfile ∧
      program.worldTerminalAtom restriction.1.1 ∈ program.occurrence.trace
  cutoff_marker : ∃ restriction : program.ExactCutoffRestriction,
    restriction.1.1 = cutoffCanonicalProfile ∧
      program.cutoffAtom restriction.1.1 ∈ program.occurrence.trace
  cutoff_no_terminal : ¬ ∃ terminal : program.ExactWorldTerminalRestriction,
    terminal.1.1 = cutoffCanonicalProfile
  terminal_payoffs : ∃ payoffs,
    game.outcome terminalProfile = some payoffs ∧
      payoffs generatedPlayer0 = 5 ∧ payoffs generatedPlayer1 = -3
  cutoff_outcome : game.outcome cutoffProfile = none
  whole_exchange : WholeExchangeSettlementCertificate
  search_occurrence : program.processGame.occurrence = program.occurrence
  search_trace : program.occurrence.trace = .origin :: program.programEvents

theorem generated_extensive_game_end_to_end :
    GeneratedExtensiveGameCertificate where
  recovered := rfl
  player_count := exactly_three_M0_players
  strategy0_count := M2_strategy_fibres_are_heterogeneous.1
  strategy1_count := M2_strategy_fibres_are_heterogeneous.2.1
  strategy2_count := M2_strategy_fibres_are_heterogeneous.2.2
  participation := every_player_has_exact_M0_M2_participation
  root_action_exact := root_action_is_M2_generated_and_exact
  history_exact := terminal_history_actions_have_exact_source_restrictions
  fold_unique := authority_tree_evaluator_is_unique
  terminal_status := terminal_and_cutoff_status_are_distinct.1
  cutoff_status := terminal_and_cutoff_status_are_distinct.2
  terminal_marker := terminal_and_cutoff_have_exact_markers_and_outcomes.1
  cutoff_marker := cutoff_has_exact_restriction_but_no_terminal_exchange.1
  cutoff_no_terminal := cutoff_has_exact_restriction_but_no_terminal_exchange.2
  terminal_payoffs := terminal_and_cutoff_have_exact_markers_and_outcomes.2.2.1
  cutoff_outcome := terminal_and_cutoff_have_exact_markers_and_outcomes.2.2.2
  whole_exchange := terminal_outcome_is_fully_fulfilled_whole_exchange
  search_occurrence := search_preserves_actual_source_occurrence.1
  search_trace := search_preserves_actual_source_occurrence.2.1

end
end M4GeneratedExtensiveGameRegression
end Society
end ProcessGame
end SaturationMonoid
