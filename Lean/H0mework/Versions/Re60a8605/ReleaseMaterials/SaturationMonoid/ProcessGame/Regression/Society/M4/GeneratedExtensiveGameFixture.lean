import Mathlib.Data.Fintype.BigOperators
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Recovery.GeneratedStrategicGame

/-!
# M4 non-Go generated extensive-game fixture

The closed source syntax has three participating M0 players, heterogeneous
M2 strategy fibres of sizes one, two and three, both terminal and cutoff
profiles, and settlement coordinates `5`, `-3`, and `0`.  These concrete
values belong only to this consumer fixture; the production mouth is universal.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M4GeneratedExtensiveGameRegression

noncomputable section

open _root_.SaturationMonoid.ProcessGame.Society.Classical
open Classical.Source Classical.Source.FreeStrategicSyntax

def cardinalSkeleton : FreeStrategicSyntax where
  playerCount := 3
  strategyCounts := [1, 2, 3]
  terminalFlags := []
  settlementValues := []
  authorityResiduals := []

theorem cardinalSkeleton_profile_card :
    Fintype.card cardinalSkeleton.CanonicalProfile = 6 := by
  classical
  rw [Fintype.card_pi]
  decide

noncomputable def terminalFlagStream : List Bool :=
  List.ofFn fun index : Fin 6 => decide (index.val ≠ 0)

noncomputable def settlementValueStream : List ℚ :=
  List.ofFn fun index : Fin (Fintype.card cardinalSkeleton.OutcomeIndex) =>
    let outcome := cardinalSkeleton.outcomeEquivFin.symm index
    if outcome.2.val = 0 then 5
    else if outcome.2.val = 1 then -3
    else 0

noncomputable def program : FreeStrategicSyntax := {
  cardinalSkeleton with
  terminalFlags := terminalFlagStream
  settlementValues := settlementValueStream
}

theorem program_profile_card :
    Fintype.card program.CanonicalProfile = 6 := by
  classical
  rw [Fintype.card_pi]
  decide

@[simp] theorem program_profileEquivFin_eq_cardinalSkeleton :
    program.profileEquivFin = cardinalSkeleton.profileEquivFin := rfl

@[simp] theorem program_outcomeEquivFin_eq_cardinalSkeleton :
    program.outcomeEquivFin = cardinalSkeleton.outcomeEquivFin := rfl

def player0 : program.Player := ⟨0, by simp [program, cardinalSkeleton]⟩
def player1 : program.Player := ⟨1, by simp [program, cardinalSkeleton]⟩
def player2 : program.Player := ⟨2, by simp [program, cardinalSkeleton]⟩

noncomputable def cutoffCanonicalProfile : program.CanonicalProfile :=
  program.profileEquivFin.symm
    ⟨0, by rw [program_profile_card]; decide⟩

noncomputable def terminalCanonicalProfile : program.CanonicalProfile :=
  program.profileEquivFin.symm
    ⟨1, by rw [program_profile_card]; decide⟩

@[simp] theorem cutoffCanonicalProfile_index :
    program.profileIndex cutoffCanonicalProfile = 0 := by
  exact congrArg Fin.val
    (program.profileEquivFin.apply_symm_apply
      ⟨0, by rw [program_profile_card]; decide⟩)

@[simp] theorem terminalCanonicalProfile_index :
    program.profileIndex terminalCanonicalProfile = 1 := by
  exact congrArg Fin.val
    (program.profileEquivFin.apply_symm_apply
      ⟨1, by rw [program_profile_card]; decide⟩)

theorem cutoff_profile_is_not_world_terminal :
    program.isWorldTerminal cutoffCanonicalProfile = false := by
  rw [FreeStrategicSyntax.isWorldTerminal, cutoffCanonicalProfile_index]
  simp [program, terminalFlagStream]

theorem terminal_profile_is_world_terminal :
    program.isWorldTerminal terminalCanonicalProfile = true := by
  rw [FreeStrategicSyntax.isWorldTerminal, terminalCanonicalProfile_index]
  simp [program, terminalFlagStream]

theorem settlementValue_eq_player_readout
    (profile : program.CanonicalProfile) (player : program.Player) :
    program.settlementValue profile player =
      if player.val = 0 then 5
      else if player.val = 1 then -3
      else 0 := by
  unfold FreeStrategicSyntax.settlementValue
  rw [show program.outcomeIndex (profile, player) =
      (cardinalSkeleton.outcomeEquivFin (profile, player)).val by rfl]
  have bound :
      (cardinalSkeleton.outcomeEquivFin (profile, player)).val <
        Fintype.card cardinalSkeleton.OutcomeIndex :=
    (cardinalSkeleton.outcomeEquivFin (profile, player)).isLt
  have bound' :
      (cardinalSkeleton.outcomeEquivFin (profile, player)).val <
        (∏ candidate : cardinalSkeleton.Player,
          cardinalSkeleton.strategyCount candidate) *
            cardinalSkeleton.playerCount := by
    simpa only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin] using bound
  simp [program, settlementValueStream, bound']

theorem terminal_settlement_values_are_positive_negative_zero :
    program.settlementValue terminalCanonicalProfile player0 = 5 ∧
      program.settlementValue terminalCanonicalProfile player1 = -3 ∧
      program.settlementValue terminalCanonicalProfile player2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [settlementValue_eq_player_readout]
    simp [player0]
  · rw [settlementValue_eq_player_readout]
    simp [player1]
  · rw [settlementValue_eq_player_readout]
    simp [player2]

def game : GeneratedFiniteExtensiveGame program := recoverExtensiveGame program

def generatedPlayer0 : game.Player := program.generatedPlayerOf player0
def generatedPlayer1 : game.Player := program.generatedPlayerOf player1
def generatedPlayer2 : game.Player := program.generatedPlayerOf player2

theorem exactly_three_M0_players : Fintype.card game.Player = 3 := by
  calc
    Fintype.card game.Player = Fintype.card program.Player :=
      Fintype.card_congr program.generatedPlayerEquiv
    _ = 3 := by
      change Fintype.card (Fin 3) = 3
      simp

theorem M2_strategy_fibres_are_heterogeneous :
    Fintype.card (game.StrategyFor generatedPlayer0) = 1 ∧
      Fintype.card (game.StrategyFor generatedPlayer1) = 2 ∧
      Fintype.card (game.StrategyFor generatedPlayer2) = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      Fintype.card (game.StrategyFor generatedPlayer0) =
          Fintype.card (program.Strategy
            (program.generatedPlayerIndex generatedPlayer0)) :=
        Fintype.card_congr (program.generatedStrategyEquiv
          (program.generatedPlayerIndex generatedPlayer0))
      _ = 1 := by change Fintype.card (Fin 1) = 1; simp
  · calc
      Fintype.card (game.StrategyFor generatedPlayer1) =
          Fintype.card (program.Strategy
            (program.generatedPlayerIndex generatedPlayer1)) :=
        Fintype.card_congr (program.generatedStrategyEquiv
          (program.generatedPlayerIndex generatedPlayer1))
      _ = 2 := by change Fintype.card (Fin 2) = 2; simp
  · calc
      Fintype.card (game.StrategyFor generatedPlayer2) =
          Fintype.card (program.Strategy
            (program.generatedPlayerIndex generatedPlayer2)) :=
        Fintype.card_congr (program.generatedStrategyEquiv
          (program.generatedPlayerIndex generatedPlayer2))
      _ = 3 := by change Fintype.card (Fin 3) = 3; simp

def terminalProfile : game.Profile :=
  program.generatedProfileOfCanonical terminalCanonicalProfile

def cutoffProfile : game.Profile :=
  program.generatedProfileOfCanonical cutoffCanonicalProfile

@[simp] theorem terminalProfile_canonical :
    program.generatedProfileEquivCanonical terminalProfile =
      terminalCanonicalProfile :=
  program.generatedProfileEquivCanonical.right_inv terminalCanonicalProfile

theorem terminalProfile_is_generated_world_terminal :
    program.isWorldTerminal
        (program.generatedProfileEquivCanonical terminalProfile) = true := by
  rw [terminalProfile_canonical]
  exact terminal_profile_is_world_terminal

end
end M4GeneratedExtensiveGameRegression
end Society
end ProcessGame
end SaturationMonoid
