import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M4.EssentialSurjectivityBoundaryRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Independent.AsymmetricFourPlayerGame

/-!
# M4 essential-surjectivity direct consumer

The regression enters recovery only through its public universal existential
mouth.  It obtains actual source codes and strong isomorphisms for two
independently presented asymmetric games, then imports the separately checked
boundary consumers into one certificate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M4EssentialSurjectivityRegression

noncomputable section

open Classical.Independent
open Classical.Recovery
open Classical.Recovery.EssentialSurjectivity
open Classical.Source

open Classical.Independent.AsymmetricFourPlayerGame

theorem playerZeroOneProfile_world_terminal :
    game.outcome playerZeroOneProfile =
      some (payoff playerZeroOneProfile) := by
  simp [game, outcome, playerZeroOneProfile,
    baseProfile_playerTwo_ne_last]

theorem base_playerOne_utility :
    game.utility baseProfile playerOne = some (-3) := by
  unfold FiniteStrategicGame.utility
  rw [baseProfile_world_terminal]
  change some (payoff baseProfile playerOne) = some (-3)
  rw [payoff_base_playerOne]

theorem base_playerTwo_utility :
    game.utility baseProfile playerTwo = some 5 := by
  unfold FiniteStrategicGame.utility
  rw [baseProfile_world_terminal]
  change some (payoff baseProfile playerTwo) = some 5
  rw [payoff_base_playerTwo]

theorem playerZeroOne_utility :
    game.utility playerZeroOneProfile playerZero = some 1 := by
  unfold FiniteStrategicGame.utility
  rw [playerZeroOneProfile_world_terminal]
  change
    some (payoff playerZeroOneProfile playerZero) = some 1
  rw [payoff_playerZeroOne_playerZero]

theorem playerZero_utility_is_nonconstant :
    game.utility baseProfile playerZero ≠
      game.utility playerZeroOneProfile playerZero := by
  rw [base_playerZero_utility, playerZeroOne_utility]
  intro equal
  have impossible : (0 : ℚ) = 1 := Option.some.inj equal
  have distinct : (0 : ℚ) ≠ 1 := by decide
  exact distinct impossible

structure AsymmetricBridgeObservations
    (code : ValidCode) (iso : StrategicGameIso (recovered code) game) : Prop where
  targetBaseTerminal :
    game.outcome baseProfile = some (payoff baseProfile)
  targetCutoff : game.outcome cutoffProfile = none
  recoveredBaseTerminal :
    ∃ payoffs,
      (recovered code).outcome (iso.profileEquiv.symm baseProfile) =
        some payoffs
  recoveredCutoff :
    (recovered code).outcome (iso.profileEquiv.symm cutoffProfile) = none
  recoveredLoss :
    (recovered code).utility (iso.profileEquiv.symm baseProfile)
        (iso.playerEquiv.symm playerOne) = some (-3)
  recoveredGain :
    (recovered code).utility (iso.profileEquiv.symm baseProfile)
        (iso.playerEquiv.symm playerTwo) = some 5
  recoveredUtilityNonconstant :
    (recovered code).utility (iso.profileEquiv.symm baseProfile)
        (iso.playerEquiv.symm playerZero) ≠
      (recovered code).utility (iso.profileEquiv.symm playerZeroOneProfile)
        (iso.playerEquiv.symm playerZero)
  targetPayoffShape :
    payoff baseProfile playerOne < 0 ∧
      0 < payoff baseProfile playerTwo ∧
      payoff baseProfile playerZero ≠
        payoff playerZeroOneProfile playerZero

/-- The first independent target is reached through the final universal
existential theorem.  The resulting witness is immediately consumed together
with both outcome branches and the mixed, nonconstant utility observations. -/
theorem asymmetricGame_has_generated_preimage :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) game,
        AsymmetricBridgeObservations code iso := by
  rcases recovery_essentially_surjective game with ⟨code, ⟨iso⟩⟩
  have recoveredBaseTerminal :
      ∃ payoffs,
        (recovered code).outcome (iso.profileEquiv.symm baseProfile) =
          some payoffs := by
    have mapped := recoveredOutcome_map_at_target iso baseProfile
    cases result :
        (recovered code).outcome (iso.profileEquiv.symm baseProfile) with
    | none => simp [result, baseProfile_world_terminal] at mapped
    | some payoffs => exact ⟨payoffs, rfl⟩
  have recoveredCutoff :
      (recovered code).outcome (iso.profileEquiv.symm cutoffProfile) =
        none := by
    have mapped := recoveredOutcome_map_at_target iso cutoffProfile
    rw [cutoffProfile_is_cutoff] at mapped
    exact Option.map_eq_none_iff.mp mapped.symm
  have recoveredLoss :
      (recovered code).utility (iso.profileEquiv.symm baseProfile)
          (iso.playerEquiv.symm playerOne) = some (-3) := by
    calc
      _ = game.utility (show game.Profile from baseProfile)
          (show game.Player from playerOne) :=
        recoveredUtility_at_target iso
          (show game.Profile from baseProfile)
          (show game.Player from playerOne)
      _ = some (-3) := base_playerOne_utility
  have recoveredGain :
      (recovered code).utility (iso.profileEquiv.symm baseProfile)
          (iso.playerEquiv.symm playerTwo) = some 5 := by
    calc
      _ = game.utility (show game.Profile from baseProfile)
          (show game.Player from playerTwo) :=
        recoveredUtility_at_target iso
          (show game.Profile from baseProfile)
          (show game.Player from playerTwo)
      _ = some 5 := base_playerTwo_utility
  have recoveredZero :
      (recovered code).utility (iso.profileEquiv.symm baseProfile)
          (iso.playerEquiv.symm playerZero) = some 0 := by
    calc
      _ = game.utility (show game.Profile from baseProfile)
          (show game.Player from playerZero) :=
        recoveredUtility_at_target iso
          (show game.Profile from baseProfile)
          (show game.Player from playerZero)
      _ = some 0 := base_playerZero_utility
  have recoveredOne :
      (recovered code).utility (iso.profileEquiv.symm playerZeroOneProfile)
          (iso.playerEquiv.symm playerZero) = some 1 := by
    calc
      _ = game.utility (show game.Profile from playerZeroOneProfile)
          (show game.Player from playerZero) :=
        recoveredUtility_at_target iso
          (show game.Profile from playerZeroOneProfile)
          (show game.Player from playerZero)
      _ = some 1 := playerZeroOne_utility
  have recoveredNonconstant :
      (recovered code).utility (iso.profileEquiv.symm baseProfile)
          (iso.playerEquiv.symm playerZero) ≠
        (recovered code).utility (iso.profileEquiv.symm playerZeroOneProfile)
          (iso.playerEquiv.symm playerZero) := by
    rw [recoveredZero, recoveredOne]
    intro equal
    have impossible : (0 : ℚ) = 1 := Option.some.inj equal
    have distinct : (0 : ℚ) ≠ 1 := by decide
    exact distinct impossible
  exact ⟨code, iso,
    ⟨baseProfile_world_terminal, cutoffProfile_is_cutoff,
      recoveredBaseTerminal, recoveredCutoff, recoveredLoss, recoveredGain,
      recoveredNonconstant, mixed_sign_and_nonconstant⟩⟩

structure AlteredBridgeObservations
    (code : ValidCode)
    (iso : StrategicGameIso (recovered code) alteredGame) : Prop where
  targetUtility : alteredGame.utility baseProfile playerZero = some 7
  recoveredUtility :
    (recovered code).utility (iso.profileEquiv.symm baseProfile)
        (iso.playerEquiv.symm playerZero) = some 7
  anchoredDistinct :
    ¬ ∃ bridge : StrategicGameIso game alteredGame,
      PreservesBaseObservable bridge

/-- The payoff-altered independent target has its own generated preimage,
while the anchored observable still prevents confusion with the first game. -/
theorem alteredGame_has_generated_preimage :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) alteredGame,
        AlteredBridgeObservations code iso := by
  rcases recovery_essentially_surjective alteredGame with
    ⟨code, ⟨iso⟩⟩
  have recoveredUtility :
      (recovered code).utility (iso.profileEquiv.symm baseProfile)
          (iso.playerEquiv.symm playerZero) = some 7 := by
    calc
      _ = alteredGame.utility (show alteredGame.Profile from baseProfile)
          (show alteredGame.Player from playerZero) :=
        recoveredUtility_at_target iso
          (show alteredGame.Profile from baseProfile)
          (show alteredGame.Player from playerZero)
      _ = some 7 := altered_base_playerZero_utility
  exact ⟨code, iso,
    ⟨altered_base_playerZero_utility, recoveredUtility,
      no_strong_iso_preserving_base_observable⟩⟩

structure EssentialSurjectivityDirectCertificate : Prop where
  asymmetric :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) game,
        AsymmetricBridgeObservations code iso
  altered :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) alteredGame,
        AlteredBridgeObservations code iso
  emptyTerminal :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) zeroPlayerTerminalGame,
        ZeroPlayerTerminalBridgeObservations code iso
  emptyCutoff :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) zeroPlayerCutoffGame,
        ZeroPlayerCutoffBridgeObservations code iso
  emptyStrategyFibre :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) emptyStrategyFibreGame,
        EmptyStrategyFibreBridgeObservations code iso

/-- One sink consumes both independent targets, both outcome branches, the
anchored payoff negative, both zero-player games, and an existing player with
an empty strategy fibre. -/
theorem essentialSurjectivityDirectConsumer :
    EssentialSurjectivityDirectCertificate where
  asymmetric := asymmetricGame_has_generated_preimage
  altered := alteredGame_has_generated_preimage
  emptyTerminal := zeroPlayerTerminalGame_has_generated_preimage
  emptyCutoff := zeroPlayerCutoffGame_has_generated_preimage
  emptyStrategyFibre := emptyStrategyFibreGame_has_generated_preimage

end
end M4EssentialSurjectivityRegression
end Society
end ProcessGame
end SaturationMonoid
