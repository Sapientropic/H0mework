import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.NormalFormEquivalence
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.CrossOccurrencePathResidual

/-!
# G7 cross-replay normal-form equivalence regression

The two exact terminal replays have equal generated visible states but
different emitted paths, position histories and rooted occurrences.  The
production transporter therefore uses equivalences for `N`, `Sᵢ` and
profiles and proves utility preservation; it never casts the replay indices
to equality.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G7NormalFormEquivalenceRegression

open _root_.SaturationMonoid.ProcessGame.Go.Classical
open CrossOccurrencePathResidual

def horizon : Nat := 2

def normalEquivalence :
    CrossReplayNormalFormEquivalence
      koTerminalReplay freshTerminalReplay horizon :=
  terminalNormalFormEquivalence koTerminalReplay freshTerminalReplay
    horizon (.resignation .negative) terminal_visible_eq terminal_status_eq.1

theorem transporter_preserves_distinct_actual_occurrences :
    koTerminalReplay.final.visible = freshTerminalReplay.final.visible ∧
      koTerminalReplay.final.positionHistory ≠
        freshTerminalReplay.final.positionHistory ∧
      koTerminalReplay.toOccurrence ≠ freshTerminalReplay.toOccurrence :=
  terminal_paths_close_classically_but_not_actually

theorem generated_player_coordinate_N_is_equivalent :
    normalEquivalence.playerEquiv
          (koTerminalReplay.player .positive) =
        freshTerminalReplay.player .positive ∧
      normalEquivalence.playerEquiv
          (koTerminalReplay.player .negative) =
        freshTerminalReplay.player .negative ∧
      (terminalNormalForm koTerminalReplay horizon).players.map
          normalEquivalence.playerEquiv =
        (terminalNormalForm freshTerminalReplay horizon).players :=
  ⟨crossReplayPlayerEquiv_player _ _ _ _,
    crossReplayPlayerEquiv_player _ _ _ _,
    normalEquivalence.players_map⟩

theorem every_strategy_fibre_Si_and_profile_are_equivalent :
    (∀ player : (terminalNormalForm koTerminalReplay horizon).Player,
      Function.Bijective (normalEquivalence.strategyEquiv player)) ∧
      Function.Bijective normalEquivalence.profileEquiv :=
  ⟨fun player => (normalEquivalence.strategyEquiv player).bijective,
    normalEquivalence.profileEquiv.bijective⟩

def koProfile :
    (terminalNormalForm koTerminalReplay horizon).Profile :=
  (terminalGame koTerminalReplay horizon).resignProfile

def freshTransportedProfile :
    (terminalNormalForm freshTerminalReplay horizon).Profile :=
  normalEquivalence.profileEquiv koProfile

theorem transported_profile_is_fibrewise_strategy_transport
    (player : (terminalNormalForm koTerminalReplay horizon).Player) :
    freshTransportedProfile.strategy (normalEquivalence.playerEquiv player) =
      normalEquivalence.strategyEquiv player (koProfile.strategy player) :=
  normalEquivalence.profile_strategy_commutes koProfile player

theorem every_utility_ui_is_preserved
    (player : (terminalNormalForm koTerminalReplay horizon).Player) :
    (terminalNormalForm freshTerminalReplay horizon).utility
        freshTransportedProfile (normalEquivalence.playerEquiv player) =
      (terminalNormalForm koTerminalReplay horizon).utility
        koProfile player :=
  normalEquivalence.utility_preserved koProfile player

theorem positive_and_negative_terminal_utilities_are_exact_and_preserved :
    (terminalNormalForm koTerminalReplay horizon).utility koProfile
          (koTerminalReplay.player .positive) = some (-1) ∧
      (terminalNormalForm freshTerminalReplay horizon).utility
          freshTransportedProfile
          (normalEquivalence.playerEquiv
            (koTerminalReplay.player .positive)) = some (-1) ∧
      (terminalNormalForm koTerminalReplay horizon).utility koProfile
          (koTerminalReplay.player .negative) = some 1 ∧
      (terminalNormalForm freshTerminalReplay horizon).utility
          freshTransportedProfile
          (normalEquivalence.playerEquiv
            (koTerminalReplay.player .negative)) = some 1 := by
  have positiveLeft :
      (terminalNormalForm koTerminalReplay horizon).utility koProfile
          (koTerminalReplay.player .positive) = some (-1) := by
    rw [terminalNormalForm_utility_eq_directTerminalPayoff horizon
      (.resignation .negative) terminal_status_eq.1]
    decide
  have negativeLeft :
      (terminalNormalForm koTerminalReplay horizon).utility koProfile
          (koTerminalReplay.player .negative) = some 1 := by
    rw [terminalNormalForm_utility_eq_directTerminalPayoff horizon
      (.resignation .negative) terminal_status_eq.1]
    decide
  exact ⟨positiveLeft,
    (every_utility_ui_is_preserved
      (koTerminalReplay.player .positive)).trans positiveLeft,
    negativeLeft,
    (every_utility_ui_is_preserved
      (koTerminalReplay.player .negative)).trans negativeLeft⟩

end G7NormalFormEquivalenceRegression
end Go
end ProcessGame
end SaturationMonoid
