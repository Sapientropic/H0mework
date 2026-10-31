import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Classical.Recovery.EssentialSurjectivity

/-!
# M4 essential-surjectivity boundary consumers

The public universal existential mouth is consumed at three boundary shapes:
zero players with a terminal outcome, zero players with a cutoff outcome, and
one real player whose sole strategy fibre is empty.  The last target has no
global profile at all.
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

/-- Pull one target utility observation back through a strong recovered-game
isomorphism. -/
theorem recoveredUtility_at_target
    {target : FiniteStrategicGame} {code : ValidCode}
    (iso : StrategicGameIso (recovered code) target)
    (profile : target.Profile) (player : target.Player) :
    (recovered code).utility (iso.profileEquiv.symm profile)
        (iso.playerEquiv.symm player) =
      target.utility profile player := by
  simpa using
    (iso.utility_preserved (iso.profileEquiv.symm profile)
      (iso.playerEquiv.symm player)).symm

/-- The complete optional outcome, not only a payoff coordinate, commutes at
the target profile selected through the inverse profile equivalence. -/
theorem recoveredOutcome_map_at_target
    {target : FiniteStrategicGame} {code : ValidCode}
    (iso : StrategicGameIso (recovered code) target)
    (profile : target.Profile) :
    target.outcome profile =
      ((recovered code).outcome (iso.profileEquiv.symm profile)).map
        (reindexPayoff iso.playerEquiv) := by
  simpa using iso.outcome_preserved (iso.profileEquiv.symm profile)

/-! ## Empty-player boundary -/

abbrev EmptyPlayer := Fin 0
abbrev EmptyStrategy (_player : EmptyPlayer) := Unit
abbrev EmptyProfile := (player : EmptyPlayer) → EmptyStrategy player

def emptyProfile : EmptyProfile := fun _ => ()

def emptyPayoff : EmptyPlayer → ℚ := fun player => Fin.elim0 player

/-- A no-player game whose unique profile is world-terminal. -/
def zeroPlayerTerminalGame : FiniteStrategicGame where
  Player := EmptyPlayer
  playerFintype := inferInstance
  playerDecidableEq := inferInstance
  Strategy := EmptyStrategy
  strategyFintype := fun _ => inferInstance
  strategyDecidableEq := fun _ => inferInstance
  outcome := fun _ => some emptyPayoff

/-- A no-player game whose unique profile is an observation cutoff. -/
def zeroPlayerCutoffGame : FiniteStrategicGame where
  Player := EmptyPlayer
  playerFintype := inferInstance
  playerDecidableEq := inferInstance
  Strategy := EmptyStrategy
  strategyFintype := fun _ => inferInstance
  strategyDecidableEq := fun _ => inferInstance
  outcome := fun _ => none

theorem zeroPlayerTerminalGame_has_no_player :
    ¬ Nonempty zeroPlayerTerminalGame.Player := by
  rintro ⟨player⟩
  exact Fin.elim0 player

theorem zeroPlayerCutoffGame_has_no_player :
    ¬ Nonempty zeroPlayerCutoffGame.Player := by
  rintro ⟨player⟩
  exact Fin.elim0 player

structure ZeroPlayerTerminalBridgeObservations
    (code : ValidCode)
    (iso : StrategicGameIso (recovered code) zeroPlayerTerminalGame) : Prop where
  targetTerminal :
    zeroPlayerTerminalGame.outcome emptyProfile = some emptyPayoff
  targetHasNoPlayer : ¬ Nonempty zeroPlayerTerminalGame.Player
  recoveredTerminal :
    ∃ payoffs,
      (recovered code).outcome (iso.profileEquiv.symm emptyProfile) =
        some payoffs

theorem zeroPlayerTerminalGame_has_generated_preimage :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) zeroPlayerTerminalGame,
        ZeroPlayerTerminalBridgeObservations code iso := by
  rcases recovery_essentially_surjective zeroPlayerTerminalGame with
    ⟨code, ⟨iso⟩⟩
  have recoveredTerminal :
      ∃ payoffs,
        (recovered code).outcome (iso.profileEquiv.symm emptyProfile) =
          some payoffs := by
    have mapped := recoveredOutcome_map_at_target iso emptyProfile
    change some emptyPayoff = _ at mapped
    have sourceNe :
        (recovered code).outcome (iso.profileEquiv.symm emptyProfile) ≠
          none := by
      intro empty
      rw [empty] at mapped
      simp at mapped
    cases result :
        (recovered code).outcome (iso.profileEquiv.symm emptyProfile) with
    | none => exact False.elim (sourceNe result)
    | some payoffs => exact ⟨payoffs, rfl⟩
  exact ⟨code, iso,
    ⟨rfl, zeroPlayerTerminalGame_has_no_player, recoveredTerminal⟩⟩

structure ZeroPlayerCutoffBridgeObservations
    (code : ValidCode)
    (iso : StrategicGameIso (recovered code) zeroPlayerCutoffGame) : Prop where
  targetCutoff : zeroPlayerCutoffGame.outcome emptyProfile = none
  targetHasNoPlayer : ¬ Nonempty zeroPlayerCutoffGame.Player
  recoveredCutoff :
    (recovered code).outcome (iso.profileEquiv.symm emptyProfile) = none

theorem zeroPlayerCutoffGame_has_generated_preimage :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) zeroPlayerCutoffGame,
        ZeroPlayerCutoffBridgeObservations code iso := by
  rcases recovery_essentially_surjective zeroPlayerCutoffGame with
    ⟨code, ⟨iso⟩⟩
  have mapped := recoveredOutcome_map_at_target iso emptyProfile
  have recoveredCutoff :
      (recovered code).outcome (iso.profileEquiv.symm emptyProfile) =
        none :=
    Option.map_eq_none_iff.mp mapped.symm
  exact ⟨code, iso,
    ⟨rfl, zeroPlayerCutoffGame_has_no_player, recoveredCutoff⟩⟩

/-! ## Existing player with an empty strategy fibre -/

abbrev OnePlayer := Fin 1
abbrev NoStrategy (_player : OnePlayer) := Empty

/-- This game has a real player but no global strategy profile.  Consequently
its outcome function is eliminated from the impossible profile itself. -/
def emptyStrategyFibreGame : FiniteStrategicGame where
  Player := OnePlayer
  playerFintype := inferInstance
  playerDecidableEq := inferInstance
  Strategy := NoStrategy
  strategyFintype := fun _ => inferInstance
  strategyDecidableEq := fun _ => inferInstance
  outcome := fun profile => Empty.elim (profile (0 : OnePlayer))

theorem emptyStrategyFibreGame_has_player :
    Nonempty emptyStrategyFibreGame.Player := by
  change Nonempty OnePlayer
  exact ⟨0⟩

theorem emptyStrategyFibreGame_has_no_profile :
    ¬ Nonempty emptyStrategyFibreGame.Profile := by
  rintro ⟨profile⟩
  exact Empty.elim (profile (0 : OnePlayer))

structure EmptyStrategyFibreBridgeObservations
    (code : ValidCode)
    (iso : StrategicGameIso (recovered code) emptyStrategyFibreGame) : Prop where
  targetHasPlayer : Nonempty emptyStrategyFibreGame.Player
  targetHasNoProfile : ¬ Nonempty emptyStrategyFibreGame.Profile
  recoveredFibreIsEmpty :
    ¬ Nonempty ((recovered code).Strategy
      (iso.playerEquiv.symm (0 : OnePlayer)))

/-- Essential surjectivity reaches a target with an existing player and an
empty strategy fibre; no hidden inhabited-profile premise can be present. -/
theorem emptyStrategyFibreGame_has_generated_preimage :
    ∃ code : ValidCode,
      ∃ iso : StrategicGameIso (recovered code) emptyStrategyFibreGame,
        EmptyStrategyFibreBridgeObservations code iso := by
  rcases recovery_essentially_surjective emptyStrategyFibreGame with
    ⟨code, ⟨iso⟩⟩
  have recoveredFibreIsEmpty :
      ¬ Nonempty ((recovered code).Strategy
        (iso.playerEquiv.symm (0 : OnePlayer))) := by
    rintro ⟨strategy⟩
    exact Empty.elim
      (iso.strategyEquiv (iso.playerEquiv.symm (0 : OnePlayer)) strategy)
  exact ⟨code, iso,
    ⟨emptyStrategyFibreGame_has_player,
      emptyStrategyFibreGame_has_no_profile, recoveredFibreIsEmpty⟩⟩

end
end M4EssentialSurjectivityRegression
end Society
end ProcessGame
end SaturationMonoid
