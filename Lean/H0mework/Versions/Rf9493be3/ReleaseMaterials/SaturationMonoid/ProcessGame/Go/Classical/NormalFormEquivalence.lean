import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.NormalFormProjection

/-!
# Cross-replay terminal normal-form equivalence

Two different actual replays are not identified.  When their generated final
visible positions agree and are terminal, this module transports the
classical normal-form coordinates across the two dependent replay indices:
generated players, pure-strategy fibres/profiles and utilities.

The transporter never equates the replay occurrences or their histories and
accepts no target player, strategy family, utility table or residual.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Classical

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u

def terminalGame {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) : FiniteExtensiveGame replay horizon :=
  recoverExtensiveGame replay horizon

def terminalNormalForm {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) : NormalFormProjection (terminalGame replay horizon) :=
  toNormalForm (terminalGame replay horizon)

/-- Generated-player transport through the common polarity lineage gauge. -/
def crossReplayPlayerEquiv {n : Nat} {law : Law}
    {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) :
    (terminalNormalForm left horizon).Player ≃
      (terminalNormalForm right horizon).Player :=
  left.generatedPlayerEquiv.symm.trans right.generatedPlayerEquiv

@[simp] theorem crossReplayPlayerEquiv_player
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) (control : Polarity) :
    crossReplayPlayerEquiv left right horizon (left.player control) =
      right.player control :=
  rfl

@[simp] theorem crossReplayPlayerEquiv_control
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat)
    (player : (terminalNormalForm left horizon).Player) :
    (crossReplayPlayerEquiv left right horizon player).1.control =
      player.1.control :=
  rfl

/-- Terminal histories contain only the root word, independently of the
occurrence history hidden in the replay index. -/
theorem terminalHistory_eq_rootHistory
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} (game : FiniteExtensiveGame replay horizon)
    (reason : TerminalReason)
    (terminal : replay.final.visible.status = .terminal reason)
    (history : game.History) :
    history = game.rootHistory := by
  apply Subtype.ext
  change history.word = []
  cases wordEq : history.word with
  | nil => rfl
  | cons move tail =>
      have executes := history.executes
      rw [wordEq] at executes
      cases move <;>
        simp [replayFrom?, nativeStep?, stepVisible?, playVisible?,
          passVisible?, resignVisible?, terminal] at executes

theorem terminalOwner_eq_none
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} (game : FiniteExtensiveGame replay horizon)
    (reason : TerminalReason)
    (terminal : replay.final.visible.status = .terminal reason)
    (history : game.History) :
    game.owner? history = none := by
  rw [terminalHistory_eq_rootHistory game reason terminal history]
  apply game.owner?_eq_none_of_terminal game.rootHistory reason
  simpa using terminal

/-- History-fibre transport is a legitimate equivalence, not dependent type
equality: both terminal fibres contract to their generated root histories. -/
def terminalHistoryEquiv
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) (reason : TerminalReason)
    (leftTerminal : left.final.visible.status = .terminal reason)
    (rightTerminal : right.final.visible.status = .terminal reason) :
    (terminalGame left horizon).History ≃
      (terminalGame right horizon).History where
  toFun := fun _ => (terminalGame right horizon).rootHistory
  invFun := fun _ => (terminalGame left horizon).rootHistory
  left_inv := fun history => (terminalHistory_eq_rootHistory
    (terminalGame left horizon) reason leftTerminal history).symm
  right_inv := fun history => (terminalHistory_eq_rootHistory
    (terminalGame right horizon) reason rightTerminal history).symm

theorem terminalNextHistory_eq_none
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} (game : FiniteExtensiveGame replay horizon)
    (reason : TerminalReason)
    (terminal : replay.final.visible.status = .terminal reason)
    (profile : game.StrategyProfile) (history : game.History) :
    profile.nextHistory? history = none := by
  simp [FiniteExtensiveGame.StrategyProfile.nextHistory?,
    terminalOwner_eq_none game reason terminal history]

theorem terminalEvaluateHistory_eq_self
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} (game : FiniteExtensiveGame replay horizon)
    (reason : TerminalReason)
    (terminal : replay.final.visible.status = .terminal reason)
    (profile : game.StrategyProfile) (fuel : Nat)
    (history : game.History) :
    game.evaluateHistory profile fuel history = history := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp [FiniteExtensiveGame.evaluateHistory,
        terminalNextHistory_eq_none game reason terminal profile history]

theorem terminalNormalForm_utility_eq_directTerminalPayoff
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (horizon : Nat) (reason : TerminalReason)
    (terminal : replay.final.visible.status = .terminal reason)
    (profile : (terminalNormalForm replay horizon).Profile)
    (player : (terminalNormalForm replay horizon).Player) :
    (terminalNormalForm replay horizon).utility profile player =
      FiniteExtensiveGame.directTerminalPayoff law replay.final
        player.1.control := by
  unfold NormalFormProjection.utility
  rw [terminalEvaluateHistory_eq_self (terminalGame replay horizon)
    reason terminal profile horizon (terminalGame replay horizon).rootHistory]
  unfold FiniteExtensiveGame.payoff
  rw [(terminalGame replay horizon).rootHistory_current]

private theorem pureStrategy_ext_choose
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} {game : FiniteExtensiveGame replay horizon}
    {player : game.Player}
    {left right : game.PureStrategy player}
    (chooseEq : left.choose = right.choose) :
    left = right := by
  cases left
  cases right
  simpa only [FiniteExtensiveGame.PureStrategy.mk.injEq] using chooseEq

/-- Pure-strategy fibre equivalence transported through the terminal history
equivalence.  Legality is discharged from exact terminal ownership, not from
an equality of dependent history types. -/
def terminalPureStrategyEquiv
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) (reason : TerminalReason)
    (leftTerminal : left.final.visible.status = .terminal reason)
    (rightTerminal : right.final.visible.status = .terminal reason)
    (player : (terminalNormalForm left horizon).Player) :
    (terminalNormalForm left horizon).StrategyFor player ≃
      (terminalNormalForm right horizon).StrategyFor
        (crossReplayPlayerEquiv left right horizon player) := by
  let histories := terminalHistoryEquiv left right horizon reason
    leftTerminal rightTerminal
  exact {
    toFun := fun strategy => {
      choose := fun history => strategy.choose (histories.symm history)
      legal := by
        intro history owned _within
        rw [terminalOwner_eq_none (terminalGame right horizon)
          reason rightTerminal history] at owned
        contradiction
    }
    invFun := fun strategy => {
      choose := fun history => strategy.choose (histories history)
      legal := by
        intro history owned _within
        rw [terminalOwner_eq_none (terminalGame left horizon)
          reason leftTerminal history] at owned
        contradiction
    }
    left_inv := by
      intro strategy
      apply pureStrategy_ext_choose
      funext history
      change strategy.choose (histories.symm (histories history)) =
        strategy.choose history
      exact congrArg strategy.choose (histories.symm_apply_apply history)
    right_inv := by
      intro strategy
      apply pureStrategy_ext_choose
      funext history
      change strategy.choose (histories (histories.symm history)) =
        strategy.choose history
      exact congrArg strategy.choose (histories.apply_symm_apply history)
  }

private def strategyProfileAsPiEquiv
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {horizon : Nat} (game : FiniteExtensiveGame replay horizon) :
    game.StrategyProfile ≃ (∀ player : game.Player, game.PureStrategy player) where
  toFun := fun profile => profile.strategy
  invFun := fun strategy => ⟨strategy⟩
  left_inv := by rintro ⟨strategy⟩; rfl
  right_inv := by intro strategy; rfl

/-- Product strategy equivalence induced by the player and pure-strategy
fibre equivalences. -/
def terminalStrategyProfileEquiv
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) (reason : TerminalReason)
    (leftTerminal : left.final.visible.status = .terminal reason)
    (rightTerminal : right.final.visible.status = .terminal reason) :
    (terminalNormalForm left horizon).Profile ≃
      (terminalNormalForm right horizon).Profile :=
  (strategyProfileAsPiEquiv (terminalGame left horizon)).trans <|
    (Equiv.piCongr (crossReplayPlayerEquiv left right horizon)
      (terminalPureStrategyEquiv left right horizon reason
        leftTerminal rightTerminal)).trans <|
      (strategyProfileAsPiEquiv (terminalGame right horizon)).symm

theorem terminalStrategyProfileEquiv_strategy_commutes
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) (reason : TerminalReason)
    (leftTerminal : left.final.visible.status = .terminal reason)
    (rightTerminal : right.final.visible.status = .terminal reason)
    (profile : (terminalNormalForm left horizon).Profile)
    (player : (terminalNormalForm left horizon).Player) :
    (terminalStrategyProfileEquiv left right horizon reason leftTerminal
        rightTerminal profile).strategy
          (crossReplayPlayerEquiv left right horizon player) =
      terminalPureStrategyEquiv left right horizon reason leftTerminal
        rightTerminal player (profile.strategy player) := by
  change (Equiv.piCongr (crossReplayPlayerEquiv left right horizon)
      (terminalPureStrategyEquiv left right horizon reason leftTerminal
        rightTerminal) profile.strategy)
        (crossReplayPlayerEquiv left right horizon player) =
    terminalPureStrategyEquiv left right horizon reason leftTerminal
      rightTerminal player (profile.strategy player)
  exact Equiv.piCongr_apply_apply _ _ _ _

/-- The finite generated-player coordinate `N` is carried by the lineage
equivalence. -/
theorem terminalPlayers_map_crossReplayPlayerEquiv
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) :
    (terminalNormalForm left horizon).players.map
        (crossReplayPlayerEquiv left right horizon) =
      (terminalNormalForm right horizon).players := by
  change [crossReplayPlayerEquiv left right horizon (left.player .positive),
      crossReplayPlayerEquiv left right horizon (left.player .negative)] =
    [right.player .positive, right.player .negative]
  rw [crossReplayPlayerEquiv_player, crossReplayPlayerEquiv_player]

/-- Terminal payoff depends only on the visible position, not on the replay's
occurrence history. -/
theorem directTerminalPayoff_eq_of_visible_eq
    {n : Nat} {law : Law} {left right : Frame n}
    (visibleEq : left.visible = right.visible) (control : Polarity) :
    FiniteExtensiveGame.directTerminalPayoff law left control =
      FiniteExtensiveGame.directTerminalPayoff law right control := by
  cases left with
  | mk leftVisible leftHistory =>
      cases right with
      | mk rightVisible rightHistory =>
          simp only at visibleEq
          subst rightVisible
          rfl

theorem rightTerminal_of_visible_eq
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    {left : GeneratedReplay law (Frame.initial n) leftMoves}
    {right : GeneratedReplay law (Frame.initial n) rightMoves}
    {reason : TerminalReason}
    (visibleEq : left.final.visible = right.final.visible)
    (leftTerminal : left.final.visible.status = .terminal reason) :
    right.final.visible.status = .terminal reason := by
  calc
    right.final.visible.status = left.final.visible.status :=
      (congrArg VisiblePosition.status visibleEq).symm
    _ = .terminal reason := leftTerminal

theorem terminalNormalForm_utility_preserved
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) (reason : TerminalReason)
    (visibleEq : left.final.visible = right.final.visible)
    (leftTerminal : left.final.visible.status = .terminal reason)
    (profile : (terminalNormalForm left horizon).Profile)
    (player : (terminalNormalForm left horizon).Player) :
    (terminalNormalForm right horizon).utility
        (terminalStrategyProfileEquiv left right horizon reason leftTerminal
          (rightTerminal_of_visible_eq visibleEq leftTerminal) profile)
        (crossReplayPlayerEquiv left right horizon player) =
      (terminalNormalForm left horizon).utility profile player := by
  let rightTerminal := rightTerminal_of_visible_eq visibleEq leftTerminal
  rw [terminalNormalForm_utility_eq_directTerminalPayoff horizon reason
      rightTerminal,
    terminalNormalForm_utility_eq_directTerminalPayoff horizon reason
      leftTerminal,
    crossReplayPlayerEquiv_control]
  exact (directTerminalPayoff_eq_of_visible_eq visibleEq player.1.control).symm

/-- Legal cross-occurrence normal-form transporter.  Its fields cover
`N`, every `Sᵢ`, their product profile and `uᵢ`; no dependent carrier is
identified by equality. -/
structure CrossReplayNormalFormEquivalence
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) where
  playerEquiv :
    (terminalNormalForm left horizon).Player ≃
      (terminalNormalForm right horizon).Player
  players_map :
    (terminalNormalForm left horizon).players.map playerEquiv =
      (terminalNormalForm right horizon).players
  strategyEquiv : ∀ player : (terminalNormalForm left horizon).Player,
    (terminalNormalForm left horizon).StrategyFor player ≃
      (terminalNormalForm right horizon).StrategyFor (playerEquiv player)
  profileEquiv :
    (terminalNormalForm left horizon).Profile ≃
      (terminalNormalForm right horizon).Profile
  profile_strategy_commutes : ∀ profile player,
    (profileEquiv profile).strategy (playerEquiv player) =
      strategyEquiv player (profile.strategy player)
  utility_preserved : ∀ profile player,
    (terminalNormalForm right horizon).utility
        (profileEquiv profile) (playerEquiv player) =
      (terminalNormalForm left horizon).utility profile player

/-- Source-only producer from two actual replays, their common final visible
state and terminality of that state. -/
def terminalNormalFormEquivalence
    {n : Nat} {law : Law} {leftMoves rightMoves : List (Move n)}
    (left : GeneratedReplay law (Frame.initial n) leftMoves)
    (right : GeneratedReplay law (Frame.initial n) rightMoves)
    (horizon : Nat) (reason : TerminalReason)
    (visibleEq : left.final.visible = right.final.visible)
    (leftTerminal : left.final.visible.status = .terminal reason) :
    CrossReplayNormalFormEquivalence left right horizon := by
  let rightTerminal := rightTerminal_of_visible_eq visibleEq leftTerminal
  exact {
    playerEquiv := crossReplayPlayerEquiv left right horizon
    players_map :=
      terminalPlayers_map_crossReplayPlayerEquiv left right horizon
    strategyEquiv := terminalPureStrategyEquiv left right horizon reason
      leftTerminal rightTerminal
    profileEquiv := terminalStrategyProfileEquiv left right horizon reason
      leftTerminal rightTerminal
    profile_strategy_commutes :=
      terminalStrategyProfileEquiv_strategy_commutes left right horizon reason
        leftTerminal rightTerminal
    utility_preserved := terminalNormalForm_utility_preserved left right
      horizon reason visibleEq leftTerminal
  }

end Classical
end Go
end ProcessGame
end SaturationMonoid
