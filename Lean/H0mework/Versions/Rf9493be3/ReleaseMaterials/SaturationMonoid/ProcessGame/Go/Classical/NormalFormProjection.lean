import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.StrategyEvaluation

/-!
# Generated normal-form projection

The normal-form coordinates `(N, Sᵢ, uᵢ)` are read from one recovered finite
extensive game.  `N` is the exact generated-player carrier, `Sᵢ` is its pure
strategy family, and `uᵢ` is the payoff after native-commuting strategy
evaluation.  The projection token has no utility-table field.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Classical

/-- Closed normal-form projection of one recovered game. -/
inductive NormalFormProjection {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) : Type where
  | generated

/-- Sole normal-form producer; callers provide no player set, strategy family
or utility table. -/
def toNormalForm {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) : NormalFormProjection game :=
  .generated

namespace NormalFormProjection

/-- `N`: exactly the replay-generated players. -/
abbrev Player {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (_normal : NormalFormProjection game) := game.Player

def players {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (normal : NormalFormProjection game) : List normal.Player :=
  game.players

theorem players_nodup {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (normal : NormalFormProjection game) : normal.players.Nodup :=
  game.players_nodup

theorem player_mem_players {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (normal : NormalFormProjection game) (player : normal.Player) :
    player ∈ normal.players :=
  game.player_mem_players player

/-- `Sᵢ`: the exact pure-strategy type of generated player `i`. -/
abbrev StrategyFor {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (_normal : NormalFormProjection game) (player : game.Player) :=
  FiniteExtensiveGame.PureStrategy game player

/-- Product of the `Sᵢ`: the recovered strategy-profile type. -/
abbrev Profile {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (_normal : NormalFormProjection game) :=
  FiniteExtensiveGame.StrategyProfile game

/-- `uᵢ`: payoff generated after evaluating the whole finite observation
budget from the recovered root history. -/
def utility {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (_normal : NormalFormProjection game)
    (profile : FiniteExtensiveGame.StrategyProfile game)
    (player : game.Player) : Option ℚ :=
  game.payoff (game.evaluateHistory profile horizon game.rootHistory) player

/-- Independent direct-native readout of the same utility. -/
def directUtility {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (_normal : NormalFormProjection game)
    (profile : FiniteExtensiveGame.StrategyProfile game)
    (player : game.Player) : Option ℚ :=
  FiniteExtensiveGame.directTerminalPayoff law
    (game.directProcessEvaluate profile horizon game.rootHistory)
    player.1.control

theorem utility_eq_evaluatedPayoff {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (normal : NormalFormProjection game) (profile : normal.Profile)
    (player : normal.Player) :
    normal.utility profile player =
      game.payoff (game.evaluateHistory profile horizon game.rootHistory)
        player :=
  rfl

/-- Utility commutes with the independent native-process evaluator; no caller
utility table participates in either side. -/
theorem utility_commutes_with_directProcess
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (normal : NormalFormProjection game) (profile : normal.Profile)
    (player : normal.Player) :
    normal.utility profile player = normal.directUtility profile player := by
  unfold utility directUtility FiniteExtensiveGame.payoff
  rw [FiniteExtensiveGame.evaluateHistory_current_eq_directProcessEvaluate]

end NormalFormProjection

end Classical
end Go
end ProcessGame
end SaturationMonoid
