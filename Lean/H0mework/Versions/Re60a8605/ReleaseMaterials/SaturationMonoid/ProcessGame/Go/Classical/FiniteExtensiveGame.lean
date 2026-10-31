import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.FutureFreedom
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.ScoreReadout

/-!
# Finite classical readout of one generated Go current

The classical carrier below is indexed by one authoritative `GeneratedReplay`
and one finite observation horizon.  Its histories are exactly the bounded
move words executed by the native compiler.  The token has no fields: callers
cannot install players, histories, actions, targets, terminal labels or
payoffs.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Classical

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-- Canonical finite extensive-game readout at one replay-generated current.
The sole constructor carries no data; every public coordinate is recomputed
from `replay`, `horizon` and the fixed Go compiler. -/
inductive FiniteExtensiveGame {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) : Type where
  | generated

namespace FiniteExtensiveGame

/-- The classical player carrier is exactly G2's lineage-generated carrier. -/
abbrev Player {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (_game : FiniteExtensiveGame replay horizon) :=
  GeneratedReplay.GeneratedPlayer replay

/-- The two generated player lineages, exposed without installing names. -/
def players {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) : List game.Player :=
  [replay.player .positive, replay.player .negative]

theorem players_nodup {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) : game.players.Nodup := by
  have distinct : replay.player .positive ≠ replay.player .negative := by
    intro equal
    have controlsEqual := replay.generatedPlayerEquiv.injective equal
    cases controlsEqual
  simp [players, distinct]

theorem player_mem_players {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) (player : game.Player) :
    player ∈ game.players := by
  rcases player with ⟨candidate, ⟨control, rfl⟩⟩
  cases control with
  | positive =>
      apply List.mem_cons.mpr
      exact Or.inl (Subtype.ext rfl)
  | negative =>
      apply List.mem_cons.mpr
      apply Or.inr
      exact List.mem_singleton.mpr (Subtype.ext rfl)

/-- Finite history words: bounded words which execute from the generated
current under the sole `nativeStep?` compiler. -/
def historyWords {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (_game : FiniteExtensiveGame replay horizon) : Finset (List (Move n)) :=
  ((moveWordsUpTo n horizon).filter fun word =>
    (replayFrom? law replay.final word).isSome).toFinset

theorem mem_historyWords_iff {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) (word : List (Move n)) :
    word ∈ game.historyWords ↔
      word.length ≤ horizon ∧
        (replayFrom? law replay.final word).isSome = true := by
  simp [historyWords, mem_moveWordsUpTo_iff_length_le]

/-- A history is only a member of the canonical finite word carrier. -/
def History {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) :=
  { word : List (Move n) // word ∈ game.historyWords }

namespace History

def word {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) : List (Move n) :=
  history.1

def length {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) : Nat :=
  history.word.length

theorem bounded {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) : history.length ≤ horizon :=
  (game.mem_historyWords_iff history.word).mp history.2 |>.1

theorem executes {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) :
    (replayFrom? law replay.final history.word).isSome = true :=
  (game.mem_historyWords_iff history.word).mp history.2 |>.2

/-- Current generated by executing the history word. -/
def current {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) : Frame n :=
  (replayFrom? law replay.final history.word).get history.executes

theorem replayFrom_eq_some_current {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) :
    replayFrom? law replay.final history.word = some history.current := by
  cases execution : replayFrom? law replay.final history.word with
  | none =>
      have executes := history.executes
      simp [execution] at executes
  | some target => simp [current, execution]

end History

/-- Empty history at the replay-generated current. -/
def rootHistory {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) : game.History :=
  ⟨[], (game.mem_historyWords_iff []).mpr ⟨by simp, by simp [replayFrom?]⟩⟩

@[simp] theorem rootHistory_word {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) :
    game.rootHistory.word = [] :=
  rfl

@[simp] theorem rootHistory_current {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) :
    game.rootHistory.current = replay.final := by
  have generated := game.rootHistory.replayFrom_eq_some_current
  rw [game.rootHistory_word] at generated
  change some replay.final = some game.rootHistory.current at generated
  injection generated

/-- The generated control channel at any history, including terminal
histories where it is not a decision owner. -/
def controlChannel {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) : game.Player :=
  replay.player history.current.visible.toMove

/-- Decision ownership exists only while the generated world is playing. -/
def owner? {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) : Option game.Player :=
  match history.current.visible.status with
  | .playing => some (game.controlChannel history)
  | .terminal _ => none

theorem owner?_eq_some_generatedPlayer_toMove_of_playing
    {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History)
    (playing : history.current.visible.status = .playing) :
    game.owner? history =
      some (replay.player history.current.visible.toMove) := by
  simp [owner?, controlChannel, playing]

theorem owner?_eq_none_of_terminal {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) (reason : TerminalReason)
    (terminal : history.current.visible.status = .terminal reason) :
    game.owner? history = none := by
  simp [owner?, terminal]

/-- Available actions at a non-cutoff history are precisely the move
projection of `legalExpansion`.  A fuel boundary suppresses children but does
not assert world terminality. -/
def actions {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) : List (Move n) :=
  if history.length < horizon then
    (legalExpansion law history.current).map Prod.fst
  else
    []

theorem actions_eq_legalExpansion_moves_of_lt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) (within : history.length < horizon) :
    game.actions history = (legalExpansion law history.current).map Prod.fst := by
  simp [actions, within]

theorem mem_actions_iff {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) (move : Move n) :
    move ∈ game.actions history ↔
      history.length < horizon ∧
        ∃ target, LegalStep law history.current move target := by
  constructor
  · intro member
    by_cases within : history.length < horizon
    · rw [game.actions_eq_legalExpansion_moves_of_lt history within] at member
      rcases List.mem_map.mp member with ⟨pair, pairMember, moveEq⟩
      rcases pair with ⟨emitted, target⟩
      exact ⟨within, target, by
        rw [← moveEq]
        exact legalExpansion_sound pairMember⟩
    · simp [actions, within] at member
  · rintro ⟨within, target, step⟩
    rw [game.actions_eq_legalExpansion_moves_of_lt history within]
    exact List.mem_map.mpr ⟨(move, target), legalExpansion_complete step, rfl⟩

theorem mem_actions_iff_nativeStep_isSome {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) (move : Move n) :
    move ∈ game.actions history ↔
      history.length < horizon ∧
        (nativeStep? law history.current move).isSome = true := by
  rw [game.mem_actions_iff history move]
  constructor
  · rintro ⟨within, target, step⟩
    refine ⟨within, ?_⟩
    rw [step]
    rfl
  · rintro ⟨within, isSome⟩
    refine ⟨within, ?_⟩
    cases stepEq : nativeStep? law history.current move with
    | none => simp [stepEq] at isSome
    | some target => exact ⟨target, stepEq⟩

/-- World terminality is read only from the generated status. -/
def WorldTerminal {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) : Prop :=
  ∃ reason, history.current.visible.status = .terminal reason

/-- A playing leaf caused solely by the finite observation budget. -/
def PlayingCutoff {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) : Prop :=
  history.length = horizon ∧ history.current.visible.status = .playing

theorem playingCutoff_not_worldTerminal {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    {history : game.History} (cutoff : PlayingCutoff history) :
    ¬ WorldTerminal history := by
  rintro ⟨reason, terminal⟩
  rw [cutoff.2] at terminal
  cases terminal

/-- Direct generated-frame terminal payoff.  Two passes use area-score
margin; resignation uses the winner carried by the terminal reason. -/
def directTerminalPayoff {n : Nat} (law : Law) (frame : Frame n)
    (control : Polarity) : Option ℚ :=
  match frame.visible.status with
  | .playing => none
  | .terminal .twoPasses =>
      if control = .positive then
        some (scoreMargin law frame.visible.board)
      else
        some (-scoreMargin law frame.visible.board)
  | .terminal (.resignation winner) =>
      if control = winner then some 1 else some (-1)

/-- Classical payoff is a readout through the exact generated player
carrier; it cannot accept a separately named player. -/
def payoff {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) (player : game.Player) : Option ℚ :=
  directTerminalPayoff law history.current player.1.control

theorem payoff_generatedPlayer_eq_direct {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) (control : Polarity) :
    game.payoff history (replay.player control) =
      directTerminalPayoff law history.current control :=
  rfl

end FiniteExtensiveGame

end Classical
end Go
end ProcessGame
end SaturationMonoid
