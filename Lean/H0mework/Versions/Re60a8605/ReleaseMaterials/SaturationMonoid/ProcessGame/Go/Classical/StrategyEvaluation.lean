import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.ClassicalGameRecovery

/-!
# Pure strategies and commuting evaluation

Pure strategies select native moves at exact bounded histories owned by one
G2-generated player.  The classical history evaluator and the direct process
evaluator follow the same `nativeStep?` images.  Their commuting theorem is
therefore a theorem about the recovered game, not a second transition law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Classical

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

namespace FiniteExtensiveGame

/-- A pure strategy is indexed by one generated player.  Its legality law is
required only at exact non-cutoff histories actually owned by that player. -/
structure PureStrategy {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) (player : game.Player) where
  choose : game.History → Move n
  legal : ∀ history,
    game.owner? history = some player →
      history.length < horizon → choose history ∈ game.actions history

/-- One pure strategy for each and every generated player. -/
structure StrategyProfile {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) where
  strategy : ∀ player : game.Player, PureStrategy game player

namespace StrategyProfile

def actionAt {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) (history : game.History)
    (player : game.Player) : Move n :=
  (profile.strategy player).choose history

theorem actionAt_mem_actions {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) (history : game.History)
    (player : game.Player) (owned : game.owner? history = some player)
    (within : history.length < horizon) :
    profile.actionAt history player ∈ game.actions history :=
  (profile.strategy player).legal history owned within

theorem actionAt_nativeStep_isSome {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) (history : game.History)
    (player : game.Player) (owned : game.owner? history = some player)
    (within : history.length < horizon) :
    (nativeStep? law history.current
      (profile.actionAt history player)).isSome = true :=
  ((game.mem_actions_iff_nativeStep_isSome history
    (profile.actionAt history player)).mp
      (profile.actionAt_mem_actions history player owned within)).2

end StrategyProfile

/-- One strategy-generated successor history.  Decision ownership is checked
before the strategy is consulted; the actual child is produced by the
recovered game's `transition?`, hence ultimately by `nativeStep?`. -/
def StrategyProfile.nextHistory? {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) (history : game.History) :
    Option game.History :=
  match game.owner? history with
  | none => none
  | some player =>
      if history.length < horizon then
        game.transition? history (profile.actionAt history player)
      else
        none

theorem StrategyProfile.nextHistory?_of_decision
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) (history : game.History)
    (player : game.Player) (owned : game.owner? history = some player)
    (within : history.length < horizon) :
    ∃ next : game.History,
      profile.nextHistory? history = some next ∧
        next.word = history.word ++ [profile.actionAt history player] ∧
        nativeStep? law history.current (profile.actionAt history player) =
          some next.current := by
  rcases game.transition?_of_action history (profile.actionAt history player)
      (profile.actionAt_mem_actions history player owned within) with
    ⟨next, transition, wordEq, nativeEq⟩
  refine ⟨next, ?_, wordEq, nativeEq⟩
  simp [StrategyProfile.nextHistory?, owned, within, transition]

/-- Exact result package of one raw native compiler call. -/
structure NativeStepWitness {n : Nat} (law : Law) (current : Frame n)
    (action : Move n) where
  target : Frame n
  step : LegalStep law current action target

/-- Direct dependent packaging of `nativeStep?`; no classical transition or
history carrier enters this compiler mouth. -/
def nativeStepWitness? {n : Nat} (law : Law) (current : Frame n)
    (action : Move n) : Option (NativeStepWitness law current action) :=
  match step : nativeStep? law current action with
  | none => none
  | some target => some ⟨target, step⟩

theorem nativeStepWitness?_eq_some_of_legal {n : Nat} {law : Law}
    {current target : Frame n} {action : Move n}
    (step : LegalStep law current action target) :
    nativeStepWitness? law current action = some ⟨target, step⟩ := by
  unfold LegalStep at step
  unfold nativeStepWitness?
  split
  · rename_i noneEq
    rw [step] at noneEq
    contradiction
  · rename_i generatedTarget generatedEq
    have targetEq : generatedTarget = target :=
      Option.some.inj (generatedEq.symm.trans step)
    subst generatedTarget
    rfl

/-- Independent direct native successor.  This definition does not call the
classical `transition?` or `nextHistory?`: it executes the selected action
with `nativeStep?` and constructs the exact extended history from that step. -/
def StrategyProfile.directNativeNext? {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) (history : game.History) :
    Option game.History :=
  match game.owner? history with
  | none => none
  | some player =>
      if within : history.length < horizon then
        let action := profile.actionAt history player
        match nativeStepWitness? law history.current action with
        | none => none
        | some nativeChild =>
            some (history.extend action nativeChild.target nativeChild.step
              (Nat.succ_le_iff.mpr within))
      else
        none

/-- The independently computed native successor and the recovered classical
successor coincide.  Equality is forced by the same selected action, native
target uniqueness and the exact appended history word. -/
theorem StrategyProfile.directNativeNext?_eq_nextHistory?
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) (history : game.History) :
    profile.directNativeNext? history = profile.nextHistory? history := by
  cases ownerEq : game.owner? history with
  | none =>
      simp [StrategyProfile.directNativeNext?,
        StrategyProfile.nextHistory?, ownerEq]
  | some player =>
      by_cases within : history.length < horizon
      · rcases profile.nextHistory?_of_decision history player ownerEq within with
          ⟨next, nextEq, wordEq, nativeEq⟩
        have nativeStep : LegalStep law history.current
            (profile.actionAt history player) next.current := nativeEq
        have directEq : profile.directNativeNext? history =
            some (history.extend (profile.actionAt history player)
              next.current nativeStep (Nat.succ_le_iff.mpr within)) := by
          simp [StrategyProfile.directNativeNext?, ownerEq, within,
            nativeStepWitness?_eq_some_of_legal nativeStep]
        rw [directEq, nextEq]
        apply congrArg some
        apply Subtype.ext
        change (history.extend (profile.actionAt history player)
          next.current nativeStep (Nat.succ_le_iff.mpr within)).word =
            next.word
        rw [History.extend_word, wordEq]
      · simp [StrategyProfile.directNativeNext?,
          StrategyProfile.nextHistory?, ownerEq, within]

/-- Classical evaluation returns the selected exact bounded history.  It
consults a strategy only after `owner?` has produced a decision owner and
stops at either a world terminal or the observation cutoff. -/
def evaluateHistory {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) : Nat → game.History → game.History
  | 0, history => history
  | fuel + 1, history =>
      match profile.nextHistory? history with
      | none => history
      | some next => evaluateHistory profile fuel next

/-- Direct native-process evaluation of the same strategy profile.  It
returns only the generated current and writes neither the actual replay nor
its history/lineage faces. -/
def directProcessEvaluate {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) : Nat → game.History → Frame n
  | 0, history => history.current
  | fuel + 1, history =>
      match profile.directNativeNext? history with
      | none => history.current
      | some next => directProcessEvaluate profile fuel next

/-- Strategy evaluation commutes with the native process evaluator at every
bounded starting history. -/
theorem evaluateHistory_current_eq_directProcessEvaluate
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) (fuel : Nat)
    (history : game.History) :
    (evaluateHistory profile fuel history).current =
      directProcessEvaluate profile fuel history := by
  induction fuel generalizing history with
  | zero => rfl
  | succ fuel ih =>
      cases nextEq : profile.nextHistory? history with
      | none =>
          have directEq : profile.directNativeNext? history = none := by
            rw [profile.directNativeNext?_eq_nextHistory?, nextEq]
          simp [evaluateHistory, directProcessEvaluate, nextEq, directEq]
      | some next =>
          have directEq : profile.directNativeNext? history = some next := by
            rw [profile.directNativeNext?_eq_nextHistory?, nextEq]
          simpa [evaluateHistory, directProcessEvaluate, nextEq, directEq] using
            ih next

/-- The payoff square commutes: the recovered classical payoff after
strategy evaluation is exactly the direct terminal payoff of the generated
current reached by the native evaluator. -/
theorem evaluatePayoff_commutes {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (profile : StrategyProfile game) (fuel : Nat)
    (history : game.History) (control : Polarity) :
    game.payoff (evaluateHistory profile fuel history)
        (replay.player control) =
      directTerminalPayoff law
        (directProcessEvaluate profile fuel history) control := by
  rw [game.payoff_generatedPlayer_eq_direct]
  rw [evaluateHistory_current_eq_directProcessEvaluate]

private theorem resignStep_of_playing {n : Nat} (law : Law)
    (current : Frame n) (playing : current.visible.status = .playing) :
    ∃ target, LegalStep law current .resign target := by
  let resignedVisible : VisiblePosition n := {
    board := current.visible.board
    toMove := current.visible.toMove
    consecutivePasses := current.visible.consecutivePasses
    status := .terminal (.resignation current.visible.toMove.other)
  }
  let target := Frame.advance current resignedVisible
  refine ⟨target, ?_⟩
  unfold LegalStep nativeStep? stepVisible? resignVisible?
  rw [playing]
  rfl

private theorem playing_of_owner?_eq_some {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) (player : game.Player)
    (owned : game.owner? history = some player) :
    history.current.visible.status = .playing := by
  cases statusEq : history.current.visible.status with
  | playing => rfl
  | terminal reason =>
      rw [game.owner?_eq_none_of_terminal history reason statusEq] at owned
      contradiction

/-- Canonical total pure strategy used by direct regressions: resign at every
owned playing history. -/
def resignPureStrategy {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) (player : game.Player) :
    PureStrategy game player where
  choose := fun _ => .resign
  legal := by
    intro history owned within
    apply (game.mem_actions_iff history .resign).mpr
    exact ⟨within,
      resignStep_of_playing law history.current
        (playing_of_owner?_eq_some history player owned)⟩

def resignProfile {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) : StrategyProfile game where
  strategy := game.resignPureStrategy

/-- Strategy search remains a readout of the unchanged actual occurrence,
position-history ledger and generated lineage bundle. -/
theorem strategyEvaluation_actual_noninterference
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (_profile : StrategyProfile game) (_fuel : Nat) :
    replay.toOccurrence.trace = replay.stateTrace ∧
      replay.toOccurrence.trace.map
          (fun frame => frame.visible.situation) = replay.final.positionHistory ∧
      Nonempty (GeneratedDancersAt replay) :=
  ⟨(game.stateTree_actual_noninterference).2.1,
    (game.stateTree_actual_noninterference).2.2.1,
    (game.stateTree_actual_noninterference).2.2.2⟩

end FiniteExtensiveGame

end Classical
end Go
end ProcessGame
end SaturationMonoid
