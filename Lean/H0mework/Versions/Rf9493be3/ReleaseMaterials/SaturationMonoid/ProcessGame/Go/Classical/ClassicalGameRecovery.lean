import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Classical.FiniteExtensiveGame

/-!
# Recovery of the finite classical game from one generated replay

`recoverExtensiveGame` has no caller-supplied coordinates.  The recovered
state tree is definitionally the G3 future cone, and every admitted bounded
history reconstructs a dependent compiler replay whose path occurs in that
same tree.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Classical

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-- Canonical recovery producer. -/
def recoverExtensiveGame {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves)
    (horizon : Nat) : FiniteExtensiveGame replay horizon :=
  .generated

namespace FiniteExtensiveGame

/-- The recovered classical state tree is exactly the existing finite future
cone, not a second state-tree compiler. -/
def stateTree {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (_game : FiniteExtensiveGame replay horizon) :
    RootedAccountedUnfolding (Frame n) :=
  futureConeAt replay horizon

theorem stateTree_eq_futureConeAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) :
    game.stateTree = futureConeAt replay horizon :=
  rfl

@[simp] theorem stateTree_root {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) :
    game.stateTree.root = replay.final :=
  futureConeAt_root replay horizon

theorem stateTree_legal {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) :
    LegalExposure law game.stateTree :=
  futureConeAt_legal replay horizon

/-- Direct public consumption of the shared unfolding's evaluator uniqueness
law at the recovered state tree. -/
theorem stateTree_fold_unique {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    {Carrier : Type*}
    (atOccurrence : Frame n → List Carrier → Carrier)
    (candidate : RootedAccountedUnfolding (Frame n) → Carrier)
    (commutes : ∀ (origin : Frame n)
        (branches : AccountedBranches (Frame n)),
      candidate (.occur origin branches) =
        atOccurrence origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate game.stateTree = game.stateTree.fold atOccurrence :=
  RootedAccountedUnfolding.fold_unique
    atOccurrence candidate commutes game.stateTree

/-- Executing an append first executes the prefix and then its suffix. -/
theorem replayFrom_append {n : Nat} (law : Law) (start : Frame n)
    (headWords tailWords : List (Move n)) :
    replayFrom? law start (headWords ++ tailWords) =
      (replayFrom? law start headWords).bind fun current =>
        replayFrom? law current tailWords := by
  induction headWords generalizing start with
  | nil => rfl
  | cons move headWords ih =>
      simp only [List.cons_append, replayFrom?]
      cases step : nativeStep? law start move with
      | none => rfl
      | some target => exact ih target

/-- Exact dependent extension of one admitted history by one generated native
step.  The target remains indexed by its `LegalStep`; it is not a shell field
of the game. -/
def History.extend {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) (move : Move n) (target : Frame n)
    (step : LegalStep law history.current move target)
    (bounded : history.length + 1 ≤ horizon) : game.History :=
  ⟨history.word ++ [move], (game.mem_historyWords_iff _).mpr ⟨by
      simpa [History.length] using bounded, by
      change nativeStep? law history.current move = some target at step
      rw [replayFrom_append, history.replayFrom_eq_some_current]
      simp [replayFrom?, step]⟩⟩

@[simp] theorem History.extend_word {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) (move : Move n) (target : Frame n)
    (step : LegalStep law history.current move target)
    (bounded : history.length + 1 ≤ horizon) :
    (history.extend move target step bounded).word = history.word ++ [move] :=
  rfl

@[simp] theorem History.extend_current {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) (move : Move n) (target : Frame n)
    (step : LegalStep law history.current move target)
    (bounded : history.length + 1 ≤ horizon) :
    (history.extend move target step bounded).current = target := by
  have generated :=
    (history.extend move target step bounded).replayFrom_eq_some_current
  rw [History.extend_word, replayFrom_append,
    history.replayFrom_eq_some_current] at generated
  change nativeStep? law history.current move = some target at step
  simp [replayFrom?, step] at generated
  exact generated.symm

/-- Executable classical transition.  Both its bound and its target are
computed; callers provide only a history and an action. -/
def transition? {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) (move : Move n) : Option game.History :=
  if bounded : history.length + 1 ≤ horizon then
    match step : nativeStep? law history.current move with
    | none => none
    | some target => some (history.extend move target step bounded)
  else
    none

theorem transition?_of_action {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    (history : game.History) (move : Move n)
    (action : move ∈ game.actions history) :
    ∃ next : game.History,
      game.transition? history move = some next ∧
        next.word = history.word ++ [move] ∧
        nativeStep? law history.current move = some next.current := by
  rcases (game.mem_actions_iff history move).mp action with
    ⟨within, target, step⟩
  have bounded : history.length + 1 ≤ horizon :=
    Nat.succ_le_iff.mpr within
  have stepEq : nativeStep? law history.current move = some target := step
  let next := history.extend move target step bounded
  refine ⟨next, ?_, rfl, ?_⟩
  · simp only [transition?, dif_pos bounded]
    split
    · rename_i noTarget
      rw [stepEq] at noTarget
      contradiction
    · rename_i generatedTarget generatedEq
      have targetsEq : generatedTarget = target :=
        Option.some.inj (generatedEq.symm.trans stepEq)
      subst generatedTarget
      rfl
  · calc
      nativeStep? law history.current move = some target := stepEq
      _ = some next.current := by
        have nextCurrent : next.current = target := by
          dsimp [next]
          exact history.extend_current move target step bounded
        rw [nextCurrent]

/-- Every admitted history reconstructs a dependent compiler continuation and
its full state path is a branch of the same recovered state tree. -/
theorem History.factors_through_stateTree {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    {game : FiniteExtensiveGame replay horizon}
    (history : game.History) :
    ∃ continuation : GeneratedReplay law replay.final history.word,
      continuation.final = history.current ∧
        continuation.stateTrace ∈ rootedPaths game.stateTree := by
  rcases exists_generatedReplay_of_replayFrom_eq_some
      history.replayFrom_eq_some_current with ⟨continuation, finalEq⟩
  refine ⟨continuation, finalEq, ?_⟩
  exact generatedReplay_stateTrace_mem_rootedPaths_finiteExposureFrom
    continuation history.bounded

/-- Conversely, every bounded dependent continuation gives one canonical
classical history. -/
def historyOfGeneratedReplay {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    {word : List (Move n)} (continuation : GeneratedReplay law replay.final word)
    (bounded : word.length ≤ horizon) : game.History :=
  ⟨word, (game.mem_historyWords_iff word).mpr ⟨bounded, by
    rw [replayFrom_eq_some_of_generatedReplay continuation]
    rfl⟩⟩

@[simp] theorem historyOfGeneratedReplay_current {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon)
    {word : List (Move n)} (continuation : GeneratedReplay law replay.final word)
    (bounded : word.length ≤ horizon) :
    (game.historyOfGeneratedReplay continuation bounded).current =
      continuation.final := by
  have generated :=
    (game.historyOfGeneratedReplay continuation bounded).replayFrom_eq_some_current
  change replayFrom? law replay.final word = some _ at generated
  rw [replayFrom_eq_some_of_generatedReplay continuation] at generated
  exact (Option.some.inj generated).symm

/-- Search exposure reads the unchanged actual root, trace, position history
and generated lineage bundle.  It has no write mouth into any of them. -/
theorem stateTree_actual_noninterference {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves} {horizon : Nat}
    (game : FiniteExtensiveGame replay horizon) :
    game.stateTree.root = replay.final ∧
      replay.toOccurrence.trace = replay.stateTrace ∧
      replay.toOccurrence.trace.map
          (fun frame => frame.visible.situation) = replay.final.positionHistory ∧
      Nonempty (GeneratedDancersAt replay) :=
  futureCone_actual_noninterference replay horizon

end FiniteExtensiveGame

end Classical
end Go
end ProcessGame
end SaturationMonoid
