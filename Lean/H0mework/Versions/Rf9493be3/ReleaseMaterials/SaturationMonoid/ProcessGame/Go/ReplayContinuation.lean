import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.HistoryKernel

/-!
# Unique actual replay continuation

This is the sole extension seam for a generated Go replay.  An exact
`LegalStep` at the current actual frontier produces one `snoc`; its final
current, state trace and rooted occurrence advance commute.  Player lineage,
group lineage and later possibility exposure consume this module instead of
issuing sibling continuation grammars.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

namespace GeneratedReplay

/-- Append one compiler-generated legal move at the unique actual frontier. -/
def snoc {n : Nat} {law : Law} {start : Frame n}
    {moves : List (Move n)} (replay : GeneratedReplay law start moves)
    {target : Frame n} (move : Move n)
    (step : LegalStep law replay.final move target) :
    GeneratedReplay law start (moves ++ [move]) :=
  match replay with
  | .nil _ => .cons move step (.nil target)
  | .cons head headStep tail =>
      .cons head headStep (tail.snoc move step)

@[simp] theorem snoc_final {n : Nat} {law : Law} {start : Frame n}
    {moves : List (Move n)} (replay : GeneratedReplay law start moves)
    {target : Frame n} (move : Move n)
    (step : LegalStep law replay.final move target) :
    (replay.snoc move step).final = target := by
  induction replay with
  | nil => rfl
  | cons head headStep tail ih => exact ih step

@[simp] theorem snoc_stateTrace {n : Nat} {law : Law} {start : Frame n}
    {moves : List (Move n)} (replay : GeneratedReplay law start moves)
    {target : Frame n} (move : Move n)
    (step : LegalStep law replay.final move target) :
    (replay.snoc move step).stateTrace = replay.stateTrace ++ [target] := by
  induction replay with
  | nil => rfl
  | @cons source next tailMoves head headStep tail ih =>
      simp only [snoc, stateTrace, List.cons_append]
      exact congrArg (List.cons source) (ih step)

/-- Appending the actual move is exactly `advance` on the shared unfolding's
unique frontier; the old leaf remains in the occurrence trace. -/
theorem toOccurrence_snoc_eq_advance {n : Nat} {law : Law}
    {start : Frame n} {moves : List (Move n)}
    (replay : GeneratedReplay law start moves) {target : Frame n}
    (move : Move n) (step : LegalStep law replay.final move target) :
    (replay.snoc move step).toOccurrence =
      replay.toOccurrence.advance
        (fun _ => RootedAccountedUnfolding.zero target) := by
  induction replay with
  | nil =>
      simp [snoc, toOccurrence, RootedAccountedUnfolding.advance,
        AccountedBranches.singleton, RootedAccountedUnfolding.zero]
  | cons head headStep tail ih =>
      simp [snoc, toOccurrence, RootedAccountedUnfolding.advance,
        AccountedBranches.singleton, ih step]

/-- One source-generated ply after a replay reachable from `Frame.initial`.
No raw frame can be supplied independently of `replayPrefix.final`. -/
structure ActualPly {n : Nat} {law : Law} {moves : List (Move n)}
    (replayPrefix : GeneratedReplay law (Frame.initial n) moves) where
  target : Frame n
  emitted : Move n
  step : LegalStep law replayPrefix.final emitted target

namespace ActualPly

/-- Same-root replay after this exact actual ply. -/
def extended {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (ply : ActualPly replayPrefix) :
    GeneratedReplay law (Frame.initial n) (moves ++ [ply.emitted]) :=
  replayPrefix.snoc ply.emitted ply.step

theorem extended_stateTrace_eq {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (ply : ActualPly replayPrefix) :
    ply.extended.stateTrace = replayPrefix.stateTrace ++ [ply.target] :=
  replayPrefix.snoc_stateTrace ply.emitted ply.step

/-- The same adjacent current is present in the existing rooted occurrence. -/
theorem extended_occurrence_trace_eq {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (ply : ActualPly replayPrefix) :
    ply.extended.toOccurrence.trace = replayPrefix.stateTrace ++ [ply.target] := by
  rw [ply.extended.occurrence_trace_eq_stateTrace]
  exact ply.extended_stateTrace_eq

end ActualPly
end GeneratedReplay

end Go
end ProcessGame
end SaturationMonoid
