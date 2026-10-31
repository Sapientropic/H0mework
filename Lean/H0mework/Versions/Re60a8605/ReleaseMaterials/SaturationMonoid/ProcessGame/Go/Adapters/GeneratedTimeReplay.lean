import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.HistoryKernel
import H0mework.Realization.Reflexive.Iteration

/-!
# P98/P99 replay readout for generated Go histories

This narrow adapter consumes the already-proved reflexive time field and
`repeatEval` theorem.  The query state is a generated Go current plus the
remaining source script.  P98/P99 replay the already fixed script; they do not
select a live move or create a second history authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

/-- Cursor used only by the P98/P99 replay readout. -/
structure ReplayCursor (n : Nat) where
  current : Option (Frame n)
  remaining : List (Move n)

namespace ReplayCursor

/-- One total cursor write.  An invalid generated step propagates `none`; the
authoritative theorem below consumes a `GeneratedReplay`, so its branch is
always the exact successful compiler image. -/
def write {n : Nat} (law : Law) (cursor : ReplayCursor n) : ReplayCursor n :=
  match cursor.remaining with
  | [] => cursor
  | move :: moves => {
      current := cursor.current.bind (fun frame => nativeStep? law frame move)
      remaining := moves
    }

end ReplayCursor

/-- Reflexive-query presentation of one fixed Go script. -/
def generatedReplayQuery {n : Nat} (law : Law) :
    ReflexiveQuery (ReplayCursor n) (Option (Frame n)) where
  read := ReplayCursor.current
  write := ReplayCursor.write law

/-- P98's generated time field reaches exactly the final current of the
dependent actual replay after the script length. -/
theorem generatedReplay_timeField_final {n : Nat} {law : Law}
    {start : Frame n} {moves : List (Move n)}
    (replay : GeneratedReplay law start moves) :
    (reflexiveQueryIteratedTimeField (generatedReplayQuery law)
      { current := some start, remaining := moves }).stateAt moves.length =
        { current := some replay.final, remaining := [] } := by
  induction replay with
  | nil => rfl
  | @cons start next moves move step tail ih =>
      let cursor : ReplayCursor n := {
        current := some start
        remaining := move :: moves
      }
      have write_eq :
          (generatedReplayQuery law).write cursor =
            ({ current := some next, remaining := moves } : ReplayCursor n) := by
        unfold generatedReplayQuery ReplayCursor.write cursor
        unfold LegalStep at step
        simp [step]
      calc
        (reflexiveQueryIteratedTimeField (generatedReplayQuery law) cursor).stateAt
            (move :: moves).length =
            (reflexiveQueryIteratedTimeField (generatedReplayQuery law) cursor).stateAt
              (Nat.succ moves.length) := rfl
        _ = (reflexiveQueryIteratedTimeField (generatedReplayQuery law)
              ((generatedReplayQuery law).write cursor)).stateAt moves.length :=
          (reflexiveQueryIterated_stateAt_shift
            (generatedReplayQuery law) cursor moves.length).symm
        _ = (reflexiveQueryIteratedTimeField (generatedReplayQuery law)
              ({ current := some next, remaining := moves } : ReplayCursor n)).stateAt
                moves.length := by rw [write_eq]
        _ = { current := some tail.final, remaining := [] } := ih

/-- P99's repeated stateful plan produces the canonical observation trace and
the same final cursor as the actual occurrence. -/
theorem generatedReplay_repeatEval {n : Nat} {law : Law}
    {start : Frame n} {moves : List (Move n)}
    (replay : GeneratedReplay law start moves) :
    StatefulGenAlg.repeatEval
        (reflexiveQueryPrimitive (generatedReplayQuery law))
        (reflexiveQueryStatefulPlan (generatedReplayQuery law))
        moves.length
        ({ current := some start, remaining := moves } : ReplayCursor n)
        (reflexiveQueryIteratedObservationTrace (generatedReplayQuery law)
          { current := some start, remaining := moves } moves.length)
        ({ current := some replay.final, remaining := [] } : ReplayCursor n) := by
  apply (reflexiveStatefulPlan_repeatEval_iff_iteratedTimeField
    (generatedReplayQuery law) moves.length
    ({ current := some start, remaining := moves } : ReplayCursor n)
    (reflexiveQueryIteratedObservationTrace (generatedReplayQuery law)
      { current := some start, remaining := moves } moves.length)
    ({ current := some replay.final, remaining := [] } : ReplayCursor n)).2
  exact ⟨rfl, (generatedReplay_timeField_final replay).symm⟩

/-- The P99 endpoint and the shared occurrence fold are the same current. -/
theorem generatedReplay_repeatEndpoint_eq_occurrenceFold {n : Nat} {law : Law}
    {start : Frame n} {moves : List (Move n)}
    (replay : GeneratedReplay law start moves) :
    some replay.final =
      some (replay.toOccurrence.fold GeneratedReplay.finalAlgebra) := by
  exact congrArg some replay.occurrence_fold_eq_final.symm

end Go
end ProcessGame
end SaturationMonoid
