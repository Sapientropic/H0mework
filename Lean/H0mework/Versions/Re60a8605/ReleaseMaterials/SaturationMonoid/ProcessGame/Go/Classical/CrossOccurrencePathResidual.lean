import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Path.KoFreshReplay
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Ko.PrincipalHolonomy

/-!
# Cross-occurrence actual-path residual

Two different G1 actual replays reach the same visible current.  Appending the
same exact resignation event makes both paths terminal while preserving their
different occurrence histories.  The residual phase is a structural fold of
each replay's own exact emitted moves: `.play p00` contributes `1 : C4` and
every other actual event contributes zero.  No `K` field, foreign replay state
or G5 path label is installed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace CrossOccurrencePathResidual

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open AffineRelaxation
open G1HistoryCounterexample

/-! ## Same terminal event on two distinct actual paths -/

theorem koResignTarget_isSome :
    (nativeStep? law koReplay.final (.resign : Move 2)).isSome = true := by
  decide

def koResignTarget : Frame 2 :=
  (nativeStep? law koReplay.final (.resign : Move 2)).get
    koResignTarget_isSome

def koResignPly : GeneratedReplay.ActualPly koReplay where
  target := koResignTarget
  emitted := .resign
  step := by
    unfold LegalStep koResignTarget
    exact (Option.some_get koResignTarget_isSome).symm

theorem freshResignTarget_isSome :
    (nativeStep? law freshReplay.final (.resign : Move 2)).isSome = true := by
  decide

def freshResignTarget : Frame 2 :=
  (nativeStep? law freshReplay.final (.resign : Move 2)).get
    freshResignTarget_isSome

def freshResignPly : GeneratedReplay.ActualPly freshReplay where
  target := freshResignTarget
  emitted := .resign
  step := by
    unfold LegalStep freshResignTarget
    exact (Option.some_get freshResignTarget_isSome).symm

def koTerminalReplay :
    GeneratedReplay law (Frame.initial 2) (koMoves ++ [.resign]) :=
  koResignPly.extended

def freshTerminalReplay :
    GeneratedReplay law (Frame.initial 2) (freshMoves ++ [.resign]) :=
  freshResignPly.extended

@[simp] theorem koTerminalReplay_final :
    koTerminalReplay.final = koResignTarget := by
  exact koReplay.snoc_final koResignPly.emitted koResignPly.step

@[simp] theorem freshTerminalReplay_final :
    freshTerminalReplay.final = freshResignTarget := by
  exact freshReplay.snoc_final freshResignPly.emitted freshResignPly.step

theorem same_exact_terminal_event :
    koResignPly.emitted = (.resign : Move 2) ∧
      freshResignPly.emitted = (.resign : Move 2) :=
  ⟨rfl, rfl⟩

theorem emitted_move_paths_ne :
    koMoves ++ [(.resign : Move 2)] ≠ freshMoves ++ [.resign] := by
  decide

theorem terminal_stateTraces_ne :
    koTerminalReplay.stateTrace ≠ freshTerminalReplay.stateTrace := by
  decide

theorem terminal_occurrences_ne :
    koTerminalReplay.toOccurrence ≠ freshTerminalReplay.toOccurrence := by
  intro occurrencesEqual
  apply terminal_stateTraces_ne
  calc
    koTerminalReplay.stateTrace = koTerminalReplay.toOccurrence.trace :=
      koTerminalReplay.occurrence_trace_eq_stateTrace.symm
    _ = freshTerminalReplay.toOccurrence.trace :=
      congrArg RootedAccountedUnfolding.trace occurrencesEqual
    _ = freshTerminalReplay.stateTrace :=
      freshTerminalReplay.occurrence_trace_eq_stateTrace

theorem terminal_visible_eq :
    koTerminalReplay.final.visible = freshTerminalReplay.final.visible := by
  rw [koTerminalReplay_final, freshTerminalReplay_final]
  apply VisiblePosition.ext
  · apply boardSignature_injective
    decide
  · decide
  · decide
  · decide

theorem terminal_status_eq :
    koTerminalReplay.final.visible.status =
        .terminal (.resignation .negative) ∧
      freshTerminalReplay.final.visible.status =
        .terminal (.resignation .negative) := by
  decide

theorem terminal_positionHistory_ne :
    koTerminalReplay.final.positionHistory ≠
      freshTerminalReplay.final.positionHistory := by
  intro historiesEqual
  have koHistory := nativeStep_positionHistory_eq koResignPly.step
  have freshHistory := nativeStep_positionHistory_eq freshResignPly.step
  change koResignTarget.positionHistory =
    koReplay.final.positionHistory ++ [koResignTarget.visible.situation]
      at koHistory
  change freshResignTarget.positionHistory =
    freshReplay.final.positionHistory ++ [freshResignTarget.visible.situation]
      at freshHistory
  change koResignTarget.positionHistory =
    freshResignTarget.positionHistory at historiesEqual
  rw [koHistory, freshHistory] at historiesEqual
  have terminalVisible : koResignTarget.visible = freshResignTarget.visible := by
    simpa using terminal_visible_eq
  rw [terminalVisible] at historiesEqual
  exact final_positionHistory_ne (List.append_cancel_right historiesEqual)

theorem terminal_paths_close_classically_but_not_actually :
    koTerminalReplay.final.visible = freshTerminalReplay.final.visible ∧
      koTerminalReplay.final.positionHistory ≠
        freshTerminalReplay.final.positionHistory ∧
      koTerminalReplay.toOccurrence ≠ freshTerminalReplay.toOccurrence :=
  ⟨terminal_visible_eq, terminal_positionHistory_ne, terminal_occurrences_ne⟩

/-! ## Replay-native exact-event residual -/

/-- Fixed intrinsic contribution of one exact emitted move. -/
def emittedP00Phase : Move 2 → TacticalPhase
  | .play point => if point = p00 then 1 else 0
  | .pass => 0
  | .resign => 0

/-- Structural fold of one replay's own actual constructor spine. -/
def actualizationK {start : Frame 2} {moves : List (Move 2)} :
    GeneratedReplay law start moves → TacticalPhase
  | .nil _ => 0
  | .cons move _ tail => emittedP00Phase move + actualizationK tail

@[simp] theorem actualizationK_nil (start : Frame 2) :
    actualizationK (GeneratedReplay.nil (law := law) start) = 0 :=
  rfl

@[simp] theorem actualizationK_cons {start next : Frame 2}
    {moves : List (Move 2)} (move : Move 2)
    (step : LegalStep law start move next)
    (tail : GeneratedReplay law next moves) :
    actualizationK (GeneratedReplay.cons move step tail) =
      emittedP00Phase move + actualizationK tail :=
  rfl

/-- The structural replay fold agrees with the exact emitted move index. -/
theorem actualizationK_eq_emittedMovesFold {start : Frame 2}
    {moves : List (Move 2)} (replay : GeneratedReplay law start moves) :
    actualizationK replay =
      moves.foldr (fun move accumulated =>
        emittedP00Phase move + accumulated) 0 := by
  induction replay with
  | nil => rfl
  | cons move step tail ih =>
      simp [actualizationK, ih]

theorem koTerminalK_eq_one : actualizationK koTerminalReplay = 1 := by
  decide

theorem freshTerminalK_eq_zero : actualizationK freshTerminalReplay = 0 := by
  decide

/-- Difference of the two independently generated actualization residuals. -/
def pathKDifference : TacticalPhase :=
  actualizationK koTerminalReplay - actualizationK freshTerminalReplay

theorem pathKDifference_eq_one : pathKDifference = 1 := by
  rw [pathKDifference, koTerminalK_eq_one, freshTerminalK_eq_zero]
  rfl

theorem pathKDifference_rotation_ne_one :
    TacticalPhase.rotation pathKDifference ≠ 1 := by
  apply (TacticalPhase.rotation_ne_one_iff pathKDifference).mpr
  rw [pathKDifference_eq_one]
  decide

/-! ## Existing G5 / P259 / P260 consumers -/

noncomputable def crossOccurrenceTransition :
    Ko.ProjectedLoopIndex → Ko.ProjectedLoopIndex → Circle :=
  Ko.projectedLoopTransition pathKDifference

noncomputable def topologicalCrossOccurrenceTransition :
    Ko.ProjectedLoopIndex → Ko.ProjectedLoopIndex → Unit → Circle :=
  Ko.topologicalProjectedLoopTransition pathKDifference

theorem crossOccurrence_P259_obstruction_nonflat_and_transportMismatch :
    PrincipalHolonomyObstruction crossOccurrenceTransition ∧
      ¬ FlatPrincipalConnection crossOccurrenceTransition ∧
      principalTransport crossOccurrenceTransition .lifted .returned
          (principalTransport crossOccurrenceTransition
            .source .lifted (1 : Circle)) ≠
        principalTransport crossOccurrenceTransition
          .source .returned (1 : Circle) :=
  ⟨Ko.projectedLoop_principalHolonomyObstruction
      pathKDifference_rotation_ne_one,
    Ko.projectedLoop_not_flat pathKDifference_rotation_ne_one,
    Ko.projectedLoop_transport_comp_mismatch
      pathKDifference_rotation_ne_one⟩

theorem crossOccurrence_P260_obstruction_nonflat_and_transportMismatch :
    ContinuousOnPrincipalTransitions Ko.projectedLoopCover
        topologicalCrossOccurrenceTransition ∧
      TopologicalPrincipalHolonomyObstruction Ko.projectedLoopCover
        topologicalCrossOccurrenceTransition ∧
      ¬ TopologicalPrincipalFlatOn Ko.projectedLoopCover
        topologicalCrossOccurrenceTransition ∧
      topologicalPrincipalTransport topologicalCrossOccurrenceTransition
          .lifted .returned ()
          (topologicalPrincipalTransport topologicalCrossOccurrenceTransition
            .source .lifted () (1 : Circle)) ≠
        topologicalPrincipalTransport topologicalCrossOccurrenceTransition
          .source .returned () (1 : Circle) :=
  ⟨Ko.topologicalProjectedLoopTransition_continuous pathKDifference,
    Ko.topologicalProjectedLoop_obstruction pathKDifference_rotation_ne_one,
    Ko.topologicalProjectedLoop_not_flat pathKDifference_rotation_ne_one,
    Ko.topologicalProjectedLoop_transport_comp_mismatch
      pathKDifference_rotation_ne_one⟩

/-- The fresh path's independently computed zero residual remains the exact
flat negative control. -/
theorem fresh_actualization_zero_is_not_obstruction :
    ¬ PrincipalHolonomyObstruction
      (Ko.projectedLoopTransition (actualizationK freshTerminalReplay)) := by
  rw [freshTerminalK_eq_zero]
  exact Ko.projectedLoop_zero_not_obstruction

end CrossOccurrencePathResidual
end Go
end ProcessGame
end SaturationMonoid
