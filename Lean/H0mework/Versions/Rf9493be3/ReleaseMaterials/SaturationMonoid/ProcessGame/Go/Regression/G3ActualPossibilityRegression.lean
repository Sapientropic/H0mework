import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.RootedOccurrence

/-!
# G3 actual / possibility separation regression

The empty 2×2 current has four legal placements, pass and resignation.  One
exact placement is actualized through `ActualPly`; a board-lookalike pass leaf
remains possible but does not enter the actual replay, position history or
generated-dancers face.  An actual resignation then checks that terminal
currents remain rooted leaves.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G3ActualPossibilityRegression

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

def testLaw : Law := Law.positionalSuperko 0

def p00 : Point 2 := (0, 0)

def emptyReplay :
    GeneratedReplay testLaw (Frame.initial 2) [] :=
  .nil (Frame.initial 2)

theorem playTarget_isSome :
    (nativeStep? testLaw emptyReplay.final (.play p00)).isSome = true := by
  decide

def playTarget : Frame 2 :=
  (nativeStep? testLaw emptyReplay.final (.play p00)).get playTarget_isSome

/-- The chosen child is indexed by a replay from `Frame.initial`, not by a raw
frame plus a free legal-step witness. -/
def chosenPly : GeneratedReplay.ActualPly emptyReplay where
  target := playTarget
  emitted := .play p00
  step := by
    unfold LegalStep playTarget
    exact (Option.some_get playTarget_isSome).symm

theorem passTarget_isSome :
    (nativeStep? testLaw emptyReplay.final (.pass : Move 2)).isSome = true := by
  decide

def passTarget : Frame 2 :=
  (nativeStep? testLaw emptyReplay.final (.pass : Move 2)).get passTarget_isSome

theorem initial_pass_is_possible :
    ((.pass : Move 2), passTarget) ∈
      legalExpansion testLaw emptyReplay.final := by
  apply legalExpansion_complete
  unfold LegalStep passTarget
  exact (Option.some_get passTarget_isSome).symm

theorem resignTarget_isSome :
    (nativeStep? testLaw emptyReplay.final (.resign : Move 2)).isSome = true := by
  decide

def resignTarget : Frame 2 :=
  (nativeStep? testLaw emptyReplay.final (.resign : Move 2)).get
    resignTarget_isSome

/-- Four placements plus pass and resign are exposed at the empty 2×2
current. -/
theorem initial_has_six_legal_branches :
    (legalExpansion testLaw emptyReplay.final).length = 6 := by
  decide

theorem initial_possibility_trace_has_root_and_six_children :
    (rootedPossibilityAt emptyReplay).trace.length = 7 := by
  rw [rootedPossibilityAt, possibilityStep_trace]
  decide

/-- Exact actualization selects a target already present in the finite
possibility frontier. -/
theorem chosen_child_is_exposed :
    chosenPly.target ∈ (rootedPossibilityAt emptyReplay).frontier :=
  actualPly_target_mem_frontier chosenPly

theorem chosen_child_is_actual_final :
    chosenPly.extended.final = chosenPly.target :=
  rfl

theorem chosen_actual_occurrence_is_shared_advance :
    chosenPly.extended.toOccurrence =
      emptyReplay.toOccurrence.advance
        (fun _ => RootedAccountedUnfolding.zero chosenPly.target) :=
  emptyReplay.toOccurrence_snoc_eq_advance chosenPly.emitted chosenPly.step

/-- Chosen placement and unchosen pass coexist in the same possibility
frontier, but actual trace/history and generated dancers are computed only
from the chosen `ActualPly.extended`. -/
theorem chosen_unchosen_exact_separation :
    chosenPly.target ∈ (rootedPossibilityAt emptyReplay).frontier ∧
      passTarget ∈ (rootedPossibilityAt emptyReplay).frontier ∧
      chosenPly.extended.stateTrace =
        emptyReplay.stateTrace ++ [chosenPly.target] ∧
      chosenPly.extended.final.positionHistory =
        emptyReplay.final.positionHistory ++
          [chosenPly.target.visible.situation] ∧
      Nonempty (GeneratedDancersAt chosenPly.extended) := by
  rcases actualPly_chosen_unchosen_separation chosenPly
      initial_pass_is_possible (by decide) with
    ⟨_chosenPossible, _unchosenPossible, chosenFrontier,
      unchosenFrontier, _moveNe, actualTrace, actualHistory,
      actualDancers⟩
  exact ⟨chosenFrontier, unchosenFrontier, actualTrace,
    actualHistory, actualDancers⟩

/-- From the actual child, pass is still a possible continuation.  Its board
is deliberately a visible lookalike of the actual current while its replay
state remains unchosen. -/
theorem afterPlayPassTarget_isSome :
    (nativeStep? testLaw chosenPly.extended.final (.pass : Move 2)).isSome =
      true := by
  decide

def afterPlayPassTarget : Frame 2 :=
  (nativeStep? testLaw chosenPly.extended.final (.pass : Move 2)).get
    afterPlayPassTarget_isSome

theorem afterPlay_pass_is_possible :
    ((.pass : Move 2), afterPlayPassTarget) ∈
      legalExpansion testLaw chosenPly.extended.final := by
  apply legalExpansion_complete
  unfold LegalStep afterPlayPassTarget
  exact (Option.some_get afterPlayPassTarget_isSome).symm

theorem unchosen_pass_has_same_board :
    afterPlayPassTarget.visible.board =
      chosenPly.extended.final.visible.board := by
  decide

theorem unchosen_pass_is_not_actual_current :
    afterPlayPassTarget ≠ chosenPly.extended.final := by
  decide

theorem unchosen_pass_is_not_in_actual_trace :
    afterPlayPassTarget ∉ chosenPly.extended.stateTrace := by
  decide

theorem unchosen_pass_situation_is_not_in_actual_positionHistory :
    afterPlayPassTarget.visible.situation ∉
      chosenPly.extended.final.positionHistory := by
  decide

/-- The possible pass supplies no write authority: actual trace/history and
the replay-indexed player/group face remain those generated by the chosen
one-ply replay. -/
theorem unchosen_pass_preserves_actual_faces :
    (rootedPossibilityAt chosenPly.extended).root.positionHistory =
        chosenPly.extended.final.positionHistory ∧
      chosenPly.extended.toOccurrence.trace =
        chosenPly.extended.stateTrace ∧
      chosenPly.extended.toOccurrence.trace.map
          (fun frame => frame.visible.situation) =
        chosenPly.extended.final.positionHistory ∧
      Nonempty (GeneratedDancersAt chosenPly.extended) :=
  rootedPossibilityAt_actual_faces chosenPly.extended

/-- Resignation is actualized through its own exact ply so the terminal-leaf
test also retains initial-replay provenance. -/
def resignationPly : GeneratedReplay.ActualPly emptyReplay where
  target := resignTarget
  emitted := .resign
  step := by
    unfold LegalStep resignTarget
    exact (Option.some_get resignTarget_isSome).symm

def terminalReplay := resignationPly.extended

theorem terminalReplay_status :
    terminalReplay.final.visible.status =
      .terminal (.resignation .negative) := by
  decide

theorem terminal_expansion_is_empty :
    legalExpansion testLaw terminalReplay.final = [] :=
  legalExpansion_eq_nil_of_terminal testLaw terminalReplay.final
    (.resignation .negative) terminalReplay_status

/-- Empty legal expansion does not erase the terminal current or counterfeit
a completed future: the possibility occurrence is exactly its rooted leaf. -/
theorem terminal_current_is_rooted_leaf :
    rootedPossibilityAt terminalReplay =
      RootedAccountedUnfolding.zero terminalReplay.final :=
  possibilityStep_eq_zero_of_terminal testLaw terminalReplay.final
    (.resignation .negative) terminalReplay_status

theorem terminal_frontier_retains_current :
    (rootedPossibilityAt terminalReplay).frontier =
      [terminalReplay.final] :=
  possibilityStep_terminal_frontier testLaw terminalReplay.final
    (.resignation .negative) terminalReplay_status

end G3ActualPossibilityRegression
end Go
end ProcessGame
end SaturationMonoid
