import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.SearchExposure

/-!
# G3 finite search-exposure regression

This regression reuses the exact 2×2 actual/possibility instance.  It checks
the pruned finite future cone, labelled legal-edge provenance, fold consumer,
fuel monotonicity, actualized-child regeneration, unchosen-branch
noninterference and terminal-leaf stability.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G3SearchExposureRegression

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

def chosenPly : GeneratedReplay.ActualPly emptyReplay where
  target := playTarget
  emitted := .play p00
  step := by
    unfold LegalStep playTarget
    exact (Option.some_get playTarget_isSome).symm

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

theorem unchosen_pass_is_not_in_actual_trace :
    afterPlayPassTarget ∉ chosenPly.extended.stateTrace := by
  decide

theorem unchosen_pass_situation_is_not_in_actual_positionHistory :
    afterPlayPassTarget.visible.situation ∉
      chosenPly.extended.final.positionHistory := by
  decide

theorem resignTarget_isSome :
    (nativeStep? testLaw emptyReplay.final (.resign : Move 2)).isSome = true := by
  decide

def resignTarget : Frame 2 :=
  (nativeStep? testLaw emptyReplay.final (.resign : Move 2)).get
    resignTarget_isSome

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

/-- Fuel zero is a rooted observation leaf even though the current is still
playing.  It therefore cannot serve as a terminal classifier. -/
theorem zero_fuel_leaf_is_not_terminal :
    (futureConeAt emptyReplay 0).frontier = [emptyReplay.final] ∧
      emptyReplay.final.visible.status = .playing ∧
      ¬ ∃ reason, emptyReplay.final.visible.status = .terminal reason := by
  refine ⟨rfl, rfl, ?_⟩
  rintro ⟨reason, impossible⟩
  cases impossible

/-- The empty 2×2 current exposes four placements, pass and resignation. -/
theorem one_fuel_has_six_branches :
    (futureConeAt emptyReplay 1).frontier.length = 6 := by
  rw [futureConeAt_one_eq_rootedPossibilityAt, rootedPossibilityAt]
  have targetsNonempty : legalTargets testLaw emptyReplay.final ≠ [] := by
    decide
  rw [possibilityStep_frontier_of_targets_ne_nil
    testLaw emptyReplay.final targetsNonempty]
  decide

theorem one_fuel_trace_has_root_and_six_children :
    (futureConeAt emptyReplay 1).trace.length = 7 := by
  rw [futureConeAt_one_eq_rootedPossibilityAt, rootedPossibilityAt,
    possibilityStep_trace]
  decide

/-- The edge-labelled invariant proves every parent-child edge in the
two-layer cone is an exact `LegalStep` of `testLaw`. -/
theorem two_fuel_all_edges_are_compiler_generated :
    LegalExposure testLaw (futureConeAt emptyReplay 2) :=
  futureConeAt_legal emptyReplay 2

/-- Fuel growth preserves the root and every previously exposed trace node. -/
theorem zero_to_two_is_generated_prefix :
    ExposurePrefix (futureConeAt emptyReplay 0)
      (futureConeAt emptyReplay 2) := by
  exact finiteExposureFrom_fuel_mono testLaw (by decide)
    emptyReplay.final

/-- The sole occurrence fold is a direct finite-cone consumer. -/
theorem chosen_target_is_read_by_futureCone_fold :
    chosenPly.target ∈
      (futureConeAt emptyReplay 1).fold futureConeTraceAlgebra := by
  rw [futureConeAt_fold_eq_trace,
    futureConeAt_one_eq_rootedPossibilityAt, rootedPossibilityAt,
    possibilityStep_trace]
  exact List.mem_cons_of_mem _
    (actualPly_target_mem_legalTargets chosenPly)

theorem futureCone_fold_is_exact_trace :
    (futureConeAt emptyReplay 2).fold futureConeTraceAlgebra =
      (futureConeAt emptyReplay 2).trace :=
  futureConeAt_fold_eq_trace emptyReplay 2

/-- Actualization selects an already exposed child and generates a new cone
rooted at the compiler-owned target. -/
theorem actualized_child_generates_new_cone :
    chosenPly.target ∈ (futureConeAt emptyReplay 1).frontier ∧
      futureConeAt chosenPly.extended 2 =
        finiteExposureFrom testLaw 2 chosenPly.target ∧
      (futureConeAt chosenPly.extended 2).root = chosenPly.target := by
  exact ⟨actualPly_target_mem_futureCone_one_frontier chosenPly,
    actualPly_extended_generates_new_futureCone chosenPly 2,
    actualPly_extended_futureCone_root chosenPly 2⟩

/-- A board-lookalike pass is exposed after the actual play but remains absent
from both the actual occurrence trace and the superko position history. -/
theorem unchosen_lookalike_branch_has_no_actual_write :
    afterPlayPassTarget ∈
        (futureConeAt chosenPly.extended 1).frontier ∧
      afterPlayPassTarget.visible.board =
        chosenPly.extended.final.visible.board ∧
      afterPlayPassTarget ∉ chosenPly.extended.toOccurrence.trace ∧
      afterPlayPassTarget.visible.situation ∉
        chosenPly.extended.final.positionHistory := by
  refine ⟨?_, unchosen_pass_has_same_board, ?_,
    unchosen_pass_situation_is_not_in_actual_positionHistory⟩
  · rw [futureConeAt_one_eq_rootedPossibilityAt]
    exact legalExpansion_target_mem_frontier afterPlay_pass_is_possible
  · rw [chosenPly.extended.occurrence_trace_eq_stateTrace]
    exact unchosen_pass_is_not_in_actual_trace

/-- Search fuel changes only the possibility face.  The same actual current,
trace, position-history write and generated dancers remain authoritative. -/
theorem two_fuel_preserves_actual_faces :
    (futureConeAt chosenPly.extended 2).root =
        chosenPly.extended.final ∧
      chosenPly.extended.toOccurrence.trace =
        chosenPly.extended.stateTrace ∧
      chosenPly.extended.toOccurrence.trace.map
          (fun frame => frame.visible.situation) =
        chosenPly.extended.final.positionHistory ∧
      Nonempty (GeneratedDancersAt chosenPly.extended) :=
  futureCone_actual_noninterference chosenPly.extended 2

/-- Terminality is read from the actual current.  Every finite fuel keeps the
same true rooted leaf; no empty frontier and no repeated self-step is created. -/
theorem terminal_is_same_rooted_leaf_at_every_fuel (fuel : Nat) :
    futureConeAt terminalReplay fuel =
        RootedAccountedUnfolding.zero terminalReplay.final ∧
      (futureConeAt terminalReplay fuel).frontier =
        [terminalReplay.final] ∧
      (futureConeAt terminalReplay fuel).trace =
        [terminalReplay.final] := by
  have leaf := finiteExposureFrom_eq_zero_of_terminal testLaw
    terminalReplay.final (.resignation .negative) terminalReplay_status fuel
  exact ⟨leaf,
    finiteExposureFrom_terminal_frontier testLaw terminalReplay.final
      (.resignation .negative) terminalReplay_status fuel,
    finiteExposureFrom_terminal_trace testLaw terminalReplay.final
      (.resignation .negative) terminalReplay_status fuel⟩

end G3SearchExposureRegression
end Go
end ProcessGame
end SaturationMonoid
