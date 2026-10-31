import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.GeneratedDancers

/-!
# Same-root actual play and finite Go possibility

The fixed Go compiler finitely enumerates every placement, pass and
resignation from one current.  The resulting branches are exposed through the
existing `RootedAccountedUnfolding`; they are possibility readouts only.

Actual authority remains indexed by a `GeneratedReplay` from `Frame.initial`.
Only an `ActualPly` may select one generated child and extend that replay, so
the other legal leaves never enter actual position history or generated
player/group lineage.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-- The fixed finite move carrier: every board point, followed by pass and
resignation.  It is a compiler input enumeration, not an actual event list. -/
def allPoints (n : Nat) : List (Point n) :=
  (List.ofFn fun row : Fin n =>
    List.ofFn fun column : Fin n => (row, column)).flatten

def allMoves (n : Nat) : List (Move n) :=
  (allPoints n).map Move.play ++
    [.pass, .resign]

theorem point_mem_allPoints {n : Nat} (point : Point n) :
    point ∈ allPoints n := by
  simp [allPoints]

theorem move_mem_allMoves {n : Nat} (move : Move n) :
    move ∈ allMoves n := by
  cases move with
  | play point => simp [allMoves, point_mem_allPoints]
  | pass => simp [allMoves]
  | resign => simp [allMoves]

/-- All and only successful images of `nativeStep?` at one fixed current.
The pair retains the emitted move so a later actual ply can identify its exact
compiler image. -/
def legalExpansion {n : Nat} (law : Law) (current : Frame n) :
    List (Move n × Frame n) :=
  (allMoves n).filterMap fun move =>
    (nativeStep? law current move).map fun target => (move, target)

theorem mem_legalExpansion_iff {n : Nat} {law : Law}
    {current target : Frame n} {move : Move n} :
    (move, target) ∈ legalExpansion law current ↔
      LegalStep law current move target := by
  simp [legalExpansion, LegalStep, move_mem_allMoves]

theorem legalExpansion_complete {n : Nat} {law : Law}
    {current target : Frame n} {move : Move n}
    (step : LegalStep law current move target) :
    (move, target) ∈ legalExpansion law current :=
  mem_legalExpansion_iff.mpr step

theorem legalExpansion_sound {n : Nat} {law : Law}
    {current target : Frame n} {move : Move n}
    (member : (move, target) ∈ legalExpansion law current) :
    LegalStep law current move target :=
  mem_legalExpansion_iff.mp member

/-- Target projection of the exact move-indexed expansion. -/
def legalTargets {n : Nat} (law : Law) (current : Frame n) : List (Frame n) :=
  (legalExpansion law current).map Prod.snd

/-- Existing branch storage populated only with rooted leaves.  An empty list
stays `.nil`; its enclosing current therefore remains a rooted leaf. -/
def possibilityBranches {n : Nat} :
    List (Frame n) → AccountedBranches (Frame n)
  | [] => .nil
  | target :: targets =>
      .cons (RootedAccountedUnfolding.zero target)
        (possibilityBranches targets)

@[simp] theorem frontierBranches_possibilityBranches {n : Nat}
    (targets : List (Frame n)) :
    RootedAccountedUnfolding.frontierBranches
        (possibilityBranches targets) = targets := by
  induction targets with
  | nil => rfl
  | cons target targets ih =>
      change [target] ++
          RootedAccountedUnfolding.frontierBranches
            (possibilityBranches targets) = target :: targets
      simp [ih]

@[simp] theorem traceBranches_possibilityBranches {n : Nat}
    (targets : List (Frame n)) :
    RootedAccountedUnfolding.traceBranches
        (possibilityBranches targets) = targets := by
  induction targets with
  | nil => rfl
  | cons target targets ih =>
      change [target] ++
          RootedAccountedUnfolding.traceBranches
            (possibilityBranches targets) = target :: targets
      simp [ih]

/-- One finite possibility exposure at a calculation current.  This function
has no actual-write mouth: it only builds the existing occurrence constructor
from compiler-generated leaves. -/
def possibilityStep {n : Nat} (law : Law) (current : Frame n) :
    RootedAccountedUnfolding (Frame n) :=
  .occur current (possibilityBranches (legalTargets law current))

@[simp] theorem possibilityStep_root {n : Nat} (law : Law)
    (current : Frame n) :
    (possibilityStep law current).root = current :=
  rfl

@[simp] theorem possibilityStep_trace {n : Nat} (law : Law)
    (current : Frame n) :
    (possibilityStep law current).trace =
      current :: legalTargets law current := by
  change current ::
      RootedAccountedUnfolding.traceBranches
        (possibilityBranches (legalTargets law current)) = _
  rw [traceBranches_possibilityBranches]

theorem possibilityStep_frontier_of_targets_ne_nil {n : Nat}
    (law : Law) (current : Frame n)
    (nonempty : legalTargets law current ≠ []) :
    (possibilityStep law current).frontier = legalTargets law current := by
  cases targetsEq : legalTargets law current with
  | nil => exact False.elim (nonempty targetsEq)
  | cons target targets =>
      unfold possibilityStep
      rw [targetsEq]
      change RootedAccountedUnfolding.frontierBranches
          (possibilityBranches (target :: targets)) = target :: targets
      exact frontierBranches_possibilityBranches (target :: targets)

theorem legalExpansion_target_mem_frontier {n : Nat} {law : Law}
    {current target : Frame n} {move : Move n}
    (member : (move, target) ∈ legalExpansion law current) :
    target ∈ (possibilityStep law current).frontier := by
  have targetMem : target ∈ legalTargets law current :=
    List.mem_map_of_mem member
  have targetsNonempty : legalTargets law current ≠ [] := by
    intro targetsEmpty
    simp [targetsEmpty] at targetMem
  rw [possibilityStep_frontier_of_targets_ne_nil law current
    targetsNonempty]
  exact targetMem

/-- The actual-root-indexed possibility mouth.  Unlike `possibilityStep`, it
cannot be invoked with a raw frame: its current is the final current of the
same replay generated from `Frame.initial`. -/
def rootedPossibilityAt {n : Nat} {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) :
    RootedAccountedUnfolding (Frame n) :=
  possibilityStep law replay.final

@[simp] theorem rootedPossibilityAt_root {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) :
    (rootedPossibilityAt replay).root = replay.final :=
  rfl

@[simp] theorem rootedPossibilityAt_positionHistory {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) :
    (rootedPossibilityAt replay).root.positionHistory =
      replay.final.positionHistory :=
  rfl

/-- Chosen-child membership requires an exact `ActualPly` on the same replay;
a raw `LegalStep` is intentionally insufficient for this actual mouth. -/
theorem actualPly_mem_legalExpansion {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replayPrefix) :
    (ply.emitted, ply.target) ∈
      legalExpansion law replayPrefix.final :=
  legalExpansion_complete ply.step

theorem actualPly_target_mem_legalTargets {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replayPrefix) :
    ply.target ∈ legalTargets law replayPrefix.final := by
  exact List.mem_map_of_mem (actualPly_mem_legalExpansion ply)

/-- The selected actual child is one of the possibility leaves exposed at the
same generated current. -/
theorem actualPly_target_mem_frontier {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replayPrefix) :
    ply.target ∈ (rootedPossibilityAt replayPrefix).frontier := by
  exact legalExpansion_target_mem_frontier
    (actualPly_mem_legalExpansion ply)

/-- Exact chosen/unchosen separation at one generated replay frontier.  Both
compiler images remain visible in the same possibility frontier, while the
actual replay, position-history write and generated dancers are indexed only
by `ply.extended`.  No claim is made that distinct moves can never converge to
the same target; concrete exclusion is a domain regression responsibility. -/
theorem actualPly_chosen_unchosen_separation {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replayPrefix)
    {unchosenMove : Move n} {unchosenTarget : Frame n}
    (unchosenPossible :
      (unchosenMove, unchosenTarget) ∈
        legalExpansion law replayPrefix.final)
    (move_ne : unchosenMove ≠ ply.emitted) :
    (ply.emitted, ply.target) ∈
        legalExpansion law replayPrefix.final ∧
      (unchosenMove, unchosenTarget) ∈
        legalExpansion law replayPrefix.final ∧
      ply.target ∈ (rootedPossibilityAt replayPrefix).frontier ∧
      unchosenTarget ∈ (rootedPossibilityAt replayPrefix).frontier ∧
      unchosenMove ≠ ply.emitted ∧
      ply.extended.stateTrace = replayPrefix.stateTrace ++ [ply.target] ∧
      ply.extended.final.positionHistory =
        replayPrefix.final.positionHistory ++
          [ply.target.visible.situation] ∧
      Nonempty (GeneratedDancersAt ply.extended) := by
  refine ⟨actualPly_mem_legalExpansion ply, unchosenPossible,
    actualPly_target_mem_frontier ply, ?_, move_ne,
    ply.extended_stateTrace_eq, ?_, ⟨generatedDancersAt ply.extended⟩⟩
  · exact legalExpansion_target_mem_frontier unchosenPossible
  · simpa [GeneratedReplay.ActualPly.extended] using
      nativeStep_positionHistory_eq ply.step

/-- Possibility exposure and actual lineage are two readouts at the same
generated current.  The exposure root reads the existing position history;
the actual trace and player/group faces remain indexed by the original replay.
Concrete unchosen-branch exclusion is checked by the direct regression. -/
theorem rootedPossibilityAt_actual_faces {n : Nat} {law : Law}
    {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) :
    (rootedPossibilityAt replay).root.positionHistory =
        replay.final.positionHistory ∧
      replay.toOccurrence.trace = replay.stateTrace ∧
      replay.toOccurrence.trace.map
          (fun frame => frame.visible.situation) =
        replay.final.positionHistory ∧
      Nonempty (GeneratedDancersAt replay) := by
  exact ⟨rfl, replay.occurrence_trace_eq_stateTrace,
    generated_occurrence_situations_eq_positionHistory replay,
    ⟨generatedDancersAt replay⟩⟩

theorem nativeStep_eq_none_of_terminal {n : Nat} (law : Law)
    (current : Frame n) (reason : TerminalReason)
    (terminal : current.visible.status = .terminal reason)
    (move : Move n) :
    nativeStep? law current move = none := by
  cases move <;>
    simp [nativeStep?, stepVisible?, playVisible?, passVisible?,
      resignVisible?, terminal]

/-- Terminality is calculated from the current.  Its legal expansion is
empty, but the current itself is not erased. -/
theorem legalExpansion_eq_nil_of_terminal {n : Nat} (law : Law)
    (current : Frame n) (reason : TerminalReason)
    (terminal : current.visible.status = .terminal reason) :
    legalExpansion law current = [] := by
  simp [legalExpansion,
    nativeStep_eq_none_of_terminal law current reason terminal]

theorem possibilityStep_eq_zero_of_terminal {n : Nat} (law : Law)
    (current : Frame n) (reason : TerminalReason)
    (terminal : current.visible.status = .terminal reason) :
    possibilityStep law current = RootedAccountedUnfolding.zero current := by
  simp [possibilityStep, legalTargets,
    legalExpansion_eq_nil_of_terminal law current reason terminal,
    possibilityBranches, RootedAccountedUnfolding.zero]

theorem possibilityStep_terminal_frontier {n : Nat} (law : Law)
    (current : Frame n) (reason : TerminalReason)
    (terminal : current.visible.status = .terminal reason) :
    (possibilityStep law current).frontier = [current] := by
  rw [possibilityStep_eq_zero_of_terminal law current reason terminal]
  rfl

end Go
end ProcessGame
end SaturationMonoid
