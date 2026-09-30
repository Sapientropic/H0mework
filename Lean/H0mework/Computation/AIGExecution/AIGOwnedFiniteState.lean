import H0mework.Computation.AIGExecution.AIGOwnedBatch
import Mathlib.Data.Finite.Defs

/-!
# Exact finite source-execution orbits

For a fixed graph and assignment, the stored cursor is a complete coordinate of
an owned current. Its inverse executes the existing source history to that
cursor; it does not install a completed table into runtime boot. External clocks
classify the same current exactly when their source-bounded minima agree.
The batch classification also includes zero jobs: its finite control cursor is
retained even when there are no tables to read.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat

variable {α : Type} [DecidableEq α] [Hashable α] {jobs : Nat}

/-- The whole owned orbit has exactly one current for each source-bounded cursor. -/
def aigOwnedProgressEquivCursor (graph : AIG α) (assign : α → Bool) :
    AIGOwnedProgress graph assign ≃ Fin (graph.decls.size + 1) where
  toFun current := current.cursor
  invFun cursor := aigOwnedProgressAfter graph assign cursor.val
  left_inv current := by
    apply aigOwnedProgress_ext_cursor
    apply Fin.ext
    change (aigOwnedProgressAfter graph assign current.cursor.val).ticks = current.cursor.val
    rw [aigOwnedProgressAfter_ticks]
    exact Nat.min_eq_left (Nat.le_of_lt_succ current.cursor.isLt)
  right_inv cursor := by
    apply Fin.ext
    change (aigOwnedProgressAfter graph assign cursor.val).ticks = cursor.val
    rw [aigOwnedProgressAfter_ticks]
    exact Nat.min_eq_left (Nat.le_of_lt_succ cursor.isLt)

instance aigOwnedProgressFinite (graph : AIG α) (assign : α → Bool) :
    Finite (AIGOwnedProgress graph assign) :=
  ⟨aigOwnedProgressEquivCursor graph assign⟩

/-- All parallel source histories share the same exact finite clock coordinate. -/
def aigOwnedBatchEquivCursor (graph : AIG α) (assign : Fin jobs → α → Bool) :
    AIGOwnedBatch graph assign ≃ Fin (graph.decls.size + 1) where
  toFun current := current.cursor
  invFun cursor := aigOwnedBatchAfter graph assign cursor.val
  left_inv current := by
    apply aigOwnedBatch_ext_cursor
    apply Fin.ext
    change (aigOwnedBatchAfter graph assign current.cursor.val).ticks = current.cursor.val
    rw [aigOwnedBatchAfter_ticks]
    exact Nat.min_eq_left (Nat.le_of_lt_succ current.cursor.isLt)
  right_inv cursor := by
    apply Fin.ext
    change (aigOwnedBatchAfter graph assign cursor.val).ticks = cursor.val
    rw [aigOwnedBatchAfter_ticks]
    exact Nat.min_eq_left (Nat.le_of_lt_succ cursor.isLt)

instance aigOwnedBatchFinite (graph : AIG α) (assign : Fin jobs → α → Bool) :
    Finite (AIGOwnedBatch graph assign) :=
  ⟨aigOwnedBatchEquivCursor graph assign⟩

theorem aigOwnedProgressAfter_eq_iff (graph : AIG α) (assign : α → Bool)
    (left right : Nat) :
    aigOwnedProgressAfter graph assign left = aigOwnedProgressAfter graph assign right ↔
      min left graph.decls.size = min right graph.decls.size := by
  constructor
  · intro same
    simpa only [aigOwnedProgressAfter_ticks] using congrArg AIGOwnedProgress.ticks same
  · intro same
    apply aigOwnedProgress_ext_cursor
    apply Fin.ext
    change (aigOwnedProgressAfter graph assign left).ticks =
      (aigOwnedProgressAfter graph assign right).ticks
    simpa only [aigOwnedProgressAfter_ticks] using same

theorem aigOwnedBatchAfter_eq_iff (graph : AIG α) (assign : Fin jobs → α → Bool)
    (left right : Nat) :
    aigOwnedBatchAfter graph assign left = aigOwnedBatchAfter graph assign right ↔
      min left graph.decls.size = min right graph.decls.size := by
  constructor
  · intro same
    simpa only [aigOwnedBatchAfter_ticks] using congrArg AIGOwnedBatch.ticks same
  · intro same
    apply aigOwnedBatch_ext_cursor
    apply Fin.ext
    change (aigOwnedBatchAfter graph assign left).ticks =
      (aigOwnedBatchAfter graph assign right).ticks
    simpa only [aigOwnedBatchAfter_ticks] using same

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
