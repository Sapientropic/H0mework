import Std.Sat.AIG.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Array.Extract

/-!
# Fixed AIG storage and its written-prefix view

The actual state is a source-sized Boolean buffer plus a bounded frontier.
The array prefix is a compatibility readout for proofs, never the execution
storage. Only the frontier determines which initialized slots are written.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat

variable {α : Type} [DecidableEq α] [Hashable α]

structure AIGExecutionPrefix (graph : AIG α) where
  buffer : Vector Bool graph.decls.size
  cursor : Fin (graph.decls.size + 1)

namespace AIGExecutionPrefix

@[ext] theorem ext {graph : AIG α} {left right : AIGExecutionPrefix graph}
    (buffers : left.buffer = right.buffer) (cursors : left.cursor = right.cursor) :
    left = right := by
  cases left
  cases right
  cases buffers
  cases cursors
  rfl

theorem cursor_le {graph : AIG α} (state : AIGExecutionPrefix graph) :
    state.cursor.val ≤ graph.decls.size :=
  Nat.le_of_lt_succ state.cursor.isLt

/-- Proof/compatibility view of written slots; runtime operators use the buffer directly. -/
def values {graph : AIG α} (state : AIGExecutionPrefix graph) : Array Bool :=
  state.buffer.toArray.take state.cursor.val

@[simp] theorem values_size {graph : AIG α} (state : AIGExecutionPrefix graph) :
    state.values.size = state.cursor.val := by
  simp only [values, Array.size_extract, Vector.size_toArray, Nat.sub_zero]
  exact Nat.min_eq_left state.cursor_le

theorem bounded {graph : AIG α} (state : AIGExecutionPrefix graph) :
    state.values.size ≤ graph.decls.size := by
  rw [values_size]
  exact state.cursor_le

theorem values_get {graph : AIG α} (state : AIGExecutionPrefix graph)
    (index : Nat) (present : index < state.values.size) :
    state.values[index] =
      state.buffer[index]'(Nat.lt_of_lt_of_le (by simpa only [values_size] using present)
        state.cursor_le) := by
  simp only [values, Array.getElem_extract, Nat.zero_add]
  rfl

theorem values_eq_buffer_of_complete {graph : AIG α} (state : AIGExecutionPrefix graph)
    (complete : state.values.size = graph.decls.size) :
    state.values = state.buffer.toArray := by
  have cursor : state.cursor.val = graph.decls.size := by
    simpa only [values_size] using complete
  simp [values, cursor]

end AIGExecutionPrefix

theorem aigExecution_set_take_frontier {size : Nat} (buffer : Vector Bool size)
    (cursor : Nat) (ready : cursor < size) (value : Bool) :
    (buffer.set cursor value ready).toArray.take (cursor + 1) =
      (buffer.toArray.take cursor).push value := by
  apply Array.ext
  · simp only [Array.size_extract, Vector.size_toArray, Nat.sub_zero, Array.size_push]
    omega
  · intro index leftBound rightBound
    simp only [Array.size_extract, Vector.size_toArray, Nat.sub_zero] at leftBound
    simp only [Vector.toArray_set, Array.getElem_extract, Nat.zero_add, Array.getElem_set,
      Array.getElem_push, Array.size_extract, Vector.size_toArray, Nat.sub_zero]
    by_cases old : index < cursor
    · simp [Nat.min_eq_left (Nat.le_of_lt ready), old, Ne.symm (Nat.ne_of_lt old)]
    · have newest : index = cursor := by omega
      subst index
      simp [Nat.min_eq_left (Nat.le_of_lt ready)]

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
