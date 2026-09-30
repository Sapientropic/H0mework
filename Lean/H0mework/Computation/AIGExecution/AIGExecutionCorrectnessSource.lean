import H0mework.Computation.AIGExecution.AIGExecutionSource

/-!
# Exact semantics of the generated AIG table

The semantic invariant is proved from the zero-frontier buffer and the actual one-node
step. It is not a field of the runtime state or an input to the public executor.
Completed reference reads equal the library's recursive denotation.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat

variable {α : Type} [DecidableEq α] [Hashable α]

/-- Proof-only invariant over values generated so far. -/
def AIGExecutionConsistent (graph : AIG α) (assign : α → Bool)
    (state : AIGExecutionPrefix graph) : Prop :=
  ∀ (index : Nat) (present : index < state.values.size),
    state.values[index] = AIG.denote.go index graph.decls assign
      (Nat.lt_of_lt_of_le present state.bounded) graph.hdag

theorem aigExecutionEmpty_consistent (graph : AIG α) (assign : α → Bool) :
    AIGExecutionConsistent graph assign (aigExecutionEmpty graph) := by
  intro index present
  simp only [AIGExecutionPrefix.values_size, aigExecutionEmpty] at present
  exact False.elim (Nat.not_lt_zero index present)

theorem aigExecutionNextValue_eq_denote (graph : AIG α) (assign : α → Bool)
    (state : AIGExecutionPrefix graph) (ready : state.values.size < graph.decls.size)
    (consistent : AIGExecutionConsistent graph assign state) :
    aigExecutionNextValue graph assign state ready =
      AIG.denote.go state.values.size graph.decls assign ready graph.hdag := by
  unfold aigExecutionNextValue
  simp only [AIGExecutionPrefix.values_size] at ready ⊢
  rw [AIG.denote.go.eq_def]
  split
  · rename_i selected
    split <;> rename_i branch <;> simp only [selected] at branch <;> first | rfl | contradiction
  · rename_i input selected
    split <;> rename_i branch <;> simp only [selected] at branch
    · contradiction
    · cases branch
      rfl
    · contradiction
  · rename_i left right selected
    have fanins := graph.hdag ready selected
    split <;> rename_i branch <;> simp only [selected] at branch
    · contradiction
    · contradiction
    · cases branch
      dsimp only
      have leftValue := consistent left.gate
        (by simpa only [AIGExecutionPrefix.values_size] using fanins.1)
      have rightValue := consistent right.gate
        (by simpa only [AIGExecutionPrefix.values_size] using fanins.2)
      rw [AIGExecutionPrefix.values_get] at leftValue rightValue
      rw [leftValue, rightValue]

theorem aigExecutionStep_consistent (graph : AIG α) (assign : α → Bool)
    (state : AIGExecutionPrefix graph)
    (consistent : AIGExecutionConsistent graph assign state) :
    AIGExecutionConsistent graph assign (aigExecutionStep graph assign state) := by
  by_cases ready : state.values.size < graph.decls.size
  · intro index present
    have values := aigExecutionStep_values graph assign state ready
    have size : (aigExecutionStep graph assign state).values.size = state.values.size + 1 := by
      rw [values, Array.size_push]
    by_cases old : index < state.values.size
    · simpa only [values, Array.getElem_push_lt old] using consistent index old
    · have newest : index = state.values.size := by omega
      subst index
      simpa only [values, Array.getElem_push_eq] using
        aigExecutionNextValue_eq_denote graph assign state ready consistent
  · have notReady : ¬ state.cursor.val < graph.decls.size := by
      simpa only [AIGExecutionPrefix.values_size] using ready
    simpa only [aigExecutionStep, dif_neg notReady] using consistent

/-- The invariant is generated for every finite execution, with no semantic premise. -/
theorem aigExecutionAfter_consistent (graph : AIG α) (assign : α → Bool) (ticks : Nat) :
    AIGExecutionConsistent graph assign (aigExecutionAfter graph assign ticks) := by
  induction ticks with
  | zero => exact aigExecutionEmpty_consistent graph assign
  | succ ticks ih =>
    exact aigExecutionStep_consistent graph assign (aigExecutionAfter graph assign ticks) ih

theorem aigExecutionRun_consistent (graph : AIG α) (assign : α → Bool) :
    AIGExecutionConsistent graph assign (aigExecutionRun graph assign) :=
  aigExecutionAfter_consistent graph assign graph.decls.size

/-- A completed buffer read consumes the generated written-prefix invariant. -/
theorem aigExecutionReadAt_eq_denote_of_consistent (graph : AIG α) (assign : α → Bool)
    (state : AIGExecutionPrefix graph) (complete : state.values.size = graph.decls.size)
    (consistent : AIGExecutionConsistent graph assign state) (ref : AIG.Ref graph) :
    aigExecutionReadAt state complete ref = AIG.denote assign ⟨graph, ref⟩ := by
  have present : ref.gate < state.values.size := by rw [complete]; exact ref.hgate
  have value := consistent ref.gate present
  rw [AIGExecutionPrefix.values_get] at value
  unfold aigExecutionReadAt AIG.denote
  rw [value]

/-- All references are classified by the same generated table, including inverted refs. -/
theorem aigExecutionRun_read_eq_denote (graph : AIG α) (assign : α → Bool)
    (ref : AIG.Ref graph) :
    aigExecutionReadAt (aigExecutionRun graph assign)
      (aigExecutionRun_size graph assign) ref =
        AIG.denote assign ⟨graph, ref⟩ :=
  aigExecutionReadAt_eq_denote_of_consistent graph assign (aigExecutionRun graph assign)
    (aigExecutionRun_size graph assign) (aigExecutionRun_consistent graph assign) ref

theorem aigExecutionRead_eq_denote (graph : AIG α) (assign : α → Bool)
    (ref : AIG.Ref graph) :
    aigExecutionRead assign ref = AIG.denote assign ⟨graph, ref⟩ :=
  aigExecutionRun_read_eq_denote graph assign ref

theorem aigExecutionRun_read?_eq_denote (graph : AIG α) (assign : α → Bool)
    (ref : AIG.Ref graph) :
    aigExecutionRead? (aigExecutionRun graph assign) ref =
      some (AIG.denote assign ⟨graph, ref⟩) := by
  have complete := aigExecutionRun_size graph assign
  have cursor : (aigExecutionRun graph assign).cursor.val = graph.decls.size := by
    simpa only [AIGExecutionPrefix.values_size] using complete
  simp only [aigExecutionRead?, if_pos cursor]
  exact congrArg some (aigExecutionRun_read_eq_denote graph assign ref)

/-- A correct value copied from elsewhere does not authorize an early completed read. -/
theorem aigExecutionAfter_output_iff_complete (graph : AIG α) (assign : α → Bool)
    (ticks : Nat) (ref : AIG.Ref graph) :
    (aigExecutionRead? (aigExecutionAfter graph assign ticks) ref).isSome = true ↔
      graph.decls.size ≤ ticks := by
  unfold aigExecutionRead?
  split
  · rename_i complete
    have sizes := aigExecutionAfter_cursor graph assign ticks
    simp only [Option.isSome_some, true_iff]
    omega
  · rename_i incomplete
    have sizes := aigExecutionAfter_cursor graph assign ticks
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    omega

/-- The active source declaration writes exactly the current frontier slot. -/
theorem aigExecutionStep_writes_frontier (graph : AIG α) (assign : α → Bool)
    (state : AIGExecutionPrefix graph) (ready : state.cursor.val < graph.decls.size) :
    (aigExecutionStep graph assign state).buffer[state.cursor.val] =
      aigExecutionNextValue graph assign state
        (by simpa only [AIGExecutionPrefix.values_size] using ready) := by
  rw [aigExecutionStep_buffer graph assign state ready, Vector.getElem_set_self]

theorem aigExecutionStep_preserves_other (graph : AIG α) (assign : α → Bool)
    (state : AIGExecutionPrefix graph) (index : Fin graph.decls.size)
    (different : state.cursor.val ≠ index.val) :
    (aigExecutionStep graph assign state).buffer[index.val] = state.buffer[index.val] := by
  unfold aigExecutionStep
  split
  · rename_i ready
    exact Vector.getElem_set_ne ready index.isLt different
  · rfl

/-- Every gate at the frontier addresses two strictly earlier written slots. -/
theorem aigExecutionNextValue_fanins_written {graph : AIG α}
    (state : AIGExecutionPrefix graph) (ready : state.cursor.val < graph.decls.size)
    (left right : AIG.Fanin)
    (selected : graph.decls[state.cursor.val] = .gate left right) :
    left.gate < state.cursor.val ∧ right.gate < state.cursor.val :=
  graph.hdag ready selected

theorem aigExecutionAfter_unwritten_zero (graph : AIG α) (assign : α → Bool)
    (ticks : Nat) (index : Fin graph.decls.size) (future : ticks ≤ index.val) :
    (aigExecutionAfter graph assign ticks).buffer[index.val] = false := by
  induction ticks with
  | zero => simp [aigExecutionAfter_zero, aigExecutionEmpty]
  | succ ticks ih =>
      rw [aigExecutionAfter_succ]
      have different : (aigExecutionAfter graph assign ticks).cursor.val ≠ index.val := by
        rw [aigExecutionAfter_cursor]
        omega
      rw [aigExecutionStep_preserves_other graph assign _ index different]
      exact ih (by omega)

theorem aigExecutionAfter_unwritten_zero_of_cursor (graph : AIG α) (assign : α → Bool)
    (ticks : Nat) (index : Fin graph.decls.size)
    (future : (aigExecutionAfter graph assign ticks).cursor.val ≤ index.val) :
    (aigExecutionAfter graph assign ticks).buffer[index.val] = false := by
  apply aigExecutionAfter_unwritten_zero
  rw [aigExecutionAfter_cursor] at future
  have bound := index.isLt
  omega

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
