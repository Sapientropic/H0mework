import H0mework.Computation.AIGExecution.AIGExecutionCorrectnessSource

/-!
# Source-owned partial AIG progress

The source graph and assignment are fixed indices. A current stores its actual
fixed buffer and its written frontier; its proof-only lineage identifies that
buffer with the source's boot-to-step history. Boot accepts no correctness
certificate. Step updates the existing table, and completed reads never rerun it.
This is internal execution provenance, not a new root or recurrence calculus.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat

variable {α : Type} [DecidableEq α] [Hashable α]

/-- A partial current of one fixed source execution, not an arbitrary valid-size table. -/
structure AIGOwnedProgress (graph : AIG α) (assign : α → Bool) where
  state : AIGExecutionPrefix graph
  lineage : state = aigExecutionAfter graph assign state.cursor.val

/-- The unique stored cursor belongs to the actual fixed-buffer state. -/
@[inline] def AIGOwnedProgress.cursor {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) : Fin (graph.decls.size + 1) :=
  current.state.cursor

/-- Compatibility readout of the finite cursor, not an unbounded runtime counter. -/
@[inline] def AIGOwnedProgress.ticks {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) : Nat := current.cursor.val

theorem aigOwnedProgress_ticks_le {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) : current.ticks ≤ graph.decls.size :=
  Nat.le_of_lt_succ current.cursor.isLt

/-- Fixed assignment and finite cursor uniquely determine the actual cached state. -/
theorem aigOwnedProgress_ext_cursor {graph : AIG α} {assign : α → Bool}
    {left right : AIGOwnedProgress graph assign} (same : left.cursor = right.cursor) :
    left = right := by
  have states : left.state = right.state :=
    left.lineage.trans ((congrArg (aigExecutionAfter graph assign)
      (congrArg Fin.val same)).trans right.lineage.symm)
  cases left
  cases right
  cases states
  rfl

/-- Boot is always the actual empty table at tick zero. -/
def aigOwnedProgressBoot (graph : AIG α) (assign : α → Bool) :
    AIGOwnedProgress graph assign :=
  ⟨aigExecutionEmpty graph, rfl⟩

@[simp] theorem aigOwnedProgressBoot_ticks (graph : AIG α) (assign : α → Bool) :
    (aigOwnedProgressBoot graph assign).ticks = 0 := rfl

/-- One source declaration is consumed from the current cached table. -/
def aigOwnedProgressStep {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) : AIGOwnedProgress graph assign where
  state := aigExecutionStep graph assign current.state
  lineage := by
    calc
      aigExecutionStep graph assign current.state =
          aigExecutionStep graph assign
            (aigExecutionAfter graph assign current.state.cursor.val) :=
        congrArg (aigExecutionStep graph assign) current.lineage
      _ = aigExecutionAfter graph assign (current.state.cursor.val + 1) :=
        (aigExecutionAfter_succ graph assign current.state.cursor.val).symm
      _ = aigExecutionAfter graph assign
          (aigExecutionStep graph assign current.state).cursor.val := by
        rw [aigExecutionStep_cursor, aigExecutionAfter_min]

theorem aigOwnedProgressStep_state {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) :
    (aigOwnedProgressStep current).state = aigExecutionStep graph assign current.state := rfl

theorem aigOwnedProgressStep_ticks {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) :
    (aigOwnedProgressStep current).ticks = min (current.ticks + 1) graph.decls.size :=
  aigExecutionStep_cursor graph assign current.state

theorem aigOwnedProgress_size {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) :
    current.state.values.size = min current.ticks graph.decls.size := by
  rw [current.lineage, aigExecutionAfter_size]
  rfl

theorem aigOwnedProgress_size_eq_ticks {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) :
    current.state.values.size = current.ticks := by
  rw [aigOwnedProgress_size, Nat.min_eq_left (aigOwnedProgress_ticks_le current)]

/-- Unwritten cells belong to the same complete source history as the visible prefix. -/
theorem aigOwnedProgress_unwritten_zero {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) (index : Fin graph.decls.size)
    (future : current.ticks ≤ index.val) : current.state.buffer[index.val] = false := by
  rw [current.lineage]
  exact aigExecutionAfter_unwritten_zero graph assign current.state.cursor.val index future

theorem aigOwnedProgressStep_writes_frontier {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) (ready : current.ticks < graph.decls.size) :
    (aigOwnedProgressStep current).state.buffer[current.cursor.val]'ready =
      aigExecutionNextValue graph assign current.state
        (by simpa only [AIGExecutionPrefix.values_size,
          AIGOwnedProgress.ticks, AIGOwnedProgress.cursor] using ready) :=
  aigExecutionStep_writes_frontier graph assign current.state ready

theorem aigOwnedProgressStep_preserves_other {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) (index : Fin graph.decls.size)
    (different : current.cursor.val ≠ index.val) :
    (aigOwnedProgressStep current).state.buffer[index.val] = current.state.buffer[index.val] :=
  aigExecutionStep_preserves_other graph assign current.state index different

/-- Semantic correctness is derived from lineage, never supplied to fresh boot. -/
theorem aigOwnedProgress_consistent {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) :
    AIGExecutionConsistent graph assign current.state := by
  rw [current.lineage]
  exact aigExecutionAfter_consistent graph assign current.ticks

theorem aigOwnedProgress_complete_iff {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) :
    current.state.values.size = graph.decls.size ↔ graph.decls.size ≤ current.ticks := by
  rw [aigOwnedProgress_size]
  omega

/-- A completed source current stays legal; later clock attempts do not rewrite its table. -/
theorem aigOwnedProgressStep_complete_state {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign)
    (complete : current.state.values.size = graph.decls.size) :
    (aigOwnedProgressStep current).state = current.state :=
  aigExecutionStep_complete graph assign current.state complete

/-- Completion fixes the whole finite current, including its cursor. -/
theorem aigOwnedProgressStep_complete {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) (complete : graph.decls.size ≤ current.ticks) :
    aigOwnedProgressStep current = current := by
  apply aigOwnedProgress_ext_cursor
  apply Fin.ext
  change (aigOwnedProgressStep current).ticks = current.ticks
  rw [aigOwnedProgressStep_ticks]
  have bounded := aigOwnedProgress_ticks_le current
  omega

/-- Run the existing one-declaration step, retaining ownership after each step. -/
def aigOwnedProgressAfter (graph : AIG α) (assign : α → Bool) (ticks : Nat) :
    AIGOwnedProgress graph assign :=
  Nat.repeat aigOwnedProgressStep ticks (aigOwnedProgressBoot graph assign)

theorem aigOwnedProgressAfter_zero (graph : AIG α) (assign : α → Bool) :
    aigOwnedProgressAfter graph assign 0 = aigOwnedProgressBoot graph assign := rfl

theorem aigOwnedProgressAfter_succ (graph : AIG α) (assign : α → Bool) (ticks : Nat) :
    aigOwnedProgressAfter graph assign (ticks + 1) =
      aigOwnedProgressStep (aigOwnedProgressAfter graph assign ticks) := rfl

theorem aigOwnedProgressAfter_ticks (graph : AIG α) (assign : α → Bool) (ticks : Nat) :
    (aigOwnedProgressAfter graph assign ticks).ticks = min ticks graph.decls.size := by
  induction ticks with
  | zero => rfl
  | succ ticks ih =>
    rw [aigOwnedProgressAfter_succ, aigOwnedProgressStep_ticks, ih]
    omega

theorem aigOwnedProgressAfter_state (graph : AIG α) (assign : α → Bool) (ticks : Nat) :
    (aigOwnedProgressAfter graph assign ticks).state = aigExecutionAfter graph assign ticks := by
  change (aigOwnedProgressAfter graph assign ticks).state = _
  rw [(aigOwnedProgressAfter graph assign ticks).lineage]
  change aigExecutionAfter graph assign (aigOwnedProgressAfter graph assign ticks).ticks = _
  rw [aigOwnedProgressAfter_ticks, aigExecutionAfter_min]

theorem aigOwnedProgressAfter_source_count_completes (graph : AIG α) (assign : α → Bool) :
    (aigOwnedProgressAfter graph assign graph.decls.size).state.values.size =
      graph.decls.size := by
  rw [aigOwnedProgressAfter_state, aigExecutionAfter_size, Nat.min_self]

/-- Completion reads the stored table only; the source's canonical reader occurs only in proofs. -/
def aigOwnedProgressReadAt {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign)
    (complete : current.state.values.size = graph.decls.size) (ref : AIG.Ref graph) : Bool :=
  aigExecutionReadAt current.state complete ref

/-- A partial current exposes no finished output. -/
def aigOwnedProgressRead? {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) (ref : AIG.Ref graph) : Option Bool :=
  aigExecutionRead? current.state ref

/-- Any completed owned table reads the canonical source value. -/
theorem aigOwnedProgressReadAt_eq_read {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign)
    (complete : current.state.values.size = graph.decls.size) (ref : AIG.Ref graph) :
    aigOwnedProgressReadAt current complete ref = aigExecutionRead assign ref := by
  rw [aigExecutionRead_eq_denote]
  exact aigExecutionReadAt_eq_denote_of_consistent graph assign current.state complete
    (aigOwnedProgress_consistent current) ref

theorem aigOwnedProgressRead?_complete {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign)
    (complete : current.state.values.size = graph.decls.size) (ref : AIG.Ref graph) :
    aigOwnedProgressRead? current ref = some (aigExecutionRead assign ref) := by
  have cursorComplete : current.state.cursor.val = graph.decls.size := by
    rw [← AIGExecutionPrefix.values_size]
    exact complete
  simp only [aigOwnedProgressRead?, aigExecutionRead?, if_pos cursorComplete]
  exact congrArg some (aigOwnedProgressReadAt_eq_read current complete ref)

theorem aigOwnedProgressRead?_early {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) (early : current.ticks < graph.decls.size)
    (ref : AIG.Ref graph) :
    aigOwnedProgressRead? current ref = none := by
  apply aigExecutionRead?_incomplete
  rw [aigOwnedProgress_size]
  omega

theorem aigOwnedProgressRead?_isSome_iff {graph : AIG α} {assign : α → Bool}
    (current : AIGOwnedProgress graph assign) (ref : AIG.Ref graph) :
    (aigOwnedProgressRead? current ref).isSome = true ↔ graph.decls.size ≤ current.ticks := by
  unfold aigOwnedProgressRead?
  rw [current.lineage]
  exact aigExecutionAfter_output_iff_complete graph assign current.ticks ref

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
