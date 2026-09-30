import H0mework.Computation.AIGExecution.AIGOwnedProgress
import Init.Data.Vector.Lemmas
import Init.Data.List.Nat.Pairwise

/-!
# One-declaration parallel batches on one source graph

Jobs have distinct fixed assignments and one shared graph-bounded cursor. Actual
storage is a vector of source-sized Boolean buffers, not deferred functions or
variable-length prefixes. Each batch step moves one buffer slot out before
writing its current source address. The legacy prefix table is a proof/readout
view only.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat

variable {α : Type} [DecidableEq α] [Hashable α] {jobs : Nat}

/-- `modify` releases the old buffer slot before executing its one addressed write. -/
private def aigOwnedBatchMoveOne (graph : AIG α) (assign : Fin jobs → α → Bool)
    (cursor : Fin (graph.decls.size + 1))
    (buffers : Vector (Vector Bool graph.decls.size) jobs) (job : Fin jobs) :
    Vector (Vector Bool graph.decls.size) jobs :=
  ⟨buffers.toArray.modify job.val (fun buffer =>
      (aigExecutionStep graph (assign job) ⟨buffer, cursor⟩).buffer), by simp⟩

private theorem aigOwnedBatchMoveOne_get (graph : AIG α) (assign : Fin jobs → α → Bool)
    (cursor : Fin (graph.decls.size + 1))
    (buffers : Vector (Vector Bool graph.decls.size) jobs) (job index : Fin jobs) :
    (aigOwnedBatchMoveOne graph assign cursor buffers job)[index.val] =
      if job = index then
        (aigExecutionStep graph (assign index) ⟨buffers[index.val], cursor⟩).buffer
      else buffers[index.val] := by
  change (buffers.toArray.modify job.val _)[index.val] = _
  rw [Array.getElem_modify]
  by_cases same : job = index
  · subst job; simp
  · have different : job.val ≠ index.val := fun equal => same (Fin.ext equal)
    simp [same, different]

private theorem aigOwnedBatchMoveFold_get (graph : AIG α) (assign : Fin jobs → α → Bool)
    (cursor : Fin (graph.decls.size + 1))
    (todo : List (Fin jobs)) (unique : todo.Nodup)
    (buffers : Vector (Vector Bool graph.decls.size) jobs) (index : Fin jobs) :
    (todo.foldl (aigOwnedBatchMoveOne graph assign cursor) buffers)[index.val] =
      if index ∈ todo then
        (aigExecutionStep graph (assign index) ⟨buffers[index.val], cursor⟩).buffer
      else buffers[index.val] := by
  induction todo generalizing buffers with
  | nil => simp
  | cons job todo ih =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
      rw [List.foldl_cons, ih unique, aigOwnedBatchMoveOne_get]
      by_cases same : job = index
      · subst job
        simp [absent]
      · by_cases member : index ∈ todo <;> simp [same, Ne.symm same, member]

private def aigOwnedBatchMoveAll (graph : AIG α) (assign : Fin jobs → α → Bool)
    (cursor : Fin (graph.decls.size + 1))
    (buffers : Vector (Vector Bool graph.decls.size) jobs) :
    Vector (Vector Bool graph.decls.size) jobs :=
  Fin.foldl jobs (aigOwnedBatchMoveOne graph assign cursor) buffers

private theorem aigOwnedBatchMoveAll_get (graph : AIG α) (assign : Fin jobs → α → Bool)
    (cursor : Fin (graph.decls.size + 1))
    (buffers : Vector (Vector Bool graph.decls.size) jobs) (job : Fin jobs) :
    (aigOwnedBatchMoveAll graph assign cursor buffers)[job.val] =
      (aigExecutionStep graph (assign job) ⟨buffers[job.val], cursor⟩).buffer := by
  rw [aigOwnedBatchMoveAll, Fin.foldl_eq_finRange_foldl,
    aigOwnedBatchMoveFold_get graph assign cursor _ (List.nodup_finRange jobs)]
  simp

/-- All jobs store fixed source-sized buffers and one shared written frontier. -/
structure AIGOwnedBatch (graph : AIG α) (assign : Fin jobs → α → Bool) where
  buffers : Vector (Vector Bool graph.decls.size) jobs
  cursor : Fin (graph.decls.size + 1)
  bufferLineage : ∀ job : Fin jobs,
    buffers[job.val] = (aigExecutionAfter graph (assign job) cursor.val).buffer

@[inline] def AIGOwnedBatch.ticks {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) : Nat := current.cursor.val

theorem aigOwnedBatch_ticks_le {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) : current.ticks ≤ graph.decls.size :=
  Nat.le_of_lt_succ current.cursor.isLt

/-- Every actual job buffer has the source graph's fixed cell capacity. -/
@[simp] theorem aigOwnedBatch_buffer_size {graph : AIG α}
    {assign : Fin jobs → α → Bool} (current : AIGOwnedBatch graph assign)
    (job : Fin jobs) : current.buffers[job.val].toArray.size = graph.decls.size :=
  Vector.size_toArray _

/-- Initialized tail cells remain visibly unwritten zeroes behind the shared frontier. -/
theorem aigOwnedBatch_unwritten_zero {graph : AIG α}
    {assign : Fin jobs → α → Bool} (current : AIGOwnedBatch graph assign)
    (job : Fin jobs) (index : Fin graph.decls.size)
    (future : current.ticks ≤ index.val) :
    current.buffers[job.val][index.val] = false := by
  rw [current.bufferLineage job]
  exact aigExecutionAfter_unwritten_zero graph (assign job) current.cursor.val index future

private theorem aigOwnedBatchState_eq_after {graph : AIG α}
    {assign : Fin jobs → α → Bool} (current : AIGOwnedBatch graph assign)
    (job : Fin jobs) :
    (⟨current.buffers[job.val], current.cursor⟩ : AIGExecutionPrefix graph) =
      aigExecutionAfter graph (assign job) current.cursor.val := by
  apply AIGExecutionPrefix.ext
  · exact current.bufferLineage job
  · apply Fin.ext
    change current.cursor.val =
      (aigExecutionAfter graph (assign job) current.cursor.val).cursor.val
    rw [aigExecutionAfter_cursor]
    have bounded := aigOwnedBatch_ticks_le current
    omega

/-- The common finite cursor determines all job tables, including the empty batch. -/
theorem aigOwnedBatch_ext_cursor {graph : AIG α} {assign : Fin jobs → α → Bool}
    {left right : AIGOwnedBatch graph assign} (same : left.cursor = right.cursor) :
    left = right := by
  rcases left with ⟨leftBuffers, leftCursor, leftLineage⟩
  rcases right with ⟨rightBuffers, rightCursor, rightLineage⟩
  cases same
  have buffers : leftBuffers = rightBuffers := by
    apply Vector.ext
    intro index bound
    exact (leftLineage ⟨index, bound⟩).trans (rightLineage ⟨index, bound⟩).symm
  cases buffers
  rfl

def aigOwnedBatchBoot (graph : AIG α) (assign : Fin jobs → α → Bool) :
    AIGOwnedBatch graph assign where
  buffers := Vector.replicate jobs (aigExecutionEmpty graph).buffer
  cursor := ⟨0, Nat.zero_lt_succ _⟩
  bufferLineage := by intro job; simp only [Vector.getElem_replicate]; rfl

@[simp] theorem aigOwnedBatchBoot_ticks (graph : AIG α) (assign : Fin jobs → α → Bool) :
    (aigOwnedBatchBoot graph assign).ticks = 0 := rfl

/-- One source declaration per job per batch clock; no job reads another job's table. -/
def aigOwnedBatchStep {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) : AIGOwnedBatch graph assign where
  buffers := aigOwnedBatchMoveAll graph assign current.cursor current.buffers
  cursor := ⟨min (current.ticks + 1) graph.decls.size, by omega⟩
  bufferLineage := by
    intro job
    rw [aigOwnedBatchMoveAll_get]
    rw [aigOwnedBatchState_eq_after, ← aigExecutionAfter_succ,
      aigExecutionAfter_min]
    rfl

/-- Project one owned current directly from its stored buffer and shared cursor. -/
def aigOwnedBatchJob {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (job : Fin jobs) :
    AIGOwnedProgress graph (assign job) where
  state := ⟨current.buffers[job.val], current.cursor⟩
  lineage := aigOwnedBatchState_eq_after current job

/-- Legacy table surface. It is never used by `Step`, `Job`, or completed reads. -/
def AIGOwnedBatch.tables {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) : Vector (AIGExecutionPrefix graph) jobs :=
  Vector.ofFn fun job => (aigOwnedBatchJob current job).state

/-- Compatibility lineage for proof/readout consumers of the legacy table surface. -/
theorem AIGOwnedBatch.lineage {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (job : Fin jobs) :
    current.tables[job.val] = aigExecutionAfter graph (assign job) current.cursor.val := by
  have tableEq : current.tables[job.val] = (aigOwnedBatchJob current job).state := by
    simp only [AIGOwnedBatch.tables, Vector.getElem_ofFn]
  rw [tableEq]
  exact aigOwnedBatchState_eq_after current job

theorem aigOwnedBatchStep_job_state {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (job : Fin jobs) :
    (aigOwnedBatchJob (aigOwnedBatchStep current) job).state =
      aigExecutionStep graph (assign job) (aigOwnedBatchJob current job).state := by
  apply AIGExecutionPrefix.ext
  · exact aigOwnedBatchMoveAll_get graph assign current.cursor current.buffers job
  · apply Fin.ext
    change min (current.ticks + 1) graph.decls.size =
      (aigExecutionStep graph (assign job) (aigOwnedBatchJob current job).state).cursor.val
    rw [aigExecutionStep_cursor]
    rfl

theorem aigOwnedBatchStep_ticks {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) :
    (aigOwnedBatchStep current).ticks = min (current.ticks + 1) graph.decls.size := rfl

/-- Once complete, both every job table and the shared finite cursor remain fixed. -/
theorem aigOwnedBatchStep_complete {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (complete : graph.decls.size ≤ current.ticks) :
    aigOwnedBatchStep current = current := by
  apply aigOwnedBatch_ext_cursor
  apply Fin.ext
  change (aigOwnedBatchStep current).ticks = current.ticks
  rw [aigOwnedBatchStep_ticks]
  have bounded := aigOwnedBatch_ticks_le current
  omega

theorem aigOwnedBatch_job_size {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (job : Fin jobs) :
    current.tables[job.val].values.size = min current.ticks graph.decls.size := by
  simp only [AIGOwnedBatch.tables, Vector.getElem_ofFn, AIGExecutionPrefix.values_size]
  exact (Nat.min_eq_left (aigOwnedBatch_ticks_le current)).symm

theorem aigOwnedBatch_job_size_eq_ticks {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (job : Fin jobs) :
    current.tables[job.val].values.size = current.ticks := by
  rw [aigOwnedBatch_job_size, Nat.min_eq_left (aigOwnedBatch_ticks_le current)]

def aigOwnedBatchAfter (graph : AIG α) (assign : Fin jobs → α → Bool) (ticks : Nat) :
    AIGOwnedBatch graph assign :=
  Nat.repeat aigOwnedBatchStep ticks (aigOwnedBatchBoot graph assign)

theorem aigOwnedBatchAfter_succ (graph : AIG α) (assign : Fin jobs → α → Bool)
    (ticks : Nat) :
    aigOwnedBatchAfter graph assign (ticks + 1) =
      aigOwnedBatchStep (aigOwnedBatchAfter graph assign ticks) := rfl

theorem aigOwnedBatchAfter_ticks (graph : AIG α) (assign : Fin jobs → α → Bool)
    (ticks : Nat) : (aigOwnedBatchAfter graph assign ticks).ticks = min ticks graph.decls.size := by
  induction ticks with
  | zero => rfl
  | succ ticks ih =>
      rw [aigOwnedBatchAfter_succ, aigOwnedBatchStep_ticks, ih]
      omega

theorem aigOwnedBatchAfter_job_state (graph : AIG α) (assign : Fin jobs → α → Bool)
    (ticks : Nat) (job : Fin jobs) :
    (aigOwnedBatchJob (aigOwnedBatchAfter graph assign ticks) job).state =
      aigExecutionAfter graph (assign job) ticks := by
  calc
    _ = aigExecutionAfter graph (assign job)
        (aigOwnedBatchAfter graph assign ticks).cursor.val :=
      aigOwnedBatchState_eq_after _ job
    _ = _ := by
      change aigExecutionAfter graph (assign job)
        (aigOwnedBatchAfter graph assign ticks).ticks = _
      rw [aigOwnedBatchAfter_ticks, aigExecutionAfter_min]

/-- Source declaration count completes every job; no output value enters this schedule. -/
theorem aigOwnedBatchAfter_source_count_completes (graph : AIG α)
    (assign : Fin jobs → α → Bool) (job : Fin jobs) :
    (aigOwnedBatchAfter graph assign graph.decls.size).tables[job.val].values.size =
      graph.decls.size := by
  simp only [aigOwnedBatch_job_size, aigOwnedBatchAfter_ticks, Nat.min_self]

/-- All output references of each job read its existing cached table. -/
def aigOwnedBatchReadAt {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (complete : graph.decls.size ≤ current.ticks)
    (job : Fin jobs) (ref : AIG.Ref graph) : Bool :=
  aigOwnedProgressReadAt (aigOwnedBatchJob current job)
    ((aigOwnedProgress_complete_iff (aigOwnedBatchJob current job)).mpr complete) ref

def aigOwnedBatchRead? {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (job : Fin jobs) (ref : AIG.Ref graph) : Option Bool :=
  aigOwnedProgressRead? (aigOwnedBatchJob current job) ref

theorem aigOwnedBatchReadAt_eq_read {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (complete : graph.decls.size ≤ current.ticks)
    (job : Fin jobs) (ref : AIG.Ref graph) :
    aigOwnedBatchReadAt current complete job ref = aigExecutionRead (assign job) ref :=
  aigOwnedProgressReadAt_eq_read (aigOwnedBatchJob current job) _ ref

theorem aigOwnedBatchRead?_complete {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (complete : graph.decls.size ≤ current.ticks)
    (job : Fin jobs) (ref : AIG.Ref graph) :
    aigOwnedBatchRead? current job ref = some (aigExecutionRead (assign job) ref) :=
  aigOwnedProgressRead?_complete (aigOwnedBatchJob current job)
    ((aigOwnedProgress_complete_iff (aigOwnedBatchJob current job)).mpr complete) ref

theorem aigOwnedBatchRead?_early {graph : AIG α} {assign : Fin jobs → α → Bool}
    (current : AIGOwnedBatch graph assign) (early : current.ticks < graph.decls.size)
    (job : Fin jobs) (ref : AIG.Ref graph) :
    aigOwnedBatchRead? current job ref = none :=
  aigOwnedProgressRead?_early (aigOwnedBatchJob current job) early ref

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
