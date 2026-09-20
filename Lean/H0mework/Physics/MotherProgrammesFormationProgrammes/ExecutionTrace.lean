import H0mework.Physics.MotherProgrammesFormationProgrammes.ExecutionRun

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammeExecution

open Stage9C.Revision WholePointFormation WholePointHistories MotherProgrammes

noncomputable section

def start (index : ℕ) : Cell := (index, (WholePointFormation.stateAt index).2)
def programme (index : ℕ) : List Entry := programmeAt (view (start index)).1
def completedCell (index : ℕ) : Cell := run (start index) (programme index)
def terminalCell (index : ℕ) : Cell := ((completedCell index).1 + 1, (completedCell index).2)

/-- The old actual prefix is retained. A final original zero event
continues the source even when the current programme is empty. -/
def fullEvents (index : ℕ) : List WholePointFormation.Carrier :=
  WholePointFormation.emittedHistory index ++ (events (start index) (programme index) ++ [RawSourcePaths.zeroEvent])

theorem start_view (index : ℕ) : view (start index) = WholePointFormation.stateAt index := by
  apply Prod.ext
  · have same := congrArg Prod.fst (WholePointFormation.generated_state_commutes index)
    change (WholePointFormation.stateAt index).1 = (GeneratedPotentialHistory.stateAt index).1 at same
    exact (same.trans (GeneratedPotentialHistory.visit_projection index)).symm
  · rfl

theorem replay_emitted (index : ℕ) :
    replay initial (WholePointFormation.emittedHistory index) = WholePointFormation.stateAt index := by
  induction index with
  | zero => rfl
  | succ index induction =>
      change replay initial (WholePointFormation.emittedHistory index ++
        [WholePointFormation.emit (WholePointFormation.stateAt index).1]) = _
      rw [replay_next, induction]
      rfl

theorem zero_next (cell : Cell) :
    replay (view cell) [RawSourcePaths.zeroEvent] = view (cell.1 + 1, cell.2) := by
  simpa only [List.replicate_one, view, Nat.add_assoc] using RawSourcePaths.replay_wait (10 + cell.1) 1 cell.2

theorem full_replay (index : ℕ) : replay initial (fullEvents index) = view (terminalCell index) := by
  rw [fullEvents, replay_append, replay_emitted, ← start_view, replay_append, events_replay]
  exact zero_next _

theorem terminal_late (index : ℕ) : index < (terminalCell index).1 := by
  have bound := index_mono (start index) (programme index)
  change index ≤ (completedCell index).1 at bound
  change index < (completedCell index).1 + 1
  omega

theorem retained_events (index : ℕ) :
    (WholePointFormation.emittedHistory index).IsPrefix (fullEvents index) := ⟨_, rfl⟩

theorem retained_trace (index : ℕ) :
    (trace initial (WholePointFormation.emittedHistory index)).IsPrefix (trace initial (fullEvents index)) :=
  trace_prefix initial _ _

theorem full_order (index : ℕ) :
    List.Sublist ((programme index).map entryReadout) (RawSourcePaths.pathReadout initial (fullEvents index)) := by
  have ordered := ordered_arrivals (start index) (programme index)
  rw [fullEvents, RawSourcePaths.pathReadout, steps_append, replay_emitted, ← start_view,
    steps_append, events_replay, List.map_append, List.map_append]
  have prior := List.nil_sublist ((steps initial (WholePointFormation.emittedHistory index)).map RawSourcePaths.readout)
  have suffix := List.nil_sublist ((steps (view (completedCell index)) [RawSourcePaths.zeroEvent]).map RawSourcePaths.readout)
  simpa only [List.nil_append, List.append_nil, List.append_assoc, RawSourcePaths.pathReadout, completedCell] using
    (prior.append ordered).append suffix

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammeExecution
