import H0mework.Versions.R2.Physics.MotherProgrammesFormationProgrammes.ExecutionSegment

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammeExecution

open WholePointFormation WholePointHistories MotherProgrammes

noncomputable section

def run (cell : Cell) : List Entry → Cell
  | [] => cell
  | entry :: entries => run (arrival cell entry) entries

def events (cell : Cell) : List Entry → List WholePointFormation.Carrier
  | [] => []
  | entry :: entries => segment cell entry ++ events (arrival cell entry) entries

theorem events_replay (cell : Cell) (entries : List Entry) :
    replay (view cell) (events cell entries) = view (run cell entries) := by
  induction entries generalizing cell with
  | nil => rfl
  | cons entry entries induction =>
      rw [events, replay_append, segment_replay, induction]
      rfl

theorem index_mono (cell : Cell) (entries : List Entry) : cell.1 ≤ (run cell entries).1 := by
  induction entries generalizing cell with
  | nil => exact le_rfl
  | cons entry entries induction =>
      exact (Nat.le_of_lt (finish_late cell entry)).trans (induction (arrival cell entry))

theorem run_append (cell : Cell) (first last : List Entry) :
    run cell (first ++ last) = run (run cell first) last := by
  induction first generalizing cell with
  | nil => rfl
  | cons entry entries induction => simpa only [List.cons_append, run] using induction (arrival cell entry)

theorem events_append (cell : Cell) (first last : List Entry) :
    events cell (first ++ last) = events cell first ++ events (run cell first) last := by
  induction first generalizing cell with
  | nil => rfl
  | cons entry entries induction => simp only [List.cons_append, events, run, induction, List.append_assoc]

theorem ordered_arrivals (cell : Cell) (entries : List Entry) :
    List.Sublist (entries.map entryReadout) (RawSourcePaths.pathReadout (view cell) (events cell entries)) := by
  induction entries generalizing cell with
  | nil => exact List.nil_sublist _
  | cons entry entries induction =>
      have member : entryReadout entry ∈ RawSourcePaths.pathReadout (view cell) (segment cell entry) := by
        apply List.mem_map.mpr
        refine ⟨view (arrival cell entry), ?_, arrival_readout cell entry⟩
        rw [← segment_replay]
        exact RawSourcePaths.replay_mem_steps _ _ (segment_nonempty cell entry)
      rw [events, RawSourcePaths.pathReadout, steps_append, segment_replay, List.map_append]
      exact (List.singleton_sublist.mpr member).append (induction (arrival cell entry))

theorem prefix_arrival (cell : Cell) (prior : List Entry) (entry : Entry) :
    replay (view cell) (events cell (prior ++ [entry])) = view (arrival (run cell prior) entry) := by
  rw [events_replay, run_append]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammeExecution
