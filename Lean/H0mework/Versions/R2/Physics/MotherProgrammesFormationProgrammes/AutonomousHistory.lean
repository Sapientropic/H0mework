import H0mework.Versions.R2.Physics.MotherProgrammesFormationProgrammes.AutonomousState
import H0mework.Versions.R2.Physics.MotherProgrammesFormationProgrammes.ExecutionTrace

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes

open Stage9C.Revision MotherFamilyOccurrence WholePointHistories MotherProgrammes MotherProgrammeExecution

noncomputable section

def roundEvents (round : ℕ) : List WholePointFormation.Carrier :=
  MotherProgrammeExecution.events (roundCell round) (roundProgramme round) ++ [RawSourcePaths.zeroEvent]

def globalEvents : ℕ → List WholePointFormation.Carrier
  | 0 => []
  | round + 1 => globalEvents round ++ roundEvents round

theorem round_replay (round : ℕ) :
    replay (view (roundCell round)) (roundEvents round) = view (roundCell (round + 1)) := by
  rw [roundEvents, replay_append, events_replay]
  exact zero_next _

theorem global_replay (round : ℕ) :
    replay WholePointFormation.initial (globalEvents round) = view (roundCell round) := by
  induction round with
  | zero => rfl
  | succ round induction => rw [globalEvents, replay_append, induction, round_replay]

theorem global_length (round : ℕ) : (globalEvents round).length = (roundCell round).1 := by
  have visits := congrArg Prod.fst (global_replay round)
  change (replay (SpinPair.visit 10, WholePointFormation.initial.2) (globalEvents round)).1 =
    SpinPair.visit (10 + (roundCell round).1) at visits
  rw [RawSourcePaths.replay_visit] at visits
  have depths := congrArg (fun visit : MotherVisit => temporalDepth visit.history) visits
  rw [visit_depth, visit_depth] at depths
  omega

theorem retained_events (round : ℕ) :
    (globalEvents round).IsPrefix (globalEvents (round + 1)) := ⟨roundEvents round, rfl⟩

theorem retained_trace (round : ℕ) :
    (trace WholePointFormation.initial (globalEvents round)).IsPrefix
      (trace WholePointFormation.initial (globalEvents (round + 1))) :=
  trace_prefix WholePointFormation.initial (globalEvents round) (roundEvents round)

theorem events_prefix_of_le {earlier later : ℕ} (bound : earlier ≤ later) :
    (globalEvents earlier).IsPrefix (globalEvents later) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  clear bound
  induction extra with
  | zero => exact ⟨[], List.append_nil _⟩
  | succ extra induction => exact induction.trans (retained_events (earlier + extra))

theorem trace_prefix_of_le {earlier later : ℕ} (bound : earlier ≤ later) :
    (trace WholePointFormation.initial (globalEvents earlier)).IsPrefix
      (trace WholePointFormation.initial (globalEvents later)) := by
  obtain ⟨suffix, same⟩ := events_prefix_of_le bound
  rw [← same]
  exact trace_prefix _ _ _

theorem all_microvisits (round : ℕ) :
    (trace WholePointFormation.initial (globalEvents round)).map Prod.fst =
      (List.range' 10 ((globalEvents round).length + 1)).map SpinPair.visit :=
  RawSourcePaths.trace_visits 10 WholePointFormation.initial.2 (globalEvents round)

theorem round_order (round : ℕ) :
    List.Sublist ((roundProgramme round).map entryReadout)
      (RawSourcePaths.pathReadout WholePointFormation.initial (globalEvents (round + 1))) := by
  have ordered := ordered_arrivals (roundCell round) (roundProgramme round)
  rw [globalEvents, RawSourcePaths.pathReadout, steps_append, global_replay,
    roundEvents, steps_append, events_replay, List.map_append, List.map_append]
  have prior := List.nil_sublist
    ((steps WholePointFormation.initial (globalEvents round)).map RawSourcePaths.readout)
  have suffix := List.nil_sublist ((steps
    (view (MotherProgrammeExecution.run (roundCell round) (roundProgramme round)))
    [RawSourcePaths.zeroEvent]).map RawSourcePaths.readout)
  simpa only [List.nil_append, List.append_nil, List.append_assoc, RawSourcePaths.pathReadout] using
    (prior.append ordered).append suffix

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes
