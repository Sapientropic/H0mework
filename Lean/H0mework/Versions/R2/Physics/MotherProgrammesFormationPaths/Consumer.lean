import H0mework.Versions.R2.Physics.MotherProgrammesFormationPaths.Late

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RawSourcePaths

open Stage9C.Revision WholePointFormation WholePointHistories MotherFamilyOccurrence

noncomputable section

/-- Sublist records strictly ordered occurrences in the full list of
post-step states. Every connecting microstep remains in the generated trace. -/
theorem ordered_sources (start : ℕ) (before : Carrier) (targets : List Datum) :
    ∃ events : List Carrier,
      List.Sublist targets (pathReadout (SpinPair.visit (10 + start), before) events) := by
  induction targets generalizing start before with
  | nil => exact ⟨[], List.nil_sublist _⟩
  | cons target targets induction =>
      obtain ⟨finish, value, late, hit⟩ := arbitrary_late_state start target
      obtain ⟨segment, length, nonempty, reached⟩ := segment_to start finish before value late
      obtain ⟨tail, later⟩ := induction finish value
      have member : target ∈ pathReadout (SpinPair.visit (10 + start), before) segment := by
        apply List.mem_map.mpr
        refine ⟨(SpinPair.visit (10 + finish), value), ?_, hit⟩
        rw [← reached]
        exact replay_mem_steps _ segment nonempty
      refine ⟨segment ++ tail, ?_⟩
      rw [pathReadout, steps_append, reached, List.map_append]
      exact (List.singleton_sublist.mpr member).append later

/-- Targets select a legal finite path in the coverage theorem. The
factory itself remains the original act/replay on complete event operands. -/
theorem ordered_physical_sources (targets : List Datum) :
    ∃ events : List Carrier,
      List.Sublist targets (pathReadout initial events) ∧
      (trace initial events).map Prod.fst =
        (List.range' 10 (events.length + 1)).map SpinPair.visit ∧
      recover (trace initial events) = events ∧
      (rawRecover ((trace initial events).map statePoints)).map pointEquiv.symm = events ∧
      (trace initial events).map statePoints = rawTrace (statePoints initial) (events.map points) ∧
      Lawful (trace initial events) ∧ NativeHistory initial events ∧
      (∀ state ∈ trace initial events, PhysicalAt state) := by
  obtain ⟨events, covered⟩ := ordered_sources 0 initial.2 targets
  exact ⟨events, covered, trace_visits 10 initial.2 events, whole_finite_history events⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RawSourcePaths
