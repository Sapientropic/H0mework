import H0mework.Physics.MotherProgrammesFormationProgrammes.AutonomousCoverage
import H0mework.Physics.MotherProgrammesFormationProgrammes.ExecutionConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes

open Stage9C.Revision MotherFamilyOccurrence MotherProgrammes MotherProgrammeExecution WholePointHistories
open ProofFreeRicherAnholonomicSource

noncomputable section

def birthCell (round : ℕ) (prior : List Entry) (entry : Entry) : Cell :=
  arrival (MotherProgrammeExecution.run (roundCell round) prior) entry

def birthEvents (round : ℕ) (prior : List Entry) (entry : Entry) : List WholePointFormation.Carrier :=
  globalEvents round ++ MotherProgrammeExecution.events (roundCell round) (prior ++ [entry])

theorem birth_replay (round : ℕ) (prior : List Entry) (entry : Entry) :
    replay WholePointFormation.initial (birthEvents round prior entry) = view (birthCell round prior entry) := by
  rw [birthEvents, replay_append, global_replay, prefix_arrival]
  rfl

theorem birth_prefix (round : ℕ) (prior : List Entry) (entry : Entry) (suffix : List Entry)
    (position : roundProgramme round = prior ++ entry :: suffix) :
    (birthEvents round prior entry).IsPrefix (globalEvents (round + 1)) := by
  have split : roundProgramme round = (prior ++ [entry]) ++ suffix := by
    simpa only [List.append_assoc, List.singleton_append] using position
  change (globalEvents round ++ MotherProgrammeExecution.events (roundCell round) (prior ++ [entry])).IsPrefix
    (globalEvents round ++ (MotherProgrammeExecution.events (roundCell round) (roundProgramme round) ++
      [RawSourcePaths.zeroEvent]))
  rw [split, MotherProgrammeExecution.events_append (roundCell round) (prior ++ [entry]) suffix]
  refine ⟨MotherProgrammeExecution.events
    (MotherProgrammeExecution.run (roundCell round) (prior ++ [entry])) suffix ++ [RawSourcePaths.zeroEvent], ?_⟩
  simp only [List.append_assoc]

theorem birth_word (round : ℕ) (prior : List Entry) (entry : Entry) :
    StageEightDiscreteFormation.programAt (StageEightDiscreteFormation.codeOf (view (birthCell round prior entry)).1) =
      GeneratedDiscreteRecurrence.padded entry.word ((MotherProgrammeExecution.run (roundCell round) prior).1 + 1) := by
  change StageEightDiscreteFormation.programAt (StageEightDiscreteFormation.codeOf
    (SpinPair.visit (10 + finish (MotherProgrammeExecution.run (roundCell round) prior) entry))) = _
  rw [StageEightDiscreteFormation.code_at, finish, GeneratedDiscreteRecurrence.complete_word_recovered]

theorem birth_parents (round : ℕ) (prior : List Entry) (entry : Entry) (suffix : List Entry)
    (position : roundProgramme round = prior ++ entry :: suffix) :
    temporalDepth entry.discreteVisit.history < temporalDepth (view (birthCell round prior entry)).1.history ∧
      temporalDepth entry.coordinateVisit.history < temporalDepth (view (birthCell round prior entry)).1.history := by
  have member : entry ∈ roundProgramme round := by rw [position]; simp
  have parents := programme_prefixes (roundOrigin round) entry member
  have originPast := origin_is_past round
  have current := index_mono (roundCell round) prior
  have later := finish_late (MotherProgrammeExecution.run (roundCell round) prior) entry
  change temporalDepth (roundOrigin round).history ≤
    temporalDepth (SpinPair.visit (10 + (roundCell round).1)).history at originPast
  rw [visit_depth] at originPast
  change temporalDepth entry.discreteVisit.history < temporalDepth (SpinPair.visit
      (10 + finish (MotherProgrammeExecution.run (roundCell round) prior) entry)).history ∧
    temporalDepth entry.coordinateVisit.history < temporalDepth (SpinPair.visit
      (10 + finish (MotherProgrammeExecution.run (roundCell round) prior) entry)).history
  rw [visit_depth]
  omega

/-- Every birth keeps the originating entry, its padded complete word,
all coordinates and both parents at its actual global prefix. -/
theorem source_birth_consumed (round : ℕ) (prior : List Entry) (entry : Entry) (suffix : List Entry)
    (position : roundProgramme round = prior ++ entry :: suffix)
    (center : BasePoint) (epoch : ℕ) (point : BasePoint) :
    let cell := birthCell round prior entry
    let born := view cell
    (birthEvents round prior entry).IsPrefix (globalEvents (round + 1)) ∧
      replay WholePointFormation.initial (birthEvents round prior entry) = born ∧
      StageEightDiscreteFormation.programAt (StageEightDiscreteFormation.codeOf born.1) =
        GeneratedDiscreteRecurrence.padded entry.word ((MotherProgrammeExecution.run (roundCell round) prior).1 + 1) ∧
      WholePointFormation.source born.1 born.2 = entry.source ∧
      MotherCoordinateCompletion.coordinates (65 * 4) born.2 = (fun slot => (entry.data.2 slot : ℝ)) ∧
      (temporalDepth entry.discreteVisit.history < temporalDepth born.1.history ∧
        temporalDepth entry.coordinateVisit.history < temporalDepth born.1.history) ∧
      NativeOperatorAt cell center epoch point :=
  ⟨birth_prefix round prior entry suffix position, birth_replay round prior entry,
    birth_word round prior entry, arrival_source _ _, entry.carrier_coordinates,
    birth_parents round prior entry suffix position, native_operator_at _ center epoch point⟩

theorem autonomous_history_consumed (round : ℕ) :
    round ≤ (roundCell round).1 ∧ (roundCell round).1 < (roundCell (round + 1)).1 ∧
      (globalEvents round).length = (roundCell round).1 ∧
      replay WholePointFormation.initial (globalEvents round) = view (roundCell round) ∧
      (globalEvents round).IsPrefix (globalEvents (round + 1)) ∧
      (trace WholePointFormation.initial (globalEvents round)).map Prod.fst =
        (List.range' 10 ((globalEvents round).length + 1)).map SpinPair.visit ∧
      recover (trace WholePointFormation.initial (globalEvents round)) = globalEvents round ∧
      (rawRecover ((trace WholePointFormation.initial (globalEvents round)).map WholePointFormation.statePoints)).map
        WholePointFormation.pointEquiv.symm = globalEvents round ∧
      (trace WholePointFormation.initial (globalEvents round)).map WholePointFormation.statePoints =
        rawTrace (WholePointFormation.statePoints WholePointFormation.initial)
          ((globalEvents round).map WholePointFormation.points) ∧
      Lawful (trace WholePointFormation.initial (globalEvents round)) ∧
      NativeHistory WholePointFormation.initial (globalEvents round) ∧
      (∀ state ∈ trace WholePointFormation.initial (globalEvents round), PhysicalAt state) :=
  ⟨round_bound round, round_progress round, global_length round, global_replay round,
    retained_events round, all_microvisits round, whole_finite_history (globalEvents round)⟩

theorem every_programme_consumed (targets : List MotherProgrammes.Datum) :
    ∃ round,
      (roundProgramme round).map Entry.data = targets ∧
      List.Sublist (targets.map datumReadout)
        (RawSourcePaths.pathReadout WholePointFormation.initial (globalEvents (round + 1))) ∧
      NativeHistory WholePointFormation.initial (globalEvents (round + 1)) ∧
      recover (trace WholePointFormation.initial (globalEvents (round + 1))) = globalEvents (round + 1) ∧
      (∀ state ∈ trace WholePointFormation.initial (globalEvents (round + 1)), PhysicalAt state) ∧
      ∀ (center : BasePoint) (epoch : ℕ) (point : BasePoint),
        NativeOperatorAt (roundCell (round + 1)) center epoch point := by
  obtain ⟨round, data, ordered⟩ := every_programme_in_history targets
  obtain ⟨recovered, _, _, _, native, physics⟩ := whole_finite_history (globalEvents (round + 1))
  exact ⟨round, data, ordered, native, recovered, physics, fun center epoch point => native_operator_at _ center epoch point⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes
