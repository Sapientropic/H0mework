import H0mework.Physics.MotherProgrammesFormationProgrammes.Programme
import H0mework.Physics.MotherProgrammesFormationPaths.Late

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammeExecution

open Stage9C.Revision StageEightDiscreteFormation GeneratedDiscreteRecurrence
open MotherFamilyOccurrence MotherCoordinateCompletion WholePointFormation WholePointHistories MotherProgrammes

noncomputable section

abbrev Cell := ℕ × WholePointFormation.Carrier

def view (cell : Cell) : WholePointFormation.State := (SpinPair.visit (10 + cell.1), cell.2)
def finish (cell : Cell) (entry : Entry) : ℕ := paddedCode entry.word (cell.1 + 1)
def arrival (cell : Cell) (entry : Entry) : Cell := (finish cell entry, entry.carrier)

def segment (cell : Cell) (entry : Entry) : List WholePointFormation.Carrier :=
  List.replicate (finish cell entry - cell.1 - 1) RawSourcePaths.zeroEvent ++
    [completedSub (65 * 4) entry.carrier cell.2]

theorem finish_late (cell : Cell) (entry : Entry) : cell.1 < finish cell entry := by
  have bound := code_after_bound entry.word (cell.1 + 1)
  change cell.1 + 1 ≤ finish cell entry at bound
  omega

theorem segment_nonempty (cell : Cell) (entry : Entry) : segment cell entry ≠ [] := by
  intro empty
  have lengths := congrArg List.length empty
  simp only [segment, List.length_append, List.length_replicate, List.length_cons, List.length_nil] at lengths
  omega

theorem segment_length (cell : Cell) (entry : Entry) :
    (segment cell entry).length = finish cell entry - cell.1 := by
  have late := finish_late cell entry
  simp only [segment, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

theorem segment_replay (cell : Cell) (entry : Entry) :
    replay (view cell) (segment cell entry) = view (arrival cell entry) := by
  have late := finish_late cell entry
  rw [segment, replay_append]
  change replay (replay (SpinPair.visit (10 + cell.1), cell.2)
    (List.replicate (finish cell entry - cell.1 - 1) RawSourcePaths.zeroEvent)) _ = _
  rw [RawSourcePaths.replay_wait]
  change act (SpinPair.visit (10 + cell.1 + (finish cell entry - cell.1 - 1)), cell.2)
    (completedSub (65 * 4) entry.carrier cell.2) = _
  rw [RawSourcePaths.act_at]
  apply Prod.ext
  · exact congrArg SpinPair.visit (show 10 + cell.1 + (finish cell entry - cell.1 - 1) + 1 =
      10 + finish cell entry by omega)
  · exact (completed_event_recovered (65 * 4) cell.2 entry.carrier).1

theorem arrival_source (cell : Cell) (entry : Entry) :
    WholePointFormation.source (view (arrival cell entry)).1 (view (arrival cell entry)).2 = entry.source := by
  have material : materialAt (finish cell entry) = entry.data.1 := by
    rw [finish, paddedCode, materialAt_program, run_padded]
    exact entry.word_generates
  have discrete : sourceAtVisit (SpinPair.visit (10 + finish cell entry)) =
      sourceAtVisit entry.discreteVisit := by
    rw [sourceAtVisit, code_at, material]
    change toSource (readMaterial (toSource (materialAt (codeOf entry.discreteVisit)))) = _
    rw [full_material_recovered]
    rfl
  change PotentialSourceFormation.sourceOf (SpinPair.visit (10 + finish cell entry))
    (WholePointFormation.points entry.carrier) =
      PotentialSourceFormation.sourceOf entry.discreteVisit (WholePointFormation.points entry.carrier)
  unfold PotentialSourceFormation.sourceOf
  rw [discrete]

def entryReadout (entry : Entry) : RawSourcePaths.Datum :=
  (entry.source, PotentialSourceFormation.remainders (WholePointFormation.points entry.carrier))

theorem arrival_readout (cell : Cell) (entry : Entry) :
    RawSourcePaths.readout (view (arrival cell entry)) = entryReadout entry :=
  Prod.ext (arrival_source cell entry) rfl

/-- The parents supply material. Birth is the strictly later original
occurrence at which the generated complete source is actually reached. -/
theorem birth_after_parents (origin : ℕ) (cell : Cell) (entry : Entry)
    (current : origin ≤ cell.1) (member : entry ∈ programmeAt (SpinPair.visit (10 + origin))) :
    temporalDepth entry.discreteVisit.history < temporalDepth (view (arrival cell entry)).1.history ∧
      temporalDepth entry.coordinateVisit.history < temporalDepth (view (arrival cell entry)).1.history := by
  have parents := programme_prefixes _ entry member
  have late := finish_late cell entry
  change temporalDepth entry.discreteVisit.history < temporalDepth (SpinPair.visit (10 + finish cell entry)).history ∧
    temporalDepth entry.coordinateVisit.history < temporalDepth (SpinPair.visit (10 + finish cell entry)).history
  rw [visit_depth]
  rw [visit_depth] at parents
  omega

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammeExecution
