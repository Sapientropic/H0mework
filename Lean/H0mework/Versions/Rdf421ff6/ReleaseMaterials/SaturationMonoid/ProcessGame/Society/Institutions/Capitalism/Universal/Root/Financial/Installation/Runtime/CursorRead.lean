import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def cursorAt (depth : Nat) : Nat → Cursor.State input
  | 0 => Cursor.next input (Ingress.start input depth)
  | count + 1 => Cursor.next input (cursorAt depth count)

theorem initial_cursor (depth : Nat) : (initialFrame input depth).cursor input = cursorAt input depth 0 := rfl

theorem frames_cursor (depth count : Nat) : (frames input depth count).cursor input = cursorAt input depth count := by
  induction count with
  | zero => exact initial_cursor input depth
  | succ count prior =>
      change ((frames input depth count).next input).cursor input = _
      rw [Frame.next_cursor, prior]
      rfl

def physical (frame : Frame input) : RawCurrent Party Good Technology Instrument :=
  ProgrammeSource.rawCurrent input (Cursor.physicalVisit input (frame.cursor input)).current

theorem bookkeeping_has_no_second_body (frame : Frame input)
    (already : ¬ Cursor.FreshBody input (frame.cursor input)) :
    physical input (frame.next input) = physical input frame := by
  unfold physical
  rw [Frame.next_cursor, Cursor.physical_next_of_bookkeeping input (frame.cursor input) already]

theorem fresh_body_is_the_original_next (frame : Frame input)
    (fresh : Cursor.FreshBody input (frame.cursor input)) :
    physical input (frame.next input) = input.law.next (physical input frame)
      (ProgrammeSource.rawEvent input (Cursor.physicalVisit input (frame.cursor input)).current) := by
  unfold physical
  rw [Frame.next_cursor, Cursor.physical_next_of_fresh input (frame.cursor input) fresh,
    ProgrammeSource.actual_raw_next]

theorem observation_reads_original_pending (depth count : Nat) : HEq
    ((frames input depth count).native.root.toAuthoritativeRoot.source.projectionLaw.project
      (frames input depth count).native.projection
      ((frames input depth count).native.root.emitted (frames input depth count).visit.current)
      ((frames input depth count).native.active (frames input depth count).visit.current))
    (observe input (cursorAt input depth count)) := by
  have original := (frames input depth count).native.observation_heq (frames input depth count).visit.current
  exact original.trans (heq_of_eq (congrArg (observe input) (frames_cursor input depth count)))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
