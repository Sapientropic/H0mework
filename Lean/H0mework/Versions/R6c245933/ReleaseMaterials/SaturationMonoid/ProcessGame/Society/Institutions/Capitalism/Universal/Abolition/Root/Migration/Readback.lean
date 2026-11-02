import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Assessment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Readback

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation
open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

/-- Read the original committed cut without reconstructing its installed authority frame. -/
def cohort : List Party :=
  Source.ProgrammeFace.ActualBirth.participants input
    (ProgrammeHistory.visitAt input
      (Cursor.physicalVisitIndex input (Runtime.cursorAt input depth count) - 1))

def origin : RawCurrent Party Good Technology Instrument :=
  ProgrammeSource.rawCurrent input
    (Cursor.physicalVisit input (Runtime.cursorAt input depth count)).current

theorem cohort_exact : cohort input depth count = Migration.cohort input depth count := by
  unfold cohort Migration.cohort Settlement.members Settlement.committedVisit
    Settlement.physicalIndex Settlement.oldCursor Settlement.oldFrame Admission.frame
  rw [Runtime.frames_cursor]

theorem origin_exact : origin input depth count = Migration.origin input depth count := by
  unfold origin Migration.origin Migration.frame Continuation.initial Runtime.physical Admission.frame
  rw [Runtime.frames_cursor]

@[csimp] theorem cohort_codegen : @Migration.cohort = @cohort := by
  funext party good port tech instrument eqP eqG eqPort eqI source d c
  exact (cohort_exact source d c).symm

@[csimp] theorem origin_codegen : @Migration.origin = @origin := by
  funext party good port tech instrument eqP eqG eqPort eqI source d c
  exact (origin_exact source d c).symm

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Readback
