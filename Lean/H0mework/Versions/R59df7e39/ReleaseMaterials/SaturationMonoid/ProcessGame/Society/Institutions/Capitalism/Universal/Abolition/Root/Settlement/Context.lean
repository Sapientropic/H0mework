import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

def oldCursor := (oldFrame input depth count).cursor input
def physicalIndex := Cursor.physicalVisitIndex input (oldCursor input depth count)

def committedVisit := ProgrammeHistory.visitAt input (physicalIndex input depth count - 1)
def members := Source.ProgrammeFace.ActualBirth.participants input (committedVisit input depth count)

def memberBirth (person : Party) (member : person ∈ members input depth count) :
    Source.ProgrammeFace.ActualBirth.At input (committedVisit input depth count) person :=
  Source.ProgrammeFace.ActualBirth.fromHistory input (committedVisit input depth count) person member

theorem physical_index_positive : 0 < physicalIndex input depth count := by
  unfold physicalIndex oldCursor oldFrame
  rw [Runtime.frames_cursor]
  induction count with
  | zero =>
      change 0 < Cursor.physicalVisitIndex input (Cursor.next input (Ingress.start input depth))
      rw [Cursor.entry_has_one_actual_body input _ rfl]
      exact Nat.zero_lt_succ _
  | succ count previous =>
      exact previous.trans_le (Cursor.physical_index_monotone input (Runtime.cursorAt input depth count))

theorem committed_next_is_fee_before :
    input.law.next (ProgrammeSource.rawCurrent input (committedVisit input depth count).current)
      (ProgrammeSource.rawEvent input (committedVisit input depth count).current) =
        Continuation.initial input (oldFrame input depth count) := by
  have positive := physical_index_positive input depth count
  have index : physicalIndex input depth count - 1 + 1 = physicalIndex input depth count := by omega
  calc
    _ = ProgrammeSource.rawCurrent input
        (ProgrammeHistory.visitAt input (physicalIndex input depth count - 1 + 1)).current :=
      (ProgrammeSource.actual_raw_next input (committedVisit input depth count).current).symm
    _ = _ := by rw [index]; rfl

theorem bookkeeping_recognizes_the_original_observer
    (bookkeeping : ¬ Cursor.FreshBody input (oldCursor input depth count)) :
    committedVisit input depth count = (observe input (oldCursor input depth count)).completed :=
  (Cursor.bookkeeping_reads_only_completed_body input (oldCursor input depth count) bookkeeping).2.symm

theorem committed_prefix_is_strictly_before_the_next_word :
    physicalIndex input depth count - 1 < physicalIndex input depth count := by
  have positive := physical_index_positive input depth count
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement
