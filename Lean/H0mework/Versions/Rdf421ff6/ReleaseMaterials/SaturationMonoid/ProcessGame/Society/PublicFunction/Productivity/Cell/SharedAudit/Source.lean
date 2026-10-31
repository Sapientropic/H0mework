import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Method

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

/-- The cache is generated from this programme's prefix, as the original
OutstandingSource generates its payment register from that same prefix. -/
def source : OutstandingSource Party Good Port Technology Unit :=
  { Cell.source with
    completionReport := fun current => .original current (respond current (frameAt current.round).method).word }

theorem same_original_input : source.seed = Cell.source.seed := rfl

theorem raw_current_frame (ordinal : Nat) :
    source.currentAt ordinal = (source.frameAt ordinal).raw := (source.canonical_frame ordinal).1

theorem source_round (ordinal : Nat) : (source.currentAt ordinal).round = ordinal := by
  have round := source.current_round ordinal
  change (source.currentAt ordinal).round = 0 + ordinal at round
  simpa only [Nat.zero_add] using round

theorem original_service_paid : source.pendingSlots (source.frameAt 2).payments = [] := by
  decide +kernel

theorem actual_word (ordinal : Nat) (started : 2 ≤ ordinal) :
    ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current =
      (respond (source.currentAt ordinal) (frameAt ordinal).method).word := by
  have complete := source.completion_persists 2 (ordinal - 2) original_service_paid
  have emitted := source.completed_word_is_source_continuation ordinal 0 started
    (by simpa only [Nat.add_sub_of_le started] using complete) rfl
  simp only [Nat.add_zero] at emitted
  rw [emitted]
  change (respond (source.currentAt ordinal) (frameAt (source.currentAt ordinal).round).method).word = _
  rw [source_round]

theorem current_is_generated_machine (ordinal : Nat) : source.currentAt ordinal = (frameAt ordinal).raw := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change ProgrammeSource.rawCurrent source.input
      (ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input ordinal).current) = _
    rw [ProgrammeSource.actual_raw_next]
    change law.next (source.currentAt ordinal) _ = _
    by_cases zero : ordinal = 0
    · subst ordinal; rfl
    by_cases first : ordinal = 1
    · subst ordinal; rw [ih]; rfl
    · rw [actual_word ordinal (by omega), ih]
      change law.next (frameAt ordinal).raw (respond (frameAt ordinal).raw (frameAt ordinal).method).word =
        law.next (frameAt ordinal).raw (wordAt ordinal (frameAt ordinal))
      rw [wordAt, if_neg zero, if_neg first]

theorem actual_word_is_machine (ordinal : Nat) :
    ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current =
      wordAt ordinal (frameAt ordinal) := by
  by_cases zero : ordinal = 0
  · subst ordinal; rfl
  by_cases first : ordinal = 1
  · subst ordinal; rfl
  · rw [actual_word ordinal (by omega), current_is_generated_machine]
    simp only [wordAt, if_neg zero, if_neg first]

theorem actual_execution_word (depth : Nat) :
    (source.actualExecution depth).submitted = wordAt (depth + 1) (frameAt (depth + 1)) :=
  actual_word_is_machine (depth + 1)

theorem actual_execution_after (depth : Nat) :
    (source.actualExecution depth).after = (frameAt (depth + 2)).raw :=
  (source.actualExecution depth).root_next_exact.trans (current_is_generated_machine (depth + 2))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
