import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (inputs : List (RawEvent Party Good Port Technology Instrument))

def executedWords (count : Nat) : List (RawEvent Party Good Port Technology Instrument) :=
  (List.range count).map fun depth => word source inputs (depth + 2) (trailAt source inputs (depth + 2)).frame

theorem executedWords_length (count : Nat) : (executedWords source inputs count).length = count := by
  simp [executedWords]

theorem executedWords_get (count index : Nat) (inside : index < count) :
    (executedWords source inputs count)[index]? =
      some (word source inputs (index + 2) (trailAt source inputs (index + 2)).frame) := by
  simp [executedWords, List.getElem?_map, List.getElem?_range inside]

theorem executed_words_preserve_their_actual_prefix (count : Nat)
    (later : List (RawEvent Party Good Port Technology Instrument))
    (visit : Nat) (inside : visit ≤ count + 2) :
    trailAt source (executedWords source inputs count ++ later) visit = trailAt source inputs visit := by
  induction visit with
  | zero => rfl
  | succ visit ih =>
      have prior := ih (by omega)
      change (trailAt source (executedWords source inputs count ++ later) visit).append
        (word source (executedWords source inputs count ++ later) visit
          (trailAt source (executedWords source inputs count ++ later) visit).frame) =
        (trailAt source inputs visit).append (word source inputs visit (trailAt source inputs visit).frame)
      rw [prior]
      congr 1
      by_cases bootstrap : visit = 0
      · simp only [word, if_pos bootstrap]
      · by_cases original : visit = 1
        · simp only [word, report, if_neg bootstrap, if_pos original]
        · have address : visit - 2 < count := by omega
          have earlier : visit - 2 < (executedWords source inputs count).length := by
            rw [executedWords_length]; exact address
          rw [word, if_neg bootstrap, report, if_neg original,
            List.getElem?_append_left earlier, executedWords_get source inputs count (visit - 2) address]
          dsimp only
          rw [show visit - 2 + 2 = visit by omega]
          rfl

theorem executed_words_replay_the_actual_cut (count : Nat) :
    replay source (executedWords source inputs count) = trailAt source inputs (count + 2) := by
  have actual := executed_words_preserve_their_actual_prefix source inputs count [] (count + 2) (Nat.le_refl _)
  rw [List.append_nil] at actual
  have replayed := finite_prefix_exact source (executedWords source inputs count)
    (executedWords source inputs count).length (Nat.le_refl _)
  rw [List.take_length, executedWords_length] at replayed
  exact replayed.symm.trans actual


theorem written_report_is_the_actual_local_report (depth : Nat) :
    (writtenReceipt source inputs depth).val =
      report source inputs (depth + 1) (trailAt source inputs (depth + 1)).frame := by
  calc
    _ = reportAt source inputs (currentAt source inputs (depth + 1)) :=
      (writtenReceipt source inputs depth).property
    _ = _ := by
      unfold reportAt
      rw [ordinal_exact, (actual_frame source inputs (depth + 1)).1]

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History
