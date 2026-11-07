import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- Two cuts of the original request word, including the empty boundary. -/
structure Slice (length : Nat) where
  start : Nat
  count : Nat
  inside : start + count ≤ length

namespace Slice

def before (word : Script) (slice : Slice word.length) := word.take slice.start

def body (word : Script) (slice : Slice word.length) := (word.drop slice.start).take slice.count

def after (word : Script) (slice : Slice word.length) := (word.drop slice.start).drop slice.count

def current (source : C) (word : Script) (slice : Slice word.length) := endAt source (slice.before word)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem parts_are_the_original_word (word : Script) (slice : Slice word.length) :
    slice.before word ++ slice.body word ++ slice.after word = word := by
  unfold before body after
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem read_at_the_end_of_a_slice_uses_the_literal_original_successor
    (source : C) (word : Script) (slice : Slice word.length) :
    endAt source word = endAt (endAt (slice.current source word) (slice.body word)) (slice.after word) := by
  exact (congrArg (endAt source) (slice.parts_are_the_original_word word).symm).trans
    ((endAt_append _ _ _).trans (congrArg (fun current => endAt current (slice.after word)) (endAt_append _ _ _)))

theorem the_slice_preserves_original_receipt_positions_and_committing_clocks
    (source : C) (word : Script) (slice : Slice word.length) :
    timedInventory source word =
      timedInventory source (slice.before word) ++
        timedInventory (slice.current source word) (slice.body word) ++
        timedInventory (endAt (slice.current source word) (slice.body word)) (slice.after word) := by
  nth_rewrite 1 [← slice.parts_are_the_original_word word]
  rw [timedInventory_append, timedInventory_append, endAt_append]
  rfl

theorem every_slice_keeps_its_whole_account_and_the_original_terminal_cut
    (source : C) (word : Script) (slice : Slice word.length) :
    Recorded source (slice.before word) ∧ Recorded (slice.current source word) (slice.body word) ∧
      Recorded (endAt (slice.current source word) (slice.body word)) (slice.after word) ∧
      (type_of% (slice.read_at_the_end_of_a_slice_uses_the_literal_original_successor source word)) :=
  ⟨record _ _, record _ _, record _ _, slice.read_at_the_end_of_a_slice_uses_the_literal_original_successor source word⟩

/-- Any decomposition of the actual word has exactly these original cut positions. -/
def ofParts (front middle tail : Script) : Slice (front ++ middle ++ tail).length :=
  ⟨front.length, middle.length, by simp only [List.length_append, Nat.le_add_right]⟩

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem parts_at_their_literal_positions (front middle tail : Script) :
    let slice := ofParts front middle tail
    slice.before (front ++ middle ++ tail) = front ∧
      slice.body (front ++ middle ++ tail) = middle ∧
      slice.after (front ++ middle ++ tail) = tail := by
  simp [before, body, after, ofParts, List.append_assoc]

end Slice
end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
