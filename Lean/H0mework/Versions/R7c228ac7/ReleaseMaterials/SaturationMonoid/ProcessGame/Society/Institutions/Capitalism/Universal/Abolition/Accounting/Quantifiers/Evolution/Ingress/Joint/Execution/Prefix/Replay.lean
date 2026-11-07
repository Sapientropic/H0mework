import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Replay.Trace
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
private theorem resigns_literal_word (word : RawEvent Party Good Port Technology Instrument)
    (noConsents : ∀ request ∈ word, request.consents = []) :
    word.map (fun request => request.resign request.signer) = word := by
  induction word with
  | nil => rfl
  | cons request rest later =>
      rw [List.map_cons, request.resign_self (noConsents request List.mem_cons_self),
        later (fun next member => noConsents next (List.mem_cons_of_mem request member))]

theorem the_original_public_compiler_accepts_its_checked_word
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (word : RawEvent Party Good Port Technology Instrument)
    (noConsents : ∀ request ∈ word, request.consents = [])
    (valid : ∀ item ∈ (Physical.Public.interpreter input).rawItems before.raw word,
      (Physical.Public.interpreter input).Valid item.before item.request) :
    (Physical.Public.compile input before (.execute word)).isAccepted = true ∧
      (Physical.Public.compile input before (.execute word)).next.raw =
        (Physical.Public.interpreter input).next before.raw word := by
  unfold Physical.Public.compile
  simp only [Physical.Public.wordAt, resigns_literal_word word noConsents]
  split
  · exact ⟨rfl,rfl⟩
  · rename_i item member failed inspected
    exact (failed (valid item (by simpa only [resigns_literal_word word noConsents] using member))).elim

def reencoded (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :=
  Functions.Replay.wordAt input.law current word

theorem reencoded_consents_are_empty
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    ∀ request ∈ reencoded input current word, request.consents = [] := by
  rw [reencoded, Functions.Replay.replay_is_computed_from_the_original_actual_inventory input.law current 0 word]
  intro request member
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
  exact (Functions.Replay.the_computed_request_has_the_same_signer_and_no_consents input.law item.before item.request).2

/-- This changes the source representation of an already executed word;
the result is its original full next, never a second payment. -/
theorem reencoded_reads_the_same_original_next
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (word : RawEvent Party Good Port Technology Instrument) :
    (Physical.Public.compile input before (.execute (reencoded input before.raw word))).isAccepted = true ∧
      (Physical.Public.compile input before (.execute (reencoded input before.raw word))).next.raw =
        input.law.next before.raw word := by
  have checked := the_original_public_compiler_accepts_its_checked_word input before
    (reencoded input before.raw word) (reencoded_consents_are_empty input before.raw word)
    (fun item member =>
      (Functions.Replay.every_replay_item_is_lawful_and_has_no_controller_consents
        input.law before.raw 0 word item member).1)
  exact ⟨checked.1,checked.2.trans (Functions.Replay.replay_preserves_the_original_full_next input.law before.raw word)⟩

def publicReencoded (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :=
  Functions.Replay.wordAt (Physical.Public.interpreter input) current word

theorem public_reencoded_reads_the_same_original_next
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (word : RawEvent Party Good Port Technology Instrument) :
    (Physical.Public.compile input before (.execute (publicReencoded input before.raw word))).next.raw =
      (Physical.Public.interpreter input).next before.raw word := by
  let opened : ProgrammeSource.Input Party Good Port Technology Instrument :=
    { input with law := Physical.Public.interpreter input }
  have checked := the_original_public_compiler_accepts_its_checked_word input before
    (publicReencoded input before.raw word) (reencoded_consents_are_empty opened before.raw word)
    (fun item member =>
      (Functions.Replay.every_replay_item_is_lawful_and_has_no_controller_consents
        (Physical.Public.interpreter input) before.raw 0 word item member).1)
  exact checked.2.trans (Functions.Replay.replay_preserves_the_original_full_next
    (Physical.Public.interpreter input) before.raw word)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix
