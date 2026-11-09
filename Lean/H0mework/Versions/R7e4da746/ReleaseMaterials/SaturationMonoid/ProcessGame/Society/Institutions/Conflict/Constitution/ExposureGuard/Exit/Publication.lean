import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Checked Window)
open Quantities.Execution (endAt endAt_append inventory inventory_append next_input)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Conflict.Root.Cut Party Good Port Technology Instrument
local notation "W" => Window Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument

private theorem original_authority_of_checked {origin : C} {command : List Party}
    {community : Party → Community} {window : W} {word : Word}
    (checked : Checked origin command community true window word) :
    Reparation.Actual.SourceAuthority window.current word := by
  induction word generalizing window with
  | nil => exact fun _ listed => (List.not_mem_nil listed).elim
  | cons input tail earlier =>
    intro item listed
    change item ∈ inventory window.current ([input] ++ tail) at listed
    rw [inventory_append] at listed
    rcases List.mem_append.mp listed with here | later
    · exact (checked.1.originalAuthority rfl item here).2
    · have reached : item ∈ inventory (window.write input).current tail := by
        rw [Window.write_current, Window.nextCut]
        exact later
      have lawful := earlier checked.2 item reached
      rw [Window.write_current, Window.nextCut, next_input] at lawful
      exact lawful

variable {seed : Conflict.Root.Cut Party Good Port Technology Instrument}
  {community : Party → Community}
  {anchor history : Reparation.Actual.Script Party Good Port Technology Instrument}
  {control : RawCurrent Party Good Technology Instrument → List Party}

theorem Certificate.original_authority {word : Word}
    (verified : Certificate seed community anchor history control word) :
    Reparation.Actual.SourceAuthority (endAt seed history) word :=
  original_authority_of_checked verified.renewal.own

omit [DecidableEq Community] in
/-- Original signers choose the actual material items on their personal
lanes. The selected word carries no answer bits. -/
def SignersChose (answers : OwnerAnswers seed) : Word → Word → Prop
  | _, [] => True
  | past, input :: rest =>
    let items := Boundary.Actual.items (endAt seed past) input
    (∀ position : Fin items.length, answers past input position items[position].request.signer = true) ∧
      SignersChose answers (past ++ [input]) rest

omit [DecidableEq Community] in
theorem the_first_actual_signer_can_withhold_their_exit_item (answers : OwnerAnswers seed)
    (person : Party) (past : Word) (input : Reparation.Actual.Input Party Good Port Technology Instrument)
    (tail : Word) (position : Fin (Boundary.Actual.items (endAt seed past) input).length)
    (owner : (Boundary.Actual.items (endAt seed past) input)[position].request.signer = person) :
    ¬ SignersChose (withhold answers person) past (input :: tail) := by
  intro chosen
  have answer := chosen.1 position
  change withhold answers person past input position
    (Boundary.Actual.items (endAt seed past) input)[position].request.signer = true at answer
  rw [owner, withholding_uses_the_original_personal_lane] at answer
  cases answer

structure Chosen (answers : OwnerAnswers seed) where
  word : Word
  verified : Certificate seed community anchor history control word
  chosen : SignersChose answers history word

/-- Consume only a selected exit. Its exact certified word is passed to
the original whole-ledger continuation. -/
def exercise {answers : OwnerAnswers seed} (prior : Reparation.Actual.State seed community history)
    (choice : Chosen (community := community) (anchor := anchor) (history := history) (control := control) answers) :
    Reparation.Actual.Published seed community (history ++ choice.word) :=
  Reparation.Actual.publishAfter prior choice.word

theorem the_exercised_exit_consumes_the_retained_ledger_and_all_original_victims
    {answers : OwnerAnswers seed}
    (choice : Chosen (community := community) (anchor := anchor) (history := history) (control := control) answers) :
    let result := exercise (Reparation.Actual.run seed community history) choice
    Quantities.Recorded seed (history ++ choice.word) ∧
      result.next = Reparation.Actual.run seed community (history ++ choice.word) ∧
      Reparation.Actual.SourceAuthority (endAt seed history) choice.word ∧
      StandingAt (roster seed community anchor history) (endAt seed (history ++ choice.word)) ∧
      ∀ old ∈ Reparation.Actual.originalLosses seed community history,
        ∃ balance, ∃ row, result.next.read row = .inr (old, balance) := by
  refine ⟨(exercise (Reparation.Actual.run seed community history) choice).recorded,
    Reparation.Actual.publication_consumes_the_retained_visit seed community history choice.word,
    choice.verified.original_authority, ?_, Reparation.Actual.publication_keeps_every_previous_loss seed community history choice.word⟩
  rw [endAt_append]
  exact StandingAlong.at_original_cut (tail := [])
    (by simpa only [List.append_nil] using choice.verified.standing)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit
